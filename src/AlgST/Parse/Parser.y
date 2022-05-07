{
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
module AlgST.Parse.Parser
  ( -- * Parsers
    Parser
  , parseType
  , parseProg
  , parseKind
  , parseExpr

    -- * Running Parsers
  , feedParser
  , runParser
  , runParserIO
  , runParserSimple
  ) where

import           Control.Category              ((>>>), (<<<))
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Bifunctor
import qualified Data.DList                    as DL
import           Data.Foldable
import           Data.Functor.Identity
import           Data.List.NonEmpty            (NonEmpty(..))
import qualified Data.Map.Strict               as Map
import           Data.Maybe
import           Data.Monoid
import           Data.Proxy
import           Data.Sequence                 (Seq(..))
import qualified Data.Sequence                 as Seq
import           AlgST.Builtins.Names
import           AlgST.Parse.Lexer
import           AlgST.Parse.Operators
import           AlgST.Parse.ParseUtils
import           AlgST.Parse.Phase
import           AlgST.Syntax.Decl
import           AlgST.Syntax.Expression       as E
import qualified AlgST.Syntax.Kind             as K
import           AlgST.Syntax.Module
import           AlgST.Syntax.Name
import qualified AlgST.Syntax.Type             as T
import           AlgST.Util
import           AlgST.Util.Error
import           AlgST.Util.ErrorMessage
import           Syntax.Base

}

%name parseType_ Type
%name parseProg_ Prog
%name parseKind_ Kind
%name parseExpr_ Exp

%tokentype { Token }
%error { parseError }
%monad { ParseM } { (>>=) } { return }

%token
  nl       {TokenNL _}
  '()'     {TokenUnit _}
  '->'     {TokenUnArrow _}
  '-o'     {TokenLinArrow _}
  lambda   {TokenLambda _}
  '('      {TokenLParen _}
  ')'      {TokenRParen _}
  ','      {TokenComma _}
  '['      {TokenLBracket _}
  ']'      {TokenRBracket _}
  ':'      {TokenColon _}
  '!'      {TokenMOut _}
  '?'      {TokenMIn _}
  '{'      {TokenLBrace _}
  '}'      {TokenRBrace _}
  '_'      {TokenWild _}
  '.'      {TokenDot _}
  '(,)'    {TokenPairCon _}

  -- Identifiers. 'as' and '(*)' can appear as special syntax items.
  as        {TokenLowerId _ "as"}
  '(*)'     {TokenLowerId _ "(*)"}
  LOWER_ID  {TokenLowerId _ _}
  UPPER_ID  {TokenUpperId _ _}
  UPPER_IDq {TokenUpperIdQ _ _}
  -- Not yet used.
  -- LOWER_IDq {TokenLowerIdQ _ _}

  -- Operators. +/-/* can appear as special syntax items.
  '+'      {TokenOperator _ "+"}
  '-'      {TokenOperator _ "-"}
  '*'      {TokenOperator _ "*"}
  OPERATOR {TokenOperator _ _}

  KIND     {TokenKind _ _}
  INT      {TokenInt _ _}
  CHAR     {TokenChar _ _}
  STR      {TokenString _ _}
  rec      {TokenRec _}
  let      {TokenLet _}
  in       {TokenIn _}
  '='      {TokenEq _}
  data     {TokenData _}
  protocol {TokenProtocol _}
  type     {TokenType _}
  '|'      {TokenPipe _}
  if       {TokenIf _}
  then     {TokenThen _}
  else     {TokenElse _}
  new      {TokenNew _}
  select   {TokenSelect _}
  fork     {TokenFork _}
  fork_    {TokenFork_ _}
  case     {TokenCase _}
  of       {TokenOf _}
  forall   {TokenForall _}
  dualof   {TokenDualof _}
  end      {TokenEnd _}
  import   {TokenImport _}

%%

-------------
-- MODULES --
-------------

Prog :: { PModule -> ParseM PModule }
  : {- empty -}       { pure }
  | Decls             { \base -> runModuleBuilder base $1 }
  | Imports           { \base -> runModuleBuilder base $1 }
  | Imports NL Decls  { \base -> runModuleBuilder base ($1 >>> $3) }


NL :: { () }
  : nl      { () }
  | NL nl   { () }


-------------------------------------------------------------------------------
-- Imports
-------------------------------------------------------------------------------

Imports :: { ModuleBuilder }
  : Import              { addImport $1 }
  | Imports NL Import   { $1 <<< addImport $3 }

Import :: { Import }
  : import ModuleName ImportList {
      Import {
        importTarget = unL $2,
        importQualifier = emptyModuleName,
        importSelection = $3
      }
    }
  | import ModuleName as ModuleName ImportList {
      Import {
        importTarget = unL $2,
        importQualifier = unL $4,
        importSelection = $5
      }
    }

ImportList :: { ImportSelection }
  -- optional NL: allow closing parenthesis to appear in column 0.
  : {- empty -}                       { ImportAll [] }
  | '(*)'                             { ImportAll [] }
  | '()'                              { ImportOnly [] }
  | '(' opt(NL) ')'                   { ImportOnly [] }
  | '(' ImportSelection opt(NL) ')'   { $2 }

ImportSelection :: { ImportSelection }
  : ImportItems         opt(',')      { ImportOnly (DL.toList $1) }
  | '*'                 opt(',')      { ImportAll [] }
  | '*' ',' ImportItems opt(',')      { ImportAll (DL.toList $3) }

ImportItems :: { DL.DList ImportItem }
  : ImportItem                        { DL.singleton $1 }
  | ImportItems ',' ImportItem        { $1 `DL.snoc` $3 }

ImportItem :: { ImportItem }
  : UnqualifiedVar                    { ImportName (unL $1) }
  | UnqualifiedCon                    { ImportName (unL $1) }
  | UnqualifiedVar as '_'             { ImportHide (unL $1) }
  | UnqualifiedCon as '_'             { ImportHide (unL $1) }
  | UnqualifiedVar as UnqualifiedVar  { ImportRename (unL $1) (unL $3) }
  | UnqualifiedCon as UnqualifiedCon  { ImportRename (unL $1) (unL $3) }


-------------------------------------------------------------------------------
-- Declarations
-------------------------------------------------------------------------------

Decls :: { ModuleBuilder }
  : Decl          { $1 }
  | Decls NL Decl { $1 >>> $3 }

Decl :: { ModuleBuilder }
  -- Function signature
  : ProgVar TySig {
      moduleValueDecl $1 $2
    }
  -- Function declaration
  | ProgVar ValueParams '=' Exp {
      moduleValueBinding $1 $2 $4
    }
  -- Type abbreviation
  | type KindedTVar TypeParams '=' Type {% do
      let (name, mkind) = $2
      let decl = AliasDecl (OriginUser (pos $1)) TypeAlias
            { aliasParams = $3
            , aliasKind = mkind
            , aliasType = $5
            }
      pure $ moduleTypeDecl (unL name) decl
    }
  -- Datatype declaration
  | data KindedTVar TypeParams {% do
      let (name, mkind) = $2
      let decl = DataDecl (OriginUser (pos $1)) TypeNominal
            { nominalParams = $3
            , nominalKind = K.TU `fromMaybe` mkind
            , nominalConstructors = mempty
            }
      pure $ moduleTypeDecl (unL name) decl
    }
  | data KindedTVar TypeParams '=' DataCons {% do
      let (name, mkind) = $2
      let decl = DataDecl (OriginUser (pos $1)) TypeNominal
            { nominalParams = $3
            , nominalKind = K.TU `fromMaybe` mkind
            , nominalConstructors = $5
            }
      pure $ moduleTypeDecl (unL name) decl
    }
  | protocol KindedTVar TypeParams '=' DataCons {% do
      let (name, mkind) = $2
      let decl = ProtoDecl (OriginUser (pos $1)) TypeNominal
            { nominalParams = $3
            , nominalKind = K.P `fromMaybe` mkind
            , nominalConstructors = $5
            }
      pure $ moduleTypeDecl (unL name) decl
    }

TySig :: { PType }
  : ':' Type     { $2 }

TypeParams :: { [(Located (TypeVar PStage), K.Kind)] }
  : {- empty -}   { [] }
  | TypeParams1   { toList $1 }

-- A `forall` requires a non-empty list of type var bindings.
TypeParams1 :: { NonEmpty (Located (TypeVar PStage), K.Kind) }
  : bindings1(KindBind) {% $1 \(locName, _) -> Identity locName }

DataCons :: { Constructors PStage PType }
  : DataCon              {  uncurry Map.singleton $1 }
  | DataCons '|' DataCon {% uncurry insertNoDuplicates $3 $1 }

DataCon :: { (ProgVar PStage, (Pos, [PType])) }
  : Constructor TypeSeq { (unL $1, (pos $1, DL.toList $2)) }

ValueParams :: { [Located AName] }
  : bindings(ValueParam) {%
      let isAWildcard = either isWild isWild . unL
       in concat `fmap` $1 (filter (not . isAWildcard))
    }

ValueParam :: { [Located AName] }
  : ProgVarWild         { [fmap liftName $1] }
  | '[' TyVarList ']'   { DL.toList $2 }

TyVarList :: { DL.DList (Located AName) }
  : wildcard(TypeVar)                       { DL.singleton (fmap liftName $1) }
  | TyVarList ',' wildcard(TypeVar)         { $1 `DL.snoc` fmap liftName $3 }


-------------------------------------------------------------------------------
-- Expressions
-------------------------------------------------------------------------------

EAtom :: { PExp }
  : INT                            { let (TokenInt p x) = $1    in E.Lit p $ E.Int    x }
  | CHAR                           { let (TokenChar p x) = $1   in E.Lit p $ E.Char   x }
  | STR                            { let (TokenString p x) = $1 in E.Lit p $ E.String x }
  | '()'                           { E.Lit (pos $1) E.Unit }
  | '(,)'                          {% fatalError $ errorMisplacedPairCon @Values (pos $1) Proxy }
  | ProgVar                        { uncurryL E.Var $1 }
  | Constructor                    { uncurryL E.Con $1 }
  | '(' ExpInner ')'               {% $2 InParens }
  | '(' Exp ',' Exp ')'            { E.Pair (pos $1) $2 $4 }
  | case Exp of Cases              { E.Case (pos $1) $2 $4 }
  | new                            { E.Exp $ BuiltinNew (pos $1) }
  | fork                           { E.Exp $ BuiltinFork (pos $1) }
  | fork_                          { E.Exp $ BuiltinFork_ (pos $1) }

ETail :: { PExp }
  : LamExp                         { $1 }
  | if Exp then Exp else Exp       { E.Cond (pos $1) $2 $4 $6 }
  | let LetBind '=' Exp in Exp     { $2 (pos $1) $4 $6 }
  | RecExp                         {% $1 E.Rec }
  | let RecExp in Exp              {% $2 \p v t r ->
      E.UnLet (pos $1) v Nothing (E.Rec p v t r) $4
    }

EApp :: { PExp }
  : EAtom                          { $1 }
  | EApp EAtom                     { E.App (pos $1) $1 $2 }
  | EApp '[' TypeApps ']'          { E.foldTypeApps (const pos) $1 $3 }
  | select Constructor             { E.Select (pos $1) $2 }
  | select '(,)'                   { E.Select (pos $1) ($2 @- PairCon) }

EAppTail :: { PExp }
  : EApp                           { $1 }
  | ETail                          { $1 }
  | EApp ETail                     { E.App (pos $1) $1 $2 }

EOps :: { Parenthesized -> ParseM PExp }
  : OpsExp                        { \ps -> resolveOpSeq ps $1 }
  | OpTys                         { \ps -> resolveOpSeq ps $ Operator $1 Nil }
  | OpTys EAppTail                { \ps -> resolveOpSeq ps $ Operator $1 (Operand $2 Nil) }
  | OpTys OpsExp                  { \ps -> resolveOpSeq ps $ Operator $1 $2 }

ExpInner :: { Parenthesized -> ParseM PExp }
  : EOps                           { $1 }
  | EAppTail                       { const (pure $1) }

Exp :: { PExp }
  : ExpInner                       {% $1 TopLevel }

TypeApps :: { DL.DList PType }
  : Type                           { DL.singleton $1 }
  | TypeApps ',' Type              { $1 `DL.snoc` $3 }
  
RecExp :: { forall a. (Pos -> ProgVar PStage -> PType -> E.RecLam Parse -> a) -> ParseM a }
  : rec ProgVar TySig '=' Exp {
      \f -> case $5 of
        E.RecAbs r -> pure $ f (pos $1) (unL $2) $3 r
        _ -> fatalError $ errorRecNoTermLambda (pos $5)
    }

LetBind :: { Pos -> PExp -> PExp -> PExp }
  : ProgVarWild opt(TySig)        { \p -> E.UnLet p (unL $1) $2 }
  | Pattern                       { \p -> do
      let (pat, binds) = $1
      E.PatLet p (unL pat) binds
    }

LamExp :: { PExp }
  : lambda Abs Arrow Exp {% do
      let (build, Any anyTermAbs) = $2
      let (arrPos, arrMul) = $3
      when (arrMul == Lin && not anyTermAbs) do
        addErrors [errorNoTermLinLambda (pos $1) arrPos]
      pure $ appEndo (build arrMul) $4
    }

Abs :: { (Multiplicity -> Endo PExp, Any) }
  : bindings1(Abs1) {% do
      binds <- $1 $ \case
            p :@ Left (v, _)  | not (isWild v) -> Just (p @- Left v)
            p :@ Right (v, _) | not (isWild v) -> Just (p @- Right v)
            _ -> Nothing
      let termAbs loc (v, t) =
            ( \m -> Endo $ E.Abs @Parse loc . E.Bind loc m v t
            , Any True
            )
      let typeAbs loc (v, k) =
            ( \_ -> Endo $ E.TypeAbs @Parse loc . K.Bind loc v k
            , Any False
            )
      let build loc abs =
            either (termAbs loc) (typeAbs loc) abs
      pure $ foldMap (uncurryL build) binds
    }

Abs1 :: { Located (Either (ProgVar PStage, PType) (TypeVar PStage, K.Kind)) } 
  : '(' wildcard(ProgVar) ':' Type ')' { $2 @- Left (unL $2, $4) }
  | '[' wildcard(TypeVar) ':' Kind ']' { $2 @- Right (unL $2, unL $4) }

Cases :: { PCaseMap }
  : -- An empty case is not allowed. Accepting it here allows us to provide
    -- better error messages.
    '{' '}' { emptyCaseMap }
  | -- optional NL: The closing brace may be on column 0 of a new line. Usually
    -- NL separates declarations.
    '{' CaseMap opt(',') opt(NL) '}' { $2 }

CaseMap :: { PCaseMap }
  : Case             {% $1 emptyCaseMap }
  | CaseMap ',' Case {% $3 $1 }

Case :: { PCaseMap -> ParseM PCaseMap }
  : Pattern '->' Exp { \pcm -> do
      let (con, binds) = $1
      let branch = CaseBranch
            { branchPos = pos con
            , branchBinds = binds
            , branchExp = $3
            }
      cases <- insertNoDuplicates (unL con) branch (E.casesPatterns pcm)
      pure pcm{ E.casesPatterns = cases }
    }
  | ProgVarWild '->' Exp { \pcm -> do
      let wildBranch = CaseBranch
            { branchPos = pos $1
            , branchBinds = Identity $1
            , branchExp = $3
            }
      whenJust (E.casesWildcard pcm) \prevWild ->
        addErrors [errorMultipleWildcards prevWild wildBranch]
      pure pcm{ E.casesWildcard = Just wildBranch }
    }

Pattern :: { (Located (ProgVar PStage), [Located (ProgVar PStage)]) }
  : Constructor ProgVarWildSeq            { ($1, $2) }
  | '(,)' ProgVarWildSeq                  { ($1 @- PairCon, $2) }
  | '(' ProgVarWild ',' ProgVarWild ')'   {% do
      when (onUnL (==) $2 $4 && not (isWild (unL $2))) do
        addErrors [errorDuplicateBind $2 (pos $2) (pos $4)]
      pure ($1 @- PairCon, [$2, $4])
    }

ProgVarWildSeq :: { [Located (ProgVar PStage)] }
  : bindings(ProgVarWild)   {% $1 \v ->
      -- Only check for duplicates if it is not a wildcard.
      if isWild (unL v)
      then Nothing
      else Just v
    }

Op :: { Located (ProgVar PStage) }
  : OPERATOR  {% ($1 @-) `fmap` mkName (Unqualified (getText $1)) }
  | '+'       {% ($1 @-) `fmap` mkName (Unqualified "+") }
  | '-'       {% ($1 @-) `fmap` mkName (Unqualified "-") }
  | '*'       {% ($1 @-) `fmap` mkName (Unqualified "*") }

OpTys :: { (Located (ProgVar PStage), [PType]) }
  : OpTys_                    { DL.toList `fmap` $1 }

OpTys_ :: { (Located (ProgVar PStage), DL.DList PType) }
  : Op                        { ($1, DL.empty) }
  | OpTys_ '[' TypeApps ']'   { let (op, tys) = $1 in (op, tys <> $3) }

OpsExp :: { OpSeq OpsExp (Located (ProgVar PStage), [PType]) }
  : EApp OpTys           { Operand $1 $ Operator $2 Nil }
  | EApp OpTys EAppTail  { Operand $1 $ Operator $2 $ Operand $3 Nil }
  | EApp OpTys OpsExp    { Operand $1 $ Operator $2 $3 }


-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

-- polarised(t :: PType) :: PType
polarised(t)
  :     t              { $1 }
  | '+' polarised(t)   { $2 }
  | '-' polarised(t)   { T.Negate (pos $1) $2 :: PType }

TypeAtom :: { PType }
  : '()'                          { T.Unit (pos $1) }
  | '(,)'                         {% fatalError $ errorMisplacedPairCon @Types (pos $1) Proxy }
  | '(' Type ',' TupleType ')'    { T.Pair (pos $1) $2 $4 }
  | end                           { T.End (pos $1) }
  | TypeVar                       { uncurryL T.Var $1 }
  | TypeName                      { uncurryL T.Con $1 }
  | '(' Type ')'                  { $2 }

Type1 :: { PType }
  : TypeAtom                      { $1 }
  | Type1 polarised(TypeAtom)     { T.App (pos $1) $1 $2 }

Type2 :: { PType }
  : polarised(Type1)              { $1 }

Type3 :: { PType }
  : Type2                         { $1 }
  | Polarity Type2 '.' Type3      { uncurry T.Session $1 $2 $4 }

Type4 :: { PType }
  : Type3                         { $1 }
  | dualof Type4                  { T.Dualof (pos $1) $2 }

Type5 :: { PType }
  : Type4                         { $1 }
  | Type4 Arrow Type5             { uncurry T.Arrow $2 $1 $3 }
  | Forall Type5                  { $1 $2 }

Type :: { PType }
  : Type5                         { $1 }

Forall :: { PType -> PType }
  : forall TypeParams1 '.' { do
      let bind (v, k) = Endo $ T.Forall @Parse (pos $1) . uncurryL K.Bind v k
      appEndo $ foldMap bind $2
    }

TupleType :: { PType }
  : Type               { $1 }
  | Type ',' TupleType { T.Pair (pos $1) $1 $3 }

Arrow :: { (Pos, Multiplicity) }
  : '->' { (pos $1, Un) }
  | '-o' { (pos $1, Lin) }

Polarity :: { (Pos, T.Polarity) }
  : '!' { (pos $1, T.Out) }
  | '?' { (pos $1, T.In) }

-- A sequence of types to be used in a constructor declaration.
TypeSeq :: { DL.DList PType }
  : {- empty -}                     { DL.empty }
  | TypeSeq polarised(TypeAtom)     {  $1 `DL.snoc` $2 }
    -- TypeAtom by itself does not allow prefixing with +/- without wrapping in
    -- parentheses. The polarisation also can't be moved to TypeAtom since it
    -- has a lower precedence than type application


-------------------------------------------------------------------------------
-- Kinds
-------------------------------------------------------------------------------

Kind :: { Located K.Kind }
  : KIND { let TokenKind p k = $1 in p @- k }


-------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------

UnqualifiedCon :: { Located Unqualified }
  : UPPER_ID        { $1 @- Unqualified (getText $1) }
  | -- Allow the kinds to be used as constructor names.
    Kind            { $1 @- Unqualified (show (unL $1)) }

UnqualifiedVar :: { Located Unqualified }
  : LOWER_ID        { $1 @- Unqualified (getText $1) }
  | -- (*) is special syntax in import lists.
    '(*)'           { $1 @- Unqualified "(*)" }
  | -- 'as' is a contextual keyword.
    as              { $1 @- Unqualified "as" }

ModuleName :: { Located ModuleName }
  : UnqualifiedCon  { $1 @- ModuleName (getUnqualified (unL $1)) }
  | UPPER_IDq       { $1 @- ModuleName (getText $1) }

NameVar :: { Located UnscopedName }
  : UnqualifiedVar  {% traverse mkNameU $1 }

NameCon :: { Located UnscopedName }
  : UnqualifiedCon  {% traverse mkNameU $1 }

ProgVar :: { Located (ProgVar PStage) }
  : NameVar { scopeName `fmap` $1 }

Constructor :: { Located (ProgVar PStage) }
  : NameCon { scopeName `fmap` $1 }

ProgVarWild :: { Located (ProgVar PStage) }
  : wildcard(ProgVar)   { $1 }

TypeVar :: { Located (TypeVar PStage) }
  : NameVar { scopeName `fmap` $1 }

TypeName :: { Located (TypeVar PStage) }
  : NameCon { scopeName `fmap` $1 }

KindBind :: { (Located (TypeVar PStage), K.Kind) }
  : '(' TypeVar ':' Kind ')'  { ($2, unL $4) }
  | '(' TypeVar ')'           { ($2, K.TU) }
  | TypeVar                   { ($1, K.TU) }

KindedTVar :: { (Located (TypeVar PStage), Maybe K.Kind) }
  : TypeName ':' Kind { ($1, Just (unL $3)) }
  | TypeName          { ($1, Nothing) }

-- wildcard(v) : v ~ Located s => Located (Name s)
wildcard(v)
  : v     { $1 }
  | '_'   { $1 @- Wildcard }

-- bindings(p) :
--   (Foldable f, Eq a, Hashable a, ErrorMsg a) => (p -> f (Located a)) -> ParseM [p]
--
-- Parses a sequence of `p` and ensures that the extracted `a`s are different.
bindings(p)
  : bindings_(p) { fmap DL.toList . $1 Map.empty }

-- bindings1(p) :
--   (Foldable f, Eq a, Hashable a, ErrorMsg a) => (p -> f (Located a)) -> ParseM (NonEmpty p)
--
-- Like `bindings` but for a non-empty sequence.
bindings1(p)
  : p bindings_(p) { \extractAs -> do
      bound <- foldM
        (flip \(p :@ a) -> insertNoDuplicates a p)
        Map.empty
        (extractAs $1)
      ps <- $2 bound extractAs
      pure $ $1 :| DL.toList ps
    }

bindings_(p)
  : {- empty -} { \_ _ ->
      pure $ DL.empty
    }
  | bindings_(p) p { \bound extractAs -> do
      bound' <- foldM
        (flip \(p :@ a) -> insertNoDuplicates a p)
        bound
        (extractAs $2)
      ps <- $1 bound' extractAs
      pure $ ps `DL.snoc` $2
    }


-------------------------------------------------------------------------------
-- Generic Helpers
-------------------------------------------------------------------------------

-- opt(t) : Maybe t
opt(t)
  : {- empty -}  { Nothing }
  | t            { Just $1 }


{
newtype Parser a = Parser ([Token] -> ParseM a)
  deriving (Functor)

parseProg :: PModule -> Parser PModule
parseProg base = Parser \toks -> do
  mkP <- parseProg_ toks
  mkP base

parseType :: Parser PType
parseType = Parser $ parseType_ . dropNewlines

parseKind :: Parser K.Kind
parseKind = Parser $ fmap unL . parseKind_ . dropNewlines

parseExpr :: Parser PExp
parseExpr = Parser $ parseExpr_ . dropNewlines

feedParser :: Parser a -> String -> ParseM a
feedParser = flip lexer

runParser :: Parser a -> String -> Either (NonEmpty Diagnostic) a
runParser parser = runParseM (ModuleName "") . feedParser parser
-- TODO: Pass in the actual module.

-- | Runs a parser with the contents of the provided file. This function may
-- throw for all of the reasons 'readFile' may throw.
runParserIO :: Parser a -> FilePath -> IO (Either (NonEmpty Diagnostic) a)
runParserIO parser file = runParser parser <$> readFile file

-- | Runs a parser from on the given input string, returning either the
-- rendered errors (mode 'Plain') or the successfull result.
runParserSimple :: Parser a -> String -> Either String a
runParserSimple p = first (renderErrors Plain "" . toList) . runParser p

lexer :: String -> Parser a -> ParseM a
lexer str (Parser f) = either fatalError f $ scanTokens str

parseError :: [Token] -> ParseM a
parseError = fatalError <<< \case
  [] -> PosError defaultPos [Error "Unexpected end of file."]
  t:_ -> PosError (pos t) [Error "Unexpected token", Error t]
}
