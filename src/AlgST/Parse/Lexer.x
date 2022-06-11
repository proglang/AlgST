{
{-# LANGUAGE StrictData #-}

module AlgST.Parse.Lexer
( Token(..)
, scanTokens
, dropNewlines
) where

import qualified AlgST.Syntax.Kind as K
import           AlgST.Util.ErrorMessage
import           AlgST.Util.Output
import           Syntax.Base
}

%wrapper "posn"

$greek = [\880-\1023] -- # λ  -- forall not in range ([λ ∀])

$upperA  = [A-Z]
$upper = [$upperA$greek]

-- $lowerU  = \x02 -- Trick Alex into handling Unicode. See [Unicode in Alex].
$lowerA = [a-z]
$lower = [$lowerA$greek\_] --  $greek \_]

$letter = [$lower$upper$greek]

-- $unidigit  = \x03
$ascdigit = 0-9
$digit = [$ascdigit] -- $unidigit]

$opsymbol = [\!\#\$\%\&\+\-\*\/\<\=\>\@\\\^\|\~\:≤≠≥∧∨]
@operator = $opsymbol+

$alphaNumeric = [$letter$digit\_\']

$eol=[\n]

@blockComment = "{-" (\-[^\}]|[^\-]|\n)* "-}"

$greekId = [λ ∀]
@lowerId = ($lower # $greekId) $alphaNumeric*
@upperId = ($upper # $greekId) $alphaNumeric*

-- Supported escape sequences:
--
--  \n \" \' \\
@escape = \\ [\\ \" \' n]
@char   = \' (@escape | [^ \\ \']) \'
@string = \" (@escape | [^ \\ \"])* \"

tokens :-
  $white*$eol+                  { simpleToken TokenNL }
  $white+                       ;
  $white*"--".*                 ;
  @blockComment                 ;
  ("->"|→)                      { simpleToken TokenUnArrow }
  ("-o"|⊸)                      { simpleToken TokenLinArrow }
  [\\ λ]                        { simpleToken TokenLambda }
  "("                           { simpleToken TokenLParen }
  ")"                           { simpleToken TokenRParen }
  "["                           { simpleToken TokenLBracket }
  "]"                           { simpleToken TokenRBracket }
  "{"                           { simpleToken TokenLBrace }
  "}"                           { simpleToken TokenRBrace }
  ","                           { simpleToken TokenComma }
  ":"                           { simpleToken TokenColon }
  "!"                           { simpleToken TokenMOut }
  "?"                           { simpleToken TokenMIn }
  "."                           { simpleToken TokenDot }
  "="                           { simpleToken TokenEq }
  "|"                           { simpleToken TokenPipe }
  "_"                           { simpleToken TokenWild }
-- Kinds
  SU                            { simpleToken \p -> TokenKind (p @- K.SU) }
  SL                            { simpleToken \p -> TokenKind (p @- K.SL) }
  TU                            { simpleToken \p -> TokenKind (p @- K.TU) }
  TL                            { simpleToken \p -> TokenKind (p @- K.TL) }
  MU                            { simpleToken \p -> TokenKind (p @- K.MU) }
  ML                            { simpleToken \p -> TokenKind (p @- K.ML) }
  P                             { simpleToken \p -> TokenKind (p @- K.P)  }
-- Keywords
  rec                           { simpleToken TokenRec }
  let                           { simpleToken TokenLet }
  in                            { simpleToken TokenIn }
  data                          { simpleToken TokenData }
  protocol                      { simpleToken TokenProtocol }
  type                          { simpleToken TokenType }
  if                            { simpleToken TokenIf }
  then                          { simpleToken TokenThen }
  else                          { simpleToken TokenElse }
  new                           { simpleToken TokenNew }
  select                        { simpleToken TokenSelect }
  fork                          { simpleToken TokenFork }
  fork_                         { simpleToken TokenFork_ }
  case                          { simpleToken TokenCase }
  of                            { simpleToken TokenOf }
  (forall|∀)                    { simpleToken TokenForall }
  dual                          { simpleToken TokenDualof }
  end                           { simpleToken TokenEnd }
  import                        { simpleToken TokenImport }
-- Values
  \(\)                          { simpleToken TokenUnit }
  (0+|[1-9]$digit*)             { textToken' read TokenInt }
  @char                         { textToken' read TokenChar }
  @string                       { textToken' read TokenString }
-- Identifiers
  @operator                     { textToken TokenOperator }
  "(" @operator ")"             { textToken TokenLowerId }
  @lowerId                      { textToken TokenLowerId }
  @upperId                      { textToken TokenUpperId }
  "(,)"                         { simpleToken TokenPairCon }

{

data Token =
    TokenNL Pos
  | TokenUnit Pos
  | TokenLambda Pos
  | TokenUnArrow Pos
  | TokenLinArrow Pos
  | TokenLParen Pos
  | TokenRParen Pos
  | TokenLBracket Pos
  | TokenRBracket Pos
  | TokenComma Pos
  | TokenColon Pos
  | TokenUpperId (Located String)
  | TokenPairCon Pos
  | TokenMOut Pos
  | TokenMIn Pos
  | TokenLBrace Pos
  | TokenRBrace Pos
  | TokenDot Pos
  | TokenLowerId (Located String)
  | TokenOperator (Located String)
  | TokenKind (Located K.Kind)
  | TokenInt (Located Integer)
  | TokenChar (Located Char)
  | TokenString (Located String)
  | TokenBool (Located Bool)
  | TokenRec Pos
  | TokenLet Pos
  | TokenIn Pos
  | TokenEq Pos
  | TokenData Pos
  | TokenProtocol Pos
  | TokenType Pos
  | TokenPipe Pos
  | TokenIf Pos
  | TokenThen Pos
  | TokenElse Pos
  | TokenNew Pos
  | TokenSelect Pos
  | TokenFork Pos
  | TokenFork_ Pos
  | TokenCase Pos
  | TokenOf Pos
  | TokenForall Pos
  | TokenDualof Pos
  | TokenEnd Pos
  | TokenWild Pos
  | TokenImport Pos

instance Show Token where
  show (TokenNL _) = "\\n"
  show (TokenUnit _) = "()"
  show (TokenLambda _) = "λ"
  show (TokenUnArrow _) = "->"
  show (TokenLinArrow _) = "-o"
  show (TokenLParen _) = "("
  show (TokenRParen _) = ")"
  show (TokenLBracket _) = "["
  show (TokenRBracket _) = "]"
  show (TokenComma _) = ","
  show (TokenColon _) = ":"
  show (TokenUpperId (_ :@ c)) = c
  show (TokenPairCon _) = "(,)"
  show (TokenMOut _) = "!"
  show (TokenMIn _) = "?"
  show (TokenLBrace _) = "{"
  show (TokenRBrace _) = "}"
  show (TokenDot _) = "."
  show (TokenLowerId (_ :@ s)) = s
  show (TokenOperator (_ :@ s)) = s
  show (TokenKind (_ :@ k)) = show k
  show (TokenInt (_ :@ i)) = show i
  show (TokenChar (_ :@ c)) = show c
  show (TokenBool (_ :@ b)) = show b
  show (TokenString (_ :@ s)) = s
  show (TokenRec _) = "rec"
  show (TokenLet _) = "let"
  show (TokenIn _) = "in"
  show (TokenEq _) = "="
  show (TokenData _) = "data"
  show (TokenProtocol _) = "protocol"
  show (TokenType _) = "type"
  show (TokenPipe _) = "|"
  show (TokenIf _) = "if"
  show (TokenThen _) = "then"
  show (TokenElse _) = "else"
  show (TokenNew _) = "new"
  show (TokenSelect _) = "select"
  show (TokenFork _) = "fork"
  show (TokenFork_ _) = "fork_"
  show (TokenCase _) = "case"
  show (TokenForall _) = "forall"
  show (TokenWild _) = "_"
  show (TokenOf _) = "of"
  show (TokenDualof _) = "dualof"
  show (TokenEnd _) = "end"
  show (TokenImport _) = "import"

scanTokens :: String -> Either Diagnostic [Token]
scanTokens str = trim <$> go (alexStartPos, '\n', [], str)
  where
    go inp@(pos,_,_,str) =
      case alexScan inp 0 of
        AlexEOF ->
          Right []
        AlexError _ ->
          Left $ PosError (internalPos pos)
            [ Error "Unexpected error on input"
            , Error $ Unexpected $ head str
            ]
        AlexSkip  inp' _len ->
          go inp'
        AlexToken inp' len act ->
          (act pos (take len str) :) <$> go inp'

newtype Unexpected = Unexpected Char

instance ErrorMsg Unexpected where
  msg (Unexpected c) = show c
  msgStyling _ = redFGStyling

instance ErrorMsg Token where
  msg = show
  msgStyling _ = redFGStyling

getLineNum :: AlexPosn -> Int
getLineNum (AlexPn _offset lineNum _colNum) = lineNum

getColumnNum :: AlexPosn -> Int
getColumnNum (AlexPn _offset _lineNum colNum) = colNum

-- Trim newlines
trim :: [Token] -> [Token]
trim = reverse . trim' . reverse . trim'
  where
    trim' :: [Token] -> [Token]
    trim' [] = []
    trim' (TokenNL _ : ts) = trim' ts
    trim' ts = ts

dropNewlines :: [Token] -> [Token]
dropNewlines = filter \case
  TokenNL _ -> False
  _         -> True

-- POSITIONS

internalPos :: AlexPosn -> Pos
internalPos (AlexPn _ l c) = Pos l c

instance Position Token where
  pos (TokenNL p) = p
  pos (TokenUnit p) = p
  pos (TokenLambda p) = p
  pos (TokenUnArrow p) = p
  pos (TokenLinArrow p) = p
  pos (TokenLParen p) = p
  pos (TokenRParen p) = p
  pos (TokenLBracket p) = p
  pos (TokenRBracket p) = p
  pos (TokenComma p) = p
  pos (TokenColon p) = p
  pos (TokenUpperId (p :@ _)) = p
  pos (TokenPairCon p) = p
  pos (TokenMOut p) = p
  pos (TokenMIn p) = p
  pos (TokenLBrace p) = p
  pos (TokenRBrace p) = p
  pos (TokenDot p) = p
  pos (TokenLowerId (p :@ _)) = p
  pos (TokenOperator (p :@ _)) = p
  pos (TokenKind (p :@ _)) = p
  pos (TokenInt (p :@ _)) = p
  pos (TokenChar (p :@ _)) = p
  pos (TokenBool (p :@ _)) = p
  pos (TokenString (p :@ _)) = p
  pos (TokenRec p) = p
  pos (TokenLet p) = p
  pos (TokenIn p) = p
  pos (TokenEq p) = p
  pos (TokenData p) = p
  pos (TokenProtocol p) = p
  pos (TokenType p) = p
  pos (TokenPipe p) = p
  pos (TokenNew p) = p
  pos (TokenSelect p) = p
  pos (TokenFork p) = p
  pos (TokenFork_ p) = p
  pos (TokenCase p) = p
  pos (TokenForall p) = p
  pos (TokenWild p) = p
  pos (TokenIf p) = p
  pos (TokenThen p) = p
  pos (TokenElse p) = p
  pos (TokenOf p) = p
  pos (TokenDualof p) = p
  pos (TokenEnd p) = p
  pos (TokenImport p) = p

simpleToken :: (Pos -> t) -> AlexPosn -> a -> t
simpleToken t p _ = t (internalPos p)

textToken :: (Located String -> t) -> AlexPosn -> String -> t
textToken = textToken' id

textToken' :: (String -> a) -> (Located a -> t) -> AlexPosn -> String -> t
textToken' f t p s = t (internalPos p @- f s)
}
