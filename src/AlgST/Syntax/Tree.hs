{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module AlgST.Syntax.Tree
  ( LabTree,
    LabeledTree (..),
    drawLabeledTree,
    putLabeledTree,

    -- * Helpers & Re-exports
    Tree (..),
    tree,
    leaf,
    fieldMapTree,
  )
where

import AlgST.Parse.Unparser ()
import qualified AlgST.Syntax.Decl as D
import qualified AlgST.Syntax.Expression as E
import qualified AlgST.Syntax.Kind as K
import AlgST.Syntax.Program
import qualified AlgST.Syntax.Type as T
import AlgST.Syntax.Variable
import Control.Category ((>>>))
import Data.Foldable
import Data.Functor.Identity
import qualified Data.Map.Strict as Map
import Data.Tree
import Data.Void
import Syntax.Base

type LabTree = Tree String

class LabeledTree a where
  labeledTree :: a -> [LabTree]

drawLabeledTree :: LabeledTree a => a -> String
drawLabeledTree = labeledTree >>> drawForest

putLabeledTree :: LabeledTree a => a -> IO ()
putLabeledTree = drawLabeledTree >>> putStr

instance LabeledTree () where
  labeledTree _ = []

instance LabeledTree Void where
  labeledTree = absurd

instance LabeledTree a => LabeledTree (Maybe a) where
  labeledTree = concatMap labeledTree

instance LabeledTree a => LabeledTree [a] where
  labeledTree = pure . tree "" . map labeledTree

-- | @Pos@ values are ignored. They are not part of the tree visualization.
instance LabeledTree Pos where
  labeledTree _ = []

instance LabeledTree K.Kind where
  labeledTree = pure . leaf . show

instance LabeledTree TypeVar where
  labeledTree v = [leaf (intern v)]

instance LabeledTree ProgVar where
  labeledTree v = [leaf (intern v)]

instance LabeledTree E.Lit where
  labeledTree =
    pure . leaf . \case
      E.Unit -> "Lit.Unit"
      E.Int x -> "Lit.Int " ++ show x
      E.Char x -> "Lit.Char " ++ show x
      E.String x -> "Lit.String " ++ show x

instance (T.ForallX LabeledTree x, E.ForallX LabeledTree x) => LabeledTree (E.Exp x) where
  labeledTree =
    pure . \case
      E.Lit x l ->
        tree "Exp.Lit" [labeledTree x, labeledTree l]
      E.Var x v ->
        tree ("Exp.Var " ++ intern v) [labeledTree x]
      E.Con x v ->
        tree ("Exp.Con " ++ intern v) [labeledTree x]
      E.Abs x1 (E.Bind x2 m v t e) ->
        let label = unwords ["Exp.Abs", show m, intern v]
         in tree label [labeledTree x1, labeledTree x2, labeledTree t, labeledTree e]
      E.App x e1 e2 ->
        tree "Exp.App" [labeledTree x, labeledTree e1, labeledTree e2]
      E.Pair x e1 e2 ->
        tree "Exp.Pair" [labeledTree x, labeledTree e1, labeledTree e2]
      E.Cond x e1 e2 e3 ->
        tree "Exp.Cond" [labeledTree x, labeledTree e1, labeledTree e2, labeledTree e3]
      E.Case x e branches ->
        tree "Exp.Case" [labeledTree x, labeledTree e, fieldMapTree branches]
      E.TypeAbs x b ->
        let Node label ts = kbindNode "Exp.TypeAbs" b
         in Node label (labeledTree x ++ ts)
      E.TypeApp x e t ->
        tree "Exp.TypeApp" [labeledTree x, labeledTree e, labeledTree t]
      E.UnLet x v mty e1 e2 ->
        tree
          ("Exp.UnLet " ++ intern v)
          [ labeledTree x,
            foldMap labeledTree mty,
            labeledTree e1,
            labeledTree e2
          ]
      E.PatLet x c vs e1 e2 ->
        tree
          ("Exp.PatLet " ++ unwords (intern <$> c : vs))
          [ labeledTree x,
            labeledTree e1,
            labeledTree e2
          ]
      E.Rec x v ty e ->
        tree
          ("Exp.Rec " ++ intern v)
          [ labeledTree x,
            labeledTree ty,
            labeledTree (E.RecAbs e)
          ]
      E.New x t ->
        tree "Exp.New" [labeledTree x, labeledTree t]
      E.Select x c ->
        tree ("Exp.Select " ++ show c) [labeledTree x]
      E.Fork x e ->
        tree "Exp.Fork" [labeledTree x, labeledTree e]
      E.Fork_ x e ->
        tree "Exp.Fork_" [labeledTree x, labeledTree e]
      E.Exp x ->
        tree "Exp.Exp" [labeledTree x]

instance T.ForallX LabeledTree x => LabeledTree (T.Type x) where
  labeledTree =
    pure . \case
      T.Unit x ->
        tree
          "Type.Unit"
          [labeledTree x]
      T.Arrow x m t1 t2 ->
        tree
          ("Type.Arrow " ++ show m)
          [labeledTree x, labeledTree t1, labeledTree t2]
      T.Pair x t1 t2 ->
        tree
          "Type.Pair"
          [labeledTree x, labeledTree t1, labeledTree t2]
      T.Session x p t1 t2 ->
        tree
          ("Type.Session (" ++ show p ++ ")")
          [labeledTree x, labeledTree t1, labeledTree t2]
      T.End x ->
        tree
          "Type.End"
          [labeledTree x]
      T.Forall x b ->
        let t = kbindNode "Type.Forall" b
         in t {subForest = labeledTree x ++ subForest t}
      T.Var x v ->
        let label = "Type.Var " ++ intern v
         in tree label [labeledTree x]
      T.Con x v ->
        let label = "Type.Con " ++ intern v
         in tree label [labeledTree x]
      T.App x t1 t2 ->
        tree
          "Type.App"
          [labeledTree x, labeledTree t1, labeledTree t2]
      T.Negate x t ->
        tree
          "Type.Negate"
          [labeledTree x, labeledTree t]
      T.Dualof x t ->
        tree
          "Type.Dualof"
          [labeledTree x, labeledTree t]
      T.Type x ->
        tree
          "Type.Type"
          [labeledTree x]

instance (D.ForallDeclX LabeledTree x, T.ForallX LabeledTree x) => LabeledTree (D.TypeDecl x) where
  labeledTree =
    pure . \case
      D.AliasDecl x alias ->
        tree
          "AliasDecl"
          [ labeledTree x,
            typeAliasTree alias
          ]
      D.DataDecl x decl ->
        tree
          "DataDecl"
          [ labeledTree x,
            nominalDeclTree labeledTree decl
          ]
      D.ProtoDecl x decl ->
        tree
          "ProtoDecl"
          [ labeledTree x,
            nominalDeclTree labeledTree decl
          ]

instance LabeledTree D.Origin where
  labeledTree =
    pure . \case
      D.OriginUser _ -> leaf "OriginUser"
      D.OriginImport i -> leaf ("OriginImport " ++ i)
      D.OriginBuiltin -> leaf "OriginBuiltin"

instance T.ForallX LabeledTree x => LabeledTree (D.TypeAlias x) where
  labeledTree alias = pure $ tree "TypeAlias" [typeAliasTree alias]

typeAliasTree :: T.ForallX LabeledTree x => D.TypeAlias x -> [LabTree]
typeAliasTree D.TypeAlias {..} =
  [ Node "kind" [leaf (show aliasKind)],
    Node "parameters" (paramsTree aliasParams),
    Node "alias" $ labeledTree aliasType
  ]

nominalDeclTree :: (a -> [LabTree]) -> D.TypeNominal a -> [Tree [Char]]
nominalDeclTree f D.TypeNominal {..} =
  [ Node "kind" [leaf (show nominalKind)],
    Node "parameters" (paramsTree nominalParams),
    Node "constructors" $
      labeledMapTree (const . show) (\_ -> concatMap f . snd) nominalConstructors
  ]

paramsTree :: D.Params -> [LabTree]
paramsTree ps = [leaf $ "(" ++ show p ++ ":" ++ show k ++ ")" | (p, k) <- ps]

instance (T.ForallX LabeledTree x) => LabeledTree (D.SignatureDecl x) where
  labeledTree D.SignatureDecl {signatureOrigin = origin, signatureType = ty} =
    [ Node "origin" $ labeledTree origin,
      Node "type" $ labeledTree ty
    ]

instance (T.ForallX LabeledTree x, E.ForallX LabeledTree x) => LabeledTree (D.ValueDecl x) where
  labeledTree vd =
    [ Node "type" $ labeledTree $ D.valueType vd,
      Node "params" $ leaf . param <$> D.valueParams vd,
      Node "definition" $ labeledTree $ D.valueBody vd
    ]
    where
      param (Left pvar) = intern pvar
      param (Right tvar) = "[" ++ intern tvar ++ "]"

instance (D.ForallConX LabeledTree x, T.ForallX LabeledTree x) => LabeledTree (D.ConstructorDecl x) where
  labeledTree =
    pure . \case
      D.DataCon x parent params mul items ->
        tree
          ("Decl.DataCon (" ++ show parent ++ ")")
          [ labeledTree x,
            [Node "parameters" (paramsTree params)],
            [Node "multiplicity" [leaf (show mul)]],
            [tree "items" (labeledTree <$> items)]
          ]
      D.ProtocolCon x parent params items ->
        tree
          ("Decl.ProtocolCon (" ++ show parent ++ ")")
          [ labeledTree x,
            [Node "parameters" (paramsTree params)],
            [tree "items" (labeledTree <$> items)]
          ]

instance ForallX LabeledTree x => LabeledTree (Program x) where
  labeledTree pp = types ++ imports ++ values
    where
      types =
        labeledMapTree
          (\tv _ -> intern tv)
          (\_ td -> labeledTree td)
          (programTypes pp)
      imports =
        labeledMapTree
          (\pv _ -> intern pv)
          (\_ sig -> labeledTree sig)
          (programImports pp)
      values =
        labeledMapTree
          (\pv _ -> intern pv)
          (\_ d -> either labeledTree labeledTree d)
          (programValues pp)

labeledMapTree ::
  (a -> b -> String) ->
  (a -> b -> [LabTree]) ->
  Map.Map a b ->
  [LabTree]
labeledMapTree f g = fmap (\(a, b) -> Node (f a b) (g a b)) . Map.toList

kbindNode :: LabeledTree a => String -> K.Bind a -> LabTree
kbindNode con (K.Bind _ v k a) =
  let label = unwords [con, intern v ++ ":" ++ show k]
   in Node label $ labeledTree a

fieldMapTree ::
  (T.ForallX LabeledTree x, E.ForallX LabeledTree x, Foldable f, Foldable g) =>
  E.CaseMap' f g x ->
  [LabTree]
fieldMapTree m = conCases ++ wildCases
  where
    conCases =
      labeledMapTree
        (\v b -> unwords [intern x | x <- v : toList (E.branchBinds b)])
        (\_ b -> labeledTree $ E.branchExp b)
        (E.casesPatterns m)
    wildCases =
      [ Node (intern x) (labeledTree e)
        | E.CaseBranch
            { branchBinds = Identity x,
              branchExp = e
            } <-
            toList (E.casesWildcard m)
      ]

leaf :: a -> Tree a
leaf a = Node a []

tree :: a -> [[Tree a]] -> Tree a
tree a = Node a . concat
