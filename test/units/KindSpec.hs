{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module KindSpec (spec) where

import Data.Foldable
import AlgST.Parse.Unparser ()
import AlgST.Syntax.Kind ((<=?))
import Syntax.Base
import Test.Hspec
import qualified AlgST.Syntax.Kind as K
import AlgST.Parse.Parser

spec :: Spec
spec = do
    it "correctly retrieves multiplicity information" do
        K.multiplicity tl `shouldBe` Just Lin
        K.multiplicity tu `shouldBe` Just Un
        K.multiplicity ml `shouldBe` Just Lin
        K.multiplicity mu `shouldBe` Just Un
        K.multiplicity sl `shouldBe` Just Lin
        K.multiplicity su `shouldBe` Just Un
        K.multiplicity p  `shouldBe` Nothing

    it "parses all kinds correctly" do
      for_ allKinds \k ->
        case runParserSimple parseKind (show k) of
          Left e -> expectationFailure $ "can't parse kind " ++ show k ++ "\n" ++ e
          Right k' -> k `shouldBe` k'

    describe "partial order" do
        it "is reflexive" do
            allKinds `allShouldSatisfy` \k ->
                k <=? k

        it "is antisymmetric" do
            let ks = (,) <$> allKinds <*> allKinds
            ks `allShouldSatisfy` \(k1, k2) ->
                k1 <=? k2 && k2 <=? k1  ==>  k1 == k2

        it "is transitive" do
            let ks = (,,) <$> allKinds <*> allKinds <*> allKinds
            ks `allShouldSatisfy` \(k1, k2, k3) ->
                k1 <=? k2 && k2 <=? k3  ==>  k1 <=? k3

        it "P is the superkind of all kinds" do
            allKinds `allShouldSatisfy` \k ->
                k <=? p

            allKinds `allShouldSatisfy` \k ->
                (p <=? k)  ==  (k == p)

    describe "least upper bound" do
        it "returns a known kind" do
            let ks = (,) <$> allKinds <*> allKinds
            ks `allShouldSatisfy` \(k1, k2) ->
                K.leastUpperBound k1 k2 `elem` allKinds

        it "returns a superkind of both" do
            let ks = (,) <$> allKinds <*> allKinds
            ks `allShouldSatisfy` \(k1, k2) -> do
                let k = K.leastUpperBound k1 k2
                k1 <=? k && k2 <=? k

        it "has P as the maximum kind" do
            allKinds `allShouldSatisfy` \k ->
                K.leastUpperBound k p == p

        it "is commutative" do
            let ks = (,) <$> allKinds <*> allKinds
            ks `allShouldSatisfy` \(k1, k2) ->
                K.leastUpperBound k1 k2  ==  K.leastUpperBound k2 k1

        it "is associative" do
            let ks = (,,) <$> allKinds <*> allKinds <*> allKinds
            ks `allShouldSatisfy` \(k1, k2, k3) -> do
                let a = do
                      let k = K.leastUpperBound k2 k3
                      K.leastUpperBound k1 k
                let b = do
                      let k = K.leastUpperBound k1 k2
                      K.leastUpperBound k k3
                a == b

        it "is idempotent" do
            let ks = (,) <$> allKinds <*> allKinds
            ks `allShouldSatisfy` \(k1, k2) -> do
                let k = K.leastUpperBound k1 k2
                k  ==  (K.leastUpperBound k1 k)

            ks `allShouldSatisfy` \(k1, k2) -> do
                let k = K.leastUpperBound k1 k2
                k  ==  (K.leastUpperBound k2 k)

tl, tu, ml, mu, sl, su, p :: K.Kind
tl = K.TL defaultPos
tu = K.TU defaultPos
ml = K.ML defaultPos
mu = K.MU defaultPos
sl = K.SL defaultPos
su = K.SU defaultPos
p  = K.P  defaultPos

allKinds :: [K.Kind]
allKinds = [tl, tu, ml, mu, sl, su, p]

infix 1 ==>

class Implication a b | a -> b where
    (==>) :: a -> b -> Bool

instance Implication Bool Bool where
    False ==> _ = True
    True  ==> x = x

instance Implication (Maybe a) (a -> Bool) where
    Nothing ==> _ = True
    Just a  ==> p = p a


allShouldSatisfy :: (HasCallStack, Show a, Foldable f) => f a -> (a -> Bool) -> Expectation
allShouldSatisfy as f = for_ as \a -> a `shouldSatisfy` f
