
module RegExp.RegExpSpec (spec) where

import Test.Hspec
import Test.QuickCheck

import RegExp.RegExp
import RegExp.Derivative (matches)

import Data.GSet()


spec :: Spec
spec = do
    describe "zero" $ do
        it "does not match the empty string" $ do
            (rZero `matches` "") `shouldBe` False
        it "does not match non-empty strings" $ do
            (rZero `matches` "a") `shouldBe` False
            (rZero `matches` "abc") `shouldBe` False
        it "does not match any string" $ do
            property $ \(w :: String) -> (rZero `matches` w) `shouldBe` False

    describe "one" $ do
        it "matches the empty string" $ do
            (rOne `matches` "") `shouldBe` True
        it "does not match non-empty strings" $ do
            property $ \c (w :: String) -> (rZero `matches` (c : w)) `shouldBe` False

    describe "times" $ do
        it "matches when both subexpressions match in order" $ do
            let r1 = "abc"
            let r2 = "def"
            (rTimes r1 r2 `matches` "af") `shouldBe` True

    describe "plus" $ do
        it "matches when either subexpression matches" $ do
            let r1 = "abc"
            let r2 = "def"
            (rPlus r1 r2 `matches` "a") `shouldBe` True

    describe "star" $ do
        it "matches the empty string" $ do
            (rStar "abc" `matches` "") `shouldBe` True
        it "matches once" $ do
            (rStar "abc" `matches` "c") `shouldBe` True
        it "matches multiple times" $ do
            (rStar "abc" `matches` "abcbabc") `shouldBe` True

    describe "literal" $ do
        it "matches one of the options" $ do
            (rLiteral "ab" `matches` "a") `shouldBe` True
            (rLiteral "ab" `matches` "b") `shouldBe` True
        it "does not match characters not in the class" $ do
            (rLiteral "ab" `matches` "c") `shouldBe` False