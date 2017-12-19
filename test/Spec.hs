import HMTI

import Test.Hspec
import Control.Exception (evaluate)

main :: IO ()
main = hspec $ do
  describe "Predefined variables" $ do
    it "returns tBool" $ do
      testInfer (Var "true") `shouldBe` tBool
    it "returns tBool" $ do
      testInfer (Var "false") `shouldBe` tBool

  describe "Invalid terms" $ do
    it "throws an exception with 'if true then false else zero'" $ do
      let t = If (Var "true") (Var "false") (Var "zero")
      evaluate (testInfer t) `shouldThrow` anyException
