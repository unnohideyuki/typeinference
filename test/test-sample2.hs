import HMTI

import Test.Hspec
import Control.Exception (evaluate)

main :: IO ()
main = hspec $ do
  describe "An example from the Scala By Example" $ do
    it "returns a4->[a4]" $ do
      let t = Lam "x" (App (App (Var ":") (Var "x")) (Var "[]"))
          e = TAp (TAp (TCon (Tycon "->")) (TVar (Tyvar "a4")))
                  (TAp (TCon (Tycon "[]")) (TVar (Tyvar "a4")))
      testInfer t `shouldBe` e
