module Main where

import HMTI

main :: IO ()
main = putStrLn $ show $ testInfer t
  where t = Lam "x" (App (App (Var ":") (Var "x")) (Var "[]"))
        e = TAp (TAp (TCon (Tycon "->")) (TVar (Tyvar "a4")))
                (TAp (TCon (Tycon "[]")) (TVar (Tyvar "a4")))

