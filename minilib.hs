import Prelude hiding(succ, pred)

data Int' = Zero | Succ Int'
          deriving Show

true :: Bool
true = True

false :: Bool
false = False

zero :: Int'
zero = Zero

succ :: Int' -> Int'
succ n = Succ n

pred :: Int' -> Int'
pred Zero = zero
pred (Succ n) = n

iszero :: Int' -> Bool
iszero Zero = true
iszero _ = false
