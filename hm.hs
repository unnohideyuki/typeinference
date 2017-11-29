import Data.List (nub, (\\), union)
import Control.Monad.State.Strict (State, runState, get, put)

type Id = String

enumId :: Int -> Id
enumId n = "a" ++ show n

data Term = Var Id
          | Lam Id Term
          | App Term Term 
          | Let Id Term Term
          | If Term Term Term
          deriving Show

data Type = TVar Tyvar
          | TCon Tycon
          | TAp Type Type
          | TGen Int
          deriving (Show, Eq)

data Tyvar = Tyvar Id deriving (Show, Eq)
data Tycon = Tycon Id deriving (Show, Eq)

tBool :: Type
tBool = TCon (Tycon "Bool")

tInt :: Type
tInt = TCon (Tycon "Int")

tList :: Type
tList = TCon (Tycon "[]")

tArrow :: Type
tArrow = TCon (Tycon "->")

infixr 4 `fn`
fn :: Type -> Type -> Type
a `fn` b = TAp (TAp tArrow a) b

type Subst = [(Tyvar, Type)]

nullSubst :: Subst
nullSubst = []

infixr 4 @@
(@@) :: Subst -> Subst -> Subst
s1 @@ s2 = [(u, apply s1 t) | (u, t) <- s2] ++ s1

(+->) :: Tyvar -> Type -> Subst
u +-> t = [(u, t)]

class Types t where
  apply :: Subst -> t -> t
  tv :: t -> [Tyvar]

instance Types Type where
  apply s (TVar u) = case lookup u s of
                       Just t -> t
                       Nothing -> TVar u
  apply s (TAp l r) = TAp (apply s l) (apply s r)
  apply _ t = t

  tv (TVar u) = [u]
  tv (TAp l r) = tv l `union` tv r
  tv _ = []

instance Types a => Types [a] where
  apply s = fmap $ apply s
  tv = nub.concat.fmap tv

data Scheme = Scheme Int Type
            deriving Show

instance Types Scheme where
  apply s (Scheme n t) = Scheme n (apply s t)
  tv (Scheme _ t) = tv t

data Assump = Id :>: Scheme
            deriving Show

instance Types Assump where
  apply s (i :>: sc) = i :>: (apply s sc)
  tv (_ :>: sc) = tv sc

gen :: [Assump] -> Type -> Scheme
gen as t = Scheme n (apply s t)
  where gs = tv t \\ tv as
        n = length gs
        s = zip gs (map TGen [0..])

find :: Monad m => Id -> [Assump] -> m Scheme
find i [] = fail $ "unbound identifier: " ++ i
find i ((i':>:sc):as) = if i==i' then return sc else find i as

mgu :: Monad m => Type -> Type -> m Subst

mgu (TAp l r) (TAp l' r') = do s1 <- mgu l l'
                               s2 <- mgu (apply s1 r) (apply s1 r')
                               return (s2@@s1)
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu (TCon tc1)(TCon tc2) | tc1 == tc2 = return nullSubst
mgu _ _ = fail "types do not unify"

varBind :: Monad m => Tyvar -> Type -> m Subst
varBind u t | t == TVar u   = return nullSubst
            | u `elem` tv t = fail "occurs check fails"
            | otherwise     = return (u +-> t)

type TI a = State (Subst, Int) a

runTI :: TI a -> a
runTI ti = x where (x, _) = runState ti (nullSubst, 0)

newTVar :: TI Type
newTVar = do (s, n) <- get
             put (s, n+1)
             return (TVar (Tyvar (enumId n)))

freshInst :: Scheme -> TI Type
freshInst (Scheme n t) = do ts <- sequence $ replicate n newTVar
                            return (inst ts t)

unify :: Type -> Type -> TI ()
unify t1 t2 = do (s, n) <- get
                 u <- mgu (apply s t1) (apply s t2)
                 put (u@@s, n)

class Instantiate t where
  inst :: [Type] -> t -> t

instance Instantiate Type where
  inst ts (TAp l r) = TAp (inst ts l) (inst ts r)
  inst ts (TGen n) = ts!!n
  inst _ t = t

getSubst :: TI Subst
getSubst = do (s, _) <- get
              return s

tpTerm :: [Assump] -> Term -> Type -> TI ()

tpTerm as (Var x) t = do sc <- find x as
                         t' <- freshInst sc
                         unify t' t

tpTerm as (Lam x e) t = do a <- newTVar
                           b <- newTVar
                           unify t (a `fn` b)
                           let as' = (x :>: Scheme 0 a):as
                           tpTerm as' e b

tpTerm as (App e1 e2) t = do a <- newTVar
                             tpTerm as e1 (a `fn` t)
                             tpTerm as e2 a

tpTerm as (Let x e1 e2) t = do a <- newTVar
                               tpTerm as e1 a
                               s <- getSubst
                               let as' = (x :>: gen as (apply s a)):as
                               tpTerm as' e2 t
                               
tpTerm as (If e1 e2 e3) t = do tpTerm as e1 tBool
                               a <- newTVar
                               tpTerm as e2 a
                               tpTerm as e3 a
                               s <- getSubst
                               unify t (apply s a)

typeOf :: [Assump] -> Term -> TI Type
typeOf as e = do a <- newTVar
                 tpTerm as e a
                 s <- getSubst
                 return (apply s a)

prims :: [Assump]
prims = [ "true"  :>: gen' tBool
        , "false" :>: gen' tBool
        , "0"     :>: gen' tInt
        , "succ"  :>: gen' (tInt `fn` tInt)
        , "[]"    :>: gen' listTy
        , ":"     :>: gen' (a `fn` listTy `fn` listTy)
        , "null"  :>: gen' (listTy `fn` tBool)
        , "head"  :>: gen' (listTy `fn` a)
        , "tail"  :>: gen' (listTy `fn` listTy)
        ]
  where gen' = gen []
        a = TVar (Tyvar "a")
        listTy = (TAp tList a)

testInfer :: Term -> Type
testInfer e = runTI $ typeOf prims e

main = putStrLn $ show $ testInfer teA
  where
    te1 = (Lam "x" (App (App (Var ":") (Var "x")) (Var "[]")))
    te2 = Var "[]"
    te3 = (Lam "x" te2)
    te4 = If (Var "true") (Var "false") (Var "0") -- error
    te5 = If (Var "true") (Var "0") (App (Var "succ") (Var "0"))
    te6 = If (Var "0") (Var "false") (Var "true")

    te7 = (App (App (Var ":") (Var "0")) (Var "[]"))
    te8 = (App (App (Var ":") (Var "0")) te7)
    te9 = (App (App (Var ":") (Var "true")) te7) -- error
    teA = Let "y" (Var "succ") (App (Var "y") (Var "0"))

