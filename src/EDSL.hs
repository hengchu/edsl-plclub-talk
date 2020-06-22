{-# LANGUAGE AllowAmbiguousTypes #-}

module EDSL where

import Control.Monad
import Type.Reflection (Typeable(..))

infixr 2 .||
infixr 3 .&&
infix  4 .==, ./=, .<, .<=, .>, .>=
class SynBool a where
  neg   :: a -> a
  (.&&) :: a -> a -> a
  (.||) :: a -> a -> a

class SynBool (SynBoolType a) => SynOrd a where
  type SynBoolType a :: *

  (.==) :: a -> a -> SynBoolType a
  (./=) :: a -> a -> SynBoolType a
  (.<)  :: a -> a -> SynBoolType a
  (.<=) :: a -> a -> SynBoolType a
  (.>)  :: a -> a -> SynBoolType a
  (.>=) :: a -> a -> SynBoolType a

class Syntactic (a :: *) where
  type DeepType a :: *

  toDeepRepr   :: a -> Expr (DeepType a)
  fromDeepRepr :: Expr (DeepType a) -> a

class (Monad m, Typeable m, Typeable int, Num int) => MonadGetInt int m | m -> int where
  getInt :: m int

newtype Codensity (m :: * -> *) (a :: *) = Codensity {
  runCodensity :: forall r. (a -> Expr (m r)) -> Expr (m r)
  }

instance Functor (Codensity m) where
  -- fmap :: (a -> b) -> Codensity m a -> Codensity m b
  fmap f (runCodensity -> x) = Codensity $ \k ->
    x (k . f)

instance Applicative (Codensity m) where
  pure a = Codensity $ \k -> k a

  -- (<*>) :: Codensity m (a -> b) -> Codensity m a -> Codensity m b
  f <*> a = liftM2 ($) f a

instance Monad (Codensity m) where
  return = pure

  -- (>>=) :: Codensity m a -> (a -> Codensity m b) -> Codensity m b
  (Codensity a) >>= f = Codensity $ \k ->
    a (\k' -> runCodensity (f k') k)

data Expr :: * -> * where
  Val    :: a -> Expr a
  Abs    :: (Expr a -> Expr b) -> Expr (a -> b)
  App    :: Expr (a -> b) -> Expr a -> Expr b
  Bind   :: Monad m => Expr (m a) -> (Expr a -> Expr (m b)) -> Expr (m b)
  Return :: Monad m => Expr a -> Expr (m a)

  Crash  :: String -> Expr a

  IsEq  :: SynOrd a => Expr a -> Expr a -> Expr (SynBoolType a)
  IsNeq :: SynOrd a => Expr a -> Expr a -> Expr (SynBoolType a)
  IsLt  :: SynOrd a => Expr a -> Expr a -> Expr (SynBoolType a)
  IsLe  :: SynOrd a => Expr a -> Expr a -> Expr (SynBoolType a)
  IsGt  :: SynOrd a => Expr a -> Expr a -> Expr (SynBoolType a)
  IsGe  :: SynOrd a => Expr a -> Expr a -> Expr (SynBoolType a)

  GetInt :: MonadGetInt int m => Expr (m int)

  NumAdd  :: Num a => Expr a -> Expr a -> Expr a
  NumSub  :: Num a => Expr a -> Expr a -> Expr a
  NumMult :: Num a => Expr a -> Expr a -> Expr a
  NumAbs  :: Num a => Expr a -> Expr a
  Signum  :: Num a => Expr a -> Expr a

  Neg    :: SynBool bool => Expr bool -> Expr bool
  And    :: SynBool bool => Expr bool -> Expr bool -> Expr bool
  Or     :: SynBool bool => Expr bool -> Expr bool -> Expr bool
  Branch :: (Typeable bool, SynBool bool) => Expr bool -> Expr a -> Expr a -> Expr a

if_ :: (Syntactic bool,
        Syntactic a,
        Typeable (DeepType bool),
        SynBool (DeepType bool)) => bool -> a -> a -> a
if_ cond t f = fromDeepRepr $ Branch (toDeepRepr cond) (toDeepRepr t) (toDeepRepr f)

crash :: Syntactic a => String -> a
crash = fromDeepRepr . Crash

instance Syntactic (Expr a) where
  type DeepType (Expr a) = a

  toDeepRepr = id
  fromDeepRepr = id

instance (Syntactic a, Syntactic b) =>
  Syntactic (a -> b) where
  type DeepType (a -> b) = DeepType a -> DeepType b

  -- toDeepRepr :: (a -> b) -> Expr (DeepType a -> DeepType b)
  toDeepRepr f = Abs $ toDeepRepr . f . fromDeepRepr

  -- fromDeepRepr :: Expr (DeepType a -> DeepType b) -> (a -> b)
  -- fromDeepRepr f = fromDeepRepr . App f . toDeepRepr -- pointfree looks better
  fromDeepRepr f x = fromDeepRepr (App f (toDeepRepr x))

instance (Monad m, Syntactic a) => Syntactic (Codensity m a) where
  type DeepType (Codensity m a) = m (DeepType a)

  -- toDeepRepr :: Codensity m a -> Expr (m (DeepType a))
  -- toDeepRper :: (forall r. (a -> (Expr (m r)) -> Expr (m r)) -> Expr (m (DeepType a))
  toDeepRepr (Codensity m) = m (Return . toDeepRepr)

  -- fromDeepRepr :: Expr (m (DeepType a)) -> Codensity m a
  fromDeepRepr m = Codensity $ \k ->
    Bind m (k . fromDeepRepr)

type ExprM' m   = Codensity m
type ExprM  m a = Codensity m (Expr a)

instance MonadGetInt int m =>
  MonadGetInt (Expr int) (ExprM' m) where
  getInt = fromDeepRepr GetInt

instance MonadGetInt Int IO where
  getInt = putStrLn "Please enter a number:" >> read <$> getLine

instance Num a => Num (Expr a) where
  (+) = NumAdd
  (-) = NumSub
  (*) = NumMult
  abs = NumAbs
  signum = Signum
  fromInteger = Val . fromInteger

instance SynBool Bool where
  neg = not
  (.&&) = (&&)
  (.||) = (||)

instance SynBool a => SynBool (Expr a) where
  neg = Neg
  (.&&) = And
  (.||) = Or

instance SynOrd Int where
  type SynBoolType Int = Bool

  (.==) = (==)
  (./=) = (/=)
  (.<=) = (<=)
  (.<)  = (<)
  (.>=) = (>=)
  (.>)  = (>)

instance SynOrd a => SynOrd (Expr a) where
  type SynBoolType (Expr a) = Expr (SynBoolType a)

  (.==) = IsEq
  (./=) = IsNeq
  (.<=) = IsLe
  (.<)  = IsLt
  (.>=) = IsGe
  (.>)  = IsGt

-- Now we can write something like this
ex1 :: forall m int. MonadGetInt int m => Expr int -> ExprM m int
ex1 x = do
  y <- getInt
  return (x + y)

ex2 :: forall m int.
  (SynOrd int,
   MonadGetInt int m,
   Typeable (SynBoolType int)) => Expr int -> ExprM m int
ex2 x = do
  if_ (x .> 5) (crash "x is too large") $ do
    y <- getInt
    if_ (y .> 5) (crash "y is too large") $
      return (x + y)

ex3 :: forall m int.
  (SynOrd int,
   MonadGetInt int m,
   Typeable (SynBoolType int)) => Expr int -> ExprM m int
ex3 x = do
  if_ (x .> 10)
    (crash "x > 10")
    (ex3 (x + 1))

-- Does not terminate.
ex4 :: forall m int.
  (SynOrd int,
   MonadGetInt int m,
   Typeable (SynBoolType int)) => Expr int -> ExprM m int
ex4 x = do
  y <- if_ (x .> 10)
    (ex4 (x - 1))
    (crash "x <= 10")
  return y

ex5 :: forall m int.
  (MonadGetInt int m,
   SynOrd int,
   Typeable (SynBoolType int)) => ExprM m int
ex5 = do
  x1 <- getInt
  x2 <- getInt
  x3 <- getInt
  if_ (x1 + x2 .> x3)
    (return (x1 + x2))
    (crash "failed")

ex6 :: forall m int.
  (MonadGetInt int m,
   SynOrd int,
   Typeable (SynBoolType int)) => ExprM m int
ex6 = do
  x <- getInt
  if_ (x .> (10 :: Expr int))
    ex6
    (crash "x <= 10")
