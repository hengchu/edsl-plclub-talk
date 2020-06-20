module Symbolic where

import EDSL
import Z3.Monad
import Control.Monad.State

data SExp :: * where
  SVal    :: Int  -> SExp
  SVar    :: String -> SExp
  SAdd    :: SExp -> SExp -> SExp
  SSub    :: SExp -> SExp -> SExp
  SMult   :: SExp -> SExp -> SExp
  SAbs    :: SExp -> SExp
  SSignum :: SExp -> SExp
  SEq     :: SExp -> SExp -> SExp
  SNeq    :: SExp -> SExp -> SExp
  SLt     :: SExp -> SExp -> SExp
  SLe     :: SExp -> SExp -> SExp
  SGt     :: SExp -> SExp -> SExp
  SGe     :: SExp -> SExp -> SExp
  SNeg    :: SExp -> SExp
  SAnd    :: SExp -> SExp -> SExp
  SOr     :: SExp -> SExp -> SExp

instance Num SExp where
  (+) = SAdd
  (-) = SSub
  (*) = SMult
  abs = SAbs
  signum = SSignum
  fromInteger = SVal . fromInteger

instance SynBool SExp where
  neg = SNeg
  (.&&) = SAnd
  (.||) = SOr

instance SynOrd SExp where
  type SynBoolType SExp = SBool

  a .== b = SBool (SEq a b)
  a ./= b = SBool (SNeq a b)
  a .<= b = SBool (SLe a b)
  a .< b  = SBool (SLt a b)
  a .>= b = SBool (SGe a b)
  a .> b  = SBool (SGt a b)

newtype SInt = SInt SExp
  deriving (SynOrd, Num) via SExp

newtype SBool = SBool SExp
  deriving SynBool via SExp

newtype Symbolic a = Symbolic { runSymbolic_ :: State Int a }
  deriving (Functor, Applicative, Monad) via (State Int)
  deriving (MonadState Int) via (State Int)

freshSVar :: Symbolic SExp
freshSVar = do
  n <- get
  modify (+1)
  return (SVar ("svar" ++ show n))

freshSInt :: Symbolic SInt
freshSInt = SInt <$> freshSVar

data Path a = Path {
  conditions :: [SBool],
  continue :: Expr a
  }

isCrash :: Expr a -> Bool
isCrash (Crash _) = True
isCrash _         = False

isValue :: Expr a -> Bool
isValue (Val _) = True
isValue (Abs _) = True
isValue (Return v) = isValue v
isValue _ = False

-- |Symbolic smallstep semantics for `Expr`.
sstep :: Path a -> Symbolic [Path a]
sstep p@(Path conds (Val x)) = return []
sstep p@(Path conds (Abs _)) = return []
sstep p@(Path conds (App f a)) =
  if isValue f
  then if isValue a
       then undefined
       else undefined
  else undefined
