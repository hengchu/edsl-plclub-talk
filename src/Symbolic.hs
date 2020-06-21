module Symbolic where

import EDSL
import Control.Monad.State.Lazy
import Type.Reflection hiding (App)
import Data.List
import Debug.Trace

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
  deriving (Show, Eq, Ord)

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

instance MonadGetInt SInt Symbolic where
  getInt = freshSInt "sint"

newtype SInt = SInt SExp
  deriving (SynOrd, Num) via SExp
  deriving (Show, Eq, Ord)

newtype SBool = SBool SExp
  deriving SynBool via SExp
  deriving (Show, Eq, Ord)

newtype Symbolic a = Symbolic { runSymbolic_ :: State Int a }
  deriving (Functor, Applicative, Monad) via (State Int)
  deriving (MonadState Int) via (State Int)

evalSymbolic :: Symbolic a -> a
evalSymbolic = flip evalState 0 . runSymbolic_

runSymbolic :: Int -> Symbolic a -> (a, Int)
runSymbolic st = flip runState st . runSymbolic_

purify :: Symbolic a -> (Int -> (a, Int))
purify = flip runSymbolic

freshSVar :: String -> Symbolic SExp
freshSVar name = do
  n <- get
  modify (+1)
  return (SVar (name ++ show n))

freshSInt :: String -> Symbolic SInt
freshSInt name = SInt <$> freshSVar name

data Some :: (* -> *) -> * where
  Some :: f a -> Some f

data Path = Path {
  conditions :: [SBool],
  continue :: Some Expr
  }

isCrash' :: Expr a -> Bool
isCrash' (Crash _) = True
isCrash' _         = False

isCrash :: Some Expr -> Bool
isCrash (Some e) = isCrash' e

isGetInt :: Some Expr -> Bool
isGetInt (Some GetInt) = True
isGetInt _ =  False

interleaveAll :: [[a]] -> [a]
interleaveAll = concat . transpose

inf1 :: [Symbolic SInt]
inf1 = repeat (freshSInt "x")

inf2 :: [Symbolic SInt]
inf2 = repeat (freshSInt "y")

stepBinop :: Expr a -> Expr b -> (Expr a -> Expr b -> Expr c) -> Step (Expr c)
stepBinop a b combine =
  case step a of
    Normal          -> combine a <$> step b
    Stepped a'      -> Stepped $ combine a' b
    PendingBranch scond k -> PendingBranch scond (\cond -> combine (k cond) b)
    PendingGetInt k -> PendingGetInt (\sint -> combine (k sint) b)
    Crashed         -> Crashed

isNormal :: Step (Expr a) -> Bool
isNormal Normal = True
isNormal _ = False

isCrashed :: Step (Expr a) -> Bool
isCrashed Crashed = True
isCrashed _ = False

data Step a where
  -- | Performed a beta reduction somewhere
  Stepped :: a -> Step a
  -- | Stepping is blocked on branch.
  PendingBranch :: SBool -> (Bool -> a) -> Step a
  -- | Stepping is blocked on effect.
  PendingGetInt :: (SInt -> a) -> Step a
  -- | Already normal form
  Normal  :: Step a
  -- | Stepped on crash
  Crashed :: Step a
  deriving (Functor)

-- |Smallstep to remove redexes.
step :: forall a. Expr a -> Step (Expr a)
step (Val _) = Normal
step (Abs _) = Normal
step (Crash _) = Crashed
step (Branch (Val scond :: Expr bool) t f) =
  case eqTypeRep (typeRep @bool) (typeRep @SBool) of
    Just HRefl -> PendingBranch scond (\case { True -> t; False -> f})
    _ -> error "step: expected SBool branch condition"
step (Branch c t f) =
  fmap (\c' -> Branch c' t f) (step c)
step GetInt =
  case eqTypeRep (typeRep @a) (typeRep @(Symbolic SInt)) of
    Just HRefl -> PendingGetInt (Return . Val . id)
    _ -> error "step: expected Symbolic monad"
step (Return a) = Return <$> step a
step (App (Abs f) e@(Val _)) = Stepped (f e)
step (App f e) = stepBinop f e App
step (Bind (Return e) f) =
  case step e of
    Stepped e' -> Stepped (Bind (Return e') f)
    Normal     -> Stepped (f e)
    Crashed    -> Crashed
    PendingBranch scond k -> PendingBranch scond (\c -> Bind (Return (k c)) f)
    PendingGetInt k -> PendingGetInt (f . k)
step (Bind m f) = fmap (\m' -> Bind m' f) (step m)
step (NumAdd (Val a) (Val b)) = Stepped (Val (a + b))
step (NumAdd a b) = stepBinop a b NumAdd
step (NumSub (Val a) (Val b)) = Stepped (Val (a - b))
step (NumSub a b) = stepBinop a b NumSub
step (NumMult (Val a) (Val b)) = Stepped (Val (a * b))
step (NumMult a b) = stepBinop a b NumMult
step (NumAbs (Val a)) = Stepped (Val (abs a))
step (NumAbs a) = NumAbs <$> step a
step (Signum (Val a)) = Stepped (Val (signum a))
step (Signum a) = Signum <$> step a
step (Neg (Val a)) = Stepped (Val (neg a))
step (Neg a) = Neg <$> step a
step (And (Val a) (Val b)) = Stepped (Val (a .&& b))
step (And a b) = stepBinop a b And
step (Or (Val a) (Val b)) = Stepped (Val (a .|| b))
step (Or a b) = stepBinop a b Or
step (IsEq (Val a) (Val b)) = Stepped (Val (a .== b))
step (IsEq a b) = stepBinop a b IsEq
step (IsNeq (Val a) (Val b)) = Stepped (Val (a ./= b))
step (IsNeq a b) = stepBinop a b IsNeq
step (IsLt (Val a) (Val b)) = Stepped (Val (a .< b))
step (IsLt a b) = stepBinop a b IsLt
step (IsLe (Val a) (Val b)) = Stepped (Val (a .<= b))
step (IsLe a b) = stepBinop a b IsLe
step (IsGt (Val a) (Val b)) = Stepped (Val (a .> b))
step (IsGt a b) = stepBinop a b IsGt
step (IsGe (Val a) (Val b)) = Stepped (Val (a .>= b))
step (IsGe a b) = stepBinop a b IsGe

type PathConditions = [SBool]

data Work a where
  Continue :: Int -> PathConditions -> Expr a -> Work a

iter' :: [Work a] -> ([PathConditions], [Work a])
iter' = go [] []
  where go crashConds ks [] = (crashConds, ks)
        go crashConds ks (Continue st conds e:xs) =
          case step e of
            Stepped e' -> go crashConds (Continue st conds e':ks) xs
            PendingBranch c k ->
              go
                crashConds
                (Continue st (c:conds)     (k True):
                 Continue st (neg c:conds) (k False):
                 ks) xs
            PendingGetInt k ->
              let (term, st') = runSymbolic st (freshSInt "sint" >>= return . k)
              in go crashConds (Continue st' conds term:ks) xs
            Normal -> go crashConds ks xs
            Crashed -> go (conds:crashConds) ks xs

searchCrashConditions :: [Work a] -> [PathConditions]
searchCrashConditions [] = []
searchCrashConditions work =
  case iter' work of
    (crashConds, moreWork) ->
      crashConds ++ (searchCrashConditions moreWork)

seval :: Expr a -> [PathConditions]
seval e = searchCrashConditions [Continue 0 [] e]
