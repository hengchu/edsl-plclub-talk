module Solver where

import Symbolic
import Z3.Monad
import Data.Foldable
import Data.Map
import Control.Monad.IO.Class
import System.Console.ANSI
import Control.Concurrent
import Control.Monad
import Control.Concurrent.Async

toZ3Binop :: MonadZ3 z3 => SExp -> SExp -> (AST -> AST -> z3 AST) -> z3 AST
toZ3Binop a b f = do
  a' <- toZ3 a
  b' <- toZ3 b
  f a' b'

toZ3Ite' :: MonadZ3 z3
         => SExp -> AST -> AST -> z3 AST
toZ3Ite' cond t f = do
  cond' <- toZ3 cond
  mkIte cond' t f

toZ3Ite :: MonadZ3 z3
        => SExp
        -> SExp
        -> SExp
        -> z3 AST
toZ3Ite cond t f = do
  t' <- toZ3 t
  f' <- toZ3 f
  toZ3Ite' cond t' f'

toZ3 :: MonadZ3 z3 => SExp -> z3 AST
toZ3 (SVal x) = mkIntSort >>= \intSort -> mkInt x intSort
toZ3 (SVar x) = mkStringSymbol x >>= mkIntVar
toZ3 (SAdd a b) = toZ3Binop a b (\a b -> mkAdd [a, b])
toZ3 (SSub a b) = toZ3Binop a b (\a b -> mkSub [a, b])
toZ3 (SMult a b) = toZ3Binop a b (\a b -> mkMul [a, b])
toZ3 (SAbs a) = toZ3Ite (a `SGe` (SVal 0)) a ((SVal 0) `SSub` a)
toZ3 (SSignum a) = do
  neq0 <- toZ3Ite (a `SGt` (SVal 0)) (SVal 1) (SVal (-1))
  zero <- toZ3 (SVal 0)
  toZ3Ite' (a `SEq` (SVal 0)) zero neq0
toZ3 (SEq a b) = toZ3Binop a b mkEq
toZ3 (SNeq a b) = toZ3Binop a b (\a b -> mkEq a b >>= mkNot)
toZ3 (SLt a b) = toZ3Binop a b mkLt
toZ3 (SLe a b) = toZ3Binop a b mkLe
toZ3 (SGt a b) = toZ3Binop a b mkGt
toZ3 (SGe a b) = toZ3Binop a b mkGe
toZ3 (SNeg a) = toZ3 a >>= mkNot
toZ3 (SAnd a b) = toZ3Binop a b (\a b -> mkAnd [a, b])
toZ3 (SOr a b) = toZ3Binop a b (\a b -> mkOr [a, b])

assertZ3 :: MonadZ3 z3 => SBool -> z3 ()
assertZ3 (SBool cond) = do
  cond' <- toZ3 cond
  solverAssertCnstr cond'

check' :: MonadZ3 z3 => PathConditions -> z3 (Maybe Model)
check' conds = do
  for_ conds assertZ3
  result <- solverCheck
  case result of
    Sat -> Just <$> solverGetModel
    Unsat -> return Nothing
    Undef -> error "constraints were too complicated..."

evalVar :: MonadZ3 z3 => Model -> String -> z3 Int
evalVar m x = do
  x' <- toZ3 (SVar x)
  v <- evalInt m x'
  case v of
    Nothing -> error $ "cannot find var " ++ x ++ " in z3 model"
    Just v -> return (fromIntegral v)

modelMap :: MonadZ3 z3 => Model -> z3 (Map String Int)
modelMap m = do
  decls <- getConsts m
  syms  <- traverse getDeclName decls
  vars  <- traverse getSymbolString syms
  vals  <- traverse (evalVar m) vars
  return (fromList $ zip vars vals)

check :: MonadZ3 z3 => PathConditions -> z3 (Maybe (Map String Int))
check conds = check' conds >>= traverse modelMap

untilCrashed :: MonadZ3 z3 => [PathConditions] -> z3 (Maybe (Map String Int))
untilCrashed [] = return Nothing
untilCrashed (c:cs) = do
  r <- Solver.check c
  case r of
    Nothing -> untilCrashed cs
    Just m -> return (Just m)

checkIO :: PathConditions -> IO (Maybe (Map String Int))
checkIO = evalZ3 . Solver.check

untilCrashedIO :: [PathConditions] -> IO (Maybe (Map String Int))
untilCrashedIO conds = do
  r <- race (evalZ3 $ Solver.untilCrashed conds)
            asciiProgress
  case r of
    Left (Just m) -> return (Just m)
    Left Nothing -> do
      putStrLn "exhausted all control flow paths and could not find satisfiable crash conditions"
      return Nothing
    Right _ -> error "impossible"

asciiProgress :: IO ()
asciiProgress = do
  Just (x, y) <- getCursorPosition
  forever $ do
    putStrLn "-"
    threadDelay 1000000
    clearLine
    setCursorPosition x y

    putStrLn "/"
    threadDelay 1000000
    clearLine
    setCursorPosition x y

    putStrLn "\\"
    threadDelay 1000000
    clearLine
    setCursorPosition x y
