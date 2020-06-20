module Concrete where

import Type.Reflection (eqTypeRep, Typeable, (:~~:)(..), typeRep)
import EDSL

eval :: Expr a -> a
eval (Val x) = x
eval (Abs f) = eval . f . Val
eval (App f a) = (eval f) (eval a)
eval (Bind m f) = eval m >>= (eval . f . Val)
eval (Return a) = return (eval a)
eval (Crash msg) = error msg
eval (IsEq a b) = eval a .== eval b
eval (IsNeq a b) = eval a ./= eval b
eval (IsLt a b) = eval a .< eval b
eval (IsLe a b) = eval a .<= eval b
eval (IsGt a b) = eval a .> eval b
eval (IsGe a b) = eval a .>= eval b
eval GetInt = getInt
eval (NumAdd a b) = eval a + eval b
eval (NumSub a b) = eval a - eval b
eval (NumMult a b) = eval a * eval b
eval (NumAbs a) = abs (eval a)
eval (Signum a) = signum (eval a)
eval (And a b) = eval a .&& eval b
eval (Or a b) = eval a .|| eval b
eval (Branch (cond :: Expr bool) a b) =
  case eqTypeRep (typeRep @bool) (typeRep @Bool) of
    Just HRefl -> if (eval cond) then (eval a) else (eval b)
    _ -> error "branch condition must be Bool"
