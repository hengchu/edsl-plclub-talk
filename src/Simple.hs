module Simple () where

type Expr a = a

lam :: (a -> b) -> Expr (a -> b)
lam = id

app :: Expr (a -> b) -> Expr a -> Expr b
app = ($)

if_ :: Expr Bool -> Expr a -> Expr a -> Expr a
if_ c t f = if c then t else f

(+), (-), (*) :: Expr Int -> Expr Int -> Expr Int
(+) = (Prelude.+)
(-) = (Prelude.-)
(*) = (Prelude.*)

newtype K m a = K (forall r. (a -> m r) -> m r)

embed :: Monad m => m a -> K m a
embed a = K (\cont -> a >>= cont)

project :: Monad m => K m a -> m a
project (K m) = m return
