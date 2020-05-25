module STLC

import Data.List
import Data.List.Quantifiers

%default total
--%access public export

data Ty = U | Imp Ty Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

data Term : List Ty -> Ty -> Type where
  TT  : Term g U
  Var : Elem a g -> Term g a
  Lam : Term (a::g) b -> Term g (a~>b)
  App : Term g (a~>b) -> Term g a -> Term g b

mutual
  Env : List Ty -> Type
  Env = All Val

  data Val : Ty -> Type where
    VT  : Val U
    VCl : Env g -> Term (a::g) b -> Val (a~>b)

eval : Term g a -> Env g -> Val a
eval  TT       env = VT
eval (Var el)  env = indexAll el env
eval (Lam t)   env = VCl env t
eval (App t u) env with (eval t env)
  eval (App t u) env | VCl env' v = assert_total $ eval v (eval u env :: env')