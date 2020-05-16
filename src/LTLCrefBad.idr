module LTLCrefBad

import Data.List
import Split
import LTy

%default total
%access public export

data Term : Ctx -> Ty -> Type where
  Var  : Term [a] a
  Lam  : Term (a::g) b -> Term g (a~@b)
  App  : Split g l r -> Term l (a~@b) -> Term r a -> Term g b
  TT   : Term [] U
  LetT : Split g l r -> Term l U -> Term r a -> Term g a
  Pair : Split g l r -> Term l a -> Term r b -> Term g (Prod a b)
  LetP : Split g l r -> Term l (Prod a b) -> Term (b::a::r) c -> Term g c
  Ref  : Term g a -> Term g (R a)
  Swap : Split g l r -> Term l (R a) -> Term r b -> Term g (Prod a (R b))
  Del  : Term g (R U) -> Term g U

mutual
  data All : Ctx -> ST -> Type where
    Nil  : All [] []
    Cons : Split g l r -> Val l a -> All d r -> All (a::d) g

  -- store + type
  data Val : ST -> Ty -> Type where
    VT    : Val [] U
    VRef  : Val [a] a
    VPair : Split g l r -> Val l a -> Val r b -> Val g (Prod a b)
    VCl   : Term (a::g) b -> All g d -> Val d (a~@b)

eval : Term g a -> All g l -> Split d l r -> All s r -> Split s d t
   -> (s2, d3, d4, d5 : List Ty) -> (All s2 d3, Split d5 d3 d4, Val d4 a, Split s2 d5 t)