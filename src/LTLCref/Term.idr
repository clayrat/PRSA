module LTLCref.Term

import Split
import Pred
import SepLogic
import LTy

%default total
%access public export

data Term : Ty -> Pred Ctx where
  Var  : One a g -> Term a g
  Lam  : ((a::) `turn` Term b) g -> Term (a ~@ b) g
  App  : (Term (a ~@ b) ^*^ Term a) g -> Term b g
  TT   : eps $ Term U
  LetT : (Term U ^*^ Term a) g -> Term a g
  Pair : (Term a ^*^ Term b) g -> Term (Prod a b) g
  LetP : (Term (Prod a b) ^*^ (([b,a]++) `turn` Term c)) g -> Term c g
  Ref  : eps $ Term a :-> Term (R a)
  Swap : (Term (Rf a) ^*^ Term b) g -> Term (Prod a (Rf b)) g
  Del  : Term (Rf U) g -> Term U g

--  let
--    (uu,refu) = swap (ref (*,*)) *
--    (u1,u2) = uu
--    * = u1
--    * = u2
--   in
--  del refu
test : Term U []
test =
  LetP $ MkStar (Swap $ MkStar (Ref $ Pair $ MkStar TT Nil TT) Nil TT)
                Nil
                (LetP $ MkStar (Var MkOne)
                               (ConsR $ ConsL Nil)
                               (LetT $ MkStar (Var MkOne)
                                              (ConsL $ ConsR $ ConsR Nil)
                                              (LetT $ MkStar (Var MkOne)
                                                             (ConsL $ ConsR Nil)
                                                             (Del $ Var MkOne))))

mutual
  Env : Ctx -> Pred ST
  Env = AllStar Val

  data Val : Ty -> Pred ST where
    VT    : Val U []
    VClos : Term b (a::d) -> Env d g -> Val (a ~@ b) g
    VPair : (Val a ^*^ Val b) g -> Val (Prod a b) g
    VRef  : One a g -> Val (R a) g

Store : Ctx -> Pred ST
Store = AllStar Val
