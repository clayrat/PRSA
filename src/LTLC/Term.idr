module LTLC.Term

import Split
import Pred
import SepLogic
import LTy

%default total
%access public export

-- LTLC

data Term : Ty -> Pred Ctx where
  Var  : One a g -> Term a g
  Lam  : ((a::) `turn` Term b) g -> Term (a ~@ b) g
  App  : (Term (a ~@ b) ^*^ Term a) g -> Term b g
  TT   : eps $ Term U
  LetT : (Term U ^*^ Term a) g -> Term a g
  Pair : (Term a ^*^ Term b) g -> Term (Prod a b) g
  LetP : (Term (Prod a b) ^*^ (([b,a]++) `turn` Term c)) g -> Term c g

-- let (a,b) = (*,*) in let * = a in b
test : Term U []
test = LetP $ MkStar (Pair $ MkStar TT Nil TT)
                      Nil
                     (LetT $ MkStar (Var MkOne)
                                    (ConsR $ ConsL Nil)
                                    (Var MkOne))

lets : All $ Term a :-> ((a::) `turn` Term b) ~* Term b
lets t = MkWand $ \sp, u => App $ MkStar (Lam u) (splitComm sp) t

mutual
  Env : Ctx -> Pred ST
  Env = AllStar Val

  data Val : Ty -> Pred ST where
    VT    : Val U []
    VClos : Term b (a::d) -> Env d g -> Val (a ~@ b) g
    VPair : (Val a ^*^ Val b) g -> Val (Prod a b) g
