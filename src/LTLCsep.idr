module LTLCsep

import Split
import Pred
import SepLogic
import LTy

%default total
%access public export

-- LTLC

data Term : Ty -> Pred Ctx where
  Var  : All $ One a :-> Term a
  Lam  : All $ (a::) `turn` Term b :-> Term (a ~@ b)
  App  : All $ Term (a ~@ b) ^*^ Term a :-> Term b
  TT   : eps $ Term U
  LetT : All $ Term U ^*^ Term a :-> Term a
  Pair : All $ Term a ^*^ Term b :-> Term (Prod a b)
  LetP : All $ Term (Prod a b) ^*^ (([b,a]++) `turn` Term c) :-> Term c

-- let (a,b) = (*,*) in let * = a in b
test : Term U []
test = LetP $ MkStar (Pair $ MkStar TT Nil TT)
                      Nil
                     (LetT $ MkStar (Var MkOne)
                                    (ConsR $ ConsL Nil)
                                    (Var MkOne))

mutual
  Env : Ctx -> Pred ST
  Env = AllStar Val

  data Val : Ty -> Pred ST where
    VT    : eps $ Val U
    VClos : Term b (a::g) -> All (Env g :-> Val (a ~@ b))
    VPair : All $ Val a ^*^ Val b :-> Val (Prod a b)

Reader : Ctx -> Ctx -> Pred ST -> Pred ST
Reader g1 g2 p = Env g1 ~* Env g2 ^*^ p

ask : eps $ Reader g [] (Env g)
ask sp as with (splitRInv sp)
  | Refl = MkStar Nil sp as

prepend : All (Env g1 :-> Reader g2 (g1++g2) Emp)
prepend e1 = \sp, e2 => MkStar (concat $ MkStar e1 sp e2) splitLeft MkEmp

append : All (Env g1 :-> Reader g2 (g2++g1) Emp)
append e1 = \sp, e2 => MkStar (concat $ starComm $ MkStar e1 sp e2) splitLeft MkEmp

pure : All $ p :-> Reader g g p
pure px = \sp, as => MkStar as (splitComm sp) px

bind : All $ (p ~* Reader g2 g3 q) :-> (Reader g1 g2 p ~* Reader g1 g3 q)
bind f = \sp1, rd, sp2, env =>
  let
    (_ ** (sp3, sp4)) = splitAssoc sp1 sp2
    MkStar env2 sp5 pr = rd sp4 env
    (_ ** (sp6, sp7)) = splitUnassoc sp3 (splitComm sp5)
   in
  f sp6 pr sp7 env2
