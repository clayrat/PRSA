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

ReaderT : Ctx -> Ctx -> Pred ST -> Pred ST
ReaderT g1 g2 p = Env g1 ~* Env g2 ^*^ p

ask : eps $ ReaderT g [] (Env g)
ask sp as with (splitRInv sp)
  | Refl = MkStar Nil sp as
