module LTLCsep

import Split
import Pred
import SepLogic
import LTy

%default total
%access public export

-- LTLC

data Term : Ty -> Pred (List Ty) where
  Var  : All $ One a :-> Term a
  Lam  : All $ (a::) `turn` Term b :-> Term (a ~@ b)
  App  : All $ Term (a ~@ b) ^*^ Term a :-> Term b
  TT   : All $ Emp :-> Term U
  LetT : All $ Term U ^*^ Term a :-> Term a
  Pair : All $ Term a ^*^ Term b :-> Term (Prod a b)
  LetP : All $ Term (Prod a b) ^*^ (([b,a]++) `turn` Term c) :-> Term c

-- let (a,b) = (*,*) in let * = a in b
test : Term U []
test = LetP $ MkStar (Pair $ MkStar (TT MkEmp)
                                    Nil
                                    (TT MkEmp))
                      Nil
                     (LetT $ MkStar (Var MkOne)
                                    (ConsR $ ConsL Nil)
                                    (Var MkOne))