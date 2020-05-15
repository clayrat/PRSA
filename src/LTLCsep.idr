module LTLCsep

import Pred
import SepLogic
import LTy

%default total
%access public export

-- LTLC

data Term : Ty -> Pred (List Ty) where
  Var  : All $ One a :-> Term a
  Lam  : All $ (a::) `turn` (Term b) :-> Term (a ~@ b)
  App  : All $ Term (a ~@ b) ^*^ (Term a) :-> Term b
  TT   : All $ Emp :-> Term U
  LetT : All $ Term U ^*^ Term a :-> Term a
  Pair : All $ Term a ^*^ Term b :-> Term (Prod a b)
  LetP : All $ Term (Prod a b) ^*^ (([b,a]++) `turn` Term c) :-> Term c
