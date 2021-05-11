module LTLCses.Term

import Split
import Pred
import SepLogic
import LTLCses.Ty

%default total
%access public export

data Term : Ty -> Pred Ctx where
  Var    : One a g -> Term a g
  Lam    : ((a::) `turn` Term b) g -> Term (a ~@ b) g
  App    : (Term (a ~@ b) ^*^ Term a) g -> Term b g
  TT     : eps $ Term U
  LetT   : (Term U ^*^ Term a) g -> Term a g
  Pair   : (Term a ^*^ Term b) g -> Term (Prod a b) g
  LetP   : (Term (Prod a b) ^*^ (([b,a]++) `turn` Term c)) g -> Term c g
  MkChan : (a : STy) -> eps $ Term (Prod (Rf a) (Rf (inv a)))
  Send   : (Term a ^*^ Term (Rf (Sd a b))) g -> Term (Rf b) g
  Recv   : Term (Rf (Rv a b)) g -> Term (Prod (Rf b) a) g
  Fork   : Term (U ~@ U) g -> Term U g
  Close  : Term (Rf End) g -> Term U g

lets : All $ Term a :-> ((a::) `turn` Term b) ~* Term b
lets t = MkWand $ \sp, u => App $ MkStar (Lam u) (splitComm sp) t

test : Term U []
test =
  LetP $ MkStar (MkChan $ Sd U End)
                Nil
                (app (lets $ Fork $
                             Lam $
                             LetP $ MkStar (Recv $ Var MkOne)
                                           (ConsR $ ConsL Nil)
                                           (LetT $ MkStar (LetT $ MkStar (Var MkOne)
                                                                         (ConsR $ ConsL Nil)
                                                                         (Var MkOne))
                                                          (ConsL $ ConsR $ ConsL Nil)
                                                          (Close $ Var MkOne)
                                           )
                     )
                     (ConsL $ ConsR Nil)
                     (app (lets $ Send $ MkStar TT (ConsR Nil) (Var MkOne))
                          (ConsR $ ConsL Nil)
                          (LetT $ MkStar (Var MkOne)
                                         (ConsR $ ConsL Nil)
                                         (Close $ Var MkOne))))

data Ends : RTy -> RTy -> RTy -> Type where
  LR : Ends (Chan a b) (Endp a) (Endp b)
  RL : Ends (Chan a b) (Endp b) (Endp a)

data SplitE : RCtx -> RCtx -> RCtx -> Type where
  NilE   : SplitE [] [] []
  ConsRE : SplitE xs ls rs -> SplitE (x::xs)     ls (x::rs)
  ConsLE : SplitE xs ls rs -> SplitE (x::xs) (x::ls)    rs
  Div    : Ends x l r -> SplitE xs ls rs -> SplitE (x::xs) (l::ls) (r::rs)

mutual
  Env : Ctx -> Pred RCtx
  Env = AllStar Val

  data Val : Ty -> Pred RCtx where
    VT    : Val U []
    VClos : Term b (a::d) -> Env d g -> Val (a ~@ b) g
    VPair : (Val a ^*^ Val b) g -> Val (Prod a b) g
    VRef  : One (Endp a) g -> Val (Rf a) g