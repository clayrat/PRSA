module LTLCsep

import Split
import Pred
import SepLogic
import LTy

%default total
%access public export

%hide Prelude.Monad.(>>=)

-- LTLC

data Term : Ty -> Pred Ctx where
  Var  : One a xs -> Term a xs
  Lam  : ((a::) `turn` Term b) xs -> Term (a ~@ b) xs
  App  : (Term (a ~@ b) ^*^ Term a) xs -> Term b xs
  TT   : eps $ Term U
  LetT : (Term U ^*^ Term a) xs -> Term a xs
  Pair : (Term a ^*^ Term b) xs -> Term (Prod a b) xs
  LetP : (Term (Prod a b) ^*^ (([b,a]++) `turn` Term c)) xs -> Term c xs

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
    VT    : Val U []
    VClos : Term b (a::g) -> Env g xs -> Val (a ~@ b) xs
    VPair : (Val a ^*^ Val b) xs -> Val (Prod a b) xs

Reader : Ctx -> Ctx -> Pred ST -> Pred ST
Reader g1 g2 p = Env g1 ~* Env g2 ^*^ p

ask : eps $ Reader g [] (Env g)
ask = MkWand $ \sp, as =>
      case splitRInv sp of
        Refl => MkStar Nil sp as

prepend : All (Env g1 :-> Reader g2 (g1++g2) Emp)
prepend e1 = MkWand $ \sp, e2 => MkStar (concat $ MkStar e1 sp e2) splitLeft MkEmp

append : All (Env g1 :-> Reader g2 (g2++g1) Emp)
append e1 = MkWand $ \sp, e2 => MkStar (concat $ starComm $ MkStar e1 sp e2) splitLeft MkEmp

pure : All $ p :-> Reader g g p
pure px = MkWand $ \sp, as => MkStar as (splitComm sp) px

bind : All $ (p ~* Reader g2 g3 q) :-> (Reader g1 g2 p ~* Reader g1 g3 q)
bind f =
  MkWand $ \sp1, rd =>
  MkWand $ \sp2, env =>
  let
    (_ ** (sp3, sp4)) = splitAssoc sp1 sp2
    MkStar env2 sp5 pr = app rd sp4 env
    (_ ** (sp6, sp7)) = splitUnassoc sp3 (splitComm sp5)
   in
  app (app f sp6 pr) sp7 env2

str : All $ Reader g1 g2 p ^*^ q :-> Reader g1 g2 (p ^*^ q)
str {p} {q} (MkStar rd sp qr) = app (bind $ MkWand $ \sp1, pl => pure {p=p^*^q} $ MkStar pl (splitComm sp1) qr)
                                    (splitComm sp) rd

(>>=) : Reader g1 g2 p t -> All (p :-> Reader g2 g3 q) -> Reader g1 g3 q t
(>>=) rd f = app (bind $ MkWand $ \sp, pr => case splitRInv sp of Refl => f pr) splitRight rd

frame : Split g l r -> All (Reader l [] p :-> Reader g r p)
frame sp c = MkWand $ \sp0, env =>
  let
    MkStar e1 sp1 e2 = repartition sp env
    (ff ** (sp2, sp3)) = splitUnassoc sp0 sp1
    MkStar Nil sp4 pr = app c sp2 e1
   in
  case splitRInv sp4 of
    Refl => MkStar e2 (splitComm sp3) pr

partial
eval : Term a g -> eps $ Reader g [] (Val a)
eval {a} (Var MkOne)                = do Cons (MkStar v sp Nil) <- ask
                                         case splitLInv sp of
                                           Refl => pure {p=Val a} v
eval (Lam {a} {b} t)                = do env <- ask
                                         pure {p=Val (a ~@ b)} $ VClos t env
eval (App (MkStar f sp t))          = do VClos {g} b env <- frame sp (eval f)
                                         ve <- str {q=Env g} $ MkStar (eval t) splitRight env
                                         MkEmp <- append $ Cons ve
                                         eval b
eval  TT                            = pure {p=Val U} VT
eval (LetT (MkStar u sp t))         = do VT <- frame sp (eval u)
                                         eval t
eval (Pair {a} {b} (MkStar x sp y)) = do v1 <- frame sp (eval x)
                                         ba <- str {q=Val a} $ MkStar (eval y) splitRight v1
                                         pure {p=Val $ Prod a b} $ VPair $ starComm ba
eval (LetP (MkStar pr sp t))        = do VPair (MkStar v1 sp0 v2) <- frame sp (eval pr)
                                         MkEmp <- prepend $ Cons $ MkStar v2 (splitComm sp0) (singleton v1)
                                         eval t
