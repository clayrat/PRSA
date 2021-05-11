module LTLC.Reader

import Split
import Pred
import SepLogic
import LTy
import LTLC.Term

%default total
%access public export

%hide Prelude.Monad.(>>=)

Reader : Ctx -> Ctx -> Pred ST -> Pred ST
Reader g1 g2 p = Env g1 ~* Env g2 ^*^ p

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

(>>=) : Reader g1 g2 p t -> All (p :-> Reader g2 g3 q) -> Reader g1 g3 q t
(>>=) rd f = app (bind $ MkWand $ \sp => rewrite splitRInv sp in f) splitRight rd

str : All $ Reader g1 g2 p ^*^ q :-> Reader g1 g2 (p ^*^ q)
str {p} {q} (MkStar rd sp qr) = app (bind $ MkWand $ \sp1, pl => pure {p=p^*^q} $ MkStar pl (splitComm sp1) qr)
                                    (splitComm sp) rd

ask : eps $ Reader g [] (Env g)
ask = MkWand $ \sp, as =>
      case splitRInv sp of
        Refl => MkStar Nil sp as

prepend : All (Env g1 :-> Reader g2 (g1++g2) Emp)
prepend e1 = MkWand $ \sp, e2 => MkStar (concat $ MkStar e1 sp e2) splitLeft MkEmp

append : All (Env g1 :-> Reader g2 (g2++g1) Emp)
append e1 = MkWand $ \sp, e2 => MkStar (concat $ starComm $ MkStar e1 sp e2) splitLeft MkEmp

frame : Split g l r -> All (Reader l [] p :-> Reader g r p)
frame sp c = MkWand $ \sp0, env =>
  let
    MkStar e1 sp1 e2 = repartition sp env
    (ff ** (sp2, sp3)) = splitUnassoc sp0 sp1
    MkStar Nil sp4 pr = app c sp2 e1
   in
  case splitRInv sp4 of
    Refl => MkStar e2 (splitComm sp3) pr
