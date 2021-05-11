module SepLogicM

import Pred
import Split
import Market

%default total
%access public export

epsM : Pred (Market a) -> Type
epsM p = p (De [])

data EmpM : Pred (Market a) where
  MkEmpM : EmpM (De [])

data StarM : {a : Type} -> Pred (Market a) -> Pred (Market a) -> Pred (Market a) where
  MkStarM : {l, r : Market a} -> p l -> MSplit g l r -> q r -> StarM p q g

infixr 9 ^**^

(^**^) : Pred (Market a) -> Pred (Market a) -> Pred (Market a)
(^**^) = StarM

-- (EmpM, ^**^) is a commutative monoid

starAssocM : All $ (p ^**^ q) ^**^ r :-> p ^**^ (q ^**^ r)
starAssocM (MkStarM (MkStarM pl l_m qm) lm_r rr) =
  let (_ ** (l_mr, m_r)) = msplitAssoc l_m lm_r in
  MkStarM pl l_mr (MkStarM qm m_r rr)

starUnassocM : All $ p ^**^ (q ^**^ r) :-> (p ^**^ q) ^**^ r
starUnassocM (MkStarM pl l_mr (MkStarM qm m_r rr)) =
  let (_ ** (l_m, lm_r)) = msplitUnassoc l_mr m_r in
  MkStarM (MkStarM pl l_m qm) lm_r rr

starEmpM : All $ p ^**^ EmpM :-> p
starEmpM (MkStarM pl sp MkEmpM) = rewrite msplitLInv sp in pl

empStarM : All $ p :-> p ^**^ EmpM
empStarM px = MkStarM px msplitLeft MkEmpM

starCommM : All $ p ^**^ q :-> q ^**^ p
starCommM (MkStarM pl sp qr) = MkStarM qr (msplitComm sp) pl

-- misc properites

starMonoM : All (p :-> q) -> All (p ^**^ r :-> q ^**^ r)
starMonoM pq (MkStarM pl sp rr) = MkStarM (pq pl) sp rr

data WandM : Pred (Market a) -> Pred (Market a) -> Pred (Market a) where
  MkWandM : ({g, r : Market a} -> MSplit g l r -> p r -> q g) -> WandM p q l

appM : WandM p q l -> {g, r : Market a} -> MSplit g l r -> p r -> q g
appM (MkWandM f) = f

infixr 8 ~~*

(~~*) : Pred (Market a) -> Pred (Market a) -> Pred (Market a)
(~~*) = WandM

-- wand properites

wandIntroM : All (p ^**^ q :-> r) -> All (p :-> q ~~* r)
wandIntroM f pl = MkWandM $ \sp, qr => f $ MkStarM pl sp qr

wandCancel0M : All (p :-> q ~~* r) -> All (p ^**^ q :-> r)
wandCancel0M f (MkStarM pl sp qr) = appM (f pl) sp qr

wandCancelM : All $ p ^**^ (p ~~* q) :-> q
wandCancelM (MkStarM pl sp wr) = appM wr (msplitComm sp) pl

wandMonoM : All (p :-> q) -> All (r :-> s) -> All (q ~~* r :-> p ~~* s)
wandMonoM pq rs wqr = MkWandM $ \sp, pr => rs $ appM wqr sp (pq pr)

wandSelfM : All $ EmpM :-> p ~~* p
wandSelfM MkEmpM = MkWandM $ \sp, pr => rewrite msplitRInv sp in pr

curryWM : All $ (p ^**^ q) ~~* r :-> p ~~* (q ~~* r)
curryWM wpq_r =
  MkWandM $ \sp1, pm =>
  MkWandM $ \sp2, qr =>
  let (_ ** (sp3, sp4)) = msplitAssoc sp1 sp2 in
  appM wpq_r sp3 (MkStarM pm sp4 qr)

uncurryWM : All $ p ~~* (q ~~* r) :-> (p ^**^ q) ~~* r
uncurryWM wpqr = MkWandM $ \sp1, (MkStarM pl sp2 qr) =>
  let (_ ** (sp3, sp4)) = msplitUnassoc sp1 sp2 in
  appM (appM wpqr sp3 pl) sp4 qr

wandStarM : All $ (p ~~* q) ^**^ r :-> p ~~* (q ^**^ r)
wandStarM (MkStarM pql sp1 rr) = MkWandM $ \sp2, pr =>
  let (_ ** (sp3, sp4)) = msplitUnassoc (msplitComm sp2) sp1 in
  MkStarM (appM pql (msplitComm sp3) pr) sp4 rr

-- Inductive separating forall over a list
data AllStarM : {a, b : Type} -> (a -> Pred b) -> List a -> Pred b where
  NilM  : epsM $ AllStarM p []
  ConsM : (p t ^**^ AllStarM p ts) xs -> AllStarM p (t::ts) xs

singletonM : All $ p x :-> AllStarM {b=Market a} p [x]
singletonM v = ConsM $ MkStarM v msplitLeft NilM

repartitionM : Split g l r -> All (AllStarM p g :-> AllStarM p l ^**^ AllStarM p r)
repartitionM  Nil        NilM                       = MkStarM NilM (Demand Nil) NilM
repartitionM (ConsL sp) (ConsM (MkStarM pt sp1 pts)) =
  let
    MkStarM xs sp2 ys = repartitionM sp pts
    (_ ** (sp3, sp4)) = msplitUnassoc sp1 sp2
   in
  MkStarM (ConsM $ MkStarM pt sp3 xs) sp4 ys
repartitionM (ConsR sp) (ConsM (MkStarM pt sp1 pts)) =
  let
    MkStarM xs sp2 ys = repartitionM sp pts
    (_ ** (sp3, sp4)) = msplitUnassoc sp1 (msplitComm sp2)
   in
  MkStarM xs (msplitComm sp4) (ConsM $ MkStarM pt sp3 ys)

concatM : All $ AllStarM p g1 ^**^ AllStarM p g2 :-> AllStarM p (g1 ++ g2)
concatM (MkStarM  NilM                       sp ras) = rewrite msplitRInv sp in ras
concatM (MkStarM (ConsM $ MkStarM pt sp0 las) sp ras) =
  let (r ** (sp1, sp2)) = msplitAssoc sp0 sp in
  ConsM $ MkStarM pt sp1 (concatM $ MkStarM las sp2 ras)
