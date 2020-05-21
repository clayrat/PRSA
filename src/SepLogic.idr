module SepLogic

import Pred
import Split

%default total
%access public export

data Emp : Pred (List a) where
  MkEmp : Emp []

data Star : {a : Type} -> Pred (List a) -> Pred (List a) -> Pred (List a) where
  MkStar : {l, r : List a} -> p l -> Split g l r -> q r -> Star p q g

infixr 9 ^*^

(^*^) : Pred (List a) -> Pred (List a) -> Pred (List a)
(^*^) = Star

-- (Emp, ^*^) is a commutative monoid

starAssoc : All $ (p ^*^ q) ^*^ r :-> p ^*^ (q ^*^ r)
starAssoc (MkStar (MkStar pl l_m qm) lm_r rr) =
  let (_ ** (l_mr, m_r)) = splitAssoc l_m lm_r in
  MkStar pl l_mr (MkStar qm m_r rr)

starUnassoc : All $ p ^*^ (q ^*^ r) :-> (p ^*^ q) ^*^ r
starUnassoc (MkStar pl l_mr (MkStar qm m_r rr)) =
  let (_ ** (l_m, lm_r)) = splitUnassoc l_mr m_r in
  MkStar (MkStar pl l_m qm) lm_r rr

starEmp : All $ p ^*^ Emp :-> p
starEmp (MkStar pl sp MkEmp) = rewrite splitLInv sp in pl

empStar : All $ p :-> p ^*^ Emp
empStar px = MkStar px splitLeft MkEmp

starComm : All $ p ^*^ q :-> q ^*^ p
starComm (MkStar pl sp qr) = MkStar qr (splitComm sp) pl

-- misc properites

starMono : All (p :-> q) -> All (p ^*^ r :-> q ^*^ r)
starMono pq (MkStar pl sp rr) = MkStar (pq pl) sp rr

infixr 8 ~*

(~*) : Pred (List a) -> Pred (List a) -> Pred (List a)
(~*) {a} p q l = {g, r : List a} -> Split g l r -> p r -> q g

-- wand properites

wandIntro : All (p ^*^ q :-> r) -> All (p :-> q ~* r)
wandIntro f pl = \sp, qr => f $ MkStar pl sp qr

wandCancel0 : All (p :-> q ~* r) -> All (p ^*^ q :-> r)
wandCancel0 f (MkStar pl sp qr) = f pl sp qr

wandCancel : All $ p ^*^ (p ~* q) :-> q
wandCancel (MkStar pl sp wr) = wr (splitComm sp) pl

wandMono : All (p :-> q) -> All (r :-> s) -> All (q ~* r :-> p ~* s)
wandMono pq rs wqr = \sp, pr => rs $ wqr sp (pq pr)

wandSelf : All $ Emp :-> p ~* p
wandSelf MkEmp = \sp, pr => rewrite splitRInv sp in pr

curryW : All $ (p ^*^ q) ~* r :-> p ~* (q ~* r)
curryW wpq_r = \sp1, pm, sp2, qr =>
  let (_ ** (sp3, sp4)) = splitAssoc sp1 sp2 in
  wpq_r sp3 (MkStar pm sp4 qr)

uncurryW : All $ p ~* (q ~* r) :-> (p ^*^ q) ~* r
uncurryW wpqr = \sp1, (MkStar pl sp2 qr) =>
  let (_ ** (sp3, sp4)) = splitUnassoc sp1 sp2 in
  wpqr sp3 pl sp4 qr

wandStar : All $ (p ~* q) ^*^ r :-> p ~* (q ^*^ r)
wandStar (MkStar pql sp1 rr) = \sp2, pr =>
  let (_ ** (sp3, sp4)) = splitUnassoc (splitComm sp2) sp1 in
  MkStar (pql (splitComm sp3) pr) sp4 rr

-- Inductive separating forall over a list
data AllStar : {a, b : Type} -> (a -> Pred b) -> List a -> Pred b where
  Nil  : eps $ AllStar p []
  Cons : (p t ^*^ AllStar p ts) xs -> AllStar p (t::ts) xs

repartition : Split g l r -> All (AllStar p g :-> AllStar p l ^*^ AllStar p r)
repartition  Nil        Nil      = MkStar Nil Nil Nil
repartition (ConsL sp) (Cons (MkStar pt sp1 pts)) =
  let
    MkStar xs sp2 ys = repartition sp pts
    (_ ** (sp3, sp4)) = splitUnassoc sp1 sp2
   in
  MkStar (Cons $ MkStar pt sp3 xs) sp4 ys
repartition (ConsR sp) (Cons (MkStar pt sp1 pts)) =
  let
    MkStar xs sp2 ys = repartition sp pts
    (_ ** (sp3, sp4)) = splitUnassoc sp1 (splitComm sp2)
   in
  MkStar xs (splitComm sp4) (Cons $ MkStar pt sp3 ys)

concat : All $ AllStar p g1 ^*^ AllStar p g2 :-> AllStar p (g1 ++ g2)
concat (MkStar  Nil                       sp ras) = rewrite splitRInv sp in ras
concat (MkStar (Cons $ MkStar pt sp0 las) sp ras) =
  let (r ** (sp1, sp2)) = splitAssoc sp0 sp in
  Cons $ MkStar pt sp1 (concat $ MkStar las sp2 ras)
