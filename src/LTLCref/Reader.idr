module LTLCref.Reader

import Split
import Pred
import SepLogic
import SepLogicM
import LTy
import Market
import LTLCref.Term
import LTLCref.State

%default total
%access public export

%hide Prelude.Monad.(>>=)

Reader : Ctx -> Ctx -> Pred ST -> Pred ST
Reader g1 g2 p = Env g1 ~* State (Env g2 ^*^ p)

pure : All $ p :-> Reader g g p
pure {g} {p} px = MkWand $ \sp, as =>
                  pure {p=Env g ^*^ p} $
                  MkStar as (splitComm sp) px

bind : All $ (p ~* Reader g2 g3 q) :-> (Reader g1 g2 p ~* Reader g1 g3 q)
bind {g2} {g3} {p} {q} f =
  MkWand $ \sp1, rd =>
  MkWand $ \sp2, env =>
  let
    (_ ** (sp3, sp4)) = splitAssoc sp1 sp2
--    MkStar env2 sp5 pr = app rd sp4 env
--    (_ ** (sp6, sp7)) = splitUnassoc sp3 (splitComm sp5)
   in
  app (State.bind {p = Env g2 ^*^ p} {q = Env g3 ^*^ q} $
      -- MkWand $ \sp5, envp =>
      -- let
      --  (_ ** env2) = projL envp in
      -- -- let (_ ** (sp7, sp8)) = splitUnassoc sp5 (splitComm sp6) in
      -- -- app (app f sp7 pr) sp8 env2
       ?wut
      )
      sp3
      (app rd sp4 env)
--  app (app f sp6 pr) sp7 env2

{-
str : All $ Reader g1 g2 p ^*^ q :-> Reader g1 g2 (p ^*^ q)
str {p} {q} (MkStar rd sp qr) = app (Reader.bind $ MkWand $ \sp1, pl => pure {p=p^*^q} $ MkStar pl (splitComm sp1) qr)
                                    (splitComm sp)
                                    rd

(>>=) : Reader g1 g2 p t -> All (p :-> Reader g2 g3 q) -> Reader g1 g3 q t
(>>=) rd f = app (Reader.bind $ MkWand $ \sp, pr => case splitRInv sp of Refl => f pr) splitRight rd
-}

ask : eps $ Reader g [] (Env g)
ask {g} = MkWand $ \sp, as =>
      case splitRInv sp of
        Refl =>
          pure {p = Env [] ^*^ Env g} $
          MkStar Nil sp as

prepend : All (Env g1 :-> Reader g2 (g1++g2) Emp)
prepend {g1} {g2} e1 = MkWand $ \sp, e2 =>
                       pure {p = Env (g1++g2) ^*^ Emp} $
                       MkStar (concat $ MkStar e1 sp e2) splitLeft MkEmp

append : All (Env g1 :-> Reader g2 (g2++g1) Emp)
append {g1} {g2} e1 = MkWand $ \sp, e2 =>
                      pure {p = Env (g2++g1) ^*^ Emp} $
                      MkStar (concat $ starComm $ MkStar e1 sp e2) splitLeft MkEmp

frame : Split g l r -> All (Reader l [] p :-> Reader g r p)
frame {r} {p} sp c = MkWand $ \sp0, env =>
  let
    MkStar e1 sp1 e2 = repartition sp env
    (ff ** (sp2, sp3)) = splitUnassoc sp0 sp1
   in
  do MkStar (MkStar Nil sp4 v) sp5 e3 <- str $ MkStar (app c sp2 e1) sp3 e2
     case splitRInv sp4 of
       Refl => pure {p=Env r ^*^ p} $ MkStar e3 (splitComm sp5) v

