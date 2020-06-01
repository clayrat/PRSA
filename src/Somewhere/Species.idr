module Somewhere.Species

-- works only in Idris2

--%access public export
%default total

public export
Sp : Type -> Type
Sp a = List a -> Type

infixr 1 :->
public export
(:->) : Sp a -> Sp a -> Type
(:->) {a} s t = {x : List a} -> s x -> t x

public export
data Var : (x : a) -> Sp a where
  MkVar : Var x [x]

public export
data Cx : List a -> Sp a where
  MkCx : Cx xs xs

Ens : Sp a
Ens xs = ()

infixr 2 :*:
public export
(:*:) : Sp a -> Sp a -> Sp a
(:*:) s t x = (s x, t x)

infixr 1 :<-
(:<-) : Sp a -> Sp a -> Sp a
(:<-) s t x = s x -> t x

parameters (op : List a -> List a -> List a)

  --data Day : Sp a -> Sp a -> Sp a where
  --  MkDay : {l, r : List a} -> s l -> g = op l r -> t r -> Day s t g

  record Day (s : Sp a) (t : Sp a) (g : List a) where
    constructor MkDay
    {l, r : List a}
    injL : s l
    part : g = op l r
    injR : t r

  parameters (i : List a)

    Un : Sp a
    Un k = k = i

    parameters (lid : (js : List a) -> js = op i js)

      leftId1 : t :-> Day Un t
      leftId1 tx = MkDay {l=i} Refl (lid x) tx

      leftId2 : Day Un t :-> t
      leftId2 (MkDay {r} sl p tr) = rewrite p in
                                    rewrite sl in
                                    rewrite sym $ lid r in
                                    tr

  public export
  Hom : Sp a -> Sp a -> Sp a
  Hom s t l = {r, g : List a} -> op l r = g -> s r -> t g

  curryD : (Day s t :-> u) -> (s :-> Hom t u)
  curryD f sx Refl tr = f $ MkDay sx Refl tr

  uncurryD : (s :-> Hom t u) -> (Day s t :-> u)
  uncurryD f (MkDay sx Refl tr) = f sx Refl tr

D : List a -> Sp a -> Sp a
D js s ks = s (ks ++ js)

parameters (is : List a)

  lll : D is t :-> Hom (++) (Cx is) t
  lll tx Refl MkCx = tx

  rrr : Hom (++) (Cx is) t :-> D is t
  rrr f = f Refl MkCx