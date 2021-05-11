module Somewhere.Lambda

import Data.List
import Somewhere.Species
import Somewhere.Thinning
import Somewhere.Schanuel

%default total

V : a -> Sp a
V x = Thin [x]

v : {z : a} -> V z :=> Var z
v = MkSh MkVar

data Ty = U | Imp Ty Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

data Db : Ty -> Sp Ty where
  VarDb : V x :-> Db x
  LamDb : Hom (flip (++)) (Cx [a]) (Db b) :-> Db (a ~> b)
  AppDb : {a : Ty} -> Db (a~>b) :*: Db a :-> Db b

mapDb : {ys : List Ty} -> Thin xs ys -> Db a xs -> Db a ys
mapDb th (VarDb v)      = VarDb $ compThin v th
mapDb th (LamDb h)      = LamDb $ \sp, cx => case cx of
                                               MkCx => rewrite sym sp in
                                                       mapDb (Take th) (h Refl MkCx)
mapDb th (AppDb (f, x)) = AppDb (mapDb th f, mapDb th x)

lamDb : {xs : List Ty} -> Db b (a::xs) -> Db (a~>b) xs
lamDb e = LamDb $ \sp, cx => case cx of
                             MkCx => rewrite sym sp in e

iDb : {x : Ty} -> {xs : List Ty} -> Db (x~>x) xs
iDb = lamDb $ VarDb $ Take skips

kDb : {x,y : Ty} -> {xs : List Ty} -> Db (x~>y~>x) xs
kDb = lamDb $ lamDb $ VarDb $ Skip $ Take skips

sDb : {x,y,z : Ty} -> {xs : List Ty} -> Db ((x~>y~>z)~>(x~>y)~>x~>z) xs
sDb = lamDb $ lamDb $ lamDb $ AppDb ( AppDb (VarDb $ Skip $ Skip $ Take skips, VarDb $ Take skips)
                                    , AppDb (VarDb $        Skip $ Take skips, VarDb $ Take skips))

data CoDb : Ty -> Sp Ty where
  VarCDb : Var x :-> CoDb x
  LamCDb : Bind [a] (CoDb b) :-> CoDb (a ~> b)
  AppCDb : Ten (CoDb (x~>y)) (CoDb x) :-> CoDb y

convert : {t : Ty} -> Db t :=> CoDb t
convert (VarDb e)          = mapSh VarCDb (v e)
convert (LamDb h)          = mapSh LamCDb $ iso1 $ \eq, cx => convert $ h eq cx
convert (AppDb {a} (f, u)) = mapSh AppCDb $ pair (convert f) (convert u)

iCDb : {x : Ty} -> {xs : List Ty} -> Sh (CoDb (x~>x)) xs
iCDb = convert iDb

kCDb : {x,y : Ty} -> {xs : List Ty} -> Sh (CoDb (x~>y~>x)) xs
kCDb = convert kDb

sCDb : {x,y,z : Ty} -> {xs : List Ty} -> Sh (CoDb ((x~>y~>z)~>(x~>y)~>x~>z)) xs
sCDb = convert sDb
