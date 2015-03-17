module Main

import Language.Reflection

import Data.Vect

%flag C "-O3"
%flag C "-fomit-frame-pointer"

%default total

-- Mostly a translation of
-- https://github.com/HoTT/book/blob/master/coq_introduction/Reading_HoTT_in_Coq.v
-- https://github.com/tzakian/homotopy_type_theory/blob/master/C.agda

infix 4 .=
-- | Agda-style, homogeneous equality.
data (.=) : {A : Type} -> A -> A -> Type where
    Hrefl : x .= x

-- These are here to allow the use of (.=) in proofs.
hetero : (a .= b) -> (a = b)
hetero Hrefl = Refl
homo : (a = b) -> (a .= b)
homo Refl = Hrefl

basedPathInd : {A : Type} ->
               (a : A) ->
               (C : (x : A) -> (a .= x) -> Type) ->
               C a Hrefl -> ((x : A) -> (p : a .= x) -> C x p)
basedPathInd a C c .a Hrefl = c

pathInd : {A : Type} ->
    (C : (x, y : A) -> (x .= y) -> Type) ->
    (c : (x : A) -> C x x Hrefl) ->
    (x, y : A) ->
    (p : x .= y) ->
    C x y p
pathInd C c x y p = basedPathInd x (C x) (c x) y p

----

Paths : Type -> Type -> Type
Paths a b = a = b

myPaths : Paths Int Int
myPaths = Refl

----

Sect : {A, B : Type} ->
       (s : A -> B) ->
       (r : B -> A) ->
       Type
Sect {A} s r = (x : A) -> r (s x) .= x

----

-- | "Every path has an inverse".
--   ("equality is symmetric".)
inverse : x .= y -> y .= x
inverse Hrefl = Hrefl
-- inverse = sym

myInv : Int .= Int
myInv = inverse Hrefl

-- | "Paths concatenate".
--   ("Equality is transitive".)
concat : x .= y -> y .= z -> x .= z
concat Hrefl Hrefl = Hrefl
-- concat = trans
infixr 8 .-
(.-) : x .= y -> y .= z -> x .= z
(.-) Hrefl Hrefl = Hrefl

concatAssoc : (p : x .= y) -> (q : y .= z) -> (r : z .= t) ->
              (p .- q) .- r .= p .- (q .- r)
concatAssoc Hrefl Hrefl Hrefl = Hrefl

inverseInvl : (p : x .= y) -> inverse p .- p .= Hrefl
inverseInvl Hrefl = Hrefl

myConcat : Int .= Int
myConcat = concat Hrefl Hrefl

concatEq : x -> x .= y -> y .= z -> x .= z
concatEq _ = concat

syntax [x] "=|" [p] "|#" [q] = concatEq x p q
--syntax [x] "=[|" [p] "|]" [q] = concatEq x p q
--syntax [x] "=|" [p] "|#" [q] = concatEq x p q

testEq : Int .= Int
testEq = 12 =| Hrefl |# Hrefl


transport : {A : Type} -> (f : A -> Type) -> x .= y -> f x -> f y
transport _ Hrefl x = x

myTransport : List Int
myTransport = transport List Hrefl [1,2,3]

----

ap : {A, B : Type} -> {x, y : A} -> (f : A -> B) -> x .= y -> f x .= f y
ap _ Hrefl = Hrefl
-- ap = cong {f}?

myAp : List Int .= List Int
myAp = ap List Hrefl


apD : {A : Type} -> {B : A -> Type} -> {x, y : A} ->
      (f : (a : A) -> B a) -> (p : x .= y) ->
      transport B p (f x) .= f y
apD pair Hrefl = Hrefl

Vec : Type -> Nat -> Type
Vec a n = Vect n a

myApD : transport {A = Nat} (Vec Int) Hrefl Nil .= Nil
myApD = apD {B = Vec Int} (\n => replicate n 12) Hrefl

----

inCtx : {A, B : Type} -> {x, y : A} ->
    x .= y -> (f : A -> B) -> f x .= f y
inCtx p f = ap f p

-- This is hard, so I just made it an axiom...
-- TODO: Actually prove it.
postulate adj : {A, B : Type} ->
      (f  : A -> B) -> (g : B -> A) ->
      (gf : (b : B) -> f (g b) .= b) ->  -- Sect g f
      (fg : (a : A) -> g (f a) .= a) ->  -- Sect f g
      (a : A) -> gf (f a) .= ap f (fg a)

unitR : {A : Type} -> {x, y : A} ->
        (q : x .= y) -> q .- Hrefl .= q
unitR Hrefl = Hrefl

unitL : {A : Type} -> {x, y : A} ->
        (q : x .= y) -> Hrefl .- q .= q
unitL Hrefl = Hrefl

antiWhiskerR : {A : Type} -> {x, y, z : A} -> {q, r : x .= y} ->
  (p : y .= z) -> (q .- p .= r .- p -> q .= r)
antiWhiskerR {q=q} {r=r} Hrefl h =
    let unitq = unitR q
        unitr = unitR r
    in ?antiWR

Main.antiWR = proof
  intro
  intro
  intro
  intro
  intro
  intro
  rewrite (hetero h)
  intros
  rewrite (hetero unitr)
  rewrite sym (hetero unitq)
  exact Hrefl

htpyNatural : {A, B : Type} -> {x, y : A} -> {f, g : A -> B} ->
  (p : (x : A) -> (f x .= g x)) -> (q : x .= y) -> ap f q .- p y .= p x .- ap g q
htpyNatural {x} p Hrefl =
    let fg = p x
    in ?htpyNatural_p

Main.htpyNatural_p = proof
  intros
  rewrite sym (hetero (unitR (p x)))
  rewrite sym (hetero (unitL (p x)))
  exact Hrefl

idf : (A : Type) -> (A -> A)
idf A = \x => x

apIdf : {A : Type} -> {u, v : A} ->
        (p : u .= v) -> ap (idf A) p .= p
apIdf Hrefl = Hrefl

-- infix 4 ~
-- (~) : {A : Type} ->
--      {B : Type} ->
--      (f, g : A -> B) ->
--      Type
-- (~) {A} f g = (x : A) -> f x .= g x

data QInv : {A, B : Type} -> (f : A -> B) -> Type where
    MkQInv : {A, B : Type} ->
             (g : B -> A) ->
             (a : Sect g f) ->
             (b : Sect f g) ->
             QInv f

idQInv : QInv id
idQInv = MkQInv id (\_ => Hrefl) (\_ => Hrefl)

----

data IsEquiv : {A, B : Type} -> (f : A -> B) -> Type where
    MkIsEquiv : {A, B : Type} ->
        (g   : B -> A) ->
        (gf  : Sect g f) ->
        (fg  : Sect f g) ->
        (adj : (a : A) -> gf (f a) .= ap f (fg a)) ->
        IsEquiv f

equiv : QInv f -> IsEquiv f
equiv {f} (MkQInv g gf fg) = MkIsEquiv g gf fg (adj f g gf fg)

----

infix 4 ~=
(~=) : (A, B : Type) -> Type
A ~= B = (a : A -> B ** IsEquiv a)

ide : {A : Type} -> A ~= A
ide = (id ** equiv idQInv)

equivPath : {A, B : Type} -> A .= B -> A ~= B
equivPath {A} {B} p =
    pathInd (\A', B' => const (A' ~= B'))
            (\_ => ide) A B p

----

postulate univalence      : (a ~= b) -> (a .= b)
postulate univalenceEquiv : (a .= b) ~= (a ~= b)

-- Doing an actual proof. We will prove that NatClone
-- is equivalent to Nat, then use the univalence axiom
-- to conclude that they are equial.

data NatClone = CZ | CS NatClone

natToClone : Nat -> NatClone
natToClone (S n) = CS (natToClone n)
natToClone  Z    = CZ

cloneToNat : NatClone -> Nat
cloneToNat (CS n) = S (cloneToNat n)
cloneToNat  CZ    = Z

leftSect : Sect cloneToNat natToClone
leftSect  CZ    = Hrefl
leftSect (CS n) = ap CS (leftSect n)

rightSect : Sect natToClone cloneToNat
rightSect  Z    = Hrefl
rightSect (S n) = ap S (rightSect n)

isEquivNatClone : IsEquiv natToClone
isEquivNatClone = MkIsEquiv cloneToNat leftSect rightSect
            (adj natToClone cloneToNat leftSect rightSect)

equivNatClone : Nat ~= NatClone
equivNatClone = (natToClone ** isEquivNatClone)

equalNatClone : Nat .= NatClone
equalNatClone = univalence equivNatClone

hfiber : {A, B : Type} -> (f : A -> B) -> (y : B) -> Type
hfiber {A} f y = (x : A ** f x .= y)
