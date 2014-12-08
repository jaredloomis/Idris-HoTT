module Main

%flag C "-O3"
%flag C "-fomit-frame-pointer"

%default total

infix 4 .=
-- | Agda-style, homogeneous equality.
data (.=) : {A : Type} -> A -> A -> Type where
    Hrefl : x .= x
{-
infix 4 -=
-- | Agda-style, homogeneous equality, with
--   the 'a' made explicit.
data (-=) : {A : Type} -> (x : A) -> (y : A) -> Type where
    Erefl : {A : Type} -> (x : A) -> x -= x
-}

basedPathInd : {A : Type} ->
               (a : A) ->
               (C : (x : A) -> (a .= x) -> Type) ->
               C a Hrefl -> ((x : A) -> (p : a .= x) -> C x p)
basedPathInd a C c .a Hrefl = c

pathInd : {A : Type} ->
  (C : (x, y : A) -> (x .= y) -> Type) ->
  (c : (x : A) -> C x x Hrefl) ->
  ((x, y : A) -> (p : x .= y) -> C x y p)
pathInd C c x y p = basedPathInd x (C x) (c x) y p

-- Mostly a translation of
-- https://github.com/HoTT/book/blob/master/coq_introduction/Reading_HoTT_in_Coq.v
-- https://github.com/tzakian/homotopy_type_theory/blob/master/C.agda

Paths : Type -> Type -> Type
Paths a b = a = b

myPaths : Paths Int Int
myPaths = Refl


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

myConcat : Int .= Int
myConcat = concat Hrefl Hrefl


transport : {A : Type} -> (f : A -> Type) -> x .= y -> f x -> f y
transport _ Hrefl x = x

myTransport : List Int
myTransport = transport List Hrefl [1,2,3]


ap : {A, B : Type} -> {x, y : A} -> (f : A -> B) -> x .= y -> f x .= f y
ap f Hrefl = Hrefl

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


-- This doesn't really work.
infix 4 ~
(~) : {A : Type} ->
      {P : A -> Type} ->
      (f, g : (x : A) -> P x) ->
      Type
(~) {A} f g = (x : A) -> f x .= g x

Sqw : {A : Type} ->
      {P : A -> Type} ->
      (f, g : (x : A) -> P x) ->
      Type
Sqw = (~)

{-
SqwId : {A : Type} ->
        (f, g : (x : A) -> x) ->
        Type
SqwId {A} f g = (x : A) -> f x .= g x
-}

data QInv : {A, B : Type} -> (f : A -> B) -> Type where
    MkQInv : {A, B : Type} ->
         (g : B -> A) ->
         (a : (x : B) -> f (g x) .= x) ->
         (b : (y : A) -> g (f y) .= y) ->
         QInv f

test : Type
test = Sqw {A = Int} {P = \_ => Int} (id . id) id

{-
data QInv' : {A, B : Type} -> (f : A -> B) -> Type where
    MkQInv' : {A, B : Type} ->
         (g : B -> A) ->
         (a : Sqw {A = B} {P = \a => a} (f . g) id) ->
         (b : (y : A) -> g (f y) .= y) ->
         QInv' f
         -}

idQInv : QInv id
idQInv = MkQInv id (\_ => Hrefl) (\_ => Hrefl)


data IsEquiv : {A, B : Type} -> (f : A -> B) -> Type where
    MkIsEquiv : {A, B : Type} ->
                (g : B -> A) ->
                (a : (x : B) -> f (g x) .= x) ->
                (h : B -> A) ->
                (b : (y : A) -> g (f y) .= y) ->
                IsEquiv {A} {B} f

equiv : {A, B : Type} -> {f : A -> B} ->
        QInv f -> IsEquiv f
equiv (MkQInv qg qa qb) = MkIsEquiv qg qa qg qb

infix 4 ~=
(~=) : (A, B : Type) -> Type
A ~= B = (a : A -> B ** IsEquiv a)

idEquiv : {A : Type} -> A ~= A
idEquiv = (id ** equiv idQInv)


equivPath : {A, B : Type} -> A .= B -> A ~= B
equivPath {A} {B} p =
    pathInd (\A', B' => const (A' ~= B'))
            (\_ => idEquiv) A B p
--equivPath Hrefl = idequiv

eqpTest : Int ~= Int
eqpTest = equivPath Hrefl


postulate univalence : {A, B : Type} -> (A .= B) ~= (A ~= B)


main : IO ()
main = putStrLn "wasabi"
