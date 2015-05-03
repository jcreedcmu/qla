module QuantitiesLinearAlgebra

import Quantities.Core
import Data.Vect

-- A unit with its quantity hidden, c.f. Quantities.Core.ElemUnit'
Unit' : Type
Unit' = (q : Quantity ** Unit q)

inverse' : Unit' -> Unit'
inverse' (q ** u) = (inverse q ** unitInverse u)

-- a Float measurement at a Unit', similar to F in Quantities.Core, except
-- we've sigma'ed out the quantity.
G : Unit' -> Type
G (q ** u) = Measurement u Float

-- A "unit of measurement" for a vector is a vector of units of measurement.
UVect : Nat -> Type
UVect n = Vect n Unit'

infixr 10 :::
data TVect : UVect n -> Type where
   TNil  : TVect Nil
   (:::) : G u -> TVect us -> TVect (u :: us)

-- the product of two quantity-hidden units
infixr 10 *@
(*@) : Unit' -> Unit' -> Unit'
(u1 ** u2) *@ (v1 ** v2) = ((u1 <*> v1) ** (u2 <**> v2))

-- scalar multiplication of a unit by a uvec
infixr 10 .*
(.*) : Unit' -> UVect n -> UVect n
u .* Nil = Nil
u .* (v :: vs) = u *@ v :: (u .* vs)

uvecInverse : UVect n -> UVect n
uvecInverse [] = []
uvecInverse (h::tl) = inverse' h :: uvecInverse tl

-- a matrix has for units of measure two vectors of units of measure
-- An n x m matrix that has units [u1, ... un] x [v1, ... vm] has
-- in its (i,j) entry a number that has units ui * vj.
data Mat : UVect n -> UVect m -> Type where
  NMat : Mat Nil rs
  CMat : TVect (u .* rs) -> Mat us rs -> Mat (u :: us) rs

zeroes : (us : UVect n) -> TVect us
zeroes [] = TNil
zeroes ((_**u)::us0) = (0.0 =| u) ::: (zeroes us0)

one_and_zeroes : {us : UVect n} -> TVect ((_ ** one) :: us)
one_and_zeroes {us} = (1.0 =| one) ::: (zeroes us)

conv : a = b -> a -> b
conv Refl x = x

-- I tried for a little while to prove this, but it requires some
-- serious diligence reasoning about free abelian groups and
-- arithmetic, not to mention some headaches caused by the bureaucracy
-- of the sigma types involved.
eq_inv_head : (h : Unit') -> (scalar ** one) = (h *@ inverse' h)
-- hole

one_and_zeroes_use : {h : Unit'} -> {us : UVect n} -> TVect ((h *@ inverse' h) :: us)
one_and_zeroes_use {h} {us} = conv (cong {f= \x => TVect(x :: us)} (eq_inv_head h)) (one_and_zeroes {us})

ident_row : (z : Vect n Unit') -> TVect (h .* (z ++ (inverse' h :: uvecInverse tl)))
ident_row {h} {tl} [] = one_and_zeroes_use

-- Associativity of vector concatenation. Just a little nontrivial
-- because heterogeneous equality is in play, since the associativity
-- of addition is not obvious during type normalization.
concat_assoc : {a : Vect an t} -> {b : Vect bn t} -> {c : Vect cn t} -> (a ++ b) ++ c = a ++ (b ++ c)
concat_assoc {a=[]} = Refl
concat_assoc {a=h::tl} = hetcong h (concat_assoc {a=tl}) where
 hetcong : {x : Vect n t} -> {y : Vect m t} -> (h : t) -> x = y -> h :: x = h :: y
 hetcong h Refl = Refl

ident0 :  (z : UVect m) -> (t : UVect n) -> Mat t (z ++ (uvecInverse t))
ident0 _ [] = NMat
ident0  z (h :: tl) = CMat (ident_row z)
                           (conv (hetcong (concat_assoc))
                             (ident0 (z ++ [inverse' h]) tl))
 where
 hetcong : v1 ~=~ v2 -> Mat t v1 = Mat t v2
 hetcong Refl = Refl

-- For any U there is a matrix with units U x (1/U). Down the
-- diagonal, the units become scalar, so putting a 1 is meaningful.
-- Off-diagonal, zeroes are invariant in units.
ident :  (u : UVect n) -> Mat u (uvecInverse u)
ident u = ident0 [] u

-- Inversion of a matrix by Gauss-Jordan elimination would consist of
-- looking at an original matrix X of type Mat U V (where U and V are
-- both of length n)

--                        V
--       /--------------------------------------\

--     /  x00:u0*v0   x01:u0*v1   ...  x0n:u0*vn
--     |  x10:u1*v0   x11:u1*v1   ...  x1n:u1*vn
--  U  |     .
--     |     .
--     \  xn0:un*v0   xn1:un*v1   ...  xnn:un*vn

-- and the correspondingly shaped identity matrix of type Mat U
-- (uvecInverse U)

--                        1/U
--       /--------------------------------------\

--     /    1:1         0:u0/u1   ...    0:u0/un
--     |    0:u1/u0     1:1       ...    0:u1/un
--  U  |     .
--     |     .
--     \    0:un/u0      0un/u1   ...    1:1

-- and first doing a bunch of row normalizations: we divide the ith row
-- of both matrices by the xii entry of the matrix X that we want to
-- invert. This leaves us with a normalized X:

--                        V
--       /--------------------------------------\

--     /              x01 v1           x0n vn
--     |    1:1       ---:--      ...  ---:--
--     |              x00 v0           x00 v0
--     |
--     |    x10 v0                     x1n vn
--     |    ---:--      1:1       ...  ---:--
-- 1/V |    x11 v1                     x10 v1
--     |
--     |     .
--     |     .
--     |    xn0 v0    xn1 v1
--     |    ---:--    ---:--      ...    1:1
--     \    xnn vn    xnn vn


-- and turns the identity matrix into:

--                             1/U
--       /---------------------------------------------------\

--     /  1/x00:1/u0*v0       0:1/u1*v0   ...       0:1/un*v0
--     |
-- 1/V |      0:1/u0*v1   1/x11:1/u1*v1   ...       0:1/un*v1
--     |       .
--     |       .
--     \      0:1/u0*vn       0:1/u1*vn   ...   1/xnn:1/un*vn

-- Now we proceed to do a whole lot of adding multiplied versions of rows
-- onto other rows, but none of this changes the type of either matrix.
-- For example, to get a zero in the 1th row and 0th column, we take the
-- 0th row of the normalized X, multiply it by -x10/x11, and add it to
-- the 1th row. But the units of both vectors we are adding is (1/v1) *
-- V.

-- Similarly we multiply the 0th row of the normalized identity matrix by
-- -x10/x11 and add it to the 1th row. But the units of both vectors we
-- are adding is (1/v1) * (1/ U).
