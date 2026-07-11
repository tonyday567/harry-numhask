{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- | numhask orphan instances and shim for harpie.
--
-- This module targets the generic 'Harpie.Fixed.Generic.Array' so that the
-- same instances work for boxed, storable and unboxed backing vectors.
module Harpie.NumHask
  ( -- * Usage
    -- $usage
    ident,
    undiag,
    mult,
    invtri,
    inverse,
    chol,
  )
where

import Data.Foldable as Foldable (sum)
import Data.Vector.Generic qualified as VG
import Data.Vector.Unboxed qualified as VU
import Fcf qualified
import GHC.TypeNats
import Harpie.Fixed.Generic as F hiding (chol, ident, inverse, invtri, mult, undiag)
import Harpie.Shape (DeleteDims, Eval, GetDims, KnownNats, Rank, type (++))
import Harpie.Shape qualified as S
import NumHask.Prelude as P hiding (Min, cycle, diff, drop, empty, find, length, repeat, sequence, sum, take, zipWith)

-- $setup
--
-- >>> :m -Prelude
-- >>> :set -XDataKinds
-- >>> :set -XRebindableSyntax
-- >>> import NumHask.Prelude hiding (cycle, repeat, empty, diff, take, drop, zipWith, find)
-- >>> import Harpie.Fixed.Generic qualified as F
-- >>> import Harpie.Fixed.Generic (Array, array, range, shape, toDynamic)
-- >>> import Harpie.NumHask
-- >>> import Prettyprinter hiding (dot,fill)
--
-- >>> s = 1 :: Array Data.Vector.Vector '[] Int
-- >>> s
-- [1]
-- >>> shape s
-- []
-- >>> pretty s
-- 1
-- >>> let v = range @'[3]
-- >>> pretty v
-- [0,1,2]
-- >>> let m = range @[2,3]
-- >>> pretty m
-- [[0,1,2],
--  [3,4,5]]
-- >>> a = range @[2,3,4]
-- >>> a
-- [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
-- >>> pretty a
-- [[[0,1,2,3],
--   [4,5,6,7],
--   [8,9,10,11]],
--  [[12,13,14,15],
--   [16,17,18,19],
--   [20,21,22,23]]]
-- >>> toDynamic a
-- UnsafeArray [2,3,4] [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23]

-- * NumHask heirarchy

instance
  ( Additive a,
    KnownNats s,
    VG.Vector v a
  ) =>
  Additive (Array v s a)
  where
  (+) = zipWith (+)

  zero = konst zero

instance
  ( Subtractive a,
    KnownNats s,
    VG.Vector v a
  ) =>
  Subtractive (Array v s a)
  where
  negate = fmapA negate

instance
  ( Multiplicative a,
    KnownNats s,
    VG.Vector v a
  ) =>
  MultiplicativeAction (Array v s a)
  where
  type Scalar (Array v s a) = a
  (|*) r s = fmapA (s *) r

instance
  ( Additive a,
    KnownNats s,
    VG.Vector v a
  ) =>
  AdditiveAction (Array v s a)
  where
  type AdditiveScalar (Array v s a) = a
  (|+) r s = fmapA (s +) r

instance
  ( Subtractive a,
    KnownNats s,
    VG.Vector v a
  ) =>
  SubtractiveAction (Array v s a)
  where
  (|-) r s = fmapA (\x -> x - s) r

instance
  ( Divisive a,
    KnownNats s,
    VG.Vector v a
  ) =>
  DivisiveAction (Array v s a)
  where
  (|/) r s = fmapA (/ s) r

instance
  ( KnownNats s,
    JoinSemiLattice a,
    VG.Vector v a,
    Eq (v a)
  ) =>
  JoinSemiLattice (Array v s a)
  where
  (\/) = zipWith (\/)

instance
  ( KnownNats s,
    MeetSemiLattice a,
    VG.Vector v a,
    Eq (v a)
  ) =>
  MeetSemiLattice (Array v s a)
  where
  (/\) = zipWith (/\)

instance
  ( KnownNats s,
    Subtractive a,
    Epsilon a,
    VG.Vector v a,
    Eq (v a)
  ) =>
  Epsilon (Array v s a)
  where
  epsilon = konst epsilon

instance
  ( FromInteger a,
    VG.Vector v a
  ) =>
  FromInteger (Array v ('[] :: [Nat]) a)
  where
  fromInteger x = toScalar (fromInteger x)

instance
  ( FromRational a,
    VG.Vector v a
  ) =>
  FromRational (Array v ('[] :: [Nat]) a)
  where
  fromRational x = toScalar (fromRational x)

-- | The identity array.
--
-- >>> pretty $ ident @[3,3]
-- [[1,0,0],
--  [0,1,0],
--  [0,0,1]]
ident ::
  ( KnownNats s,
    Additive a,
    Multiplicative a,
    VG.Vector v a
  ) =>
  Array v s a
ident = tabulate (bool zero one . S.isDiag . VU.fromList . S.fromFins)

-- | Expand the array to form a diagonal array
--
-- >>> pretty $ undiag (range @'[3])
-- [[0,0,0],
--  [0,1,0],
--  [0,0,2]]
undiag ::
  forall v s' a s.
  ( KnownNats s,
    KnownNats s',
    s' ~ Eval ((++) s s),
    Additive a,
    VG.Vector v a
  ) =>
  Array v s a ->
  Array v s' a
undiag a = tabulate (\xs -> bool zero (index a (S.UnsafeFins $ pure $ S.getDim 0 (VU.fromList (S.fromFins xs)))) (S.isDiag (VU.fromList (S.fromFins xs))))

-- | Array multiplication.
--
-- matrix multiplication
--
-- >>> pretty $ mult m (F.transpose m)
-- [[5,14],
--  [14,50]]
--
-- inner product
--
-- >>> pretty $ mult v v
-- 5
--
-- matrix-vector multiplication
--
-- >>> pretty $ mult v (F.transpose m)
-- [5,14]
--
-- >>> pretty $ mult m v
-- [5,14]
mult ::
  forall v a ds0 ds1 s0 s1 so0 so1 st si.
  ( Ring a,
    KnownNats s0,
    KnownNats s1,
    KnownNats ds0,
    KnownNats ds1,
    KnownNats so0,
    KnownNats so1,
    KnownNats st,
    KnownNats si,
    so0 ~ Eval (DeleteDims ds0 s0),
    so1 ~ Eval (DeleteDims ds1 s1),
    si ~ Eval (GetDims ds0 s0),
    si ~ Eval (GetDims ds1 s1),
    st ~ Eval ((++) so0 so1),
    ds0 ~ '[Eval ((Fcf.-) (Eval (Rank s0)) 1)],
    ds1 ~ '[0],
    Num a,
    VG.Vector v a,
    VG.Vector v (Array v si a)
  ) =>
  Array v s0 a ->
  Array v s1 a ->
  Array v st a
mult = dot sumA (*)

instance
  ( Multiplicative a,
    P.Distributive a,
    Subtractive a,
    Num a,
    KnownNat m,
    VG.Vector v a,
    VG.Vector v (Array v '[m, m] a),
    VG.Vector v (Array v '[m] a),
    VG.Vector v Int
  ) =>
  Multiplicative (Matrix v m m a)
  where
  (*) = mult

  one = ident

instance
  ( Multiplicative a,
    P.Distributive a,
    Subtractive a,
    Eq a,
    ExpField a,
    Num a,
    KnownNat m,
    VG.Vector v a,
    VG.Vector v (Array v '[m, m] a),
    VG.Vector v (Array v '[m] a),
    VG.Vector v Int,
    Functor v
  ) =>
  Divisive (Matrix v m m a)
  where
  recip a = invtri (transpose (chol a)) * invtri (chol a)

-- | Inverse of a square matrix.
--
-- > mult (inverse a) a == a
--
-- >>> e = array @[3,3] @Double [4,12,-16,12,37,-43,-16,-43,98]
-- >>> pretty (inverse e)
-- [[49.36111111111111,-13.555555555555554,2.1111111111111107],
--  [-13.555555555555554,3.7777777777777772,-0.5555555555555555],
--  [2.1111111111111107,-0.5555555555555555,0.1111111111111111]]
inverse ::
  ( Eq a,
    ExpField a,
    Num a,
    KnownNat m,
    VG.Vector v a,
    VG.Vector v (Array v '[m, m] a),
    VG.Vector v (Array v '[m] a),
    VG.Vector v Int,
    Functor v
  ) =>
  Matrix v m m a ->
  Matrix v m m a
inverse a = mult (invtri (transpose (chol a))) (invtri (chol a))

-- | [Inversion of a Triangular Matrix](https://math.stackexchange.com/questions/1003801/inversion-of-an-invertible-upper-triangular-matrix-of-order-3)
--
-- >>> t = array @[3,3] @Double [1,0,1,0,1,2,0,0,1]
-- >>> pretty (invtri t)
-- [[1.0,0.0,-1.0],
--  [0.0,1.0,-2.0],
--  [0.0,0.0,1.0]]
--
-- > ident == mult t (invtri t)
-- True
invtri ::
  forall v a n.
  ( KnownNat n,
    ExpField a,
    Eq a,
    Num a,
    VG.Vector v a,
    VG.Vector v (Array v '[n, n] a),
    VG.Vector v (Array v '[n] a),
    VG.Vector v Int,
    Functor v
  ) =>
  Matrix v n n a ->
  Matrix v n n a
invtri a = sumA (fmapA (l ^) (iota @v @n)) * ti
  where
    ti = undiag (fmapA recip (diag a))
    tl = a - undiag (diag a)
    l = negate (ti * tl)

-- | cholesky decomposition
--
-- Uses the <https://en.wikipedia.org/wiki/Cholesky_decomposition#The_Cholesky_algorithm Cholesky-Crout> algorithm.
--
-- >>> e = array @[3,3] @Double [4,12,-16,12,37,-43,-16,-43,98]
-- >>> pretty (chol e)
-- [[2.0,0.0,0.0],
--  [6.0,1.0,0.0],
--  [-8.0,5.0,3.0]]
-- >>> mult (chol e) (F.transpose (chol e)) == e
-- True
chol ::
  ( KnownNat m,
    ExpField a,
    Num a,
    VG.Vector v a,
    VG.Vector v Int
  ) =>
  Matrix v m m a ->
  Matrix v m m a
chol a =
  let l =
        unsafeTabulate
          ( \[i, j] ->
              bool
                ( one
                    / unsafeIndex l [j, j]
                    * ( unsafeIndex a [i, j]
                          - Foldable.sum
                            ( (\k -> unsafeIndex l [i, k] * unsafeIndex l [j, k])
                                <$> ([0 .. (j - 1)] :: [Int])
                            )
                      )
                )
                ( sqrt
                    ( unsafeIndex a [i, i]
                        - Foldable.sum
                          ( (\k -> unsafeIndex l [j, k] ^ (2 :: Int))
                              <$> ([0 .. (j - 1)] :: [Int])
                          )
                    )
                )
                (i == j)
          )
   in l
