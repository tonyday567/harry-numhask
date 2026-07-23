{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Value-sized square matrices backed by 'Harpie.Array'.
--
-- This module provides the canonical matrix carrier for numhask-based
-- computation: Kleene star (reflexive-transitive closure), matrix
-- multiplication, and matrix-vector products. It is intentionally
-- rank-2 and value-sized so it can serve categories whose object
-- constraints live at runtime (e.g. 'Finite' enumeration or plain list
-- channels) as well as typed settings.
module Harpie.NumHask.Matrix
  ( Matrix (..),
    fromLists,
    toLists,
    matPlus,
    matTimes,
    matVec,
    starMatrix,
  )
where

import Data.Bool (bool)
import Data.List (foldl')
import Data.Vector.Unboxed qualified as VU
import Harpie.Array as A
import NumHask.Algebra.Additive (Additive (..), sum)
import NumHask.Algebra.Multiplicative (Multiplicative (..))
import NumHask.Algebra.Ring (StarSemiring (..))
import Prelude hiding ((+), (*), drop, foldl', length, repeat, sum, take, zipWith)
import Prelude qualified as P

-- | Square matrix stored as a rank-2 'Harpie.Array' in row-major order.
newtype Matrix a = Matrix {unMatrix :: A.Array a}
  deriving (Eq, Show)

-- | Row count.
rows :: Matrix a -> Int
rows (Matrix a) = case VU.toList (A.shape a) of (r : _) -> r; _ -> 0

-- | Column count.
cols :: Matrix a -> Int
cols (Matrix a) = case VU.toList (A.shape a) of (_ : c : _) -> c; _ -> 0

-- | Build a matrix from nested rows.
--
-- An empty list becomes a 0×0 matrix.
fromLists :: [[a]] -> Matrix a
fromLists [] = Matrix (A.array [0, 0] [])
fromLists xss@(r : _) = Matrix (A.array [P.length xss, P.length r] (P.concat xss))

-- | Convert a matrix to nested rows.
toLists :: Matrix a -> [[a]]
toLists (Matrix a) =
  let r = rows (Matrix a)
      c = cols (Matrix a)
   in [[a A.! [i, j] | j <- [0 .. c - 1]] | i <- [0 .. r - 1]]

-- | Elementwise addition.
matPlus :: (Additive a) => Matrix a -> Matrix a -> Matrix a
matPlus (Matrix a) (Matrix b) = Matrix (A.zipWith (+) a b)

-- | Matrix multiplication.
matTimes ::
  (Additive a, Multiplicative a) =>
  Matrix a ->
  Matrix a ->
  Matrix a
matTimes (Matrix a) (Matrix b) =
  case (VU.toList (A.shape a), VU.toList (A.shape b)) of
    ([ra, ca], [rb, cb]) ->
      case ca == rb of
        False -> error "Harpie.NumHask.Matrix.matTimes: inner dimension mismatch"
        True ->
          Matrix $
            A.tabulate [ra, cb]
              ( \ij -> case ij of
                  [i, j] -> sum [a A.! [i, k] * b A.! [k, j] | k <- [0 .. ca - 1]]
                  _ -> error "Harpie.NumHask.Matrix.matTimes: expected rank-2 index"
              )
    _ -> error "Harpie.NumHask.Matrix.matTimes: expected rank-2 matrices"

-- | Matrix–vector product.
matVec ::
  (Additive a, Multiplicative a) =>
  Matrix a ->
  [a] ->
  [a]
matVec (Matrix a) v =
  case VU.toList (A.shape a) of
    [r, c] ->
      let n = P.length v
       in case c == n of
            False -> error "Harpie.NumHask.Matrix.matVec: dimension mismatch"
            True ->
              [ sum [a A.! [i, k] * (v P.!! k) | k <- [0 .. c - 1]]
                | i <- [0 .. r - 1]
              ]
    _ -> error "Harpie.NumHask.Matrix.matVec: expected a rank-2 matrix"

-- | Kleene star of a square matrix by the standard state-elimination
-- (Warshall / Floyd-Kleene) algorithm.
--
-- For a matrix @A@, computes @A* = I + A + A² + ...@ as the least fixed
-- point of @X ↦ I + A·X@. Requires a 'StarSemiring' element type so that
-- @star x@ is available for the pivot updates.
starMatrix ::
  (StarSemiring a) =>
  Matrix a ->
  Matrix a
starMatrix (Matrix a) =
  let sh = VU.toList (A.shape a)
   in case sh of
        [0, 0] -> Matrix a
        [n, m]
          | n == m ->
              let step arr k =
                    A.tabulate [n, n]
                      ( \ij -> case ij of
                          [i, j] ->
                            let mkk = arr A.! [k, k]
                                mik = arr A.! [i, k]
                                mkj = arr A.! [k, j]
                             in arr A.! [i, j] + mik * star mkk * mkj
                          _ -> error "Harpie.NumHask.Matrix.starMatrix: expected rank-2 index"
                      )
                  closed = foldl' step a [0 .. n - 1]
                  eye = A.array [n, n] [bool zero one (i == j) | i <- [0 .. n - 1], j <- [0 .. n - 1]]
               in Matrix (A.zipWith (+) closed eye)
        _ -> error "Harpie.NumHask.Matrix.starMatrix: expected a square matrix"
