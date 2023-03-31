{-|
Module      : Core
Description : TCB (trusted computing base).
Copyright   : (c) Alexander Bagnall, 2023
License     : MIT
Maintainer  : abagnalla@gmail.com
Stability   : experimental

This module contains core definitions for the Zar verified sampling
package including conversion functions for numeric types, pipe
helpers, and driver code for running interaction tree samplers. This
is essentially the TCB (trusted computing base) of the Zar
package. The numeric conversion functions are thoroughly tested using
QuickCheck (see the test/ directory in the the project's Github
repository).

A user of the Zar package normally does not need to use anything in
this module directly. The high-level interface for building samplers
is provided by the Coin, Die, and Findist modules.
-}

{-# LANGUAGE Trustworthy #-}
module Core
    ( positive_of_integer,
      integer_of_positive,
      z_of_integer,
      integer_of_z,
      run,
      run_pipe,
      qmake,
      bit_producer,
      default_bit_producer
    ) where

import Samplers hiding (Monad)

import Control.Monad.Primitive
import Pipes
import System.Random.MWC as MWC

-- | Convert Integer to Positive (the type of binary-encoded positive
-- integers extracted from Coq).
positive_of_integer :: Integer -- ^ Integer to convert to Positive
                    -> Positive -- ^ Positive result
positive_of_integer n =
  if n <= 0 then
    error $ "positive_of_integer: input must be positive, got " ++ show n
  else
    go n
  where
    go :: Integer -> Positive
    go j =
      if j == 1 then
        XH
      else if j `mod` 2 == 0 then
        XO $ go $ j `div` 2
      else
        XI $ go $ j `div` 2

-- | Convert Positive to Integer.
integer_of_positive :: Positive -- ^ Positive to convert to Integer
                    -> Integer -- ^ Integer result
integer_of_positive XH = 1
integer_of_positive (XO p) = 2 * integer_of_positive p
integer_of_positive (XI p) = 2 * integer_of_positive p + 1

-- | Convert Integer to Z (the type of binary-encoded integers
-- extracted from Coq)
z_of_integer :: Integer -- ^ Integer to be converted to Z
             -> Z -- ^ Z result
z_of_integer n | n < 0 = Zneg $ positive_of_integer $ - n
z_of_integer n | n > 0 = Zpos $ positive_of_integer n
z_of_integer _ = Z0

-- | Convert Z to Integer.
integer_of_z :: Z -- ^ Z to be converted to Integer
             -> Integer -- ^ Integer result
integer_of_z Z0 = 0
integer_of_z (Zpos p) = integer_of_positive p
integer_of_z (Zneg p) = - integer_of_positive p

-- | Build Q (the type of rationals extracted from Coq) from numerator
-- and denominator Integers.
qmake :: Integer -- ^ Numerator
      -> Integer -- ^ Denominator (must be positive)
      -> Q -- ^ Q result
qmake n d = Qmake (z_of_integer n) (positive_of_integer d)

-- | Create a Bool Producer with from a given MWC PRNG state.
bit_producer :: PrimMonad m
             => Gen (PrimState m) -- ^ MWC PRNG state
             -> Producer Bool m a -- ^ Boolean Producer using the input PRNG
bit_producer gen = do
  b <- lift $ uniform gen
  yield b
  bit_producer gen

-- | Default implementation of uniform random bit stream in the IO
-- monad. Uses the PRNG provided by the mwc-random package.
default_bit_producer :: IO (Producer Bool IO a)
default_bit_producer = bit_producer <$> MWC.createSystemRandom

-- | Construct from a given interaction tree sampler a Consumer that
-- consumes bits (assumed to be drawn randomly from a uniform
-- distribution) to produce a single output sample.
run :: Monad m
    => Itree () a -- ^ Interaction tree sampler
    -> Consumer Bool m a -- ^ Consumer that can be composed with a
                         -- Bool Producer to obtain an Effect with
                         -- return type 'a'
run t = case observe t of
  RetF x -> return x
  TauF t' -> run t'
  VisF _ k -> await >>= run . k . unsafeCoerce -- Coerce Bool to Any

-- | Construct from a given interaction tree sampler a Pipe that
-- consumes bits (assumed to be drawn randomly from a uniform
-- distribution) to generate a stream of output samples.
run_pipe :: Monad m
         => Itree () a -- ^ Interaction tree sampler
         -> Pipe Bool a m () -- ^ Pipe that can be composed with a
                             -- Bool Producer to obtain a Producer
                             -- that generates samples of type 'a'
run_pipe t = go t >> run_pipe t
  where
    go :: Monad m => Itree () a -> Pipe Bool a m ()
    go t' = case observe t' of
             RetF x -> yield x
             TauF t'' -> go t''
             VisF _ k -> await >>= go . k . unsafeCoerce -- Coerce Bool to Any
