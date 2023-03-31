{-|
Module      : Findist
Description : Finite distribution.
Copyright   : (c) Alexander Bagnall, 2023
License     : MIT
Maintainer  : abagnalla@gmail.com
Stability   : experimental

This module exposes an interface for constructing finite distribution
samplers via abstractions provided by the Pipes package (Consumer,
Producer, Pipe, Effect, see
https://hackage.haskell.org/package/pipes).
-}

{-# LANGUAGE Trustworthy #-}
module Findist (findist_consumer, findist, findist_pipe, findist_producer) where

import Core
import Samplers hiding (Monad)

import Pipes
import Pipes.Prelude as P (map)

-- | Given list of nonnegative Integers `weights` with at least one
-- nonzero element, create a Consumer that consumes bits (assumed to
-- be drawn randomly from a uniform distribution) to produce a single
-- Integer sample with Pr(`k`) = weightsₖ / ∑ᵢweightsᵢ for all 0 <=
-- `k` < |`weights`|. The Consumer can be composed with a Producer of
-- random bits to obtain an Effect that generates a single Integer
-- sample.
findist_consumer :: Monad m => [Integer] -> Consumer Bool m Integer
findist_consumer weights =
  let MkSamplers _ _ mkFindist = samplers in
    integer_of_z <$> (run $ mkFindist $ z_of_integer <$> weights)

-- | Given list of nonnegative Integers `weights` with at least one
-- nonzero element, create an Effect that generates a single Integer
-- sample with Pr(`k`) = weightsₖ / ∑ᵢweightsᵢ for all 0 <= `k` <
-- |`weights`|. Uses a default bit producer in the IO monad based on
-- the PRNG provided by the mwc-random package.
findist :: [Integer] -> IO (Effect IO Integer)
findist weights = do
  bits <- default_bit_producer
  return $ bits >-> findist_consumer weights

-- | Given list of nonnegative Integers `weights` with at least one
-- nonzero element, create a Pipe that consumes bits (assumed to be
-- drawn randomly from a uniform distribution) to generate a stream of
-- Integer samples with Pr(`k`) = weightsₖ / ∑ᵢweightsᵢ for all 0 <= `k` <
-- |`weights`|. The Pipe can be composed with a Producer of random
-- bits to obtain a Producer that generates a stream of Integer
-- samples.
findist_pipe :: Monad m => [Integer] -> Pipe Bool Integer m ()
findist_pipe weights =
  let MkSamplers _ _ mkFindist = samplers in
    (run_pipe $ mkFindist $ z_of_integer <$> weights)
    >-> P.map integer_of_z

-- | Given list of nonnegative Integers `weights` with at least one
-- nonzero element, create a Producer that generates a stream of
-- Integer samples with Pr(`k`) = weightsₖ / ∑ᵢweightsᵢ for all 0 <= `k` <
-- |`weights`|. Uses a default bit producer in the IO monad based on
-- the PRNG provided by the mwc-random package.
findist_producer :: [Integer] -> IO (Producer Integer IO ())
findist_producer weights = do
  bits <- default_bit_producer
  return $ bits >-> findist_pipe weights
