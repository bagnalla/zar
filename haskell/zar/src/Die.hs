{-|
Module      : Die
Description : N-sided die (uniform distribution).
Copyright   : (c) Alexander Bagnall, 2023
License     : MIT
Maintainer  : abagnalla@gmail.com
Stability   : experimental

This module exposes an interface for constructing n-sided die samplers
via abstractions provided by the pipes package (Consumer, Producer,
Pipe, Effect, see https://hackage.haskell.org/package/pipes).
-}

{-# LANGUAGE Trustworthy #-}
module Die (die_consumer, die, die_pipe, die_producer) where

import Core
import Samplers hiding (Monad)

import Pipes
import Pipes.Prelude as P (map)

-- | Given positive Integer `n`, create a Consumer that consumes bits
-- (assumed to be drawn randomly from a uniform distribution) to
-- produce a single Integer sample with Pr(`k`) = 1 / `n` for all 0 <=
-- `k` < `n`. The Consumer can be composed with a Producer of random
-- bits to obtain an Effect that generates a single Integer sample.
die_consumer :: Monad m => Integer -> Consumer Bool m Integer
die_consumer n =
  let MkSamplers _ mkDie _ = samplers in
    integer_of_z <$> (run $ mkDie $ z_of_integer n)

-- | Given positive Integer `n`, create an Effect that generates a
-- single Integer sample with Pr('k') = 1 / `n` for all 0 <= 'k' <
-- 'n'. Uses a default bit producer in the IO monad based on the PRNG
-- provided by the mwc-random package.
die :: Integer -> IO (Effect IO Integer)
die n = do
  bits <- default_bit_producer
  return $ bits >-> die_consumer n

-- | Given positive Integer `n`, create a Pipe that consumes bits
-- (assumed to be drawn randomly from a uniform distribution) to
-- generate a stream of Integer samples with Pr(`k`) = 1 / `n' for all
-- 0 <= `k` < `n`. The Pipe can be composed with a Producer of random
-- bits to obtain a Producer that generates a stream of Integer
-- samples.
die_pipe :: Monad m => Integer -> Pipe Bool Integer m ()
die_pipe n =
  let MkSamplers _ mkDie _ = samplers in
    (run_pipe $ mkDie $ z_of_integer n) >-> P.map integer_of_z

-- | Given positive Integer `n`, create a Producer that generates a
-- stream of Integer samples with Pr('k') = 1 / `n` for all 0 <= `k` <
-- `n`. Uses a default bit producer in the IO monad based on the PRNG
-- provided by the mwc-random package.
die_producer :: Integer -> IO (Producer Integer IO ())
die_producer n = do
  bits <- default_bit_producer
  return $ bits >-> die_pipe n
