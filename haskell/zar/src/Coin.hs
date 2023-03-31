{-|
Module      : Coin
Description : Biased coin (Bernoulli distribution).
Copyright   : (c) Alexander Bagnall, 2023
License     : MIT
Maintainer  : abagnalla@gmail.com
Stability   : experimental

This module exposes an interface for constructing biased coin samplers
via abstractions provided by the Pipes package (Consumer, Producer,
Pipe, Effect, see https://hackage.haskell.org/package/pipes).
-}

{-# LANGUAGE Trustworthy #-}
module Coin (coin_consumer, coin, coin_pipe, coin_producer) where

import Core
import Samplers hiding (Monad)

import Pipes

-- | Given Integers `num` and `denom` where 0 <= `num` <= `denom` and
-- 0 < `denom`, create a Consumer that consumes bits (assumed to be
-- drawn randomly from a uniform distribution) to produce a single
-- Bool sample with Pr(True) = `num` / `denom`. The Consumer can be
-- composed with a Producer of random bits to obtain an Effect that
-- generates a single Bool sample.
coin_consumer :: Monad m
              => Integer -- ^ Numerator of bias parameter p
              -> Integer -- ^ Denominator of bias parameter p (must be positive)
              -> Consumer Bool m Bool -- ^ Consumer result
coin_consumer n d =
  let MkSamplers mkCoin _ _ = samplers in
    run $ mkCoin $ qmake n d

-- | Given Integers `num` and `denom` where 0 <= `num` <= `denom` and
-- 0 < `denom`, create an Effect that generates a single Bool sample
-- with Pr(True) = `num` / `denom`. Uses a default bit producer in the
-- IO monad based on the PRNG provided by the mwc-random package.
coin :: Integer -- ^ Numerator of bias parameter p 
     -> Integer -- ^ Denominator of bias parameter p (must be positive)
     -> IO (Effect IO Bool) -- ^ IO action that creates the Effect
coin n d = do
  bits <- default_bit_producer
  return $ bits >-> coin_consumer n d

-- | Given Integers `num` and `denom` where 0 <= `num` <= `denom` and
-- 0 < `denom`, create a Pipe that consumes bits (assumed to be drawn
-- randomly from a uniform distribution) to generate a stream of Bool
-- samples with Pr(True) = `num` / `denom`. The Pipe can be composed
-- with a Producer of random bits to obtain a Producer that generates
-- a stream of Bool samples.
coin_pipe :: Monad m
          => Integer -- ^ Numerator of bias parameter p
          -> Integer -- ^ Denominator of bias parameter p (must be positive)
          -> Pipe Bool Bool m () -- ^ Pipe result
coin_pipe n d =
  let MkSamplers mkCoin _ _ = samplers in
    run_pipe $ mkCoin $ qmake n d

-- | Given Integers `num` and `denom` where 0 <= `num` <= `denom` and
-- 0 < `denom`, create a Producer that generates a stream of Bool
-- samples with Pr(True) = `num` / `denom`. Uses a default bit
-- producer in the IO monad based on the PRNG provided by the
-- mwc-random package.
coin_producer :: Integer -- ^ Numerator of bias parameter p
              -> Integer -- ^ Denominator of bias parameter p (must be positive)
              -> IO (Producer Bool IO ()) -- ^ IO action that creates
                                          -- the Producer
coin_producer n d = do
  bits <- default_bit_producer
  return $ bits >-> coin_pipe n d
