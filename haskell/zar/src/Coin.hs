module Coin (coin_consumer, coin, coin_pipe, coin_producer) where

import Core
import Samplers hiding (Monad)

import Pipes

coin_consumer :: Monad m => Integer -> Integer -> Consumer Bool m Bool
coin_consumer n d =
  let MkSamplers mkCoin _ _ = samplers in
    run $ mkCoin $ qmake n d

coin :: Integer -> Integer -> IO (Effect IO Bool)
coin n d = do
  bits <- default_bit_producer
  return $ bits >-> coin_consumer n d

coin_pipe :: Monad m => Integer -> Integer -> Pipe Bool Bool m ()
coin_pipe n d =
  let MkSamplers mkCoin _ _ = samplers in
    repeat_pipe $ run_pipe $ mkCoin $ qmake n d

coin_producer :: Integer -> Integer -> IO (Producer Bool IO ())
coin_producer n d = do
  bits <- default_bit_producer
  return $ bits >-> coin_pipe n d
