module Findist (findist_consumer, findist, findist_pipe, findist_producer) where

import Core
import Samplers hiding (Monad)

import Pipes
import Pipes.Prelude as P (map)

findist_consumer :: Monad m => [Integer] -> Consumer Bool m Integer
findist_consumer weights =
  let MkSamplers _ _ mkFindist = samplers in
    integer_of_z <$> (run $ mkFindist $ z_of_integer <$> weights)

findist :: [Integer] -> IO (Effect IO Integer)
findist weights = do
  bits <- default_bit_producer
  return $ bits >-> findist_consumer weights

findist_pipe :: Monad m => [Integer] -> Pipe Bool Integer m ()
findist_pipe weights =
  let MkSamplers _ _ mkFindist = samplers in
    (repeat_pipe $ run_pipe $ mkFindist $ z_of_integer <$> weights)
    >-> P.map integer_of_z

findist_producer :: [Integer] -> IO (Producer Integer IO ())
findist_producer weights = do
  bits <- default_bit_producer
  return $ bits >-> findist_pipe weights
