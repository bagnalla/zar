module Die (die_consumer, die, die_pipe, die_producer) where

import Core
import Samplers hiding (Monad)

import Pipes
import Pipes.Prelude as P (map)

die_consumer :: Monad m => Integer -> Consumer Bool m Integer
die_consumer n =
  let MkSamplers _ mkDie _ = samplers in
    integer_of_z <$> (run $ mkDie $ z_of_integer n)

die :: Integer -> IO (Effect IO Integer)
die n = do
  bits <- default_bit_producer
  return $ bits >-> die_consumer n

die_pipe :: Monad m => Integer -> Pipe Bool Integer m ()
die_pipe n =
  let MkSamplers _ mkDie _ = samplers in
    (repeat_pipe $ run_pipe $ mkDie $ z_of_integer n) >-> P.map integer_of_z

die_producer :: Integer -> IO (Producer Integer IO ())
die_producer n = do
  bits <- default_bit_producer
  return $ bits >-> die_pipe n
