module Core
    ( positive_of_integer,
      integer_of_positive,
      z_of_integer,
      integer_of_z,
      run,
      run_pipe,
      repeat_pipe,
      qmake,
      bit_producer,
      default_bit_producer
    ) where

import Samplers hiding (Monad)

import Pipes
import System.Random.MWC as MWC

positive_of_integer :: Integer -> Positive
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

integer_of_positive :: Positive -> Integer
integer_of_positive XH = 1
integer_of_positive (XO p) = 2 * integer_of_positive p
integer_of_positive (XI p) = 2 * integer_of_positive p + 1

z_of_integer :: Integer -> Z
z_of_integer n | n < 0 = Zneg $ positive_of_integer $ - n
z_of_integer n | n > 0 = Zpos $ positive_of_integer n
z_of_integer _ = Z0

integer_of_z :: Z -> Integer
integer_of_z Z0 = 0
integer_of_z (Zpos p) = integer_of_positive p
integer_of_z (Zneg p) = - integer_of_positive p

qmake :: Integer -> Integer -> Q
qmake n d = Qmake (z_of_integer n) (positive_of_integer d)

bit_producer :: GenIO -> Producer Bool IO a
bit_producer gen = do
  b <- lift $ uniform gen
  yield b
  bit_producer gen

default_bit_producer :: IO (Producer Bool IO a)
default_bit_producer = bit_producer <$> MWC.createSystemRandom

run :: Monad m => Itree () a -> Consumer Bool m a
run t = case observe t of
  RetF x -> return x
  TauF t' -> run t'
  VisF _ k -> await >>= run . k . unsafeCoerce

run_pipe :: Monad m => Itree () a -> Pipe Bool a m ()
run_pipe t = case observe t of
  RetF x -> yield x
  TauF t' -> run_pipe t'
  VisF _ k -> await >>= run_pipe . k . unsafeCoerce

repeat_pipe :: Monad m => Pipe a b m r -> Pipe a b m r
repeat_pipe pipe = pipe >> repeat_pipe pipe
