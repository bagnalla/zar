module Main (main) where

import Pipes
import Pipes.Prelude as P hiding (show)
import System.Random.MWC as MWC

import           Core
import qualified Coin as C
import qualified Die as D
import qualified Findist as F

main :: IO ()
main = do
  -- gen <- MWC.createSystemRandom
  -- let bits = bit_producer gen
  -- runEffect $ for (bits >-> P.take 10) (\b -> lift $ putStrLn $ show b)

  -- | Build default coin and and generate a single sample.
  coin <- C.coin 2 3
  b <- runEffect coin
  putStrLn $ "default coin: " ++ show b

  -- | Build default coin producer and generate multiple samples.
  coin_producer <- C.coin_producer 2 3
  bs <- toListM $ coin_producer >-> P.take 10
  putStrLn $ "default coin producer: " ++ show bs

  -- | Compose coin consumer with a Bool producer to obtain coin and
  -- generate a single sample.
  -- gen <- MWC.createSystemRandom
  -- let coin2 = bit_producer gen >-> C.coin_consumer 2 3
  bits <- default_bit_producer
  let coin2 = bits >-> C.coin_consumer 2 3
  b2 <- runEffect coin2
  putStrLn $ "coin consumer: " ++ show b2
  
  -- | Build default die and and generate a single sample.
  die <- D.die 200
  x <- runEffect die
  putStrLn $ "default die: " ++ show x

  -- | Build default die producer and generate multiple samples.
  die_producer <- D.die_producer 200
  xs <- toListM $ die_producer >-> P.take 10
  putStrLn $ "default die producer: " ++ show xs
  
  -- | Compose die consumer with a Bool producer to obtain die and
  -- generate a single sample.
  bits2 <- default_bit_producer -- Need new bit producer because the
                                -- first had its return type
                                -- specialized to Bool.
  let die2 = bits2 >-> D.die_consumer 200
  x2 <- runEffect die2
  putStrLn $ "die consumer: " ++ show x2

  -- | Build default findist and and generate a single sample.
  findist <- F.findist [1, 3, 2]
  y <- runEffect findist
  putStrLn $ "default findist: " ++ show y

  -- | Build default findist producer and generate multiple samples.
  findist_producer <- F.findist_producer [1, 3, 2]
  ys <- toListM $ findist_producer >-> P.take 100
  putStrLn $ "default findist producer: " ++ show ys
  
  -- | Compose findist consumer with a Bool producer to obtain findist
  -- and generate a single sample.
  let findist2 = bits2 >-> F.findist_consumer [1, 3, 2]
  y2 <- runEffect findist2
  putStrLn $ "findist consumer: " ++ show y2
