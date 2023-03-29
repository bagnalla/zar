import Test.QuickCheck

import Core
import Samplers as S

instance Eq S.Positive where
  XH == XH = True
  XO a == XO b = a == b
  XI a == XI b = a == b
  _ == _ = False

instance Eq Z where
  Z0 == Z0 = True
  Zpos a == Zpos b = a == b
  Zneg a == Zneg b = a == b
  _ == _ = False

instance Show S.Positive where
  show XH = "XH"
  show (XO p) = "XO " ++ show p
  show (XI p) = "XI " ++ show p

instance Show Z where
  show Z0 = "Z0"
  show (Zpos p) = "Zpos " ++ show p
  show (Zneg p) = "Zneg " ++ show p

instance Arbitrary S.Positive where
  arbitrary = sized go
    where
      go :: Int -> Gen (S.Positive)
      go n =
        frequency [(1, return XH),
                   (10, XO <$> go (n-1)),
                   (10, XI <$> go (n-1))]
  -- shrink = TODO

instance Arbitrary Z where
  arbitrary = frequency [(1, return Z0),
                         (100, Zpos <$> arbitrary),
                         (100, Zneg <$> arbitrary)]
  -- shrink = TODO

main :: IO ()
main = do
  let count = 10000

  putStrLn $ "\npositive_of_integer ∘ integer_of_positive = id."
  quickCheck $ withMaxSuccess count $
    \ p -> positive_of_integer (integer_of_positive p) == p

  putStrLn $ "\n∀ n > 0, integer_of_positive (positive_of_integer n) = n."
  quickCheck $ withMaxSuccess count $
    \ (Positive n) -> integer_of_positive (positive_of_integer n) == n

  putStrLn $ "\nz_of_integer ∘ integer_of_z = id."
  quickCheck $ withMaxSuccess count $
    \ n -> z_of_integer (integer_of_z n) == n

  putStrLn $ "\ninteger_of_z ∘ z_of_integer = id."
  quickCheck $ withMaxSuccess count $
    \ n -> integer_of_z (z_of_integer n) == n

  putStrLn $ "\n∀ n m, integer_of_z n + integer_of_z m = integer_of_z (n + m)."
  quickCheck $ withMaxSuccess count $
    \ n m -> integer_of_z n + integer_of_z m == integer_of_z (add2 n m)

  putStrLn $ "\n∀ n m, z_of_integer n + z_of_integer m = z_of_integer (n + m)."
  quickCheck $ withMaxSuccess count $
    \ n m -> add2 (z_of_integer n) (z_of_integer m) == z_of_integer (n + m)

  putStrLn $ "\n∀ n, integer_of_z (double n) = 2 * integer_of_z n."
  quickCheck $ withMaxSuccess count $
    \ n -> integer_of_z (double n) == 2 * integer_of_z n

  putStrLn $ "\n∀ n, double (z_of_integer n) = z_of_integer (2 * n)."
  quickCheck $ withMaxSuccess count $
    \ n -> double (z_of_integer n) == z_of_integer (2 * n)

  putStrLn $ "\n∀ n m, ltb n m ⇔ integer_of_z n < integer_of_z m."
  quickCheck $ withMaxSuccess count $
    \ n m -> ltb n m == (integer_of_z n < integer_of_z m)

  putStrLn $ "\n∀ n m, n < m ⇔ ltb (z_of_integer n) (z_of_integer m)."
  quickCheck $ withMaxSuccess count $
    \ n m -> (n < m) == ltb (z_of_integer n) (z_of_integer m)
