module Theory.NonLinearRealArithmatic.BoundedFloating where

data BoundedFloating a = PosInf | NegInf | Val a
  deriving (Eq, Show)

instance Ord a => Ord (BoundedFloating a) where
  _ <= PosInf = True
  PosInf <= y = y == PosInf

  NegInf <= _ = True
  x <= NegInf = x == NegInf

  Val x <= Val y = x <= y

instance Fractional a => Bounded (BoundedFloating a) where
  minBound = NegInf
  maxBound = PosInf

instance (Num a, Eq a) => Num (BoundedFloating a) where
  PosInf + NegInf = error "Trying to compute: +oo + -oo"
  NegInf + PosInf = error "Trying to compute: -oo + +oo"
  PosInf + PosInf = PosInf
  NegInf + NegInf = NegInf
  Val x + Val y = Val (x + y)
  inf + Val y = inf
  Val x + inf = inf

  Val x * Val y = Val (x * y)
  Val x * inf 
    | signum (Val x) == 0 = 0
    | signum (Val x) == 1 = inf
    | otherwise           = negate inf
  inf * Val x = Val x * inf
  inf1 * inf2
    | signum inf1 == 1 = inf2
    | otherwise = negate inf2

  abs NegInf = PosInf
  abs PosInf = PosInf
  abs (Val x) = Val (abs x)

  signum NegInf = Val (-1)
  signum PosInf = Val 1
  signum (Val x) = Val (signum x)

  fromInteger x = Val (fromInteger x)

  negate PosInf = NegInf
  negate NegInf = PosInf
  negate (Val x) = Val (negate x)

instance (Fractional a, Eq a) => Fractional (BoundedFloating a) where
  fromRational x = Val (fromRational x)

  recip PosInf = Val 0
  recip NegInf = Val 0
  recip (Val x) = Val (recip x)

instance (Floating a, Eq a) => Floating (BoundedFloating a) where
  pi = Val pi

  exp PosInf = PosInf
  exp NegInf = Val 0
  exp (Val x) = Val (exp x)

  log PosInf = PosInf
  log NegInf = error "Trying to compute: log(-oo)"
  log (Val x) = Val (log x)

  sin = error "TODO: not implemented"
  cos = error "TODO: not implemented"
  asin = error "TODO: not implemented"
  acos = error "TODO: not implemented"
  atan = error "TODO: not implemented"
  sinh = error "TODO: not implemented"
  cosh = error "TODO: not implemented"
  asinh = error "TODO: not implemented"
  acosh = error "TODO: not implemented"
  atanh = error "TODO: not implemented"

