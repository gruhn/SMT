module Theory.NonLinearRealArithmatic.BoundedFloating where

data BoundedFractional a = PosInf | NegInf | Val a
  deriving (Eq, Show)

instance Ord a => Ord (BoundedFractional a) where
  _ <= PosInf = True
  PosInf <= y = y == PosInf

  NegInf <= _ = True
  x <= NegInf = x == NegInf

  Val x <= Val y = x <= y

instance Fractional a => Bounded (BoundedFractional a) where
  minBound = NegInf
  maxBound = PosInf

instance Num a => Num (BoundedFractional a) where
  PosInf + NegInf = undefined
  NegInf + PosInf = undefined
  PosInf + PosInf = PosInf
  NegInf + NegInf = NegInf
  Val x + Val y = Val (x + y)
  inf + Val y = inf
  Val x + inf = inf

  PosInf * NegInf = NegInf
  NegInf * PosInf = NegInf
  PosInf * PosInf = PosInf
  NegInf * NegInf = PosInf
  Val x * Val y = Val (x * y)
  Val x * inf = if signum x == 1 then PosInf else NegInf
  inf * Val y = if signum y == 1 then PosInf else NegInf

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

-- instance Fractional a => Fractional (BoundedFractional a) where


