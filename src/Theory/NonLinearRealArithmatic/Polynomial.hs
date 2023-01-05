module Theory.NonLinearRealArithmatic.Polynomial where

newtype Polynomial a = Polynomial { getCoefficients :: [a] }
  deriving Show

derivative :: (Enum a, Num a) => Polynomial a -> Polynomial a
derivative = Polynomial . tail . zipWith (*) [0..] . getCoefficients
