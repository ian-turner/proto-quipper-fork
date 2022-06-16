-- From Peter Selinger and Neil Ross's newsynth lib.

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}

-- | This module provides type classes for rings. It also provides
-- several specific instances of rings, such as the ring ℤ₂ of
-- integers modulo 2, the ring ℚ of rational numbers, the ring ℤ[½] of
-- dyadic fractions, the ring ℤ[/i/] of Gaussian integers, the ring
-- ℤ[√2] of quadratic integers with radix 2, and the ring ℤ[ω] of
-- cyclotomic integers of degree 8.

module Ring where

import Data.Bits
import Data.Complex
import Data.Ratio

-- ----------------------------------------------------------------------
-- * Rings

-- | A type class to denote rings. We make 'Ring' a synonym of
-- Haskell's 'Num' type class, so that we can use the usual notation
-- '+', '-', '*' for the ring operations.  This is not a perfect fit,
-- because Haskell's 'Num' class also contains two non-ring operations
-- 'abs' and 'signum'.  By convention, for rings where these notions
-- don't make sense (or are inconvenient to define), we set 'abs' /x/
-- = /x/ and 'signum' /x/ = 1.

type Ring a = (Num a)

-- ----------------------------------------------------------------------
-- * Rings with particular elements

-- $ We define several classes of rings with special elements.

-- ----------------------------------------------------------------------
-- ** Rings with ½

-- | A type class for rings that contain ½.
-- 
-- Minimal complete definition: 'half'. The default definition of
-- 'fromDyadic' uses the expression @a*half^n@. However, this can give
-- potentially bad round-off errors for fixed-precision types where
-- the expression @half^n@ can underflow. For such rings, one should
-- provide a custom definition, for example by using @a/2^n@ instead.
class (Ring a) => HalfRing a where
  -- | The value ½.
  half :: a
  
  -- | The unique ring homomorphism from ℤ[½] to any 'HalfRing'. This
  -- exists because ℤ[½] is the free 'HalfRing'.
  fromDyadic :: Dyadic -> a
  fromDyadic x 
    | n >= 0    = fromInteger a * half^n
    | otherwise = fromInteger a * 2^(-n)
    where
      (a,n) = decompose_dyadic x

instance HalfRing Double where
  half = 0.5

instance HalfRing Float where
  half = 0.5

instance HalfRing Rational where
  half = 1%2

instance (HalfRing a, RealFloat a) => HalfRing (Complex a) where
  half = half :+ 0
  fromDyadic x = fromDyadic x :+ 0

-- ----------------------------------------------------------------------
-- ** Rings with √2

-- | A type class for rings that contain √2.
-- 
-- Minimal complete definition: 'roottwo'. The default definition of
-- 'fromZRootTwo' uses the expression @x+roottwo*y@. However, this can
-- give potentially bad round-off errors for fixed-precision types,
-- where the expression @roottwo*y@ can be vastly inaccurate if @y@ is
-- large. For such rings, one should provide a custom definition.
class (Ring a) => RootTwoRing a where
  -- | The square root of 2.
  roottwo :: a

  -- | The unique ring homomorphism from ℤ[√2] to any ring containing
  -- √2. This exists because ℤ[√2] is the free such ring.
  fromZRootTwo :: (RootTwoRing a) => ZRootTwo -> a
  fromZRootTwo (RootTwo x y) = fromInteger x + roottwo * fromInteger y
  
instance RootTwoRing Double where
  roottwo = sqrt 2

instance RootTwoRing Float where
  roottwo = sqrt 2

instance (RootTwoRing a, RealFloat a) => RootTwoRing (Complex a) where
  roottwo = roottwo :+ 0

-- ----------------------------------------------------------------------
-- ** Rings with 1\/√2

-- | A type class for rings that contain 1\/√2.
-- 
-- Minimal complete definition: 'roothalf'. The default definition of
-- 'fromDRootTwo' uses the expression @x+roottwo*y@. However, this can
-- give potentially bad round-off errors for fixed-precision types,
-- where the expression @roottwo*y@ can be vastly inaccurate if @y@ is
-- large. For such rings, one should provide a custom definition.
class (HalfRing a, RootTwoRing a) => RootHalfRing a where
  -- | The square root of ½.
  roothalf :: a

  -- | The unique ring homomorphism from [bold D][√2] to any ring containing
  -- 1\/√2. This exists because [bold D][√2] = ℤ[1\/√2] is the free such ring.
  fromDRootTwo :: (RootHalfRing a) => DRootTwo -> a
  fromDRootTwo (RootTwo x y) = fromDyadic x + roottwo * fromDyadic y
  
instance RootHalfRing Double where
  roothalf = sqrt 0.5

instance RootHalfRing Float where
  roothalf = sqrt 0.5

instance (RootHalfRing a, RealFloat a) => RootHalfRing (Complex a) where
  roothalf = roothalf :+ 0


-- ----------------------------------------------------------------------
-- ** Rings with /i/

-- | A type class for rings that contain a square root of -1.
class (Ring a) => ComplexRing a where
  -- | The complex unit.
  i :: a
       
instance (Ring a, RealFloat a) => ComplexRing (Complex a) where
  i = 0 :+ 1

instance (RealFloat a, RootHalfRing a) => OmegaRing (Complex a) where
  omega = roothalf * (1 + i)

-- ----------------------------------------------------------------------
-- ** Rings with ω

-- | A type class for rings that contain a square root of /i/, or
-- equivalently, a fourth root of −1.
class (Ring a) => OmegaRing a where
  -- | The square root of /i/.
  omega :: a
  
-- instance (Ring a, ComplexRing a, RootHalfRing a) => OmegaRing a where
--   omega = roothalf * (1 + i)

-- ----------------------------------------------------------------------
-- * Rings with particular automorphisms

-- ----------------------------------------------------------------------
-- ** Rings with complex conjugation

-- | A type class for rings with complex conjugation, i.e., an
-- automorphism mapping /i/ to −/i/. 
-- 
-- When instances of this type class are vectors or matrices, the
-- conjugation also exchanges the roles of rows and columns (in other
-- words, it is the adjoint).
-- 
-- For rings that are not complex, the conjugation can be defined to
-- be the identity function.
class Adjoint a where
  -- | Compute the adjoint (complex conjugate transpose).
  adj :: a -> a

instance Adjoint Integer where
  adj x = x
  
instance Adjoint Int where
  adj x = x
  
instance Adjoint Double where
  adj x = x
  
instance Adjoint Float where
  adj x = x
  
instance Adjoint Rational where  
  adj x = x
  
instance (Adjoint a, Ring a) => Adjoint (Complex a) where
  adj (a :+ b) = adj a :+ (-adj b)

-- ----------------------------------------------------------------------
-- ** Rings with √2-conjugation

-- | A type class for rings with a √2-conjugation, i.e., an
-- automorphism mapping √2 to −√2. 
-- 
-- When instances of this type class are vectors or matrices, the
-- √2-conjugation does /not/ exchange the roles of rows and columns.
-- 
-- For rings that have no √2, the conjugation can be defined to be the
-- identity function.
class Adjoint2 a where
  -- | Compute the adjoint, mapping /a/ + /b/√2 to /a/ −/b/√2.
  adj2 :: a -> a

instance Adjoint2 Integer where
  adj2 x = x

instance Adjoint2 Int where
  adj2 x = x
  
instance Adjoint2 Rational where  
  adj2 x = x
  
-- ----------------------------------------------------------------------
-- * Normed rings

-- | A (number-theoretic) /norm/ on a ring /R/ is a function /N/ : /R/
-- → ℤ such that /N/(/rs/) = /N/(/r/)/N/(/s/), for all /r/, /s/ ∈ /R/.
-- The norm also satisfies /N/(/r/) = 0 iff /r/ = 0, and /N/(/r/) = ±1
-- iff /r/ is a unit of the ring.
class (Ring r) => NormedRing r where
  norm :: r -> Integer
  
instance NormedRing Integer where
  norm x = x
  
-- ----------------------------------------------------------------------
-- * Floor and ceiling
  
-- | The 'floor' and 'ceiling' functions provided by the standard
-- Haskell libraries are predicated on many unnecessary assumptions.
-- This type class provides an alternative.
-- 
-- Minimal complete definition: 'floor_of' or 'ceiling_of'.
class (Ring r) => Floor r where
  -- | Compute the floor of /x/, i.e., the greatest integer /n/ such
  -- that /n/ ≤ /x/.
  floor_of :: r -> Integer
  floor_of x = -(ceiling_of (-x))
  -- | Compute the ceiling of /x/, i.e., the least integer /n/ such
  -- that /x/ ≤ /n/.
  ceiling_of :: r -> Integer
  ceiling_of x = -(floor_of (-x))

instance Floor Integer where
  floor_of = id
  ceiling_of = id

instance Floor Rational where
  floor_of = floor
  ceiling_of = ceiling

instance Floor Float where
  floor_of = floor
  ceiling_of = ceiling

instance Floor Double where
  floor_of = floor
  ceiling_of = ceiling

-- ----------------------------------------------------------------------
-- * Particular rings

-- ----------------------------------------------------------------------
-- ** The ring ℤ₂ of integers modulo 2

-- | The ring ℤ₂ of integers modulo 2. 
data Z2 = Even | Odd
        deriving (Eq)
                     
instance Show Z2 where
  show Even = "0"
  show Odd = "1"

instance Num Z2 where
  Even + x = x
  x + Even = x
  Odd + Odd = Even
  Even * x = Even
  x * Even = Even
  Odd * Odd = Odd
  negate x = x
  fromInteger n = if even n then Even else Odd
  abs x = x
  signum x = 1

instance Adjoint Z2 where
  adj x = x

instance Adjoint2 Z2 where
  adj2 x = x

-- ----------------------------------------------------------------------
-- ** The ring [bold D] of dyadic fractions

-- | A dyadic fraction is a rational number whose denominator is a
-- power of 2. We denote the dyadic fractions by [bold D] = ℤ[½].
-- 
-- We internally represent a dyadic fraction /a/\/2[sup /n/] as a pair
-- (/a/,/n/). Note that this representation is not unique. When it is
-- necessary to choose a canonical representative, we choose the least
-- possible /n/≥0.
data Dyadic = Dyadic !Integer !Integer

-- | Given a dyadic fraction /r/, return (/a/,/n/) such that /r/ =
-- /a/\/2[sup /n/], where /n/≥0 is chosen as small as possible.
decompose_dyadic :: Dyadic -> (Integer, Integer)
decompose_dyadic (Dyadic a n) 
  | a == 0 = (0, 0)
  | n >= k = (a `shiftR` fromInteger k, n-k)
  | otherwise = (a `shiftR` fromInteger n, 0)
  where
    k = lobit a

-- | Given a dyadic fraction /r/ and an integer /k/≥0, such that /a/ =
-- /r/2[sup /k/] is an integer, return /a/. If /a/ is not an integer,
-- the behavior is undefined.
integer_of_dyadic :: Dyadic -> Integer -> Integer
integer_of_dyadic (Dyadic a n) k =
  shift a (fromInteger (k-n))

instance Real Dyadic where
  toRational (Dyadic a n) 
    | n >= 0    = a % 2^n
    | otherwise = a * 2^(-n) % 1

instance Show Dyadic where
  showsPrec d a = showsPrec_rational d (toRational a)

instance Eq Dyadic where
  Dyadic a n == Dyadic b m = a * 2^(k-n) == b * 2^(k-m) where
    k = max n m

instance Ord Dyadic where
  compare (Dyadic a n) (Dyadic b m) = compare (a * 2^(k-n)) (b * 2^(k-m)) where
    k = max n m

instance Num Dyadic where
  Dyadic a n + Dyadic b m 
    | n < m     = Dyadic c m
    | otherwise = Dyadic d n
    where
      c = shiftL a (fromInteger (m-n)) + b
      d = a + shiftL b (fromInteger (n-m))
  Dyadic a n * Dyadic b m = Dyadic (a*b) (n+m)
  negate (Dyadic a n) = Dyadic (-a) n
  abs x = if x >= 0 then x else -x
  signum x = case compare 0 x of { LT -> 1; EQ -> 0; GT -> -1 }
  fromInteger n = Dyadic n 0

instance HalfRing Dyadic where
  half = Dyadic 1 1
  fromDyadic = id

instance Adjoint Dyadic where
  adj x = x

instance Adjoint2 Dyadic where
  adj2 x = x

-- ----------------------------------------------------------------------
-- ** The ring ℚ of rational numbers

-- | We define our own variant of the rational numbers, which is an
-- identical copy of the type 'Rational' from the standard Haskell
-- library, except that it has a more sensible 'Show' instance.
newtype Rationals = ToRationals { unRationals :: Rational }
                  deriving (Num, Eq, Ord, Fractional, Real, RealFrac, HalfRing, Adjoint, Adjoint2, ToQOmega, Floor)

-- | An auxiliary function for printing rational numbers, using
-- correct precedences, and omitting denominators of 1.
showsPrec_rational :: (Show a, Integral a) => Int -> Ratio a -> ShowS
showsPrec_rational d a
  | denom == 1 = showsPrec d numer
  | numer < 0  = showParen (d >= 7) $ showString "-" . showsPrec_rational 7 (-a)
  | otherwise  = showParen (d >= 8) $
                 showsPrec 7 numer . showString "/" . showsPrec 8 denom
    where
      numer = numerator a
      denom = denominator a

instance Show Rationals where
  showsPrec d (ToRationals a) = showsPrec_rational d a

-- | Conversion from 'Rationals' to any 'Fractional' type.
fromRationals :: (Fractional a) => Rationals -> a
fromRationals = fromRational . unRationals

-- ----------------------------------------------------------------------
-- ** The ring /R/[√2]
  
-- | The ring /R/[√2], where /R/ is any ring. The value 'RootTwo' /a/
-- /b/ represents /a/ + /b/ √2.
data RootTwo a = RootTwo !a !a
                deriving (Eq)

instance (Eq a, Num a) => Num (RootTwo a) where
  RootTwo a b + RootTwo a' b' = RootTwo a'' b'' where
    a'' = a + a'
    b'' = b + b'
  RootTwo a b * RootTwo a' b' = RootTwo a'' b'' where
    a'' = a * a' + 2 * b * b'
    b'' = a * b' + a' * b
  negate (RootTwo a b) = RootTwo a' b' where
    a' = -a
    b' = -b
  fromInteger n = RootTwo n' 0 where
    n' = fromInteger n
  abs f = f * signum f
  signum f@(RootTwo a b)
    | sa == 0 && sb == 0 = 0
    | sa /= -1 && sb /= -1 = 1
    | sa /= 1 && sb /= 1 = -1
    | sa /= -1 && sb /= 1 && signum (a*a - 2*b*b) /= -1 = 1
    | sa /= 1 && sb /= -1 && signum (a*a - 2*b*b) /= 1  = 1
    | otherwise = -1
    where
      sa = signum a
      sb = signum b

instance (Eq a, Ring a) => Ord (RootTwo a) where
  x <= y  =  signum (y-x) /= (-1)
  
instance (Show a, Eq a, Ring a) => Show (RootTwo a) where
  showsPrec d (RootTwo a 0) = showsPrec d a
  showsPrec d (RootTwo 0 1) = showString "roottwo"
  showsPrec d (RootTwo 0 (-1)) = showParen (d >= 7) $ showString "-roottwo"
  showsPrec d (RootTwo 0 b) = showParen (d >= 8) $ 
    showsPrec 7 b . showString "*roottwo"
  showsPrec d (RootTwo a b) | signum b == 1 = showParen (d >= 7) $
    showsPrec 6 a . showString " + " . showsPrec 6 (RootTwo 0 b)
  showsPrec d (RootTwo a b) | otherwise = showParen (d >= 7) $
    showsPrec 6 a . showString " - " . showsPrec 7 (RootTwo 0 (-b))

instance (Eq a, Fractional a) => Fractional (RootTwo a) where
  recip (RootTwo a b) = RootTwo (a/k) (-b/k) where
    k = a^2 - 2*b^2
  fromRational r = RootTwo (fromRational r) 0

instance (Eq a, Ring a) => RootTwoRing (RootTwo a) where
  roottwo = RootTwo 0 1

instance (Eq a, HalfRing a) => HalfRing (RootTwo a) where
  half = RootTwo half 0
  fromDyadic x = RootTwo (fromDyadic x) 0
  
instance (Eq a, HalfRing a) => RootHalfRing (RootTwo a) where
  roothalf = RootTwo 0 half
  
instance (Eq a, ComplexRing a) => ComplexRing (RootTwo a) where
  i = RootTwo i 0

instance (Eq a, ComplexRing a, HalfRing a) => OmegaRing (RootTwo a) where
  omega = roothalf * (1 + i)

instance (Adjoint a) => Adjoint (RootTwo a) where  
  adj (RootTwo a b) = RootTwo (adj a) (adj b)

instance (Adjoint2 a, Num a) => Adjoint2 (RootTwo a) where  
  adj2 (RootTwo a b) = RootTwo (adj2 a) (-adj2 b)

instance (Eq a, NormedRing a) => NormedRing (RootTwo a) where
  norm (RootTwo a b) = (norm a)^2 - 2 * (norm b)^2

-- ----------------------------------------------------------------------
-- ** The ring ℤ[√2]

-- | The ring ℤ[√2].
type ZRootTwo = RootTwo Integer

-- | Return a square root of an element of ℤ[√2], if such a square
-- root exists, or else 'Nothing'.
zroottwo_root :: ZRootTwo -> Maybe ZRootTwo
zroottwo_root z@(RootTwo a b) = res where
  d = a^2 - 2*b^2
  r = intsqrt d
  x1 = intsqrt ((a + r) `div` 2)
  x2 = intsqrt ((a - r) `div` 2)
  y1 = intsqrt ((a - r) `div` 4)
  y2 = intsqrt ((a + r) `div` 4)
  w1 = RootTwo x1 y1
  w2 = RootTwo x2 y2
  w3 = RootTwo x1 (-y1)
  w4 = RootTwo x2 (-y2)
  res 
    | w1*w1 == z = Just w1
    | w2*w2 == z = Just w2
    | w3*w3 == z = Just w3
    | w4*w4 == z = Just w4
    | otherwise  = Nothing

-- ----------------------------------------------------------------------
-- ** The ring [bold D][√2]

-- | The ring [bold D][√2] = ℤ[1\/√2]. 
type DRootTwo = RootTwo Dyadic

-- ----------------------------------------------------------------------
-- ** The field ℚ[√2]

-- | The field ℚ[√2].
type QRootTwo = RootTwo Rationals

instance Floor QRootTwo where
  floor_of x@(RootTwo a b)
    | r'+1 <= x  = r+1
    | r' <= x    = r
    | otherwise = r-1 
   where 
    a' = floor a
    b' = intsqrt (floor (2 * b^2))
    r | b >= 0    = a' + b'
      | otherwise = a' - b'
    r' = fromInteger r

-- | The unique ring homomorphism from ℚ[√2] to any ring containing
-- the rational numbers and √2. This exists because ℚ[√2] is the free
-- such ring.
fromQRootTwo :: (RootTwoRing a, Fractional a) => QRootTwo -> a
fromQRootTwo (RootTwo x y) = fromRationals x + roottwo * fromRationals y

-- ----------------------------------------------------------------------
-- ** The ring /R/[/i/]

-- | The ring /R/[/i/], where /R/ is any ring. The reason we do not
-- use the 'Complex' /a/ type from the standard Haskell libraries is
-- that it assumes too much, for example, it assumes /a/ is a member
-- of the 'RealFloat' class. Also, this allows us to define a more
-- sensible 'Show' instance.
data Cplx a = Cplx !a !a
            deriving (Eq)

instance (Eq a, Show a, Num a) => Show (Cplx a) where
  showsPrec d (Cplx a 0) = showsPrec d a
  showsPrec d (Cplx 0 1) = showString "i"
  showsPrec d (Cplx 0 (-1)) = showParen (d >= 7) $ showString "-i"
  showsPrec d (Cplx 0 b) = showParen (d >= 8) $ 
    showsPrec 7 b . showString "*i"
  showsPrec d (Cplx a b) | signum b == 1 = showParen (d >= 7) $
    showsPrec 6 a . showString " + " . showsPrec 6 (Cplx 0 b)
  showsPrec d (Cplx a b) | otherwise = showParen (d >= 7) $
    showsPrec 6 a . showString " - " . showsPrec 7 (Cplx 0 (-b))

instance (Num a) => Num (Cplx a) where
  Cplx a b + Cplx a' b' = Cplx a'' b'' where
    a'' = a + a'
    b'' = b + b'
  Cplx a b * Cplx a' b' = Cplx a'' b'' where
    a'' = a * a' - b * b'
    b'' = a * b' + a' * b
  negate (Cplx a b) = Cplx a' b' where
    a' = -a
    b' = -b
  fromInteger n = Cplx n' 0 where
    n' = fromInteger n
  abs x = x
  signum x = 1

instance (Fractional a) => Fractional (Cplx a) where
  recip (Cplx a b) = Cplx (a/d) (-b/d) where
    d = a^2 + b^2
  fromRational a = Cplx (fromRational a) 0

instance (Ring a) => ComplexRing (Cplx a) where
  i = Cplx 0 1

instance (Ring a, RootHalfRing a) => OmegaRing (Cplx a) where        
  omega = roothalf * (1 + i)

instance (HalfRing a) => HalfRing (Cplx a) where
  half = Cplx half 0
  fromDyadic x = Cplx (fromDyadic x) 0

instance (RootHalfRing a) => RootHalfRing (Cplx a) where
  roothalf = Cplx roothalf 0

instance (RootTwoRing a) => RootTwoRing (Cplx a) where
  roottwo = Cplx roottwo 0

instance (Adjoint a, Ring a) => Adjoint (Cplx a) where
  adj (Cplx a b) = (Cplx (adj a) (-(adj b)))

instance (Adjoint2 a, Ring a) => Adjoint2 (Cplx a) where
  adj2 (Cplx a b) = (Cplx (adj2 a) (adj2 b))

instance (NormedRing a) => NormedRing (Cplx a) where
  norm (Cplx a b) = (norm a)^2 + (norm b)^2

-- ----------------------------------------------------------------------
-- ** The ring ℤ[/i/] of Gaussian integers

-- | The ring ℤ[/i/] of Gaussian integers.
type ZComplex = Cplx Integer

-- | The unique ring homomorphism from ℤ[/i/] to any ring containing
-- /i/. This exists because ℤ[/i/] is the free such ring.
fromZComplex :: (ComplexRing a) => ZComplex -> a
fromZComplex (Cplx a b) = fromInteger a + i * fromInteger b

-- ----------------------------------------------------------------------
-- ** The ring [bold D][/i/]

-- | The ring [bold D][/i/] = ℤ[½, /i/] of Gaussian dyadic fractions.
type DComplex = Cplx Dyadic

-- | The unique ring homomorphism from [bold D][/i/] to any ring containing
-- ½ and /i/. This exists because [bold D][/i/] is the free such ring.
fromDComplex :: (ComplexRing a, HalfRing a) => DComplex -> a
fromDComplex (Cplx a b) = fromDyadic a + i * fromDyadic b

-- ----------------------------------------------------------------------
-- ** The ring ℚ[/i/] of Gaussian rationals

-- | The ring ℚ[/i/] of Gaussian rationals.
type QComplex = Cplx Rationals

-- | The unique ring homomorphism from ℚ[/i/] to any ring containing
-- the rational numbers and /i/. This exists because ℚ[/i/] is the
-- free such ring.
fromQComplex :: (ComplexRing a, Fractional a) => QComplex -> a
fromQComplex (Cplx a b) = fromRationals a + i * fromRationals b

-- ----------------------------------------------------------------------
-- ** The ring [bold D][√2, /i/]

-- | The ring [bold D][√2, /i/] = ℤ[1\/√2, /i/].
type DRComplex = Cplx DRootTwo

-- | The unique ring homomorphism from [bold D][√2, /i/] to any ring
-- containing 1\/√2 and /i/. This exists because [bold D][√2, /i/] =
-- ℤ[1\/√2, /i/] is the free such ring.
fromDRComplex :: (RootHalfRing a, ComplexRing a) => DRComplex -> a
fromDRComplex (Cplx a b) = fromDRootTwo a + i * fromDRootTwo b

-- ----------------------------------------------------------------------
-- ** The ring ℚ[√2, /i/]

-- | The field ℚ[√2, /i/].
type QRComplex = Cplx QRootTwo

-- | The unique ring homomorphism from ℚ[√2, /i/] to any ring
-- containing the rational numbers, √2, and /i/. This exists because
-- ℚ[√2, /i/] is the free such ring.
fromQRComplex :: (RootTwoRing a, ComplexRing a, Fractional a) => QRComplex -> a
fromQRComplex (Cplx a b) = fromQRootTwo a + i * fromQRootTwo b

-- ----------------------------------------------------------------------
-- ** The ring ℂ of complex numbers

-- $ We provide two versions of the complex numbers using floating
-- point arithmetic.

-- | Double precision complex floating point numbers.
type CDouble = Cplx Double

-- | Single precision complex floating point numbers.
type CFloat = Cplx Float

-- ----------------------------------------------------------------------
-- ** The ring /R/[ω]

-- | The ring /R/[ω], where /R/ is any ring, and ω = [exp iπ/4] is an
-- 8th root of unity. The value 'Omega' /a/ /b/ /c/ /d/ represents
-- /a/ω[sup 3]+/b/ω[sup 2]+/c/ω+/d/.
data Omega a = Omega !a !a !a !a
            deriving (Eq)

-- | An inverse to the embedding /R/ ↦ /R/[ω]: return the \"real
-- rational\" part. 
-- In other words, map /a/ω[sup 3]+/b/ω[sup 2]+/c/ω+/d/ to /d/.
omega_real :: Omega a -> a
omega_real (Omega a b c d) = d

instance (Show a, Ring a) => Show (Omega a) where
  showsPrec p (Omega a b c d) = 
    showParen (p >= 11) $ showString "Omega " . 
                         showsPrec 11 a . showString " " . 
                         showsPrec 11 b . showString " " . 
                         showsPrec 11 c . showString " " . 
                         showsPrec 11 d

instance (Num a) => Num (Omega a) where
  Omega a b c d + Omega a' b' c' d' = Omega a'' b'' c'' d'' where
    a'' = a + a'
    b'' = b + b'
    c'' = c + c'
    d'' = d + d'
  Omega a b c d * Omega a' b' c' d' = Omega a'' b'' c'' d'' where  
    a'' = a*d' + b*c' + c*b' + d*a'
    b'' = b*d' + c*c' + d*b' - a*a'
    c'' = c*d' + d*c' - a*b' - b*a'
    d'' = d*d' - a*c' - b*b' - c*a'
  negate (Omega a b c d) = Omega (-a) (-b) (-c) (-d) where
  fromInteger n = Omega 0 0 0 n' where
    n' = fromInteger n
  abs x = x
  signum x = 1

instance (Fractional a) => Fractional (Omega a) where
  recip (Omega a b c d) = x1 * x2 * x3 * Omega 0 0 0 (1/denom)
    where
      x1 = Omega (-c) (-b) (-a) d
      x2 = Omega (-a) b (-c) d
      x3 = Omega c (-b) a d
      denom = (a^2+b^2+c^2+d^2)^2-2*(a*b+b*c+c*d-d*a)^2
  fromRational r = fromInteger a / fromInteger b where
    a = numerator r
    b = denominator r

instance (HalfRing a) => HalfRing (Omega a) where
  half = Omega 0 0 0 half
  fromDyadic x = Omega 0 0 0 (fromDyadic x)

instance (HalfRing a) => RootHalfRing (Omega a) where
  roothalf = Omega (-half) 0 half 0

instance (Ring a) => RootTwoRing (Omega a) where
  roottwo = Omega (-1) 0 1 0

instance (Ring a) => ComplexRing (Omega a) where
  i = Omega 0 1 0 0

instance (Adjoint a, Ring a) => Adjoint (Omega a) where
  adj (Omega a b c d) = Omega (-(adj c)) (-(adj b)) (-(adj a)) (adj d)

instance (Adjoint2 a, Ring a) => Adjoint2 (Omega a) where
  adj2 (Omega a b c d) = Omega (-adj2 a) (adj2 b) (-adj2 c) (adj2 d)

instance (NormedRing a) => NormedRing (Omega a) where
  norm (Omega x y z w) = (a^2+b^2+c^2+d^2)^2-2*(a*b+b*c+c*d-d*a)^2
    where
      a = norm x
      b = norm y
      c = norm z
      d = norm w

instance (Ring a) => OmegaRing (Omega a) where
  omega = Omega 0 0 1 0

-- ----------------------------------------------------------------------
-- ** The ring ℤ[ω]

-- | The ring ℤ[ω] of /cyclotomic integers/ of degree 8. Such rings
-- were first studied by Kummer around 1840, and used in his proof of
-- special cases of Fermat's Last Theorem.  See also:
-- 
-- * <http://fermatslasttheorem.blogspot.com/2006/05/basic-properties-of-cyclotomic.html>
-- 
-- * <http://fermatslasttheorem.blogspot.com/2006/02/cyclotomic-integers.html>
-- 
-- * Harold M. Edwards, \"Fermat's Last Theorem: A Genetic
-- Introduction to Algebraic Number Theory\".
type ZOmega = Omega Integer

-- | The unique ring homomorphism from ℤ[ω] to any ring containing
-- ω. This exists because ℤ[ω] is the free such ring.
fromZOmega :: (OmegaRing a) => ZOmega -> a
fromZOmega (Omega a b c d) = fromInteger a * omega^3 + fromInteger b * omega^2 + fromInteger c * omega + fromInteger d

-- | Inverse of the embedding ℤ[√2] → ℤ[ω]. Note that ℤ[√2] = ℤ[ω] ∩
-- ℝ. This function takes an element of ℤ[ω] that is real, and
-- converts it to an element of ℤ[√2]. It throws an error if the input
-- is not real.
zroottwo_of_zomega :: ZOmega -> ZRootTwo
zroottwo_of_zomega (Omega a b c d)
  | a == -c && b == 0  = RootTwo d c
  | otherwise = error "zroottwo_of_zomega: non-real value"
  
-- ----------------------------------------------------------------------
-- ** The ring [bold D][ω]

-- | The ring [bold D][ω]. Here [bold D]=ℤ[½] is the ring of dyadic
-- fractions. In fact, [bold D][ω] is isomorphic to the ring [bold D][√2,
-- i], but they have different 'Show' instances.
type DOmega = Omega Dyadic

-- | The unique ring homomorphism from [bold D][ω] to any ring containing
-- ω and 1\/2. This exists because [bold D][ω] is the free such ring.
fromDOmega :: (OmegaRing a, HalfRing a) => DOmega -> a
fromDOmega (Omega a b c d) = fromDyadic a * omega^3 + fromDyadic b * omega^2 + fromDyadic c * omega + fromDyadic d

-- This is an overlapping instance. It is nicer to show an element of
-- D[ω] by pulling out a common denominator exponent. But in cases
-- where the typechecker cannot infer this, then it will just fall
-- back to the more general method.
instance Show DOmega where
  showsPrec = showsPrec_DenomExp
  
-- This is an overlapping instance. See previous comment.
instance Show DRComplex where
  showsPrec = showsPrec_DenomExp

-- ----------------------------------------------------------------------
-- ** The field ℚ[ω]

-- | The field ℚ[ω] of /cyclotomic rationals/ of degree 8.
type QOmega = Omega Rationals

-- | The unique ring homomorphism from ℚ[ω] to any ring containing the
-- rational numbers and ω. This exists because ℚ[ω] is the free
-- such ring.
fromQOmega :: (OmegaRing a, Fractional a) => QOmega -> a
fromQOmega (Omega a b c d) = fromRationals a * omega^3 + fromRationals b * omega^2 + fromRationals c * omega + fromRationals d

-- ----------------------------------------------------------------------
-- * Conversion to dyadic

-- | A type class relating \"rational\" types to their dyadic
-- counterparts.
class ToDyadic a b | a -> b where
  -- | Convert a \"rational\" value to a \"dyadic\" value, if the
  -- denominator is a power of 2. Otherwise, return 'Nothing'.
  maybe_dyadic :: a -> Maybe b

-- | Convert a \"rational\" value to a \"dyadic\" value, if the
-- denominator is a power of 2. Otherwise, throw an error.
to_dyadic :: (ToDyadic a b) => a -> b
to_dyadic a = case maybe_dyadic a of
  Just b -> b
  Nothing -> error "to_dyadic: denominator not a power of 2"

instance ToDyadic Dyadic Dyadic where
  maybe_dyadic = return

instance ToDyadic Rational Dyadic where
  maybe_dyadic x = do
    k <- log2 denom
    return (Dyadic numer k)
    where denom = denominator x
          numer = numerator x

instance ToDyadic Rationals Dyadic where
  maybe_dyadic = maybe_dyadic . unRationals

instance (ToDyadic a b) => ToDyadic (RootTwo a) (RootTwo b) where
  maybe_dyadic (RootTwo x y) = do
    x' <- maybe_dyadic x
    y' <- maybe_dyadic y
    return (RootTwo x' y')

instance (ToDyadic a b) => ToDyadic (Cplx a) (Cplx b) where
  maybe_dyadic (Cplx x y) = do
    x' <- maybe_dyadic x
    y' <- maybe_dyadic y
    return (Cplx x' y')

instance (ToDyadic a b) => ToDyadic (Omega a) (Omega b) where
  maybe_dyadic (Omega x y z w) = do
    x' <- maybe_dyadic x
    y' <- maybe_dyadic y
    z' <- maybe_dyadic z
    w' <- maybe_dyadic w
    return (Omega x' y' z' w')

-- ----------------------------------------------------------------------
-- * Real part
    
-- | A type class for rings that have a \"real\" component. A typical
-- instance is /a/ = 'DRComplex' with /b/ = 'DRootTwo'.
class RealPart a b | a -> b where
  -- | Take the real part.
  real :: a -> b

instance RealPart (Cplx a) a where
  real (Cplx a b) = a

instance (HalfRing a) => RealPart (Omega a) (RootTwo a) where
  real (Omega a b c d) = RootTwo d (half * (c - a))

-- ----------------------------------------------------------------------
-- * Rings of integers
  
-- | A type class for rings that have a distinguished subring \"of
-- integers\". A typical instance is /a/ = 'DRootTwo', which has /b/ =
-- 'ZRootTwo' as its ring of integers.
class WholePart a b | a -> b where  
  -- | The embedding of the ring of integers into the larger ring.
  from_whole :: b -> a
  -- | The inverse of 'from_whole'. Throws an error if the given
  -- element is not actually an integer in the ring.
  to_whole :: a -> b
  
instance WholePart Dyadic Integer where
  from_whole = fromInteger
  to_whole d 
    | n == 0 = a
    | otherwise = error "to_whole: non-integral value"
    where
      (a,n) = decompose_dyadic d

instance WholePart DRootTwo ZRootTwo where
  from_whole = fromZRootTwo
  to_whole (RootTwo x y) = RootTwo (to_whole x) (to_whole y)
  
instance WholePart DOmega ZOmega where
  from_whole = fromZOmega
  to_whole (Omega x y z w) = Omega (to_whole x) (to_whole y) (to_whole z) (to_whole w)
  
instance (WholePart a a', WholePart b b') => WholePart (a,b) (a',b') where
  from_whole (x,y) = (from_whole x, from_whole y)
  to_whole (x,y) = (to_whole x, to_whole y)
  
instance WholePart () () where  
  from_whole = const ()
  to_whole = const ()
  
instance (WholePart a b) => WholePart [a] [b] where  
  from_whole = map from_whole
  to_whole = map to_whole
  
instance (WholePart a b) => WholePart (Cplx a) (Cplx b) where  
  from_whole (Cplx a b) = Cplx (from_whole a) (from_whole b)
  to_whole (Cplx a b) = Cplx (to_whole a) (to_whole b)
  
-- ----------------------------------------------------------------------
-- * Common denominators
  
-- | A type class for things from which a common power of 1\/√2 (a
-- least denominator exponent) can be factored out. Typical instances
-- are 'DRootTwo', 'DRComplex', as well as tuples, lists, vectors, and
-- matrices thereof.
class DenomExp a where
  -- | Calculate the least denominator exponent /k/ of /a/. Returns
  -- the smallest /k/≥0 such that /a/ = /b/\/√2[sup /k/] for some
  -- integral /b/.
  denomexp :: a -> Integer
  
  -- | Factor out a /k/th power of 1\/√2 from /a/. In other words,
  -- calculate /a/√2[sup /k/].
  denomexp_factor :: a -> Integer -> a

-- | Calculate and factor out the least denominator exponent /k/ of
-- /a/. Return (/b/,/k/), where /a/ = /b/\/(√2)[sup /k/] and /k/≥0.
denomexp_decompose :: (WholePart a b, DenomExp a) => a -> (b, Integer)
denomexp_decompose a = (b, k) where
  k = denomexp a
  b = to_whole (denomexp_factor a k)

-- | Generic 'show'-like method that factors out a common denominator
-- exponent.
showsPrec_DenomExp :: (WholePart a b, Show b, DenomExp a) => Int -> a -> ShowS
showsPrec_DenomExp d a 
  | k == 0 = showsPrec d b
  | k == 1 = showParen (d >= 8) $ 
             showString "roothalf * " . showsPrec 7 b
  | otherwise = showParen (d >= 8) $
                showString ("roothalf^" ++ show k ++ " * ") . showsPrec 7 b
  where (b, k) = denomexp_decompose a

instance DenomExp DRootTwo where
  denomexp (RootTwo x y) = k'
    where
      (a,k) = decompose_dyadic x
      (b,l) = decompose_dyadic y
      k' = maximum [2*k, 2*l-1]
  denomexp_factor a k = a * roottwo^k

instance DenomExp DOmega where
  denomexp (Omega x y z w) = k'
      where
        (a,ak) = decompose_dyadic x
        (b,bk) = decompose_dyadic y
        (c,ck) = decompose_dyadic z
        (d,dk) = decompose_dyadic w
        k = maximum [ak, bk, ck, dk]
        a' = if k == ak then a else 0
        b' = if k == bk then b else 0
        c' = if k == ck then c else 0
        d' = if k == dk then d else 0
        k' | k>0 && even (a'-c') && even (b'-d') = 2*k-1
           | otherwise = 2*k
  denomexp_factor a k = a * roottwo^k
        
instance (DenomExp a, DenomExp b) => DenomExp (a,b) where
  denomexp (a,b) = denomexp a `max` denomexp b
  denomexp_factor (a,b) k = (denomexp_factor a k, denomexp_factor b k)

instance DenomExp () where
  denomexp _ = 0
  denomexp_factor _ k = ()

instance (DenomExp a) => DenomExp [a] where
  denomexp as = maximum (0 : [ denomexp a | a <- as ])
  denomexp_factor as k = [ denomexp_factor a k | a <- as ]

instance (DenomExp a) => DenomExp (Cplx a) where
  denomexp (Cplx a b) = denomexp a `max` denomexp b
  denomexp_factor (Cplx a b) k = Cplx (denomexp_factor a k) (denomexp_factor b k)

-- ----------------------------------------------------------------------
-- * Conversion to ℚ[ω]

-- $ 'QOmega' is the largest one of our \"exact\" arithmetic types. We
-- define a 'toQOmega' family of functions for converting just about
-- anything to 'QOmega'.

-- | A type class for things that can be exactly converted to ℚ[ω].
class ToQOmega a where
  -- | Conversion to 'QOmega'.
  toQOmega :: a -> QOmega

instance ToQOmega Integer where
  toQOmega = fromInteger

instance ToQOmega Rational where
  toQOmega = fromRational

instance (ToQOmega a) => ToQOmega (RootTwo a) where
  toQOmega (RootTwo a b) = toQOmega a + roottwo * toQOmega b
  
instance ToQOmega Dyadic where
  toQOmega (Dyadic a n)
    | n >= 0    = toQOmega a * half^n
    | otherwise = toQOmega a * 2^(-n)

instance (ToQOmega a) => ToQOmega (Cplx a) where
  toQOmega (Cplx a b) = toQOmega a + i * toQOmega b

instance (ToQOmega a) => ToQOmega (Omega a) where
  toQOmega (Omega a b c d) = omega^3 * a' + omega^2 * b' + omega * c' + d'
    where
      a' = toQOmega a
      b' = toQOmega b
      c' = toQOmega c
      d' = toQOmega d

-- ----------------------------------------------------------------------
-- * Parity
    
-- | A type class for things that have parity.
class Parity a where
  -- | Return the parity of something.
  parity :: a -> Z2

instance Integral a => Parity a where
  parity x = if even x then 0 else 1
  
instance Parity ZRootTwo where
  parity (RootTwo a b) = parity a

-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | Return the position of the rightmost \"1\" bit of an Integer, or
-- -1 if none. Do this in time O(/n/ log /n/), where /n/ is the size
-- of the integer (in digits).
lobit :: Integer -> Integer
lobit 0 = -1
lobit n = aux 1 where
  aux k
    | n .&. (2^k-1) == 0 = aux (2*k)
    | otherwise = aux2 k (k `div` 2)
  aux2 upper lower
    | upper - lower < 2 = lower
    | n .&. (2^middle-1) == 0 = aux2 upper middle
    | otherwise = aux2 middle lower
    where
      middle = (upper + lower) `div` 2

-- | If /n/ is of the form 2[sup /k/], return /k/. Otherwise, return
-- 'Nothing'.
log2 :: Integer -> Maybe Integer
log2 n
  | n <= 0 = Nothing
  | n == 2^k = Just k
  | otherwise = Nothing
    where
      k = lobit n

-- | Return 1 + the position of the leftmost \"1\" bit of a
-- non-negative 'Integer'. Do this in time O(/n/ log /n/), where /n/
-- is the size of the integer (in digits).
hibit :: Integer -> Int
hibit 0 = 0
hibit n = aux 1 where
  aux k 
    | n >= 2^k  = aux (2*k)
    | otherwise = aux2 k (k `div` 2)    -- 2^(k/2) <= n < 2^k
  aux2 upper lower 
    | upper - lower < 2  = upper
    | n >= 2^middle = aux2 upper middle
    | otherwise = aux2 middle lower
    where
      middle = (upper + lower) `div` 2

-- | For /n/ ≥ 0, return the floor of the square root of /n/. This is
-- done using integer arithmetic, so there are no rounding errors.
intsqrt :: (Integral n) => n -> n
intsqrt n 
  | n <= 0 = 0
  | otherwise = iterate a
    where
      iterate m
        | m_sq <= n && m_sq + 2*m + 1 > n = m
        | otherwise = iterate ((m + n `div` m) `div` 2)
          where
            m_sq = m*m
      a = 2^(b `div` 2)
      b = hibit (fromIntegral n)
