-- | A /semigroup/ ('Semigroup') is a set with a binary associative operation (@<>@).
--
-- This module defines a /partial semigroup/ ('PartialSemigroup'), a
-- semigroup for which @<>@ is not required to be defined over all inputs.
module Data.PartialSemigroup
  ( -- * Partial semigroup
    PartialSemigroup (..),

    -- * Either
    -- $either
    AppendLeft (..),
    AppendRight (..),

    -- * Tuples
    -- $tuple

    -- * Concatenation
    groupAndConcat,
    partialConcat,
    partialConcat1,

    -- * Zipping
    partialZip,
    partialZip1,

    -- * Total to partial
    -- $total
    Total (..),

    -- * Partial to total
    -- $partial
    Partial (..),

    -- * Refusing to combine
    -- $refusing
    One (..),
    AtMostOne (..),
  )
where

import Control.Applicative (ZipList (..), (<$>), (<*>))
import Control.Monad (foldM, (>>=))
import Data.Either (Either (..))
import Data.Function ((.), ($))
import Data.Functor.Identity (Identity (..))
import Data.List.NonEmpty (NonEmpty (..), nonEmpty)
import Data.Maybe (Maybe (..))
import Data.Monoid (Product (..), Sum (..))
import Data.Semigroup (Semigroup (..))
import Data.Void (Void)
import Prelude (Enum (..), Eq (..), error, Integral (..), Num (..), odd, Ord (..), otherwise, Read, Show)

-- $setup
--
-- >>> import Data.Function (($))
-- >>> import Data.Functor (fmap)

-- The same fixity as <>
infixr 6 <>?

-- | A 'PartialSemigroup' is like a 'Semigroup', but with an operator returning
-- @'Maybe' a@ rather than @a@.
--
-- For comparison:
--
-- @
-- ('<>')  :: 'Semigroup' a        => a -> a -> a
-- ('<>?') :: 'PartialSemigroup' a => a -> a -> 'Maybe' a
-- @
--
-- === The associativity axiom for partial semigroups
--
-- For all @x@, @y@, @z@:
--
--  * If @x '<>?' y = 'Just' xy@ and @y '<>?' z = 'Just' yz@, then
--
--      * @x '<>?' yz = xy '<>?' z@.
--
-- ==== Relationship to the semigroup associativity axiom
--
-- The partial semigroup associativity axiom is a natural adaptation of the
-- semigroup associativity axiom
--
-- @x '<>' (y '<>' z) = (x '<>' y) '<>' z@
--
-- with a slight modification to accommodate situations where '<>' is undefined. We
-- may gain some insight into the connection between 'Semigroup' and
-- 'PartialSemigroup' by rephrasing the partial semigroup associativity in terms of
-- a partial '<>' operator thusly:
--
-- For all @x@, @y@, @z@:
--
--  * If @x '<>' y@ and @y '<>' z@ are both defined, then
--
--      * @x '<>' (y '<>' z)@ is defined if and only if @(x '<>' y) '<>' z@ is
--        defined, and
--
--      * if these things /are/ all defined, then the axiom for total semigroups
--        @x '<>' (y '<>' z) = (x '<>' y) '<>' z@ must hold.
class PartialSemigroup a where
  -- | A partial associative operation.
  --
  -- @since 0.1.0.1
  (<>?) :: a -> a -> Maybe a
  x <>? y = psconcat $ x :| [y]

  -- | Reduce a non-empty list with '<>?'.
  --
  -- @since 0.7.0.0
  psconcat :: NonEmpty a -> Maybe a
  psconcat (x :| xs) = foldM (<>?) x xs

  -- | Repeat a value @n@ times.
  --
  -- @since 0.7.0.0
  pstimes :: Integral b => b -> a -> Maybe a
  pstimes = pstimesDefault

  {-# MINIMAL (<>?) | psconcat #-}

-- | Efficiently exponentiate a value @x@ to the @n@th power.
pstimesDefault :: (PartialSemigroup a, Integral b) => b -> a -> Maybe a
pstimesDefault n x
  | n <  toEnum 1 = error "Exponentiation only defined with positive exponent"
  | n == toEnum 1 = Just x
  | odd n         = pstimesDefault (pred n) x >>= (x <>?)
  | otherwise     = do
      halfNTimes <- pstimesDefault (n `quot` 2) x
      halfNTimes <>? halfNTimes

--------------------------------------------------------------------------------

-- | The empty set is a partial semigroup, with its semigroup
-- operation everywhere undefined (yields @Nothing@).
--
-- Note that this semigroup is different from the instance for
-- @'Total' 'Void'@, for which @(Total undefined) <>? (Total
-- undefined) == Just (Total undefined)@.
--
-- @since 0.7.0.0
instance PartialSemigroup Void where
  _ <>? _ = Nothing
  pstimes n _
    | n < toEnum 1 = error "Exponentiation only defined with positive exponent"
    | otherwise    = Nothing

--------------------------------------------------------------------------------

-- | The unit set is the trivial (total) semigroup.
--
-- @since 0.0.0.1
instance PartialSemigroup () where
  _ <>? _    = Just ()
  psconcat _ = Just ()
  pstimes n _
    | n < toEnum 1 = error "Exponentiation only defined with positive exponent"
    | otherwise    = Just ()

--------------------------------------------------------------------------------

-- | Lists form a (total) semigroup under concatenation.
--
-- @since 0.0.0.1
instance PartialSemigroup [a] where
  x <>? y = Just (x <> y)

--------------------------------------------------------------------------------

-- | Non-empty lists form a (total) semigroup under concatenation.
--
-- @since 0.7.0.0
instance PartialSemigroup (NonEmpty a) where
  x <>? y = Just (x <> y)

--------------------------------------------------------------------------------

instance PartialSemigroup b => PartialSemigroup (a -> b) where
  f <>? g = \x -> f x <>? g x
  stimes n f e = stimes n $ f e

--------------------------------------------------------------------------------

instance Num a => PartialSemigroup (Sum a) where
  x <>? y = Just (x <> y)

instance Num a => PartialSemigroup (Product a) where
  x <>? y = Just (x <> y)

--------------------------------------------------------------------------------

instance PartialSemigroup a => PartialSemigroup (Identity a) where
  Identity x <>? Identity y = Identity <$> (x <>? y)

--------------------------------------------------------------------------------

instance
  (PartialSemigroup a, PartialSemigroup b) =>
  PartialSemigroup (Either a b)
  where
  Left x <>? Left y = Left <$> (x <>? y)
  Right x <>? Right y = Right <$> (x <>? y)
  _ <>? _ = Nothing

-- $either
--
-- The exemplary nontrivial 'PartialSemigroup' is 'Either', for which the append
-- operator produces a 'Just' result only if both arguments are 'Left' or both
-- arguments are 'Right'.
--
-- >>> Left "ab" <>? Left "cd"
-- Just (Left "abcd")
--
-- >>> Left "ab" <>? Right [1, 2]
-- Nothing

--------------------------------------------------------------------------------

-- $tuple
--
-- A tuple forms a partial semigroups when all of its constituent parts have
-- partial semigroups. The append operator returns a 'Just' value when /all/ of the
-- fields' append operators must return 'Just' values.
--
-- >>> x = (Left "ab", Right "hi")
-- >>> y = (Left "cd", Right "jk")
-- >>> x <>? y
-- Just (Left "abcd",Right "hijk")
--
-- >>> x = (Left "ab", Right "hi")
-- >>> y = (Left "cd", Left "jk")
-- >>> x <>? y
-- Nothing

-- | The cartesian product of two partial semigroups is a partial semigroup,
-- with append defined component-wise.
instance
  ( PartialSemigroup a
  , PartialSemigroup b
  ) => PartialSemigroup (a, b)
  where
  (a, b) <>? (a', b') =
    (,)
      <$> (a <>? a')
      <*> (b <>? b')
  pstimes n (a, b) =
    (,)
      <$> pstimes n a
      <*> pstimes n b

-- | The cartesian product of three partial semigroups is a partial semigroup,
-- with append defined component-wise.
instance
  ( PartialSemigroup a
  , PartialSemigroup b
  , PartialSemigroup c
  ) => PartialSemigroup (a, b, c)
  where
  (a, b, c) <>? (a', b', c') =
    (,,)
      <$> (a <>? a')
      <*> (b <>? b')
      <*> (c <>? c')
  pstimes n (a, b, c) =
    (,,)
      <$> pstimes n a
      <*> pstimes n b
      <*> pstimes n c

-- | The cartesian product of four partial semigroups is a partial semigroup,
-- with append defined component-wise.
instance
  ( PartialSemigroup a
  , PartialSemigroup b
  , PartialSemigroup c
  , PartialSemigroup d
  ) => PartialSemigroup (a, b, c, d)
  where
  (a, b, c, d) <>? (a', b', c', d') =
    (,,,)
      <$> (a <>? a')
      <*> (b <>? b')
      <*> (c <>? c')
      <*> (d <>? d')
  pstimes n (a, b, c, d) =
    (,,,)
      <$> pstimes n a
      <*> pstimes n b
      <*> pstimes n c
      <*> pstimes n d

-- | The cartesian product of five partial semigroups is a partial semigroup,
-- with append defined component-wise.
instance
  ( PartialSemigroup a
  , PartialSemigroup b
  , PartialSemigroup c
  , PartialSemigroup d
  , PartialSemigroup e
  ) => PartialSemigroup (a, b, c, d, e)
  where
  (a, b, c, d, e) <>? (a', b', c', d', e') =
    (,,,,)
      <$> (a <>? a')
      <*> (b <>? b')
      <*> (c <>? c')
      <*> (d <>? d')
      <*> (e <>? e')
  pstimes n (a, b, c, d, e) =
    (,,,,)
      <$> pstimes n a
      <*> pstimes n b
      <*> pstimes n c
      <*> pstimes n d
      <*> pstimes n e

--------------------------------------------------------------------------------

-- | Apply a semigroup operation to any pairs of consecutive list elements where
-- the semigroup operation is defined over them.
--
-- ==== Examples
--
-- For 'Either', 'groupAndConcat' combines contiguous sublists of 'Left' and
-- contiguous sublists of 'Right'.
--
-- >>> xs = [Left "a", Right "b", Right "c", Left "d", Left "e", Left "f"]
-- >>> groupAndConcat xs
-- [Left "a",Right "bc",Left "def"]
groupAndConcat :: PartialSemigroup a => [a] -> [a]
groupAndConcat [] = []
groupAndConcat [x] = [x]
groupAndConcat (x : y : zs) =
  case x <>? y of
    Nothing -> x : groupAndConcat (y : zs)
    Just a -> groupAndConcat (a : zs)

-- | If @xs@ is nonempty and the partial semigroup operator is defined for all
-- pairs of values in @xs@, then @'partialConcat' xs@ produces a 'Just' result with
-- the combination of all the values. Otherwise, returns 'Nothing'.
--
-- ==== Examples
--
-- When all values can combine, we get a 'Just' of their combination.
--
-- >>> partialConcat [Left "a", Left "b", Left "c"]
-- Just (Left "abc")
--
-- When some values cannot be combined, we get 'Nothing'.
--
-- >>> partialConcat [Left "a", Left "b", Right "c"]
-- Nothing
--
-- When the list is empty, we get 'Nothing'.
--
-- >>> partialConcat []
-- Nothing
partialConcat :: PartialSemigroup a => [a] -> Maybe a
partialConcat x =
  nonEmpty x >>= partialConcat1

-- | Like 'partialConcat', but for non-empty lists.
--
-- ==== Examples
--
-- When all values can combine, we get a 'Just' of their combination.
--
-- >>> partialConcat1 (Left "a" :| [Left "b", Left "c"])
-- Just (Left "abc")
--
-- When some values cannot be combined, we get 'Nothing'.
--
-- >>> partialConcat1 (Left "a" :| [Left "b", Right "c"])
-- Nothing
partialConcat1 :: PartialSemigroup a => NonEmpty a -> Maybe a
partialConcat1 = psconcat
{-# DEPRECATED partialConcat1 "Use psconcat instead" #-}

-- | ==== Examples
--
-- If lists are the same length and each pair of elements successfully, then we get
-- a 'Just' result.
--
-- >>> xs = [Left "a", Left "b", Right "c"]
-- >>> ys = [Left "1", Left "2", Right "3"]
-- >>> partialZip xs ys
-- Just [Left "a1",Left "b2",Right "c3"]
--
-- If the pairs do not all combine, then we get 'Nothing'.
--
-- >>> xs = [Left "a", Left "b", Right "c"]
-- >>> ys = [Left "1", Right "2", Right "3"]
-- >>> partialZip xs ys
-- Nothing
--
-- If the lists have different lengths, then we get 'Nothing'.
--
-- >>> xs = [Left "a", Left "b", Right "c"]
-- >>> ys = [Left "1", Left "2"]
-- >>> partialZip xs ys
-- Nothing
partialZip :: PartialSemigroup a => [a] -> [a] -> Maybe [a]
partialZip [] [] = Just []
partialZip [] _ = Nothing
partialZip _ [] = Nothing
partialZip (x : xs) (y : ys) =
  (:) <$> (x <>? y) <*> partialZip xs ys

-- | Like 'partialZip', but for non-empty lists.
--
-- ==== Examples
--
-- If lists are the same length and each pair of elements successfully, then we get
-- a 'Just' result.
--
-- >>> xs = Left "a" :| [Left "b", Right "c"]
-- >>> ys = Left "1" :| [Left "2", Right "3"]
-- >>> partialZip1 xs ys
-- Just (Left "a1" :| [Left "b2",Right "c3"])
--
-- If the pairs do not all combine, then we get 'Nothing'.
--
-- >>> xs = Left "a" :| [Left "b", Right "c"]
-- >>> ys = Left "1" :| [Right "2", Right "3"]
-- >>> partialZip1 xs ys
-- Nothing
--
-- If the lists have different lengths, then we get 'Nothing'.
--
-- >>> xs = Left "a" :| [Left "b", Right "c"]
-- >>> ys = Left "1" :| [Left "2"]
-- >>> partialZip1 xs ys
-- Nothing
partialZip1 ::
  PartialSemigroup a =>
  NonEmpty a ->
  NonEmpty a ->
  Maybe (NonEmpty a)
partialZip1 (x :| xs) (y :| ys) =
  (:|) <$> (x <>? y) <*> partialZip xs ys

-- | 'partialZip'
instance PartialSemigroup a => PartialSemigroup (ZipList a) where
  ZipList x <>? ZipList y = ZipList <$> partialZip x y

--------------------------------------------------------------------------------

-- $partial
--
-- For every type @a@ with a 'PartialSemigroup', we can construct a total
-- 'Semigroup' for @'Maybe' a@ as:
--
-- @
-- 'Just' x <> 'Just' y = x '<>?' y
-- _ '<>' _ = 'Nothing'
-- @
--
-- We don't actually define this instance for 'Maybe' because it already has a
-- different 'Semigroup' defined over it, but we do provide the 'Partial' wrapper
-- which has this instance.

-- | A wrapper for 'Maybe' with an error-propagating 'Semigroup'.
newtype Partial a = Partial {unPartial :: Maybe a}
  deriving (Eq, Ord, Read, Show)

instance PartialSemigroup a => Semigroup (Partial a) where
  Partial (Just x) <> Partial (Just y) = Partial (x <>? y)
  _ <> _ = Partial Nothing

--------------------------------------------------------------------------------

-- $total
--
-- For every type with a 'Semigroup', we can trivially construct a
-- 'PartialSemigroup' as:
--
-- @
-- x '<>?' y = 'Just' (x '<>' y)
-- @
--
-- Additionally, any type with a 'Semigroup' can be treated as a 'PartialSemigroup'
-- by lifting it into 'Total'.

-- | A wrapper to turn any value with a 'Semigroup' instance into a value with a
-- 'PartialSemigroup' instance whose '<>?' operator always returns 'Just'.
--
-- ==== Examples
--
-- >>> Total "ab" <>? Total "cd"
-- Just (Total {unTotal = "abcd"})
--
-- >>> f = getProduct . unTotal
-- >>> g = Total . Product
-- >>> fmap f . partialConcat . fmap g $ [1..4]
-- Just 24
newtype Total a = Total {unTotal :: a}
  deriving (Eq, Ord, Read, Show)

instance Semigroup a => PartialSemigroup (Total a) where
  Total x <>? Total y = Just (Total (x <> y))

--------------------------------------------------------------------------------

-- | A wrapper for 'Either' where the 'PartialSemigroup' operator is defined
-- only over 'Left' values.
--
-- ==== Examples
--
-- Two 'Left's make a 'Just'.
--
-- >>> AppendLeft (Left "ab") <>? AppendLeft (Left "cd")
-- Just (AppendLeft {unAppendLeft = Left "abcd"})
--
-- Anything else produces 'Nothing'
--
-- >>> AppendLeft (Right "ab") <>? AppendLeft (Right "cd")
-- Nothing
--
-- 'groupAndConcat' combines consecutive 'Left' values, leaving the 'Right' values
-- unmodified.
--
-- >>> xs = [Left "a", Left "b", Right "c", Right "d", Left "e", Left "f"]
-- >>> fmap unAppendLeft . groupAndConcat . fmap AppendLeft $ xs
-- [Left "ab",Right "c",Right "d",Left "ef"]
newtype AppendLeft a b = AppendLeft {unAppendLeft :: Either a b}
  deriving (Eq, Ord, Read, Show)

instance PartialSemigroup a => PartialSemigroup (AppendLeft a b) where
  AppendLeft (Left x) <>? AppendLeft (Left y) =
    AppendLeft . Left <$> (x <>? y)
  _ <>? _ = Nothing

--------------------------------------------------------------------------------

-- | A wrapper for 'Either' where the 'PartialSemigroup' operator is defined
-- only over 'Right' values.
--
-- ==== Examples
--
-- Two 'Right's make a 'Just'.
--
-- >>> AppendRight (Right "ab") <>? AppendRight (Right "cd")
-- Just (AppendRight {unAppendRight = Right "abcd"})
--
-- Anything else produces 'Nothing'
--
-- >>> AppendRight (Left "ab") <>? AppendRight (Left "cd")
-- Nothing
--
-- 'groupAndConcat' combines consecutive 'Right' values, leaving the 'Left' values
-- unmodified.
--
-- >>> xs = [Left "a", Left "b", Right "c", Right "d", Left "e", Left "f"]
-- >>> fmap unAppendRight . groupAndConcat . fmap AppendRight $ xs
-- [Left "a",Left "b",Right "cd",Left "e",Left "f"]
newtype AppendRight a b = AppendRight {unAppendRight :: Either a b}
  deriving (Eq, Ord, Read, Show)

instance PartialSemigroup b => PartialSemigroup (AppendRight a b) where
  AppendRight (Right x) <>? AppendRight (Right y) =
    AppendRight . Right <$> (x <>? y)
  _ <>? _ = Nothing

--------------------------------------------------------------------------------

-- $refusing
--
-- These are 'PartialSemigroup' instances that don't really combine their values
-- at all; whenever more than one thing is present, '<>?' fails.

-- | A partial semigroup operation which always fails.
newtype One a = One {theOne :: a}
  deriving (Eq, Ord, Read, Show)

instance PartialSemigroup (One a) where
  _ <>? _ = Nothing

-- | A wrapper for 'Maybe' whose partial semigroup operation fails when two
-- 'Just's are combined.
newtype AtMostOne a = AtMostOne {theOneMaybe :: Maybe a}
  deriving (Eq, Ord, Read, Show)

instance PartialSemigroup (AtMostOne a) where
  AtMostOne Nothing <>? x = Just x
  x <>? AtMostOne Nothing = Just x
  _ <>? _ = Nothing
