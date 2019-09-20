{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
module Exercises where

import Data.Kind (Type, Constraint)
import Data.Function ((&))





{- ONE -}

-- | One of the restrictions around classes that we occasionally hit is that we
-- can only have one instance for a type. There are, for example, two good
-- candidates for a monoid instance when we think about 'Integer':

data IntegerMonoid = Sum | Product

-- | a. Write a newtype around 'Integer' that lets us choose which instance we
-- want.

newtype IntegerWith (a :: IntegerMonoid) = IntegerWith Integer

-- | b. Write the two monoid instances for 'Integer'.

instance Semigroup (IntegerWith 'Sum) where
  (<>) (IntegerWith a) (IntegerWith b) = IntegerWith $ a + b

instance Monoid (IntegerWith 'Sum) where
  mempty = IntegerWith 0

instance Semigroup (IntegerWith 'Product) where
  (<>) (IntegerWith a) (IntegerWith b) = IntegerWith $ a * b

instance Monoid (IntegerWith 'Product) where
  mempty = IntegerWith 1

-- | c. Why do we need @FlexibleInstances@ to do this?

-- Because 'Sum and 'Product are not polymorphic variables, but types



{- TWO -}

-- | We can write a type that /is/ of kind 'Type', but has no value-level
-- members. We usually call this type 'Void':

data Void -- No constructors!

-- | a. If we promote this with DataKinds, can we produce any /types/ of kind
-- 'Void'?

-- No, we only get promoted data contrucutors, but `Void` has none

-- | b. What are the possible type-level values of kind 'Maybe Void'?

-- There shouldn't be any, because there is no `Void` promoted data contructor

-- | c. Considering 'Maybe Void', and similar examples of kinds such as
-- 'Either Void Bool', why do you think 'Void' might be a useful kind?

-- It acts as a unit type, giving us the effective option of including a type or not.





{- THREE -}

-- | a. Write a GADT that holds strings or integers, and keeps track of how
-- many strings are present. Note that you might need more than 'Nil' and
-- 'Cons' this time...

data Nat = Z | S Nat

data StringAndIntList (stringCount :: Nat) where
  SINil :: StringAndIntList 'Z
  SIStringCons :: String -> StringAndIntList n -> StringAndIntList (S n)
  SIIntCons :: Int -> StringAndIntList n -> StringAndIntList n

-- | b. Update it to keep track of the count of strings /and/ integers.

data StringAndIntList' (stringCount :: Nat) (intCount :: Nat) where
  SINil' :: StringAndIntList' 'Z 'Z
  SIStringCons' :: String -> StringAndIntList' s i -> StringAndIntList' (S n) i
  SIIntCons' :: Int -> StringAndIntList' s i -> StringAndIntList' n (S i)


-- | c. What would be the type of the 'head' function?

sailHead :: StringAndIntList' s i -> Maybe (Either String Int)
sailHead SINil' = Nothing
sailHead (SIStringCons' s _) = Just $ Left s
sailHead (SIIntCons' i _) = Just $ Right i


{- FOUR -}

-- | When we talked about GADTs, we discussed existentials, and how we could
-- only know something about our value if the context told us:

data Showable where
  Showable :: Show a => a -> Showable

-- | a. Write a GADT that holds something that may or may not be showable, and
-- stores this fact in the type-level.

data MaybeShowable (isShowable :: Bool) where
  NoShowable :: a -> MaybeShowable 'False
  YesShowable :: Show a => a -> MaybeShowable 'True

-- | b. Write a 'Show' instance for 'MaybeShowable'. Your instance should not
-- work unless the type is actually 'show'able.

instance Show (MaybeShowable 'True) where
  show (YesShowable a) = show a

-- | c. What if we wanted to generalise this to @Constrainable@, such that it
-- would work for any user-supplied constraint of kind 'Constraint'? How would
-- the type change? What would the constructor look like? Try to build this
-- type - GHC should tell you exactly which extension you're missing.

data MaybeConstrainable (c :: Type -> Constraint) where
  Constrained :: c a => a -> MaybeConstrainable c

{- FIVE -}

-- | Recall our list type:

data List a = Nil | Cons a (List a)

-- | a. Use this to write a better 'HList' type than we had in the @GADTs@
-- exercise. Bear in mind that, at the type-level, 'Nil' and 'Cons' should be
-- "ticked". Remember also that, at the type-level, there's nothing weird about
-- having a list of types!

data HList (types :: List Type) where
  HNil :: HList 'Nil
  HCons :: x -> HList xs -> HList ('Cons x xs)

-- | b. Write a well-typed, 'Maybe'-less implementation for the 'tail' function
-- on 'HList'.

hListTail :: HList ('Cons x xs) -> HList xs
hListTail (HCons _ tail) = tail

-- | c. Could we write the 'take' function? What would its type be? What would
-- get in our way?

-- hListTake :: Nat -> HList ('Cons x xs) -> HList (???)

-- we can only do it with a dependently typed vector as we need the vocab to
-- talk about the size of the HList for the different types



{- SIX -}

-- | Here's a boring data type:

data BlogAction
  = AddBlog
  | DeleteBlog
  | AddComment
  | DeleteComment

-- | a. Two of these actions, 'DeleteBlog' and 'DeleteComment', should be
-- admin-only. Extend the 'BlogAction' type (perhaps with a GADT...) to
-- express, at the type-level, whether the value is an admin-only operation.
-- Remember that, by switching on @DataKinds@, we have access to a promoted
-- version of 'Bool'!

data BlogAction' (isAdmin :: Bool) where
  AddBlog' :: BlogAction' 'False
  DeleteBlog' :: BlogAction' 'True
  AddComment' :: BlogAction' 'False
  DeleteComment' :: BlogAction' 'True

-- | b. Write a 'BlogAction' list type that requires all its members to be
-- the same "access level": "admin" or "non-admin".

-- data BlogActionList (isSafe :: Bool) where
--   BALNil :: BlogActionList isSafe
--   BALCons :: BlogAction' isSafe -> BlogActionList isSafe -> BlogActionList isSafe

newtype BlogActionList (isSafe :: Bool)
  = BlogActionList [BlogAction' isSafe]

-- | c. Let's imagine that our requirements change, and 'DeleteComment' is now
-- available to a third role: moderators. Could we use 'DataKinds' to introduce
-- the three roles at the type-level, and modify our type to keep track of
-- this?

data Role
  = User
  | Moderator
  | Admin

data BlogAction'' (who :: [Role]) where
  AddBlog'' :: BlogAction'' '[ 'User ]
  DeleteBlog'' :: BlogAction'' '[ 'Admin ]
  AddComment'' :: BlogAction'' '[ 'User ]
  DeleteComment'' :: BlogAction'' '[ 'Admin, 'Moderator ]


-- Seems that `'` is optional in `'User`. I guess you automatically use the promoted data constructor
-- in the type level list


{- SEVEN -}

-- | When we start thinking about type-level Haskell, we inevitably end up
-- thinking about /singletons/. Singleton types have a one-to-one value-type
-- correspondence - only one value for each type, only one type for each value.
-- A simple example is '()', whose only value is '()'. 'Bool' is /not/ a
-- singleton, because it has multiple values.

-- We can, however, /build/ a singleton type for 'Bool':

data SBool (value :: Bool) where
  SFalse :: SBool 'False
  STrue  :: SBool 'True

-- | a. Write a singleton type for natural numbers:

data SNat (value :: Nat) where
  -- ...

-- | b. Write a function that extracts a vector's length at the type level:

length :: Vector n a -> SNat n
length = error "Implement me!"

-- | c. Is 'Proxy' a singleton type?

data Proxy a = Proxy





{- EIGHT -}

-- | Let's imagine we're writing some Industry Haskell™, and we need to read
-- and write to a file. To do this, we might write a data type to express our
-- intentions:

data Program                     result
  = OpenFile            (Program result)
  | WriteFile  String   (Program result)
  | ReadFile  (String -> Program result)
  | CloseFile (          Program result)
  | Exit                         result

-- | We could then write a program like this to use our language:

myApp :: Program Bool
myApp
  = OpenFile $ WriteFile "HEY" $ (ReadFile $ \contents ->
      if contents == "WHAT"
        then WriteFile "... bug?" $ Exit False
        else CloseFile            $ Exit True)

-- | ... but wait, there's a bug! If the contents of the file equal "WHAT", we
-- forget to close the file! Ideally, we would like the compiler to help us: we
-- could keep track of whether the file is open at the type level!
--
-- - We should /not/ be allowed to open a file if another file is currently
-- open.
--
-- - We should /not/ be allowed to close a file unless a file is open.
--
-- If we had this at the type level, the compiler should have been able to tell
-- us that the branches of the @if@ have different types, and this program
-- should never have made it into production. We should also have to say in the
-- type of 'myApp' that, once the program has completed, the file will be
-- closed.

-- | Improve the 'Program' type to keep track of whether a file is open.  Make
-- sure the constructors respect this flag: we shouldn't be able to read or
-- write to the file unless it's open. This exercise is a bit brain-bending;
-- why? How could we make it more intuitive to write?

-- | EXTRA: write an interpreter for this program. Nothing to do with data
-- kinds, but a nice little problem.

interpret :: Program {- ??? -} a -> IO a
interpret = error "Implement me?"





{- NINE -}

-- | Recall our vector type:

data Vector (n :: Nat) (a :: Type) where
  VNil  :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | Imagine we want to write the '(!!)' function for this vector. If we wanted
-- to make this type-safe, and avoid 'Maybe', we'd have to have a type that can
-- only hold numbers /smaller/ than some type-level value.

-- | a. Implement this type! This might seem scary at first, but break it down
-- into Z and S cases. That's all the hint you need :)

data SmallerThan (limit :: Nat) where
  -- ...

-- | b. Write the '(!!)' function:

(!!) :: Vector n a -> SmallerThan n -> a
(!!) = error "Implement me!"

-- | c. Write a function that converts a @SmallerThan n@ into a 'Nat'.
