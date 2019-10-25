{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
module Exercises where

import Data.Kind    (Constraint, Type)
import GHC.TypeLits (Symbol)





{- ONE -}

-- | Let's look at the following type family to build a constraint:

type family All (c :: Type -> Constraint) (xs :: [Type]) :: Constraint where
  All c '[] = ()
  All c (x ': xs) = (c x, All c xs)

-- | a. Why does it have to be restricted to 'Type'? Can you make this more
-- general?

type family All' (c :: a -> Constraint) (xs :: [a]) :: Constraint where
  All' c '[] = ()
  All' c (x ': xs) = (c x, All c xs)

-- | b. Why does it have to be restricted to 'Constraint'? Can you make this
-- more general? Why is this harder?

-- Because constraints are separate from types and kinds.. i think. They live
-- separately, so we must be explicit about the difference

-- actual answer:

-- Not really - we need some polymorphic way of "combining" things, probably
-- passed in as another parameter. Because type families can't be
-- partially-applied, this is actually really tricky to do in the general case
-- (at the moment).

-- hmm not sure if I get this
-- making it polymorphic does compile

-- playing more

-- Ok I think I get it. Constraint tuples have the property of being flattened,
-- but Type tuples do it. Thus the behavior is different and we have no generalised
-- between the two

data Omg (a :: [k]) = Omg

blah :: All' Show xs => Omg xs -> String
blah = const "asdf"

blah2 :: String
blah2 = blah (Omg :: Omg '[Int])


{- TWO -}

-- | Sometimes, we're working with a lot of values, and we'd like some way of
-- identifying them for the compiler. We could make newtypes, sure, but maybe
-- there are loads, and we just don't want the boilerplate. Luckily for us, we
-- can introduce this new type:

data Tagged (name :: Symbol) (a :: Type)
  = Tagged { runTagged :: a }

-- | 'Tagged' is just like 'Identity', except that it has a type-level string
-- attached to it. This means we can write things like this:

x :: Tagged "Important" Int
x = Tagged 42

y :: Tagged "Not so important" Int
y = Tagged 23

-- | What's more, we can use that tag in function signatures to restrict the
-- input:

f :: Tagged "Important" Int -> IO ()
f (Tagged x) = putStrLn (show x <> " is important!")

-- | a. Symbols are all well and good, but wouldn't it be nicer if we could
-- generalise this?

data Tagged' (name :: n) (a :: Type)
  = Tagged' { runTagged' :: a }

-- | b. Can we generalise 'Type'? If so, how? If not, why not?

-- data Tagged'' (name :: n) (a :: k)
--   = Tagged'' { runTagged'' :: a }

-- No, because doing that means we would need to be able to embed any kind in a data constructor
-- We can only have `Type`s with runtime values

-- | c. Often when we use the 'Tagged' type, we prefer a sum type (promoted
-- with @DataKinds@) over strings. Why do you think this might be?

-- More safe. Remove the possibility of typos. We can also possibly exaustively pattern match in
-- type familes


{- THREE -}

-- | We can use the following to test type-level equivalence.

data a :=: b where
  Refl :: a :=: a

-- | a. What do you think the kind of (:=:) is?

-- Type -> Type -> Type

-- | b. Does @PolyKinds@ make a difference to this kind?

-- Seems no? We don't specify a kind, so they should all just be Type

-- | c. Regardless of your answer to part (b), is this the most general kind we
-- could possibly give this constructor? If not (hint: it's not), what more
-- general kind could we give it, and how would we tell this to GHC?

data (a :: k) :==: (b :: k') where
  Refl' :: a :==: a

wah :: String :=: [Char]
wah = Refl

-- wah2 :: String :=: Int
-- wah2 = Refl :: String :=: String

-- My intuition is that because Refl references itself in its type
-- data a :=: b AND Refl :: a :=: a, for this to work it needs to be able to unify a and b
-- ie. a ~ b

wah3 :: String :==: [Char]
wah3 = Refl'

-- wah4 :: String :==: 'True
-- wah4 = Refl'



{- FOUR -}

-- | We've talked about singleton types previously, and how they allow us to
-- share a value between the value and type levels. Libraries such as
-- @singletons@ provide many utilities for working with these types, many of
-- which rely on a (type-level) function to get from a kind to its singleton.
-- In our toy version of the library, that type family may look like this:

type family Sing (x :: k) :: Type

-- | Notice that it's an /open/ type family, thus we define instances for it
-- using the @type instance Sing x = y@ syntax.

-- | a. Here's the singleton for the @Bool@ kind. Remembering that the
-- singleton for some @x@ of kind @Bool@ is @SBool x@, write a @Sing@ instance
-- for the @Bool@ kind. Remember that we can pattern-match on /kinds/ in type
-- families - if you're on the right lines, this is a one-liner!

data SBool (b :: Bool) where
  STrue  :: SBool 'True
  SFalse :: SBool 'False

type instance Sing x = SBool x

-- this works because SBool x, the x is of kind Bool, so we are creating an instance for Sing x :: Bool

-- | b. Repeat the process for the @Nat@ kind. Again, if you're on the right
-- lines, this is very nearly a copy-paste job!

data Nat = Z | S Nat

data SNat (n :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

type instance Sing x = SNat x



{- FIVE -}

-- | In dependently-typed programming, we talk about the notion of a "Sigma
-- type", or "dependent pair". This is a single-constructor GADT that takes two
-- arguments: a singleton for some kind, and some type indexed by the type
-- represented by the singleton. Don't panic, let's do an example:

-- | Consider the following GADT to describe a (fixed-length) list of strings:

data Strings (n :: Nat) where
  SNil ::                        Strings  'Z
  (:>) :: String -> Strings n -> Strings ('S n)

-- | If we have a working sigma type, we should be able to package a @Strings
-- n@ and an @SNat n@ into @Sigma Strings@, existentialising the actual length.
--
-- @
example :: [Sigma Strings]
example
  = [ Sigma         SZ   SNil
    , Sigma     (SS SZ)  ("hi" :> SNil)
    , Sigma (SS (SS SZ)) ("hello" :> ("world" :> SNil))
    ]
-- @

-- | a. Write this type's definition: If you run the above example, the
-- compiler should do a lot of the work for you...

data Sigma (f :: Nat -> Type) where
  Sigma :: Sing n -> f n -> Sigma f

-- | b. Surely, by now, you've guessed this question? Why are we restricting
-- ourselves to 'Nat'? Don't we have some more general way to talk about
-- singletons? The family of singletons? Any type within the family of
-- singletons? Sing it with me! Generalise that type!

data Sigma' (f :: k -> Type) where
  Sigma' :: Sing n -> f n -> Sigma' f

-- I don't really understand why it is happy with k <> n
-- Are we really making it polymorphic if we know SNat takes a Nat n
-- and our function takes an n?

data Cools (a :: Bool) where
  NotCool :: Cools 'False
  VeryCool :: Cools 'True

-- example3 :: [Sigma' Cools]
-- example3
--   = [ Sigma' SZ NotCool
--     , Sigma' (SS SZ) VeryCool
--     ]

-- ok I stuffed up, Sing n, not SNat. Now I get what Sing is doing

-- yeah so I think you can create the Type which isn't bound to Nat
-- but it is an uninhabited type, because the data constructor binds
-- the argument to Nat

example2 :: [Sigma' Strings]
example2
  = [ Sigma'         SZ   SNil
    , Sigma'     (SS SZ)  ("hi" :> SNil)
    , Sigma' (SS (SS SZ)) ("hello" :> ("world" :> SNil))
    ]

-- | c. In exercise 5, we wrote a 'filter' function for 'Vector'. Could we
-- rewrite this with a sigma type, perhaps?

data Vector (a :: Type) (n :: Nat) where -- @n@ and @a@ flipped... Hmm, a clue!
  VNil  ::                    Vector a  'Z
  VCons :: a -> Vector a n -> Vector a ('S n)

filterV :: (a -> Bool) -> Vector a n -> Sigma' (Vector a)
filterV p  VNil        = Sigma' SZ VNil
filterV p (VCons x xs)
  | p x       = cons x (filterV p xs)
  | otherwise = filterV p xs
  where
    cons :: a -> Sigma' (Vector a) -> Sigma' (Vector a)
    cons x (Sigma' n xs) = Sigma' (SS n) (VCons x xs)


-- struggled with this, mostly cheated..


{- SIX -}

-- | Our sigma type is actually very useful. Let's imagine we're looking at
-- a communication protocol over some network, and we label our packets as
-- @Client@ or @Server@:

data Label = Client | Server

-- | Client data and server data are different, however:

data ClientData
  = ClientData
      { name         :: String
      , favouriteInt :: Int
      }

data ServerData
  = ServerData
      { favouriteBool     :: Bool
      , complimentaryUnit :: ()
      }

-- | a. Write a GADT indexed by the label that holds /either/ client data or
-- server data.

data Communication (label :: Label) where
  CClientData :: ClientData -> Communication 'Client
  CServerData :: ServerData -> Communication 'Server

-- | b. Write a singleton for 'Label'.

data SLabel (label :: Label) where
  SClient :: SLabel 'Client
  SServer :: SLabel 'Server

type instance Sing x = SLabel x

-- | c. Magically, we can now group together blocks of data with differing
-- labels using @Sigma Communication@, and then pattern-match on the 'Sigma'
-- constructor to find out which packet we have! Try it:

-- data Sigma' (f :: k -> Type) where
--   Sigma' :: SNat n -> f n -> Sigma' f

serverLog :: [Sigma' Communication] -> [ServerData]
serverLog [] = []
serverLog ((Sigma' SServer (CServerData sd)):xs) = sd : serverLog xs
serverLog ((Sigma' SClient _):xs) = serverLog xs

-- | d. Arguably, in this case, the Sigma type is overkill; what could we have
-- done, perhaps using methods from previous chapters, to "hide" the label
-- until we pattern-matched?

-- I don't really get this. I understand sigma doesn't give us much, because we can just pattern
-- match on the GADT data constructor.. but the answer doesn't make much sense to me. Oh well :)
