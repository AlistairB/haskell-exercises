{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Exercises where


import Data.Foldable (fold)


{- ONE -}

-- | Let's introduce a new class, 'Countable', and some instances to match.
class Countable a where count :: a -> Int
instance Countable Int  where count   = id
instance Countable [a]  where count   = length
instance Countable Bool where count x = if x then 1 else 0

-- | a. Build a GADT, 'CountableList', that can hold a list of 'Countable'
-- things.

data CountableList where
  CLNil :: CountableList
  CLCons :: Countable a => a -> CountableList -> CountableList


-- | b. Write a function that takes the sum of all members of a 'CountableList'
-- once they have been 'count'ed.

countList :: CountableList -> Int
countList CLNil = 0
countList (CLCons a theRest) = count a + countList theRest


-- | c. Write a function that removes all elements whose count is 0.

dropZero :: CountableList -> CountableList
dropZero CLNil = CLNil
dropZero (CLCons a theRest) =
  if count a == 0
  then           dropZero theRest
  else CLCons a (dropZero theRest)


-- | d. Can we write a function that removes all the things in the list of type
-- 'Int'? If not, why not?

filterInts :: CountableList -> CountableList
filterInts = error "Contemplate me!"

-- We can't because we can only pattern match on the data constructors which can only specify down to some `Countable a => a` thing


{- TWO -}

-- | a. Write a list that can take /any/ type, without any constraints.

data AnyList where
  AnyListNil :: AnyList
  AnyListCons :: a -> AnyList -> AnyList

-- | b. How many of the following functions can we implement for an 'AnyList'?

reverseAnyList :: AnyList -> AnyList
reverseAnyList = go AnyListNil
  where
    go :: AnyList -> AnyList -> AnyList
    go acc AnyListNil         = acc
    go acc (AnyListCons x xs) = go (AnyListCons x acc) xs

-- not possible because type a is decidable by the caller (it is a rank 1 function)
-- RankNTypes can be used to make a fully polymorphic a from within the function and it works

filterAnyList :: (forall a. a -> Bool) -> AnyList -> AnyList
filterAnyList _ AnyListNil         = AnyListNil
filterAnyList f (AnyListCons x xs) =
  if f x
  then AnyListCons x (filterAnyList f xs)
  else (filterAnyList f xs)

lengthAnyList :: AnyList -> Int
lengthAnyList AnyListNil = 0
lengthAnyList (AnyListCons _ xs) = 1 + lengthAnyList xs

-- not possible, no way to know that the types are monoidal

foldAnyList :: Monoid m => AnyList -> m
foldAnyList = undefined

isEmptyAnyList :: AnyList -> Bool
isEmptyAnyList AnyListNil = True
isEmptyANyList _          = False

-- no we can't know the types are showable

instance Show AnyList where
  show = error "What about me?"





{- THREE -}

-- | Consider the following GADT:

data TransformableTo output where
  TransformWith
    :: (input -> output)
    ->  input
    -> TransformableTo output

-- | ... and the following values of this GADT:

transformable1 :: TransformableTo String
transformable1 = TransformWith show 2.5

transformable2 :: TransformableTo String
transformable2 = TransformWith (uncurry (++)) ("Hello,", " world!")

-- | a. Which type variable is existential inside 'TransformableTo'? What is
-- the only thing we can do to it?

-- input is, it appears in the data constructor, but not in the type

-- | b. Could we write an 'Eq' instance for 'TransformableTo'? What would we be
-- able to check?

-- yes, you can check the `input` is the same and `f input` = the same output

-- | c. Could we write a 'Functor' instance for 'TransformableTo'? If so, write
-- it. If not, why not?

instance Functor TransformableTo where
  fmap f (TransformWith fio i) = TransformWith (f . fio) i

{- FOUR -}

-- | Here's another GADT:

data EqPair where
  EqPair :: Eq a => a -> a -> EqPair

-- | a. There's one (maybe two) useful function to write for 'EqPair'; what is
-- it?

isEqual :: EqPair -> Bool
isEqual (EqPair a b) = a == b

isNotEqual :: EqPair -> Bool
isNotEqual (EqPair a b) = a /= b

-- | b. How could we change the type so that @a@ is not existential? (Don't
-- overthink it!)

data EqPair' a where
  EqPair' :: Eq a => a -> a -> EqPair' a

-- | c. If we made the change that was suggested in (b), would we still need a
-- GADT? Or could we now represent our type as an ADT?

-- Yes, we still have no way to specify that the `a` must be `Eq`

{- FIVE -}

-- | Perhaps a slightly less intuitive feature of GADTs is that we can set our
-- type parameters (in this case @a@) to different types depending on the
-- constructor.

data MysteryBox a where
  EmptyBox  ::                                MysteryBox ()
  IntBox    :: Int    -> MysteryBox ()     -> MysteryBox Int
  StringBox :: String -> MysteryBox Int    -> MysteryBox String
  BoolBox   :: Bool   -> MysteryBox String -> MysteryBox Bool

-- | When we pattern-match, the type-checker is clever enough to
-- restrict the branches we have to check to the ones that could produce
-- something of the given type.

getInt :: MysteryBox Int -> Int
getInt (IntBox int _) = int

-- | a. Implement the following function by returning a value directly from a
-- pattern-match:

getInt' :: MysteryBox String -> Int
getInt' (StringBox _ (IntBox i _)) = i

-- | b. Write the following function. Again, don't overthink it!

countLayers :: MysteryBox a -> Int
countLayers EmptyBox = 0
countLayers (IntBox _ _) = 1
countLayers (StringBox _ _) = 2
countLayers (BoolBox _ _) = 3

-- | c. Try to implement a function that removes one layer of "Box". For
-- example, this should turn a BoolBox into a StringBox, and so on. What gets
-- in our way? What would its type be?

-- peel :: (forall a b. MysteryBox a -> MysteryBox b)
-- peel EmptyBox = EmptyBox
-- peel (IntBox _ box) = box
-- peel (StringBox _ box) = box
-- peel (BoolBox _ box) = box

-- we can't write a type for this as different unwrappings result in different types for b
-- we can only write b as polymorhpic, but it doesn't work for all b


{- SIX -}

-- | We can even use our type parameters to keep track of the types inside an
-- 'HList'!  For example, this heterogeneous list contains no existentials:

data HList a where
  HNil  :: HList ()
  HCons :: head -> HList tail -> HList (head, tail)

exampleHList :: HList (String, (Int, (Bool, ())))
exampleHList = HCons "Tom" (HCons 25 (HCons True HNil))

-- | a. Write a 'head' function for this 'HList' type. This head function
-- should be /safe/: you can use the type signature to tell GHC that you won't
-- need to pattern-match on HNil, and therefore the return type shouldn't be
-- wrapped in a 'Maybe'!

hListHead :: HList (h, t) -> h
hListHead (HCons h _) = h

-- | b. Currently, the tuples are nested. Can you pattern-match on something of
-- type @HList (Int, String, Bool, ())@? Which constructor would work?

patternMatchMe :: HList (Int, String, Bool, ()) -> Int
patternMatchMe = undefined

-- No, we only have data constructors to make a `HList ()` or `HList (h, t)`

-- | c. Can you write a function that appends one 'HList' to the end of
-- another? What problems do you run into?

-- append2HList :: HList (h, t) -> HList (h', t') -> HList ()
-- append2HList (HCons h t) (HCons h' t') = HCons h

-- no way to merge the types of the HLists in the type signature
-- no way to to do the appending without knowing the length of each hlist ?

{- SEVEN -}

-- | Here are two data types that may help:

data Empty
data Branch left centre right

-- | a. Using these, and the outline for 'HList' above, build a heterogeneous
-- /tree/. None of the variables should be existential.

data HTree a where
  HLeaf :: HTree Empty
  HNode :: HTree l -> c -> HTree r -> HTree (Branch l c r)

-- | b. Implement a function that deletes the left subtree. The type should be
-- strong enough that GHC will do most of the work for you. Once you have it,
-- try breaking the implementation - does it type-check? If not, why not?

delLSubtree :: HTree (Branch l c r) -> HTree (Branch Empty c r)
delLSubtree (HNode _ c r) = HNode HLeaf c r

-- | c. Implement 'Eq' for 'HTree's. Note that you might have to write more
-- than one to cover all possible HTrees. You might also need an extension or
-- two, so look out for something... flexible... in the error messages!
-- Recursion is your friend here - you shouldn't need to add a constraint to
-- the GADT!

instance Eq (HTree Empty) where
  _ == _ = True

instance (Eq (HTree l), Eq c, Eq (HTree r)) => Eq (HTree (Branch l c r)) where
  (HNode l c r) == (HNode l' c' r') =    l == l'
                                      && c == c'
                                      && r == r'


tree1 :: HTree (Branch Empty Integer (Branch Empty Integer Empty))
tree1 = HNode HLeaf 5 (HNode HLeaf 6 HLeaf)

tree2 :: HTree (Branch Empty Integer (Branch Empty Integer Empty))
tree2 = HNode HLeaf 5 (HNode HLeaf 6 HLeaf)

test :: Bool
test = tree1 == tree2

{- EIGHT -}

-- | a. Implement the following GADT such that values of this type are lists of
-- values alternating between the two types. For example:
--
-- @
--   f :: AlternatingList Bool Int
--   f = ACons True (ACons 1 (ACons False (ACons 2 ANil)))
-- @

data AlternatingList a b where
  ANil :: AlternatingList a b
  ACons :: a -> AlternatingList b a -> AlternatingList a b

f :: AlternatingList Bool Int
f = ACons True (ACons 1 (ACons False (ACons 2 ANil)))

-- | b. Implement the following functions.

getFirsts :: AlternatingList a b -> [a]
getFirsts ANil = []
getFirsts (ACons a rest) = a : getSeconds rest

getSeconds :: AlternatingList a b -> [b]
getSeconds ANil = []
getSeconds (ACons _ rest) = getFirsts rest

-- | c. One more for luck: write this one using the above two functions, and
-- then write it such that it only does a single pass over the list.

foldValues :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues altList = (fold $ getFirsts altList, fold $ getSeconds altList)

foldValues' :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues' = processA (mempty, mempty)
  where
    processA :: (Monoid a, Monoid b) => (a, b) -> AlternatingList a b -> (a, b)
    processA final ANil = final
    processA (a, b) (ACons a' list) = processB (a <> a', b) list

    processB :: (Monoid a, Monoid b) => (a, b) -> AlternatingList b a -> (a, b)
    processB final ANil = final
    processB (a, b) (ACons b' list) = processA (a, b <> b') list

foldValues'' :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues''  ANil        = (mempty, mempty)
foldValues'' (ACons x xs) = let (b, a) = foldValues xs
                            in  (x <> a, b)

{- NINE -}

-- | Here's the "classic" example of a GADT, in which we build a simple
-- expression language. Note that we use the type parameter to make sure that
-- our expression is well-formed.

data Expr a where
  Equals    :: Expr Int  -> Expr Int            -> Expr Bool
  Add       :: Expr Int  -> Expr Int            -> Expr Int
  If        :: Expr Bool -> Expr a   -> Expr a  -> Expr a
  IntValue  :: Int                              -> Expr Int
  BoolValue :: Bool                             -> Expr Bool

-- | a. Implement the following function and marvel at the typechecker:

eval :: Expr a -> a
eval (Equals (IntValue i) (IntValue i')) = i == i'
eval (Add (IntValue i) (IntValue i')) = i + i'
eval (If boolExpr exprA exprB) = if eval boolExpr then eval exprA else eval exprB
eval (IntValue i) = i
eval (BoolValue b) = b

-- | b. Here's an "untyped" expression language. Implement a parser from this
-- into our well-typed language. Note that (until we cover higher-rank
-- polymorphism) we have to fix the return type. Why do you think this is?

data DirtyExpr
  = DirtyEquals    DirtyExpr DirtyExpr
  | DirtyAdd       DirtyExpr DirtyExpr
  | DirtyIf        DirtyExpr DirtyExpr DirtyExpr
  | DirtyIntValue  Int
  | DirtyBoolValue Bool

data Typed where
  IntType  :: Expr Int  -> Typed
  BoolType :: Expr Bool -> Typed

parse :: DirtyExpr -> Maybe Typed
parse (DirtyEquals (DirtyIntValue i) (DirtyIntValue i')) = Just $ BoolType $ Equals (IntValue i) (IntValue i')
parse (DirtyAdd (DirtyIntValue i) (DirtyIntValue i')) = Just $ IntType $ Add (IntValue i) (IntValue i')
parse (DirtyIf (DirtyBoolValue b) dirtyExprA dirtyExprB) = parse $ if b then dirtyExprA else dirtyExprB
parse (DirtyIntValue i) = Just $ IntType $ IntValue i
parse (DirtyBoolValue b) = Just $ BoolType $ BoolValue b
parse _ = Nothing

-- | c. Can we add functions to our 'Expr' language? If not, why not? What
-- other constructs would we need to add? Could we still avoid 'Maybe' in the
-- 'eval' function?

-- I don't think so, because there many combinations of `Expr a -> Expr a` that are not valid.
-- You could also treat Expr like a functor applying some `a -> b` function, but again the result
-- may not be a type `Expr` supports. I think you would need maybe. Although I'm slightly unsure of
-- what the signature of function support would look like

-- ok apparently this


data MoreExpr a where
-- ....
  Function :: (a -> MoreExpr b) -> MoreExpr (a -> b)
  Apply    :: MoreExpr (a -> b) -> MoreExpr a -> MoreExpr b


{- TEN -}

-- | Back in the glory days when I wrote JavaScript, I could make a composition
-- list like @pipe([f, g, h, i, j])@, and it would pass a value from the left
-- side of the list to the right. In Haskell, I can't do that, because the
-- functions all have to have the same type :(

-- | a. Fix that for me - write a list that allows me to hold any functions as
-- long as the input of one lines up with the output of the next.

data TypeAlignedList a b where
  TANil :: TypeAlignedList a b
  TACons :: (a -> b) -> TypeAlignedList b c -> TypeAlignedList a c


nested :: TypeAlignedList Int Bool
nested = TACons int2string (TACons string2bool TANil)

int2string :: Int -> String
int2string = undefined

string2bool :: String -> Bool
string2bool = undefined

-- | b. Which types are existential?

-- c?

-- | c. Write a function to append type-aligned lists. This is almost certainly
-- not as difficult as you'd initially think.

composeTALs :: TypeAlignedList b c -> TypeAlignedList a b -> TypeAlignedList a c
composeTALs xs  TANil        = xs
composeTALs xs (TACons y ys) = TACons y (composeTALs xs ys)
