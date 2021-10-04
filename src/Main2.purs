module Main where

import Prelude

import Control.Monad.Reader (Reader)
import Control.Monad.State (State, get, gets, modify, modify_)
import Control.Monad.Writer (Writer)
import Data.Const (Const(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Effect (Effect)
import Effect.Class.Console as Log
import Effect.Console (log)
import Prim.Row (class Cons, class Lacks, class Union)
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Record as Record
import Safe.Coerce (coerce)
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

newtype Foo a
  = Foo a

a = FixedPoint (Just (FixedPoint (Just (FixedPoint Nothing)))) :: FixedPoint Maybe

a' = FixedPoint (Just (FixedPoint (Just (FixedPoint (Just (FixedPoint (Just (FixedPoint (Just (FixedPoint Nothing)))))))))) :: FixedPoint Maybe

b = Just (Just Nothing) :: Maybe (Maybe (Maybe Int))

b' = Just (Nothing) :: Maybe (Maybe (Maybe Int))

c = Just (Nothing) :: Maybe ((Maybe Int))

d = Nothing :: Maybe Int

newtype FixedPoint f
  = FixedPoint (f (FixedPoint f))

-------------------------
-- monoid ::
--    append :: a -> a -> a     operation  :: Group
--    mempty :: a               identity
-- monad ::
--    join :: m (m a) -> m a    operation
--    pure :: a -> m a          identity
-------------------------
-----------
data FreeMonoid a
  = Continue' a (FreeMonoid a)
  | PlainOldValue' a

derive instance genericMF :: Generic (MikeFree f a) _

instance showMikeFree :: (Show a, Show (f (MikeFree f a))) => Show (MikeFree f a) where
  show = genericShow

data MikeFree f a
  = Continue (f (MikeFree f a))
  | PlainOldValue a

derive instance functorMikeFree :: Functor f => Functor (MikeFree f)

-- use the bind and applicative instance to express apply
instance applyMikeFree :: Functor f => Apply (MikeFree f) where
  apply = ap

instance applicativeMikeFree :: Functor f => Applicative (MikeFree f) where
  pure = PlainOldValue

instance bindMikeFree :: Functor f => Bind (MikeFree f) where
  --   functor
  --   (a -> b)                            m a             ||||  m b
  --   bind
  --   m a  (monad at time t)              (a -> m b)      ||||  m b   (monad at time t + 1)
  bind (PlainOldValue v) fOfa = fOfa v
  ---   f (MikeFree f a)  --- f (MikeFree f (MikeFree f a))
  bind (Continue v) fOfa = Continue $ map join $ (map <<< map) fOfa v

-- monad ::
--    m (m a) -> m a
--    a -> m a            Applicative
instance monadMikeFree :: Functor f => Monad (MikeFree f)

-- eventually we hit monad
-- MikeFree will be a moand, then we can use do, then we have a free monad
data GoShopping a
  = GetSpecial (String -> a)
  | Buy String a
  | Exclaim String a

derive instance functorGoShopping :: Functor GoShopping

-- GoShopping' has monad for free
type GoShopping'
  = MikeFree GoShopping

-- MyMaybe has monad for free
type MyMaybe
  = Maybe

liftF :: forall f. Functor f => f ~> MikeFree f
liftF f = Continue (map PlainOldValue f)

foldFree :: forall m f. Monad m => Functor f => (f ~> m) -> MikeFree f ~> m
foldFree _ (PlainOldValue pov) = pure pov

-------------------------------- con :: f (MikeFree f a)  -> m (MikeFree f a)  -> m (m a) -> m a
foldFree functorToMonad (Continue con) = join (map (foldFree functorToMonad) (functorToMonad con))

resume' :: forall f a r. (forall b. f b -> (b -> MikeFree f a) -> r) -> (a -> r) -> MikeFree f a -> r
resume' _ tameBeast (PlainOldValue pov) = tameBeast pov
------------------------------------------ b = MikeFree f a    f (MikeFree f a)   (MikeFree f a -> MikeFree f a)
resume' giantBeast _ (Continue con) = giantBeast con identity

type MyRow = (foo :: Int, bar :: Number, baz :: Boolean)

data VariantFRep f a = VariantFRep { key :: String, value :: f a, map :: forall x y. (x -> y) -> f x -> f y }


newtype NT f a b c = NT Int -- RHS must be a type

unVariantRep (VariantFRep z) = z

newtype VariantF (r :: Row (Type -> Type)) a = VariantF Void -- void indicates this can be nothing 

inj :: forall sym funk r' r a. IsSymbol sym => Functor funk => Cons sym funk r' r => Lacks sym r' => Proxy sym -> funk a -> VariantF r a
inj px value = VariantF (naughty x)
  where
  x :: VariantFRep funk a
  x = VariantFRep { key: reflectSymbol px, value, map }
  naughty :: VariantFRep funk a -> Void
  naughty = unsafeCoerce

{-
prj px (VariantF v) = let VariantFRep x = x' in if x.key == reflectSymbol px then Just x.value else Nothing
  where
  x' :: VariantFRep funk a
  x' = naughty v
  naughty :: Void -> VariantFRep funk a
  naughty = unsafeCoerce
-}
instance functorVariantF :: Functor (VariantF r) where
  map f (VariantF hack) = VariantF foo
    where
    bar :: forall f q. VariantFRep f q
    bar = unsafeCoerce hack
    foo :: Void
    foo = unsafeCoerce (VariantFRep ({ value: (unVariantRep bar).map f (unVariantRep bar).value, map: (unVariantRep bar).map, key: (unVariantRep bar).key }))

effectful :: Effect Unit
effectful =
  foldFree
    ( case _ of
        GetSpecial f -> f <$> pure "booze"
        Buy _ u -> pure u
        Exclaim thing u -> Log.info thing *> pure u
    )
    myLittleProgram

getSpecial :: MikeFree GoShopping String
getSpecial = liftF (GetSpecial identity)

buy :: String -> MikeFree GoShopping Unit
buy thing = liftF (Buy thing unit)

exclaim :: String -> MikeFree GoShopping Unit
exclaim exclamation = liftF (Exclaim exclamation unit)

-- do
--   special <- getSpecial
--   buy special
--   exclaim "wow!"
myProg :: MikeFree GoShopping Unit
myProg =
  Continue
    ( GetSpecial
        ( \special ->
            (Continue (Buy special (Continue (Exclaim "wow!" (PlainOldValue unit)))))
        )
    )

myLittleProgram :: MikeFree GoShopping Unit
myLittleProgram = do
  special <- getSpecial
  buy special
  exclaim "wow"
  exclaim "yay!!!"

myProg2 :: MikeFree GoShopping Unit
myProg2 =
  Continue
    ( GetSpecial
        ( \special ->
            ( Continue (Buy special (Continue (Exclaim "wow!" (Continue (Exclaim "yay!!!" (PlainOldValue unit))))))
            )
        )
    )

myProg' :: GoShopping (GoShopping (GoShopping Unit))
myProg' =
  ( GetSpecial
      ( \special ->
          (Buy special (Exclaim "wow!" unit))
      )
  )

myProg'' :: GoShopping (GoShopping (GoShopping (GoShopping Unit)))
myProg'' =
  ( GetSpecial
      ( \special ->
          (Buy special (Exclaim "wow!" (Exclaim "yay!!!" unit)))
      )
  )

foo :: VariantF (foo :: Array, bar :: Maybe) Int
foo = inj (Proxy :: _ "foo") [1]

bar :: VariantF (foo :: Array, bar :: Maybe) Int
bar = inj (Proxy :: _ "bar") (Just 1)

main :: Effect Unit
main = do
  effectful
  Log.info $ show $ prj (Proxy :: _ "bar") (map (add 1) bar)


prj :: forall sym funk r' r a. IsSymbol sym 
  => Functor funk 
  => Cons sym funk r' r -- r ' is smaller 
  => Lacks sym r' 
  => Proxy sym 
  -> VariantF r a 
  -> Maybe (funk a)
prj px = on px Just (const Nothing) 



extend :: ∀ r1 r2 r3. Union r1 r2 r3 => VariantF r1 ~> VariantF r3
extend = unsafeCoerce 

on :: forall sym funk r' r a b. IsSymbol sym => Functor funk => Cons sym funk r' r => Lacks sym r' => 
  Proxy sym 
  -> (funk a -> b)
  -> (VariantF r' a -> b)
  -> VariantF r a 
  -> b

on px trans smaller (VariantF v) = let VariantFRep x = x' in if x.key == reflectSymbol px then (trans x.value) 
  else smaller (VariantF v) 
  where
  x' :: VariantFRep funk a
  x' = naughty v
  naughty :: Void -> VariantFRep funk a
  naughty = unsafeCoerce

