{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

#if __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE DeriveGeneric #-}
#endif

#if __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif

#if __GLASGOW_HASKELL__ >= 706
{-# LANGUAGE PolyKinds #-}
#endif

#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE TypeFamilies #-}
#endif

module Data.Tree.Forest
    ( Tree (Leaf, Node)
    , Forest (Forest)

    -- * Optics
    , _Leaf
    , _Node
    , _Forest

    -- * Higher order traversals
    -- ** Trees
    , hmap
    , hfoldr
    , htraverse
    -- ** Forests
    , hmap'
    , hfoldr'
    , htraverse'
    )
where

-- aeson ---------------------------------------------------------------------
import           Data.Aeson
                     ( FromJSON
                     , ToJSON
                     , Value (Object)
                     , (.=)
                     , (.:)
                     , object
                     , parseJSON
                     , toJSON
                     )
#if MIN_VERSION_aeson(1, 0, 0)
import           Data.Aeson.Types (FromJSONKey, ToJSONKey)
#endif


-- base ----------------------------------------------------------------------
#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative (Applicative, pure, (<$>), (<*>))
#endif
import           Control.Applicative (Alternative, (<|>), empty)
import           Control.Monad
                     ( MonadPlus
                     , mzero
                     , mplus
                     , msum
                     )
#if __GLASGOW_HASKELL__ >= 800
import           Control.Monad.Fail (MonadFail)
import qualified Control.Monad.Fail as F (fail)
#endif
import           Data.Bifoldable (Bifoldable, bifoldr)
import           Data.Bifunctor (Bifunctor, bimap)
import           Data.Bitraversable (Bitraversable, bitraverse)
#if __GLASGOW_HASKELL__ < 710
import           Data.Foldable (Foldable, foldr)
#endif
import           Data.Functor.Classes
                     ( Eq1
                     , Ord1
                     , Read1
                     , Show1
                     , Eq2
                     , Ord2
                     , Read2
                     , Show2
                     , liftCompare
                     , liftCompare2
                     , liftEq
                     , liftEq2
                     , liftReadList2
                     , liftReadsPrec
                     , liftReadsPrec2
                     , liftShowList2
                     , liftShowsPrec
                     , liftShowsPrec2
                     , readsData
                     , readsUnaryWith
                     , showsUnaryWith
                     )
#if __GLASGOW_HASKELL__ < 710
import           Data.Monoid (Monoid, mappend, mconcat, mempty)
#endif
import           Data.Semigroup (Semigroup, (<>))
#if __GLASGOW_HASKELL__ < 710
import           Data.Traversable
                     ( Traversable
                     , traverse
                     )
#endif
#if __GLASGOW_HASKELL__ >= 708
import           Data.Typeable (Typeable)
#endif
#if __GLASGOW_HASKELL__ >= 708
import           GHC.Exts (IsList, Item, fromList, toList)
#endif
#if __GLASGOW_HASKELL__ >= 702
import           GHC.Generics
                     ( Generic
#if __GLASGOW_HASKELL__ >= 706
                     , Generic1
#endif
                     )
#endif
#if __GLASGOW_HASKELL__ < 710
import           Prelude hiding (foldr)
#endif


-- deepseq -------------------------------------------------------------------
import           Control.DeepSeq (NFData, rnf)


-- hashable ------------------------------------------------------------------
import           Data.Hashable (Hashable, hashWithSalt)


-- profunctors ---------------------------------------------------------------
import           Data.Profunctor (Choice, Profunctor, dimap, right')


-- semigroupoids -------------------------------------------------------------
import           Data.Functor.Alt (Alt, (<!>))
import           Data.Functor.Apply (Apply, (<.>))
import           Data.Functor.Bind (Bind, (>>-), join)
import           Data.Functor.Plus (Plus, zero)


------------------------------------------------------------------------------
data Tree f s a = Leaf !a | Node !s (Forest f s a)
  deriving
    (
#if __GLASGOW_HASKELL__ >= 702
      Generic
#if __GLASGOW_HASKELL__ >= 706
    , Generic1
#endif
#endif
#if __GLASGOW_HASKELL__ >= 708
    , Typeable
#endif
    )
deriving instance (Eq a, Eq s, Eq (Forest f s a)) => Eq (Tree f s a)
deriving instance (Ord a, Ord s, Ord (Forest f s a), Ord (f (Tree f s a))) =>
    Ord (Tree f s a)
deriving instance (Read a, Read s, Read (Forest f s a)) => Read (Tree f s a)
deriving instance (Show a, Show s, Show (Forest f s a)) => Show (Tree f s a)


------------------------------------------------------------------------------
_Leaf :: (Choice p, Applicative f)
    => p a (f a)
    -> p (Tree g s a) (f (Tree g s a))
_Leaf = dimap from (either pure (fmap to)) . right'
  where
    from (Leaf a) = Right a
    from t = Left t
    to = Leaf
{-# INLINE _Leaf #-}


------------------------------------------------------------------------------
_Node :: (Choice p, Applicative f)
    => p (s, Forest g s a) (f (s, Forest g s a))
    -> p (Tree g s a) (f (Tree g s a))
_Node = dimap from (either pure (fmap to)) . right'
  where
    from (Node s ts) = Right (s, ts)
    from t = Left t
    to = uncurry Node
{-# INLINE _Node #-}


------------------------------------------------------------------------------
instance (NFData s, NFData a, NFData (f (Tree f s a))) =>
    NFData (Tree f s a)
  where
    rnf (Leaf a) = rnf a
    rnf (Node s ts) = rnf s `seq` rnf ts
    {-# INLINE rnf #-}


------------------------------------------------------------------------------
instance (Hashable s, Hashable a, Hashable (f (Tree f s a))) =>
    Hashable (Tree f s a)
  where
    hashWithSalt s (Leaf a) = hashWithSalt s a
    hashWithSalt s (Node s' ts) = hashWithSalt (hashWithSalt s s') ts
    {-# INLINE hashWithSalt #-}


------------------------------------------------------------------------------
instance Functor f => Bifunctor (Tree f) where
    bimap _ g (Leaf a) = Leaf (g a)
    bimap f g (Node s ts) = Node (f s) (bimap f g ts)
    {-# INLINE bimap #-}


------------------------------------------------------------------------------
instance Foldable f => Bifoldable (Tree f) where
    bifoldr _ g b (Leaf a) = g a b
    bifoldr f g b (Node s ts) = f s $ bifoldr f g b ts
    {-# INLINE bifoldr #-}


------------------------------------------------------------------------------
instance Traversable f => Bitraversable (Tree f) where
    bitraverse _ g (Leaf a) = Leaf <$> g a
    bitraverse f g (Node s ts) = Node <$> f s <*> bitraverse f g ts
    {-# INLINE bitraverse #-}


------------------------------------------------------------------------------
instance Functor f => Functor (Tree f s) where
    fmap f (Leaf a) = Leaf (f a)
    fmap f (Node s ts) = Node s (fmap f ts)
    {-# INLINE fmap #-}


------------------------------------------------------------------------------
instance Foldable f => Foldable (Tree f s) where
    foldr f b (Leaf a) = f a b
    foldr f b (Node _ ts) = foldr f b ts
    {-# INLINE foldr #-}


------------------------------------------------------------------------------
instance Traversable f => Traversable (Tree f s) where
    traverse f (Leaf a) = Leaf <$> f a
    traverse f (Node s ts) = Node s <$> traverse f ts
    {-# INLINE traverse #-}


------------------------------------------------------------------------------
instance Functor f => Apply (Tree f s) where
    Leaf f <.> Leaf a = Leaf (f a)
    Leaf f <.> Node s ts = Node s (fmap f ts)
    Node s (Forest ts) <.> f = Node s $ Forest $ fmap (<.> f) ts
    {-# INLINE (<.>) #-}


------------------------------------------------------------------------------
instance Functor f => Bind (Tree f s) where
    Leaf a >>- f = f a
    Node s (Forest ts) >>- f = Node s $ Forest $ fmap (>>- f) ts
    {-# INLINE (>>-) #-}


------------------------------------------------------------------------------
instance Functor f => Applicative (Tree f s) where
    pure = Leaf
    {-# INLINE pure #-}
    (<*>) = (<.>)
    {-# INLINE (<*>) #-}


------------------------------------------------------------------------------
instance Functor f => Monad (Tree f s) where
    return = pure
    {-# INLINE return #-}
    (>>=) = (>>-)
    {-# INLINE (>>=) #-}


------------------------------------------------------------------------------
instance (FromJSON s, FromJSON a, FromJSON (f (Tree f s a))) =>
    FromJSON (Tree f s a)
  where
    parseJSON (Object o) = msum
        [ Node <$> o .: "value" <*> o .: "children"
        , Leaf <$> o .: "value"
        ]
    parseJSON _ = empty
    {-# INLINE parseJSON #-}


------------------------------------------------------------------------------
instance (ToJSON s, ToJSON a, ToJSON (f (Tree f s a))) =>
    ToJSON (Tree f s a)
  where
    toJSON (Leaf a) = object
        [ "value" .= toJSON a
        ]
    toJSON (Node s ts) = object
        [ "value" .= toJSON s
        , "children" .= toJSON ts
        ]
    {-# INLINE toJSON #-}


#if MIN_VERSION_aeson(1, 0, 0)
------------------------------------------------------------------------------
instance FromJSON (Tree f s a) => FromJSONKey (Tree f s a)


------------------------------------------------------------------------------
instance ToJSON (Tree f s a) => ToJSONKey (Tree f s a)


#endif
------------------------------------------------------------------------------
instance Eq1 f => Eq2 (Tree f) where
    liftEq2 _ eqa (Leaf a) (Leaf b) = eqa a b
    liftEq2 eqs eqa (Node s ts) (Node t tt) = and
        [ eqs s t
        , liftEq2 eqs eqa ts tt
        ]
    liftEq2 _ _ _ _ = False
    {-# INLINE liftEq2 #-}


------------------------------------------------------------------------------
instance Ord1 f => Ord2 (Tree f) where
    liftCompare2 _ cmpa (Leaf a) (Leaf b) = cmpa a b
    liftCompare2 cmps cmpa (Node s ts) (Node t tt) = mconcat
        [ cmps s t
        , liftCompare2 cmps cmpa ts tt
        ]
    liftCompare2 _ _ _ _ = mempty
    {-# INLINE liftCompare2 #-}


------------------------------------------------------------------------------
instance Read1 f => Read2 (Tree f) where
    liftReadsPrec2 rds rdss rda rdas p = readParen (p > 10) $ \s -> msum
        [ do
            ("Leaf", s') <- lex s
            (a, s'') <- rda 11 s'
            pure (Leaf a, s'')
        , do
            ("Node", s') <- lex s
            (a, s'') <- rds 11 s'
            (ts, s''') <- liftReadsPrec2 rds rdss rda rdas 11 s''
            pure (Node a ts, s''')
        ]
    {-# INLINE liftReadsPrec2 #-}


------------------------------------------------------------------------------
instance Show1 f => Show2 (Tree f) where
    liftShowsPrec2 _ _ shwa _ p (Leaf a) = showParen (p > 10) $
        showString "Leaf " . shwa 11 a
    liftShowsPrec2 shws shwss shwa shwas p (Node s ts) = showParen (p > 10)
        $ foldr (.) id
            [ showString "Node "
            , shws 11 s
            , showString " "
            , liftShowsPrec2 shws shwss shwa shwas 11 ts
            ]
    {-# INLINE liftShowsPrec2 #-}


------------------------------------------------------------------------------
instance (Eq1 f, Eq s) => Eq1 (Tree f s) where
    liftEq = liftEq2 (==)
    {-# INLINE liftEq #-}


------------------------------------------------------------------------------
instance (Ord1 f, Ord s) => Ord1 (Tree f s) where
    liftCompare = liftCompare2 compare
    {-# INLINE liftCompare #-}


------------------------------------------------------------------------------
instance (Read1 f, Read s) => Read1 (Tree f s) where
    liftReadsPrec = liftReadsPrec2 readsPrec readList
    {-# INLINE liftReadsPrec #-}


------------------------------------------------------------------------------
instance (Show1 f, Show s) => Show1 (Tree f s) where
    liftShowsPrec = liftShowsPrec2 showsPrec showList
    {-# INLINE liftShowsPrec #-}


------------------------------------------------------------------------------
newtype Forest f s a = Forest (f (Tree f s a))
  deriving
    (
#if __GLASGOW_HASKELL__ >= 702
      Generic
#if __GLASGOW_HASKELL__ >= 706
    , Generic1
#endif
#endif
#if __GLASGOW_HASKELL__ >= 708
    , Typeable
#endif
    )
deriving instance Eq (f (Tree f s a)) => Eq (Forest f s a)
deriving instance Ord (f (Tree f s a)) => Ord (Forest f s a)
deriving instance Read (f (Tree f s a)) => Read (Forest f s a)
deriving instance Show (f (Tree f s a)) => Show (Forest f s a)


------------------------------------------------------------------------------
_Forest :: (Profunctor p, Functor f)
    => p (g (Tree g s a)) (f (g (Tree g s a)))
    -> p (Forest g s a) (f (Forest g s a))
_Forest = dimap from (fmap to)
  where
    from (Forest a) = a
    to = Forest
{-# INLINE _Forest #-}


------------------------------------------------------------------------------
instance (NFData a, NFData s, NFData (f (Tree f s a))) =>
    NFData (Forest f s a)
  where
    rnf (Forest ts) = rnf ts
    {-# INLINE rnf #-}


------------------------------------------------------------------------------
instance (Hashable a, Hashable s, Hashable (f (Tree f s a))) =>
    Hashable (Forest f s a)
  where
    hashWithSalt s (Forest ts) = hashWithSalt s ts
    {-# INLINE hashWithSalt #-}


#if __GLASGOW_HASKELL__ >= 708
------------------------------------------------------------------------------
instance IsList (f (Tree f s a)) => IsList (Forest f s a) where
    type Item (Forest f s a) = Item (f (Tree f s a))
    toList (Forest ts) = toList ts
    {-# INLINE toList #-}
    fromList = Forest . fromList
    {-# INLINE fromList #-}


#endif
------------------------------------------------------------------------------
instance Functor f => Bifunctor (Forest f) where
    bimap f g (Forest ts) = Forest (fmap (bimap f g) ts)
    {-# INLINE bimap #-}


------------------------------------------------------------------------------
instance Foldable f => Bifoldable (Forest f) where
    bifoldr f g b (Forest ts) = foldr (flip (bifoldr f g)) b ts
    {-# INLINE bifoldr #-}


------------------------------------------------------------------------------
instance Traversable f => Bitraversable (Forest f) where
    bitraverse f g (Forest ts) = Forest <$> traverse (bitraverse f g) ts
    {-# INLINE bitraverse #-}


------------------------------------------------------------------------------
instance Functor f => Functor (Forest f s) where
    fmap f (Forest ts) = Forest (fmap (fmap f) ts)
    {-# INLINE fmap #-}


------------------------------------------------------------------------------
instance Foldable f => Foldable (Forest f s) where
    foldr f b (Forest ts) = foldr (flip (foldr f)) b ts
    {-# INLINE foldr #-}


------------------------------------------------------------------------------
instance Traversable f => Traversable (Forest f s) where
    traverse f (Forest ts) = Forest <$> traverse (traverse f) ts
    {-# INLINE traverse #-}


------------------------------------------------------------------------------
instance Apply f => Apply (Forest f s) where
    Forest fs <.> Forest as = Forest $ (<.>) <$> fs <.> as
    {-# INLINE (<.>) #-}


------------------------------------------------------------------------------
instance Alt f => Alt (Forest f s) where
    Forest as <!> Forest bs = Forest $ as <!> bs
    {-# INLINE (<!>) #-}


------------------------------------------------------------------------------
instance Plus f => Plus (Forest f s) where
    zero = Forest zero
    {-# INLINE zero #-}


------------------------------------------------------------------------------
instance (Applicative f, Bind f, Traversable f) => Bind (Forest f s) where
    Forest ts >>- f = Forest $ ts >>- fmap join . traverse (runForest . f)
      where
        runForest (Forest tt) = tt
    {-# INLINE (>>-) #-}


------------------------------------------------------------------------------
instance Applicative f => Applicative (Forest f s) where
    pure = Forest . pure . pure
    {-# INLINE pure #-}
    Forest fs <*> Forest as = Forest $ (<*>) <$> fs <*> as
    {-# INLINE (<*>) #-}


------------------------------------------------------------------------------
instance Alternative f => Alternative (Forest f s) where
    empty = Forest empty
    {-# INLINE empty #-}
    Forest as <|> Forest bs = Forest $ as <|> bs
    {-# INLINE (<|>) #-}


------------------------------------------------------------------------------
instance (Applicative f, Monad f, Traversable f) => Monad (Forest f s) where
    return = pure
    {-# INLINE return #-}
    Forest ts >>= f = Forest $ ts >>= fmap join . traverse (runForest . f)
      where
        runForest (Forest tt) = tt
    {-# INLINE (>>=) #-}
    fail = Forest . fail
    {-# INLINE fail #-}


#if __GLASGOW_HASKELL__ >= 800
------------------------------------------------------------------------------
instance (MonadFail f, Traversable f) => MonadFail (Forest f s) where
    fail = Forest . F.fail
    {-# INLINE fail #-}


#endif
------------------------------------------------------------------------------
instance (Alternative f, Monad f, Traversable f) => MonadPlus (Forest f s)
  where
    mzero = empty
    {-# INLINE mzero #-}
    mplus = (<|>)
    {-# INLINE mplus #-}


------------------------------------------------------------------------------
instance Alt f => Semigroup (Forest f s a) where
    (<>) = (<!>)
    {-# INLINE (<>) #-}


------------------------------------------------------------------------------
instance Alternative f => Monoid (Forest f s a) where
    mempty = empty
    {-# INLINE mempty #-}
    mappend = (<|>)
    {-# INLINE mappend #-}


------------------------------------------------------------------------------
instance (FromJSON s, FromJSON a, FromJSON (f (Tree f s a))) =>
    FromJSON (Forest f s a)
  where
    parseJSON = fmap Forest . parseJSON
    {-# INLINE parseJSON #-}


------------------------------------------------------------------------------
instance (ToJSON s, ToJSON a, ToJSON (f (Tree f s a))) =>
    ToJSON (Forest f s a)
  where
    toJSON (Forest ts) = toJSON ts
    {-# INLINE toJSON #-}


#if MIN_VERSION_aeson(1, 0, 0)
------------------------------------------------------------------------------
instance FromJSON (Forest f s a) => FromJSONKey (Forest f s a)


------------------------------------------------------------------------------
instance ToJSON (Forest f s a) => ToJSONKey (Forest f s a)


#endif
------------------------------------------------------------------------------
instance Eq1 f => Eq2 (Forest f) where
    liftEq2 eqs eqa (Forest ts) (Forest tt) = liftEq (liftEq2 eqs eqa) ts tt
    {-# INLINE liftEq2 #-}


------------------------------------------------------------------------------
instance Ord1 f => Ord2 (Forest f) where
    liftCompare2 cmps cmpa (Forest ts) (Forest tt) =
        liftCompare (liftCompare2 cmps cmpa) ts tt
    {-# INLINE liftCompare2 #-}


------------------------------------------------------------------------------
instance Read1 f => Read2 (Forest f) where
    liftReadsPrec2 rds rdss rda rdas = readsData $
        readsUnaryWith
            (liftReadsPrec
                (liftReadsPrec2 rds rdss rda rdas)
                (liftReadList2 rds rdss rda rdas))
            "Forest"
            Forest
    {-# INLINE liftReadsPrec2 #-}


------------------------------------------------------------------------------
instance Show1 f => Show2 (Forest f) where
    liftShowsPrec2 shws shwss shwa shwas p (Forest fs) =
        showsUnaryWith
            (liftShowsPrec
                (liftShowsPrec2 shws shwss shwa shwas)
                (liftShowList2 shws shwss shwa shwas))
            "Forest"
            p
            fs
    {-# INLINE liftShowsPrec2 #-}


------------------------------------------------------------------------------
instance (Eq1 f, Eq s) => Eq1 (Forest f s) where
    liftEq = liftEq2 (==)
    {-# INLINE liftEq #-}


------------------------------------------------------------------------------
instance (Ord1 f, Ord s) => Ord1 (Forest f s) where
    liftCompare = liftCompare2 compare
    {-# INLINE liftCompare #-}


------------------------------------------------------------------------------
instance (Read1 f, Read s) => Read1 (Forest f s) where
    liftReadsPrec = liftReadsPrec2 readsPrec readList
    {-# INLINE liftReadsPrec #-}


------------------------------------------------------------------------------
instance (Show1 f, Show s) => Show1 (Forest f s) where
    liftShowsPrec = liftShowsPrec2 showsPrec showList
    {-# INLINE liftShowsPrec #-}


------------------------------------------------------------------------------
hmap :: Functor f => (forall x. f x -> g x) -> Tree f s a -> Tree g s a
hmap _ (Leaf a) = Leaf a
hmap f (Node s ts) = Node s (hmap' f ts)


------------------------------------------------------------------------------
hfoldr :: Foldable f => (forall x. f x -> b -> b) -> b -> Tree f s a -> b
hfoldr _ b (Leaf _) = b
hfoldr f b (Node _ ts) = hfoldr' f b ts


------------------------------------------------------------------------------
htraverse :: (Traversable f, Applicative h, Monad h)
    => (forall x. f x -> h (g x)) -> Tree f s a -> h (Tree g s a)
htraverse _ (Leaf a) = pure (Leaf a)
htraverse f (Node s ts) = Node s <$> htraverse' f ts


------------------------------------------------------------------------------
hmap' :: Functor f => (forall x. f x -> g x) -> Forest f s a -> Forest g s a
hmap' f (Forest fs) = Forest (f (fmap (hmap f) fs))


------------------------------------------------------------------------------
hfoldr' :: Foldable f => (forall x. f x -> b -> b) -> b -> Forest f s a -> b
hfoldr' f b (Forest fs) = f fs (foldr (flip (hfoldr f)) b fs)


------------------------------------------------------------------------------
htraverse' :: (Traversable f, Applicative h, Monad h)
    => (forall x. f x -> h (g x)) -> Forest f s a -> h (Forest g s a)
htraverse' f (Forest fs) = fmap Forest $ traverse (htraverse f) fs >>= f
