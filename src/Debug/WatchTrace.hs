{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Debug.WatchTrace where

import Control.Algebra
import Control.Carrier.Lift
import Control.Carrier.Reader
import Control.Carrier.State.Strict
import Control.Concurrent.MVar
import Control.Effect.Writer
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Hashable
import Data.IORef
import Data.Int
import Data.Kind
import Data.Maybe
import qualified Data.Text as T
import Data.Word
import GHC.AssertNF
import GHC.Exts
import qualified GHC.Generics as G
import Numeric.Natural
import System.IO.Unsafe
import System.Mem.StableName
import qualified System.Mem.Weak as W
import System.Mem.Weak (Weak)
import Unsafe.Coerce
import Prelude

class WatchDot a where
  watchRecIO ::
    ( Has (State Watched) s m,
      Has (State Marked) s m,
      Has (Writer Thunks) s m,
      Has (Writer Elem) s m,
      Has (Writer Bool) s m
    ) =>
    Maybe Parent ->
    a ->
    m ()
  default watchRecIO ::
    ( G.Generic a,
      GWatchRec1 (G.Rep a),
      Has (State Watched) s m,
      Has (State Marked) s m,
      Has (Writer Thunks) s m,
      Has (Writer Elem) s m,
      Has (Writer Bool) s m
    ) =>
    Maybe Parent ->
    a ->
    m ()
  watchRecIO (Just (pId, el)) a = undefined
  watchRecIO Nothing a = undefined

instance (
    Has (State Watched) s m,
    Has (State Marked) s m,
    Has (Writer Thunks) s m,
    Has (Writer Elem) s m,
    Has (Writer Bool) s m
  ) =>
  WatchDot a
  where
  -- TODO use ghc-heap-view to show thunks and constructors
  watchRecIO (Just (pId, el)) a = undefined
  watchRecIO Nothing a = undefined

class GWatchRec1 f where
  gWatchRecIO1 :: f p -> Parent -> DataTypeName -> m ()

newtype StabName = StabName (StableName Any) deriving (Eq, G.Generic)

instance Show StabName where
  show = show . hash

instance Hashable StabName where
  hashWithSalt s (StabName a) = hashWithSalt s $ hashStableName a

type Watched = M.HashMap StabName (Bool, ElemId)

type Thunks = [AnyWatch]

type Marked = S.HashSet StabName

newtype DataTypeName = DataTypeName String
  deriving (Eq, Ord, Show, Semigroup, Monoid, IsString, G.Generic)

newtype EdgeLabel = EdgeLabel String
  deriving (Eq, Ord, Show, Semigroup, Monoid, IsString, G.Generic)

type Parent = (ElemId, EdgeLabel)

type NewNodes = IO ((Bool, Watched, Marked, Thunks, [Elem]), DataTypeName)

newtype ElemId = ElemId Int deriving (Eq, Ord, Show, G.Generic)

data Edge = Edge ElemId EdgeLabel ElemId
  deriving (Eq, Ord, Show, G.Generic)

data Elem
  = Vertex ElemId DataTypeName
  | E Edge
  deriving (Eq, Ord, Show, G.Generic)

data ElemQuery
  = Ver ElemId
  | Edg ElemId ElemId
  | Edgs ElemId
  deriving (Eq, Ord, Show, G.Generic)

data Update
  = New Elem
  | Change ElemId Elem
  | Delete ElemId
  deriving (Eq, Ord, Show, G.Generic)

data AnyWatch
  = AnyWatch
      { weak_val :: Weak Any,
        pre_name :: StabName,
        watchAny ::
          Maybe Parent ->
          Any ->
          Watched ->
          Marked ->
          Thunks ->
          IO (Bool, Watched, Marked, Thunks, [Elem])
      }
  deriving (G.Generic)

-- Effects
data MkStableName (m :: Type -> Type) k where
  MkStab :: Any -> MkStableName m StabName

mkStab :: Has MkStableName s m => Any -> m StabName
mkStab = send . MkStab

newtype MkStableNameIOC m a = MkStableNameIOC {runMkStableNameIO :: m a}
  deriving (Applicative, Functor, Monad, MonadIO)

instance (MonadIO m, Algebra sig m) => Algebra (MkStableName :+: sig) (MkStableNameIOC m) where
  alg hdl sig ctx = case sig of
    L (MkStab a) -> (<$ ctx) <$> liftIO (StabName <$> makeStableName a)
    R other -> MkStableNameIOC (alg (runMkStableNameIO . hdl) other ctx)

data MkWeakPtr (m :: Type -> Type) k where
  MkWeakPtr :: a -> Maybe (IO ()) -> MkWeakPtr m (Weak a)

mkWeakPtr :: Has MkWeakPtr s m => a -> Maybe (IO ()) -> m (Weak a)
mkWeakPtr a f = send (MkWeakPtr a f)

newtype MkWeakPtrIOC m a = MkWeakPtrIOC {runMkWeakPtrIO :: m a}
  deriving (Applicative, Functor, Monad, MonadIO)

instance (MonadIO m, Algebra sig m) => Algebra (MkWeakPtr :+: sig) (MkWeakPtrIOC m) where
  alg hdl sig ctx = case sig of
    L (MkWeakPtr a f) -> (<$ ctx) <$> liftIO (W.mkWeakPtr a f)
    R other -> MkWeakPtrIOC (alg (runMkWeakPtrIO . hdl) other ctx)

data IsHnf (m :: Type -> Type) k where
  IsHnf :: a -> IsHnf m Bool

newtype IsHnfIOC m a = IsHnfIOC {runIsHnfIO :: m a}
  deriving (Applicative, Functor, Monad, MonadIO)

isHnf :: Has IsHnf s m => a -> m Bool
isHnf = send . IsHnf

instance (MonadIO m, Algebra sig m) => Algebra (IsHnf :+: sig) (IsHnfIOC m) where
  alg hdl sig ctx = case sig of
    -- FIXME isNF is not checking for head normal form
    L (IsHnf a) -> (<$ ctx) <$> liftIO (isNF a)
    R other -> IsHnfIOC (alg (runIsHnfIO . hdl) other ctx)

data Counter (m :: Type -> Type) k where
  Add :: Int -> Counter m Int

add :: Has Counter s m => Int -> m Int
add = send . Add

inc :: Has Counter s m => m Int
inc = send $ Add 1

newtype CounterAtomicIORef m a = CounterAtomicIORef {runCounterAtomicIORef :: ReaderC (IORef Int) m a}
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance Has (Lift IO) sig m => Algebra (Counter :+: sig) (CounterAtomicIORef m) where
  alg hdl sig ctx = case sig of
    L (Add n) ->
      (<$ ctx)
        <$> ( CounterAtomicIORef ask >>= sendM
                . ( \ref ->
                      atomicModifyIORef' ref (\i -> let i' = i + n in (i', i'))
                  )
            )
    R other -> CounterAtomicIORef (alg (runCounterAtomicIORef . hdl) (R other) ctx)

newtype CounterState m a = CounterState {runCounterState :: ReaderC (IORef Int) m a}
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance Has (State Int) sig m => Algebra (Counter :+: sig) (CounterState m) where
  alg hdl sig ctx = case sig of
    L (Add n) -> (<$ ctx) <$> ((n+) <$> get >>= (\p -> put p >> pure p))
    R other -> CounterState (alg (runCounterState . hdl) (R other) ctx)

watchVal ::
  ( WatchDot a,
    GWatchRec1 (G.Rep a),
    Has (State Watched) s m,
    Has (State Marked) s m,
    Has (Writer Thunks) s m,
    Has (Writer Elem) s m,
    Has (Writer Bool) s m,
    Has MkStableName s m
  ) =>
  a ->
  Bool ->
  m ()
watchVal a is_pure_hnf = do
  let a' :: Any = unsafeCoerce a
  name <- mkStab a'
  undefined

watchRecIOPrim :: (WatchDot a, Show a, Has IsHnf s m) => Maybe Parent -> String -> a -> m ()
watchRecIOPrim p l a = do
  nf <- isHnf a
  undefined
