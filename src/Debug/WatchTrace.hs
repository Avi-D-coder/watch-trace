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
import System.Mem.Weak
import Unsafe.Coerce
import Prelude

class WatchDot a where
  watchRecIO ::
    ( Has (State Watched) s m,
      Has (State Marked) s m,
      Has (Writer Thunks) s m,
      Has (Writer Elem) s m
    ) =>
    Maybe Parent ->
    a ->
    m Bool
  default watchRecIO ::
    ( G.Generic a,
      GWatchRec1 (G.Rep a),
      Has (State Watched) s m,
      Has (State Marked) s m,
      Has (Writer Thunks) s m,
      Has (Writer Elem) s m
    ) =>
    Maybe Parent ->
    a ->
    m Bool
  watchRecIO (Just (pId, el)) a = undefined
  watchRecIO Nothing a = undefined

class GWatchRec1 f where
  gWatchRecIO1 :: f p -> Parent -> DataTypeName -> Watched -> Marked -> Thunks -> NewNodes

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

newtype MkWeakPtrIOC m a = MkWeakPtrIOC {runMkWeakPtrIO :: m a}
  deriving (Applicative, Functor, Monad, MonadIO)

instance (MonadIO m, Algebra sig m) => Algebra (MkWeakPtr :+: sig) (MkWeakPtrIOC m) where
  alg hdl sig ctx = case sig of
    L (MkWeakPtr a f) -> (<$ ctx) <$> liftIO (mkWeakPtr a f)
    R other -> MkWeakPtrIOC (alg (runMkWeakPtrIO . hdl) other ctx)

--

watchVal = undefined
