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
import Control.Carrier.Writer.Strict
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

class WatchTrace a where
  watchRec ::
    ( Has (State Watched) s m,
      Has (State Marked) s m,
      Has (Writer [AnyWatch]) s m,
      Has (Writer [Elem]) s m,
      Has MkStableName s m,
      Has MkWeakPtr s m,
      Has IsHnf s m,
      Has Counter s m
    ) =>
    Maybe Parent ->
    a ->
    m ()
  default watchRec ::
    ( G.Generic a,
      GWatchRec1 (G.Rep a),
      Has (State Watched) s m,
      Has (State Marked) s m,
      Has (Writer [AnyWatch]) s m,
      Has (Writer [Elem]) s m,
      Has MkStableName s m,
      Has MkWeakPtr s m,
      Has IsHnf s m,
      Has Counter s m
    ) =>
    Maybe Parent ->
    a ->
    m ()
  watchRec mp a = watchVal a True >>= \case
    Left eId -> do
      -- TODO datatypeName
      let dataType = ""
      tell @[Elem] [Vertex eId dataType]
      tellEdge eId
      -- FIXME why am I passing DataTypeName?
      gWatchRec1 (G.from a) (eId, "") dataType
    Right eId -> tellEdge eId
    where
      tellEdge :: Has (Writer [Elem]) s m => ElemId -> m ()
      tellEdge eId = case mp of
        (Just (pId, el)) -> tell [E $ Edge pId el eId]
        _ -> pure ()

instance
  ( Has (State Watched) s m,
    Has (State Marked) s m,
    Has (Writer [AnyWatch]) s m,
    Has (Writer [Elem]) s m,
    Has IsHnf s m
  ) =>
  WatchTrace a
  where
  -- TODO use ghc-heap-view to show thunks and constructors
  watchRec mp a = undefined

class GWatchRec1 f where
  gWatchRec1 ::
    ( Has (State Watched) s m,
      Has (State Marked) s m,
      Has (Writer [AnyWatch]) s m,
      Has (Writer [Elem]) s m,
      Has MkStableName s m,
      Has MkWeakPtr s m,
      Has IsHnf s m,
      Has Counter s m
    ) =>
    f p ->
    Parent ->
    DataTypeName ->
    m ()

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

type ElemId = Int

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
          Int ->
          Watched ->
          Marked ->
          Maybe Parent ->
          Any ->
          IO ([Elem], ([AnyWatch], (Int, (Watched, (Marked, ())))))
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

newtype CounterStateC m a = CounterStateC {runCounterStateC :: StateC Int m a}
  deriving (Applicative, Functor, Monad, MonadFail, MonadIO)

instance Algebra sig m => Algebra (Counter :+: sig) (CounterStateC m) where
  alg hdl sig ctx = case sig of
    L (Add n) -> CounterStateC (modify (n +)) >> CounterStateC (gets (<$ ctx))
    R other -> CounterStateC (alg (runCounterStateC . hdl) (R other) ctx)

runCounterState :: Int -> CounterStateC m a -> m (Int, a)
runCounterState i = runState i . runCounterStateC
{-# INLINE runCounterState #-}

-- Returns Left when the value is new, Right when value is cached and pure.
watchVal ::
  forall a s m.
  ( WatchTrace a,
    Has (State Watched) s m,
    Has (State Marked) s m,
    Has (Writer [AnyWatch]) s m,
    Has MkStableName s m,
    Has MkWeakPtr s m,
    Has IsHnf s m,
    Has Counter s m
  ) =>
  a ->
  Bool ->
  m (Either ElemId ElemId)
watchVal a isPure = do
  -- Does unsafeCoerce add a thunk
  let a' :: Any = unsafeCoerce a
  name <- mkStab a'
  hnf <- isHnf a
  watched <- get @Watched
  marked <- get @Marked
  let wa = M.lookup name watched
      isMut = fst <$> wa
      hasId = snd <$> wa
  if  | name `S.member` marked || isMut == Just False -> pure $ Right $ fromJust hasId
      | Just True == isMut -> put (S.insert name marked) >> pure (Right $ fromJust hasId)
      | isNothing isMut && hnf && isPure -> do
        eId <- inc
        put $ M.insert name (True, eId) watched
        put $ S.insert name marked
        pure $ Left eId
      | otherwise -> do
        eId <- inc
        weak <- mkWeakPtr a' Nothing
        put $ S.insert name marked
        put $ M.insert name (False, eId) watched
        tell
          [ AnyWatch weak name $
              unsafeCoerce
                ( watchRecIO ::
                    Int ->
                    Watched ->
                    Marked ->
                    Maybe Parent ->
                    a ->
                    IO ([Elem], ([AnyWatch], (Int, (Watched, (Marked, ())))))
                )
          ]
        pure $ Left eId

watchRecIO ::
  (WatchTrace a) =>
  Int ->
  Watched ->
  Marked ->
  Maybe Parent ->
  a ->
  IO ([Elem], ([AnyWatch], (Int, (Watched, (Marked, ())))))
watchRecIO count watched marked mp a =
  runM
    . runMkStableNameIO
    . runMkWeakPtrIO
    . runIsHnfIO
    . runWriter
    . runWriter
    . runCounterState count
    . runState watched
    . runState marked
    $ watchRec mp a

watchPrim :: (WatchTrace a, Show a, Has IsHnf s m) => Maybe Parent -> String -> a -> m ()
watchPrim mp l a = undefined

-- Instances

instance {-# OVERLAPPING #-} WatchTrace Bool where
  watchRec p = watchPrim p "Lazy Bool"

instance {-# OVERLAPPING #-} WatchTrace Int where
  watchRec p = watchPrim p "Lazy Int"

instance {-# OVERLAPPING #-} WatchTrace Int8 where
  watchRec p = watchPrim p "Lazy Int*"

instance {-# OVERLAPPING #-} WatchTrace Int16 where
  watchRec p = watchPrim p "Lazy Int16"

instance {-# OVERLAPPING #-} WatchTrace Int32 where
  watchRec p = watchPrim p "Lazy Int32"

instance {-# OVERLAPPING #-} WatchTrace Int64 where
  watchRec p = watchPrim p "Lazy Int64"

instance {-# OVERLAPPING #-} WatchTrace Word where
  watchRec p = watchPrim p "Lazy Word"

instance {-# OVERLAPPING #-} WatchTrace Word8 where
  watchRec p = watchPrim p "Lazy Word8"

instance {-# OVERLAPPING #-} WatchTrace Word16 where
  watchRec p = watchPrim p "Lazy Word16"

instance {-# OVERLAPPING #-} WatchTrace Word32 where
  watchRec p = watchPrim p "Lazy Word32"

instance {-# OVERLAPPING #-} WatchTrace Word64 where
  watchRec p = watchPrim p "Lazy Word64"

instance {-# OVERLAPPING #-} WatchTrace Natural where
  watchRec p = watchPrim p "Lazy Natural"

instance {-# OVERLAPPING #-} WatchTrace Integer where
  watchRec p = watchPrim p "Lazy Integer"

instance {-# OVERLAPPING #-} WatchTrace Float where
  watchRec p = watchPrim p "Lazy Float"

instance {-# OVERLAPPING #-} WatchTrace Double where
  watchRec p = watchPrim p "Lazy Double"

-- Generic instances

instance (G.Constructor m, GWatchRec1 a) => GWatchRec1 (G.C1 m a) where
  gWatchRec1 m@(G.M1 a) (pId, el) = gWatchRec1 a (pId, el <> EdgeLabel (G.conName m))

instance (G.Selector m, GWatchRec1 a) => GWatchRec1 (G.S1 m a) where
  gWatchRec1 m@(G.M1 a) (pId, el) = gWatchRec1 a (pId, el <> EdgeLabel (G.selName m))

instance (G.Datatype m, GWatchRec1 a) => GWatchRec1 (G.D1 m a) where
  gWatchRec1 d@(G.M1 a) p pd = gWatchRec1 a p $ pd <> DataTypeName (G.datatypeName d)

instance GWatchRec1 G.V1 where
  gWatchRec1 _ _ _ = pure ()

instance GWatchRec1 G.U1 where
  gWatchRec1 _ _ _ = pure ()

instance WatchTrace a => GWatchRec1 (G.Rec0 a) where
  gWatchRec1 (G.K1 a) p _ = watchRec (Just p) a

instance (GWatchRec1 a, GWatchRec1 b) => GWatchRec1 (a G.:+: b) where
  gWatchRec1 (G.L1 a) = gWatchRec1 a
  gWatchRec1 (G.R1 a) = gWatchRec1 a

instance (GWatchRec1 a, GWatchRec1 b) => GWatchRec1 (a G.:*: b) where
  gWatchRec1 (a G.:*: b) p d = gWatchRec1 a p (d <> ", ") >> gWatchRec1 b p (d <> ", ")

instance {-# OVERLAPPING #-} WatchTrace a => WatchTrace (Maybe a)

instance {-# OVERLAPPING #-} WatchTrace a => WatchTrace [a]
