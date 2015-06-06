-----------------------------------------------------------------------------
--
-- Module      :  Control.Monad.Unify
-- Copyright   :  (c) Phil Freeman 2013
-- License     :  MIT
--
-- Maintainer  :  Phil Freeman <paf31@cantab.net>
-- Stability   :  experimental
-- Portability :
--
-- |
--
--
-----------------------------------------------------------------------------

{-# LANGUAGE
    GeneralizedNewtypeDeriving
  , FlexibleInstances
  , FlexibleContexts
  , MultiParamTypeClasses
  , FunctionalDependencies
  , UndecidableInstances
  #-}

module Control.Monad.Unify where

import Data.HashMap.Strict as M

import Data.Maybe
import Data.Monoid
import Control.Applicative
import Control.Monad.State
import Control.Monad.Except


-- | Untyped unification variables
type Unknown = Int

-- | A type which can contain unification variables
class Partial t where
  unknown   :: Unknown -> t
  isUnknown :: t -> Maybe Unknown
  unknowns  :: t -> [Unknown]
  ($?)      :: Substitution t -> t -> t

-- | Identifies types which support unification
class (Partial t) => Unifiable m t | t -> m where
  (=?=) :: t -> t -> UnifyT t m ()

-- | A substitution maintains a mapping from unification variables to their values
newtype Substitution t = Substitution
  { runSubstitution :: M.HashMap Unknown t
  } deriving (Show, Eq, Functor)

-- | Substitution composition
instance (Partial t) => Monoid (Substitution t) where
  mempty = Substitution mempty
  s1 `mappend` s2 = Substitution $
    runSubstitution ((s2 $?) <$> s1) <> runSubstitution ((s1 $?) <$> s2)

-- | State required for type checking
data UnifyState t = UnifyState
  { nextFreshVar :: Int                   -- ^ The next fresh unification variable
  , currentSubstitution :: Substitution t -- ^ The current substitution
  } deriving (Show, Eq)

-- | An initial @UnifyState@
initUnifyState :: Partial t => UnifyState t
initUnifyState = UnifyState 0 mempty

-- | The type checking monad, which provides the state of the type checker,
-- and error reporting capabilities
newtype UnifyT t m a = UnifyT { unUnify :: StateT (UnifyState t) m a }
  deriving ( Functor
           , Monad
           , MonadTrans
           , MonadFix
           , Applicative
           , Alternative
           , MonadPlus
           )

instance (Partial t, Monad m) => MonadState (UnifyState t) (UnifyT t m) where
  get = UnifyT get
  put = UnifyT . put

-- | A class for errors which support unification errors
class UnificationError t e where
  occursCheckFailed :: t -> e

-- | Run a computation in the Unify monad, failing with an error, or succeeding
-- with a return value and the new next unification variable
runUnifyT :: UnifyState t -> UnifyT t m a -> m (a, UnifyState t)
runUnifyT s = flip runStateT s . unUnify

-- | Substitute a single unification variable
substituteOne :: Partial t => Unknown -> t -> Substitution t
substituteOne u t = Substitution $ M.singleton u t

-- | Replace a unification variable with the specified value in the current substitution
(=:=) :: ( UnificationError t e
         , Monad m
         , MonadError e m
         , Unifiable m t
         ) => Unknown -> t -> UnifyT t m ()
(=:=) u t' = do
  st <- get
  let sub     = currentSubstitution st
      t       = sub $? t'
      current = sub $? unknown u
  occursCheck u t
  case isUnknown current of
    Just u1 | u1 == u -> return ()
    _                 -> current =?= t
  put $ st { currentSubstitution = substituteOne u t <> currentSubstitution st }

-- | Perform the occurs check, to make sure a unification variable does not occur inside a value
occursCheck :: ( UnificationError t e
               , Monad m
               , MonadError e m
               , Partial t
               ) => Unknown -> t -> UnifyT t m ()
occursCheck u t = case isUnknown t of
  Nothing -> when (u `elem` unknowns t) $ lift $ throwError $ occursCheckFailed t
  _ -> return ()

-- TODO: Ask paf31 if `fresh'` would get borked from a `Partial` constraint
-- | Generate a fresh untyped unification variable
fresh' :: Monad m => UnifyT t m Unknown
fresh' = do
  st <- UnifyT get
  UnifyT $ put $ st { nextFreshVar = succ $ nextFreshVar st }
  return $ nextFreshVar st

-- | Generate a fresh unification variable at a specific type
fresh :: (Monad m, Partial t) => UnifyT t m t
fresh = liftM unknown fresh'
