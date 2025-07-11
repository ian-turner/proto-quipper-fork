{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
-- | This module defines the 'erasure' function, it erases
-- an annotated expression to a lambda expression without irrelevant annotations.
module Erasure
  ( erasure
  ) where

import Nominal
import SyntacticOperations
import Syntax
import TCMonad
import TypeError
import Utils

import Control.Monad.Except
import Control.Monad.State
import Data.List
import qualified Data.Set as S
import Debug.Trace
import Debug.Trace
import Text.PrettyPrint

-- | Erase a fully annotated expression to a lambda expression, for
-- runtime evaluation. Provide the variable information for variable bindings.
-- The erasure function also checks if an irrelevant variable
-- is used as an explicit argument.
erasure :: Exp -> TCMonad EExp
erasure (Pos p a) = erasure a `catchError` \e -> throwError $ collapsePos p e
erasure Star = return EStar
erasure Unit = return EUnit
erasure a@(Var x) = return (EVar x)
-- erasure a@(MetaVar x) = return (EVar x)
erasure a@(Const t) = return (EConst t)
erasure a@(Base t) = return (EBase t)
erasure a@(LBase t) = return (ELBase t)
erasure (App e1 e2) = do
  e1' <- erasure e1
  e2' <- erasure e2
  return $ EApp e1' e2'
-- Convert app' to app
erasure (AppP e1 e2) = do
  e1' <- erasure e1
  e2' <- erasure e2
  return $ EApp e1' e2'
erasure (AppDict e1 e2) = do
  e1' <- erasure e1
  e2' <- erasure e2
  return $ EApp e1' e2'
erasure (AppDep e1 e2) = do
  e1' <- erasure e1
  e2' <- erasure e2
  return $ EApp e1' e2'
erasure (AppDepTy e1 e2) = do
  e1' <- erasure e1
  e2' <- erasure e2
  return $ EApp e1' e2'
erasure (AppDepInt e1 e2) = do
  e1' <- erasure e1
  e2' <- erasure e2
  return $ EApp e1' e2'
erasure (Pair e1 e2) = do
  e1' <- erasure e1
  e2' <- erasure e2
  return $ EPair e1' e2'
erasure (Tensor e1 e2) = do
  e1' <- erasure e1
  e2' <- erasure e2
  return $ ETensor e1' e2'
erasure (Arrow e1 e2 _) = do
  e1' <- erasure e1
  e2' <- erasure e2
  return $ EArrow e1' e2'
erasure (AppType e1 e2) = erasure e1
erasure (AppTm e1 e2) = erasure e1
erasure a@(Lam (Abst xs m)) = do
  m' <- erasure m
  return $ ELam (abst xs m')
erasure a@(LamAnn _ (Abst xs m)) = do
  m' <- erasure m
  return $ ELam (abst xs m')
erasure a@(LamAnnP _ (Abst xs m)) = do
  m' <- erasure m
  return $ ELam (abst xs m')
-- Convert lam' to lam
erasure a@(LamP (Abst xs m)) = do
  m' <- erasure m
  return $ ELam (abst xs m')
erasure a@(LamDict (Abst xs m)) = do
  m' <- erasure m
  return $ ELam (abst xs m')
erasure (WithType ann t) = erasure ann

erasure (LamDep (Abst ys m)) = do
  m' <- erasure m
  return $ ELam (abst ys m')

erasure (LamDepTy (Abst ys m)) = do
  m' <- erasure m
  return $ ELam (abst ys m')
erasure (WrapR (MR l x)) = return $ EWrapR $ MR l x
erasure a@(RealOp x) = return (ERealOp x)
erasure (LamDepInt (Abst ys m)) = do
  m' <- erasure m
  return $ ELam (abst ys m')
erasure (LamTm bd) =
  open bd $ \xs m ->
  do mapM (checkExp m) xs
     erasure m
erasure (LamType bd) =
  open bd $ \xs m ->
    do mapM (checkExp m) xs
       erasure m

erasure (Lift t) = do
  t' <- erasure t
  return (ELift t')
erasure (Force t) = EForce <$> erasure t
erasure (ForceP t) = EForce <$> erasure t
erasure (UnBox) = return EUnBox
erasure (RunCirc) = return ERunCirc
erasure (Reverse) = return EReverse
erasure (Controlled) = return EControlled
erasure (WithComputed) = return EWithComputed
erasure (Dynlift) = return EDynlift
erasure a@(Box) = return EBox
erasure a@(ExBox) = return EExBox
erasure (Let m bd) =
  open bd $ \vs b -> do
    m' <- erasure m
    b' <- erasure b
    return $ ELet m' (abst vs b')
erasure (LetPair m bd) =
  open bd $ \xs b -> do
    m' <- erasure m
    b' <- erasure b
    return $ ELetPair m' (abst xs b')
erasure (LetPat m bd) =
  open bd $ \pa b ->
    case pa of
      PApp kid args -> do
        b' <- erasure b
        m' <- erasure m
        funP <- lookupId kid
        let ty = classifier funP
        args' <- helper ty args b b'
        return $ ELetPat m' (abst (EPApp kid args') b')
  where
    helper (Mod (Abst _ t)) args b b' = helper t args b b'
        -- The only way a data constructor can have a Pi type
        -- is when it is an existential type.
    helper (Pi bds t _) args b b'
      | not (isKind t) =
        open bds $ \ys m -> do
          let (vs, res) = splitAt (length ys) args
              vs1 = map (\(Right x) -> x) vs
          vs' <- helper m res b b'
          return $ vs1 ++ vs'
    helper (Forall bds t) args b b' =
      open bds $ \ys m ->
        let (vs, res) = splitAt (length ys) args
         in do checkExplicit vs b
               helper m res b b'
    helper (Arrow t1 t2 _) (x:xs) b b' = do
      vs' <- helper t2 xs b b'
      -- let Right x' = x
      -- return $ x' : vs'
      case x of
        Right x' ->
           return $ x' : vs'
        Left (NoBind a) -> error $ "helperArrowErasure" ++ show (disp a)
    helper (Imply [t1] t2 _) (x:xs) b b' = do
      vs' <- helper t2 xs b b'
      let (Right x') = x
      return $ x' : vs'
    helper (Imply (t1:ts) t2 m) (x:xs) b b' = do
      vs' <- helper (Imply ts t2 m) xs b b'
      let (Right x') = x
      return $ x' : vs'
    helper a [] b b' = return []
    helper a _ b b' = error $ "from helper erasure-letPat"

erasure l@(Case e (B br)) = do
  e' <- erasure e
  brs <- mapM helper br
  return $ ECase e' (EB brs)
  where
    helper bd =
      open bd $ \p m ->
        case p of
          PApp kid args -> do
            funP <- lookupId kid
            let ty = classifier funP
            m' <- erasure m
            args' <- helper2 ty args m m'
            return (abst (EPApp kid args') m')
    helper2 (Mod (Abst _ t)) args b b' = helper2 t args b b'
             -- The only way a data constructor can have a Pi type
             -- is when it is an existential type.
    helper2 (Pi bds t _) args ann m'
      | not (isKind t) =
        open bds $ \ys m -> do
          let (vs, res) = splitAt (length ys) args
              vs1 = map (\(Right x) -> x) vs
          vs' <- helper2 m res ann m'
          return $ vs1 ++ vs'
    helper2 (Forall bds t) args ann m' =
      open bds $ \ys m ->
        let (vs, res) = splitAt (length ys) args
         in do checkExplicit vs ann
               helper2 m res ann m'
    helper2 (Arrow t1 t2 _) (x:xs) ann m' = do
      vs' <- helper2 t2 xs ann m'
      let (Right x') = x
      return $ x' : vs'
    helper2 (Imply [t1] t2 _) (x:xs) ann m' = do
      vs' <- helper2 t2 xs ann m'
      let (Right x') = x
      return $ x' : vs'
    helper2 (Imply (t1:ts) t2 mod) (x:xs) ann m' = do
      vs' <- helper2 (Imply ts t2 mod) xs ann m'
      let (Right x') = x
      return $ x' : vs'
    helper2 a [] _ _ = return []
    helper2 a b _ _ =
      error $ "from helper2 flag-erasure-case" ++ (show $ disp a)
erasure (MetaVar x) = throwError $ UnBoundMetaVar x
erasure a = error $ "from erasure: " ++ (show $ disp a)

-- | Check if any irrelavant variables in the list is used explicitly in an expression.
checkExplicit :: [Either (NoBind Exp) Variable] -> Exp -> TCMonad ()
checkExplicit [] ann = return ()
checkExplicit (Left a:xs) ann = checkExplicit xs ann
checkExplicit (Right x:xs) ann = do
  when (isExplicit x ann) $ throwError $ ImplicitCase x ann
  checkExplicit xs ann

checkExp ann'' x =
  when (isExplicit x ann'') $ throwError $ ImplicitVarErr x ann''
