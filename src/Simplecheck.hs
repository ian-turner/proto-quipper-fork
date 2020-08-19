{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
 
-- | This module implements a simplicity checker that checks the correctness
-- of a simple data type definition. 

module Simplecheck (checkCoverage, checkIndices, preTypeToType) where


import TCMonad
import Syntax
import SyntacticOperations
import Utils
import TypeError
import TypeClass
import Substitution

import Nominal

import Data.List
import Control.Monad.Except
import Debug.Trace

-- | Make sure pattern matching is on the same argument in the simple type declaration.
-- The first argument /n/ is the length of the type arguments, /d/ is the name of the
-- simple type constructor, /ls/ is a list of pattern matching positions from each clause.  
checkIndices :: Int -> Id -> [Maybe Int] -> TCMonad (Maybe Int)
checkIndices n d ls =
  case sequence ls of
    Nothing -> do
      when (length ls > 1) $ throwError $ Ambiguous d
      return Nothing
    Just (i:inds) -> helper i inds >> return (Just (n + i))
  where
    helper :: Int -> [Int] -> TCMonad ()
    helper i (j:res) =
      if j /= i
        then throwError $ IndexInconsistent (n + i) (n + j) d
        else helper i res
    helper i [] = return ()

-- | Check the coverage of the pattern matching in the simple declaration.
checkCoverage :: Id -> [Maybe Id] -> TCMonad ()
checkCoverage d' cons =
  case sequence cons of
    Nothing -> do
      when (length cons > 1) $ throwError $ Ambiguous d'
      return ()
    Just css@(c:cs) -> do
      funPac <- lookupId c
      let (DataConstr d) = identification funPac
      typePac <- lookupId d
      let DataType _ cons _ = identification typePac
      when (length css /= length cons) $ throwError $ CoverErr css cons d'
      when (not $ null (css \\ cons)) $ throwError (CoverErr css cons d')

-- | Convert a /pretype/ expression
-- into an actual type. It will also check if the simple declaration is
-- structurally decreasing (in the sense of primitive recursion).
-- The input /n/ is the number of type variables, /k/ is the kind specified in the simple
-- declaration, /i/ is the pattern matching index, /e/ is the pretype. 'preTypeToType'
-- will return the matched constructor and the converted type.
preTypeToType :: Int -> Exp -> Maybe Int -> Exp -> TCMonad (Maybe Id, Exp)
preTypeToType n k i (Pos p e) =
  preTypeToType n k i e `catchError` \e -> throwError $ collapsePos p e
preTypeToType n k i (Lam (Abst vs m)) = handleBody n k i m
preTypeToType n k i (Forall (Abst vs m) ty) = do
  (c, t) <- preTypeToType n k i m
  return (c, Forall (abst vs t) ty)
preTypeToType n k i a = handleBody n k i a

-- | Convert a pretype into a type.
handleBody :: Int -> Exp -> Maybe Int -> Exp -> TCMonad (Maybe Id, Exp)
handleBody n k i m = do
  let (bds, h) = flattenArrows m
      Just (Right hid, args) = flatten h
      (argTypes1, _) = flattenArrows k
      argTypes = map snd argTypes1
  mapM_ (checkBody h hid) (map snd bds)
  case i of
    Just j ->
      let (vsTy, pT:resTy) = splitAt j argTypes
          (vs, p:res) = splitAt j (drop n args)
          Just (id, pargs) = flatten p
       in case id of
            Left pid -> do
              (vs', pargs', res') <- checkVars vs pargs res
              pidTy <- lookupId pid >>= \x -> return $ classifier x
              let pargTys = instantiation pT pidTy
                  pPair = zip pargs' pargTys
                  vsPair = zip vs' vsTy
                  resPair = zip res' resTy
                  finalArgs = vsPair ++ pPair ++ resPair
                  finalType =
                    foldr (\(x, t) y -> Forall (abst [x] y) t) m finalArgs
              return (Just pid, finalType)
            Right pid -> throwError $ withPosition p (TConstrErr pid)
    Nothing -> do
      (_, args', _) <- checkVars [] (drop n args) []
      let finalArgs = zip args' argTypes
          finalType = foldr (\(x, t) y -> Forall (abst [x] y) t) m finalArgs
      return (Nothing, finalType)
  where
    getVar :: Exp -> TCMonad Variable
    getVar (Var x) = return x
    getVar (Pos p e) = getVar e `catchError` \e -> throwError $ collapsePos p e
    getVar a = throwError (NonSimplePatErr a)
             -- make sure the arguments are all variable
    checkVars vs pargs res = do
      vs' <- mapM getVar vs
      pargs' <- mapM getVar pargs
      res' <- mapM getVar res
      return (vs', pargs', res')
    instantiation head ty =
      let (env, t) = removePrefixes False ty
          (argTs, h') = flattenArrows t
          (r, s) = runMatch h' head
       in if r
            then let argTs' = map (apply s) (map snd argTs)
                  in argTs'
            else error $
                 "can't match " ++
                 (show $ disp h') ++ "against " ++ (show $ disp head)

-- | Check the right hand side of the simple declaration is well-defined, i.e., they
-- form a well-defined primitive recursive definition.
checkBody :: Exp -> Id -> Exp -> TCMonad ()
checkBody h id (Pos p e) =
  checkBody h id e `catchError` \e -> throwError $ collapsePos p e
checkBody h id (Var x) = return ()
checkBody h id b
  | Just (Right kid, args) <- flatten b =
    if kid == id
      then let b' = erasePos b
               h' = erasePos h
               s1 = b' `isSubterm` h'
               s2 = b' /= h'
            in if s1 && s2
                 then return ()
                 else throwError $ SubtermErr b h
      else do
        (x, _) <- isSemiSimple kid
        when (not x) $ throwError (NotSimple b)
checkBody h id b
  | otherwise = error $ "from checkBody:" ++ (show (disp b))

-- | Determine if a term is a (first-order) subterm of another.
isSubterm :: Exp -> Exp -> Bool
isSubterm (App t1 t2) (App t3 t4) = isSubterm t1 t3 && isSubterm t2 t4
isSubterm (Var x) (Var y)
  | x == y = True
isSubterm (Const x) (Const y)
  | x == y = True
isSubterm (Base x) (Base y)
  | x == y = True
isSubterm (LBase x) (LBase y)
  | x == y = True
isSubterm (Var x) t =
  let fv = getVars All t
   in x `elem` fv
isSubterm u v = False






