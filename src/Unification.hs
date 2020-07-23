-- | This module implements a version of first-order unification. We support
-- a restricted version of unification for case expression and existential types.

module Unification (runUnify, UnifResult(..)) where

import Syntax
import Substitution
import Utils
import SyntacticOperations
import ModeResolve

import Text.PrettyPrint
import qualified Data.MultiSet as S
import qualified Data.Map as Map
import Control.Monad.State
import Debug.Trace



-- | Unify two expressions. 
runUnify :: InEquality -> Exp -> Exp -> (UnifResult, (Subst, BSubst))
runUnify b t1 t2 =
  let t1' = erasePos t1
      t2' = erasePos t2
      (r, s) = runState (unify b t1' t2') (Map.empty, ([], [], []))
  in (r, s)
   -- if r then Just s else Nothing

data UnifResult = Success | ModeError (Modality, Exp) (Modality, Exp) | UnifError
                deriving (Eq, Show)

-- | Unify two expressions. 
-- There are eigenvariables for type checking, we only allow
-- the unification of a eigenvariable [x] with itself and its variable counterpart x.
-- (the unification of x and [x] can happen due to dependent pattern matching).
unify :: InEquality -> Exp -> Exp -> State (Subst, BSubst) UnifResult
unify _ a b | trace (show $ dispRaw a <+> text ":" <+> dispRaw b) $ False = undefined
unify b Unit Unit = return Success
unify b Set Set = return Success
unify b (Base x) (Base y) | x == y = return Success
                          | otherwise = return UnifError
unify b (LBase x) (LBase y) | x == y = return Success
                            | otherwise = return UnifError
unify b (Const x) (Const y) | x == y = return Success
                            | otherwise = return UnifError

unify b (EigenVar x) (EigenVar y) | x == y = return Success
                                  | otherwise = return UnifError

 
unify b (Var x) t
  | Var x == t = return Success
  | (EigenVar y) <- t, x == y = return Success
  | x `S.member` getVars AllowEigen t = return UnifError
  | otherwise = 
    do (sub, bsub) <- get
       let subst' = mergeSub (Map.fromList [(x, t)]) sub
       put (subst', bsub)
       return Success

unify b t (Var x)
  | Var x == t = return Success
  | (EigenVar y) <- t, x == y = return Success  
  | x `S.member` getVars AllowEigen t = return UnifError
  | otherwise =
    do (sub, bsub) <- get
       let subst' = mergeSub (Map.fromList [(x, t)]) sub
       put (subst', bsub)
       return Success


unify b (GoalVar x) t
  | GoalVar x == t = return Success
  | x `S.member` getVars GetGoal t = return UnifError
  | otherwise = 
    do (sub, bsub) <- get
       let subst' = mergeSub (Map.fromList [(x, t)]) sub
       put (subst', bsub)
       return Success

unify b t (GoalVar x) 
  | GoalVar x == t = return Success
  | x `S.member` getVars GetGoal t = return UnifError
  | otherwise = 
    do (sub, bsub) <- get
       let subst' = mergeSub (Map.fromList [(x, t)]) sub
       put (subst', bsub)
       return Success


-- We allow unifying two first-order existential types.  
unify b (Exists (Abst x m) ty1) (Exists (Abst y n) ty2) =
  do r <- unify b ty1 ty2
     if r == Success then freshNames ["#existUnif"] $ \ (e:[]) ->
       do let m' = apply [(x, EigenVar e)] m
              n' = apply [(x, EigenVar e)] n
          (sub, bsub) <- get
          unify b (substitute sub m')
            (substitute sub n')
       else return r

-- We also allow unifying two case expression,
-- but only a very simple kind of unification
unify b (Case e1 (B br1)) (Case e2 (B br2)) | br1 == br2 =
  unify b e1 e2

     
unify b (Arrow t1 t2) (Arrow t3 t4) =
  do a <- unify (flipSide b) t1 t3
     if a == Success
       then do (sub, bsub) <- get
               unify b (substitute sub t2)
                 (substitute sub t4)
       else return a

unify b (Arrow' t1 t2) (Arrow' t3 t4) =
  do a <- unify (flipSide b) t1 t3
     if a == Success
       then do (sub, bsub) <- get
               unify b (substitute sub t2)
                 (substitute sub t4)
       else return a

unify b (Tensor t1 t2) (Tensor t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then do (sub, bsub) <- get
               unify b (substitute sub t2)
                 (substitute sub t4)
       else return a

unify b e1@(Circ t1 t2 mode1) e2@(Circ t3 t4 mode2) =
  do
     let r = modeResolution b mode1 mode2
     case r of
       Just bsub'@(bsub1', bsub2', bsub3') -> 
         do (sub, (bsub1, bsub2, bsub3)) <- get
            let sub' = Map.map (\ x -> bSubstitute bsub' x) sub
                new = (mergeModeSubst bsub1' bsub1, mergeModeSubst bsub2' bsub2,
                       mergeModeSubst bsub3' bsub3)
            put (sub', new)
            let t1' = bSubstitute new t1
                t3' = bSubstitute new t3
            a <- unify b t1' t3'
            if a == Success then
              do (sub, bsub'') <- get
                 let t2' = bSubstitute bsub'' t2
                     t4' = bSubstitute bsub'' t4
                 unify b (substitute sub t2') (substitute sub t4')
              else return a
       Nothing -> return $ ModeError (mode1, e1) (mode2, e2)

unify b e1@(Bang t mode1) e2@(Bang t' mode2) =
  do let r = modeResolution b  mode1 mode2
     case r of 
       Just bsub'@(bsub1', bsub2', bsub3') -> 
         do (sub, (bsub1, bsub2, bsub3)) <- get
            let sub' = Map.map (\ x -> bSubstitute bsub' x) sub
                new = (mergeModeSubst bsub1' bsub1, mergeModeSubst bsub2' bsub2,
                       mergeModeSubst bsub3' bsub3)
            put (sub', new)
            unify b (bSubstitute new t) (bSubstitute new t')
       Nothing -> return $ ModeError (mode1, e1) (mode2, e2)

unify b (Force t) (Force t') = unify b t t'
unify b (Force' t) (Force' t') = unify b t t'
unify b (Lift t) (Lift t') = unify b t t'

unify b (App t1 t2) (App t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then
       do (sub, _) <- get
          unify b (substitute sub t2) (substitute sub t4)
       else return a

unify b (App' t1 t2) (App' t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then
       do (sub, _) <- get
          unify b (substitute sub t2) (substitute sub t4)
       else return a

unify b (AppDict t1 t2) (AppDict t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then
       do (sub, _) <- get
          unify b (substitute sub t2) (substitute sub t4)
       else return a

unify b (AppDep t1 t2) (AppDep t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then
       do (sub, _) <- get
          unify b (substitute sub t2) (substitute sub t4)
       else return a


unify b (AppType t1 t2) (AppType t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then do (sub, _) <- get
               unify b (substitute sub t2) (substitute sub t4)
       else return a

unify b (AppTm t1 t2) (AppTm t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then do (sub, _) <- get
               unify b (substitute sub t2) (substitute sub t4)
       else return a

unify b (Imply t1 t2) (Imply t3 t4) =
  do a <- zipWithM (unify b) t1 t3
     if all (\ r -> r == Success) a
       then do (sub, _) <- get
               unify b (substitute sub t2) (substitute sub t4)
       else return UnifError

unify b t t' = return UnifError



