-- | This module implements a version of first-order unification. We support
-- a restricted version of unification for case expression and existential types.

module Unification (runUnify, runDUnify, UnifResult(..)) where

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

-- | Unify two expressions using dUnify. 
runDUnify :: Exp -> Exp -> (UnifResult, Subst)
runDUnify t1 t2 =
  let t1' = erasePos t1
      t2' = erasePos t2
      (r, s) = runState (dUnify t1' t2') Map.empty
  in (r, s)


data UnifResult = Success
                | ModeError (Modality, Exp) (Modality, Exp)
                | UnifError
                | DUnifError
                deriving (Eq, Show)



-- | Unify two expressions. 
unify :: InEquality -> Exp -> Exp -> State (Subst, BSubst) UnifResult

-- unify _ a b | trace (show $ dispRaw a <+> text ":" <+> dispRaw b) $ False = undefined
unify b Unit Unit = return Success
unify b Set Set = return Success
unify b (Base x) (Base y) | x == y = return Success
                          | otherwise = return UnifError
unify b (LBase x) (LBase y) | x == y = return Success
                            | otherwise = return UnifError

unify b (Const x) (Const y) | x == y = return Success
                            | otherwise = return UnifError

unify b (Var x) (Var y) | x == y = return Success
                        | otherwise = return UnifError

 
unify b (MetaVar x) t
  | MetaVar x == t = return Success
  | x `S.member` getVars All t = return UnifError
  | otherwise = 
    do (sub, bsub) <- get
       let subst' =
             mergeSub (Map.fromList [(x, bSubstitute bsub t)]) sub
       put (subst', bsub)
       return Success

unify b t (MetaVar x)
  | MetaVar x == t = return Success
  | x `S.member` getVars All t = return UnifError
  | otherwise =
    do (sub, bsub) <- get
       let subst' =
             mergeSub (Map.fromList [(x, bSubstitute bsub t)]) sub
       put (subst', bsub)
       return Success


-- We allow unifying two first-order existential types.  
-- unify b (Exists (Abst x m) ty1) (Exists (Abst y n) ty2) =
--   do r <- unify b ty1 ty2
--      if r == Success then freshNames ["#existUnif"] $ \ (e:[]) ->
--        do let m' = apply [(x, EigenVar e)] m
--               n' = apply [(x, EigenVar e)] n
--           (sub, bsub) <- get
--           unify b (substitute sub $ bSubstitute bsub m')
--             (substitute sub $ bSubstitute bsub n')
--        else return r

-- We also allow unifying two case expression,
-- but only a very simple kind of unification
unify b (Case e1 (B br1)) (Case e2 (B br2)) | br1 == br2 =
  unify b e1 e2

     
unify b (Arrow t1 t2) (Arrow t3 t4) =
  do a <- unify (flipSide b) t1 t3
     if a == Success
       then do (sub, bsub) <- get
               unify b (substitute sub $ bSubstitute bsub t2)
                 (substitute sub $ bSubstitute bsub t4)
       else return a

unify b (ArrowP t1 t2) (ArrowP t3 t4) =
  do a <- unify (flipSide b) t1 t3
     if a == Success
       then do (sub, bsub) <- get
               unify b (substitute sub $ bSubstitute bsub t2)
                 (substitute sub $ bSubstitute bsub t4)
       else return a

unify b (Tensor t1 t2) (Tensor t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then do (sub, bsub) <- get
               unify b (substitute sub $ bSubstitute bsub t2)
                 (substitute sub $ bSubstitute bsub t4)
       else return a

unify b e1@(Circ t1 t2 mode1) e2@(Circ t3 t4 mode2) =
  case modeResolution b mode1 mode2 of
       Just bsub'@(bsub1', bsub2', bsub3') -> 
         do (sub, (bsub1, bsub2, bsub3)) <- get
            let new = (mergeModeSubst bsub1' bsub1,
                       mergeModeSubst bsub2' bsub2,
                       mergeModeSubst bsub3' bsub3)
                sub' = Map.map (\ x -> bSubstitute new x) sub
            put (sub', new)
            let t1' = bSubstitute new t1
                t3' = bSubstitute new t3
            a <- unify b t1' t3'
            if a == Success then
              do (sub'', bsub'') <- get
                 let t2' = bSubstitute bsub'' t2
                     t4' = bSubstitute bsub'' t4
                 unify b (substitute sub'' t2') (substitute sub'' t4')
              else return a
       Nothing -> return $ ModeError (mode1, e1) (mode2, e2)

unify b e1@(Bang t mode1) e2@(Bang t' mode2) =
  case modeResolution b mode1 mode2 of 
    Just bsub'@(bsub1', bsub2', bsub3') -> 
      do (sub, (bsub1, bsub2, bsub3)) <- get
         let new = (mergeModeSubst bsub1' bsub1,
                    mergeModeSubst bsub2' bsub2,
                    mergeModeSubst bsub3' bsub3)
             sub' = Map.map (\ x -> bSubstitute new x) sub
         put (sub', new)
         unify b (bSubstitute new t) (bSubstitute new t')
    Nothing -> return $ ModeError (mode1, e1) (mode2, e2)

unify b (Force t) (Force t') = unify b t t'
unify b (ForceP t) (ForceP t') = unify b t t'
unify b (Lift t) (Lift t') = unify b t t'

unify b (App t1 t2) (App t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then
       do (sub, bsub) <- get
          unify b (substitute sub $ bSubstitute bsub t2)
            (substitute sub  $ bSubstitute bsub t4)
       else return a

unify b (AppP t1 t2) (AppP t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then
       do (sub, bsub) <- get
          unify b (substitute sub $ bSubstitute bsub t2)
            (substitute sub $ bSubstitute bsub t4)
       else return a

unify b (AppDict t1 t2) (AppDict t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then
       do (sub, bsub) <- get
          unify b (substitute sub $ bSubstitute bsub t2)
            (substitute sub $ bSubstitute bsub t4)
       else return a

unify b (AppDep t1 t2) (AppDep t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then
       do (sub, bsub) <- get
          unify b (substitute sub $ bSubstitute bsub t2)
            (substitute sub $ bSubstitute bsub t4)
       else return a


unify b (AppType t1 t2) (AppType t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then do (sub, bsub) <- get
               unify b (substitute sub $ bSubstitute bsub t2)
                 (substitute sub $ bSubstitute bsub t4)
       else return a

unify b (AppTm t1 t2) (AppTm t3 t4) =
  do a <- unify b t1 t3
     if a == Success
       then do (sub, bsub) <- get
               unify b (substitute sub $ bSubstitute bsub t2)
                 (substitute sub $ bSubstitute bsub t4)
       else return a

unify b (Imply [] t2) (Imply [] t4) =
  unify b t2 t2
  
unify b (Imply (t1:ts1) t2) (Imply (t3:ts3) t4) =
  do r <- unify b t1 t3
     if r == Success
       then do (sub, bsub) <- get
               let ts1' =
                     map (\x -> substitute sub $ bSubstitute bsub x) ts1
                   ts3' =
                     map (\x -> substitute sub $ bSubstitute bsub x) ts3
                   t2' = substitute sub $ bSubstitute bsub t2
                   t4' = substitute sub $ bSubstitute bsub t4
               unify b (Imply ts1' t2') (Imply ts3' t4')
       else return UnifError
    
unify b t t' = return UnifError


-- | Unify two expressions in dependent pattern matching. 
dUnify :: Exp -> Exp -> State Subst UnifResult

-- dUnify _ a b | trace (show $ dispRaw a <+> text ":" <+> dispRaw b) $ False = undefined
dUnify Unit Unit = return Success
dUnify Set Set = return Success
dUnify (Base x) (Base y) | x == y = return Success
                         | otherwise = return DUnifError
dUnify (LBase x) (LBase y) | x == y = return Success
                           | otherwise = return DUnifError

dUnify (Const x) (Const y) | x == y = return Success
                           | otherwise = return DUnifError

-- dUnify (MetaVar x) (MetaVar y) | x == y = return Success
--                                | otherwise = return DUnifError

 
dUnify (Var x) t
  | Var x == t = return Success
  | MetaVar y <- t, x == y =
    do sub <- get
       let subst' =
             mergeSub (Map.fromList [(y, Var x)]) sub
       put subst'
       return Success
       
  | x `S.member` getVars All t = return DUnifError
  | otherwise = 
    do sub <- get
       let subst' =
             mergeSub (Map.fromList [(x, t)]) sub
       put subst'
       return Success

dUnify t (Var x)
  | Var x == t = return Success
  | MetaVar y <- t, x == y =
    do sub <- get
       let subst' =
             mergeSub (Map.fromList [(y, Var x)]) sub
       put subst'
       return Success
  
  | x `S.member` getVars All t = return DUnifError
  | otherwise =
    do sub <- get
       let subst' =
             mergeSub (Map.fromList [(x, t)]) sub
       put subst'
       return Success


dUnify (MetaVar x) t
  | MetaVar x == t = return Success
  | x `S.member` getVars All t = return DUnifError
  | otherwise = 
    do sub <- get
       let subst' =
             mergeSub (Map.fromList [(x, t)]) sub
       put subst'
       return Success

dUnify t (MetaVar x)
  | MetaVar x == t = return Success
  | x `S.member` getVars All t = return DUnifError
  | otherwise =
    do sub <- get
       let subst' =
             mergeSub (Map.fromList [(x, t)]) sub
       put subst'
       return Success



dUnify (Force t) (Force t') = dUnify t t'
dUnify (ForceP t) (ForceP t') = dUnify t t'
dUnify (Lift t) (Lift t') = dUnify t t'

dUnify (App t1 t2) (App t3 t4) =
  do a <- dUnify t1 t3
     if a == Success
       then
       do sub <- get
          dUnify (substitute sub t2)
            (substitute sub t4)
       else return a

dUnify (AppP t1 t2) (AppP t3 t4) =
  do a <- dUnify t1 t3
     if a == Success
       then
       do sub <- get
          dUnify (substitute sub t2)
            (substitute sub t4)
       else return a

dUnify (AppDict t1 t2) (AppDict t3 t4) =
  do a <- dUnify t1 t3
     if a == Success
       then
       do sub <- get
          dUnify (substitute sub t2)
            (substitute sub t4)
       else return a

dUnify (AppDep t1 t2) (AppDep t3 t4) =
  do a <- dUnify t1 t3
     if a == Success
       then
       do sub <- get
          dUnify (substitute sub t2)
            (substitute sub t4)
       else return a


dUnify (AppType t1 t2) (AppType t3 t4) =
  do a <- dUnify t1 t3
     if a == Success
       then
       do sub <- get
          dUnify (substitute sub t2)
            (substitute sub t4)
       else return a

dUnify (AppTm t1 t2) (AppTm t3 t4) =
  do a <- dUnify t1 t3
     if a == Success
       then
       do sub <- get
          dUnify (substitute sub t2)
            (substitute sub t4)
       else return a

dUnify t t' = return DUnifError
