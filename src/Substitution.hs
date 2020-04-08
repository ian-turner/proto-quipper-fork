{-# LANGUAGE  FlexibleInstances #-}
-- | This module implements the usual capture-avoiding substitution. 
module Substitution (apply, Subst, substitute, mergeSub) where

import Syntax
import Utils



import Nominal
import qualified Data.Map as Map
import qualified Data.Set as S
import Data.Map (Map)
import Text.PrettyPrint


-- | A substitution is represented as a map from variables to expressions.
type Subst = Map Variable Exp


instance Disp (Map Variable Exp) where
  display b vs =
    let vs' = Map.toList vs in
    vcat $ map helper vs'
     where helper (x,  t) = display b x <+> text "|->" <+> display b t


-- | Apply a substitute to an expression.              
substitute :: Subst -> Exp -> Exp           
substitute s a@(Var y) =
  case Map.lookup y s of
    Nothing -> a
    Just t -> t

substitute s a@(GoalVar y) =
  case Map.lookup y s of
    Nothing -> a
    Just t -> t
    
substitute s a@(EigenVar y) = 
  case Map.lookup y s of
    Nothing -> a
    Just t -> t

substitute s a@(Base _) = a
substitute s a@(LBase _) = a      
substitute s a@(Unit) = a
substitute s a@(Set) = a
substitute s a@(Sort) = a
substitute s a@(Star) = a
substitute s a@(Const _) = a
substitute s (Arrow t t') =
  let t1' = substitute s t
      t2' = substitute s t'
  in Arrow t1' t2'
substitute s (WithType t t') =
  let t1' = substitute s t
      t2' = substitute s t'
  in WithType t1' t2'     
substitute s (Arrow' t t') =
  let t1' = substitute s t
      t2' = substitute s t'
  in Arrow' t1' t2'  
substitute s (Imply t t') =
  let t1' = map (substitute s) t
      t2' = substitute s t'
  in Imply t1' t2'  
substitute s (Tensor t t') =
  let t1' = substitute s t
      t2' = substitute s t'
  in Tensor t1' t2'
substitute s (Circ t t' m) =
  let t1' = substitute s t
      t2' = substitute s t'
  in Circ t1' t2' m

substitute s (Bang t m) = Bang (substitute s t) m

substitute s (Pi bind t) =
  open bind $
  \ ys m -> Pi (abst ys (substitute s m))
           (substitute s t) 

substitute s (PiImp bind t) =
  open bind $
  \ ys m -> PiImp (abst ys (substitute s m))
           (substitute s t) 

substitute s (Pi' bind t) =
  open bind $
  \ ys m -> Pi' (abst ys (substitute s m))
            (substitute s t) 

substitute s (Exists bind t) =
  open bind $
  \ ys m -> Exists (abst ys (substitute s m))
           (substitute s t) 

substitute s (Forall bind t) =
  open bind $
  \ ys m -> Forall (abst ys (substitute s m))
           (substitute s t) 

substitute s (Mod bind) =
  open bind $
  \ ys m -> Mod (abst ys (substitute s m))


substitute s (App t tm) =
  App (substitute s t) (substitute s tm)

substitute s (App' t tm) =
  App' (substitute s t) (substitute s tm)
  
substitute s (AppType t tm) =
  AppType (substitute s t) (substitute s tm)

substitute s (AppTm t tm) =
  AppTm (substitute s t) (substitute s tm)

substitute s (AppDep t tm) =
  AppDep (substitute s t) (substitute s tm)
substitute s (AppDepTy t tm) =
  AppDepTy (substitute s t) (substitute s tm)
  
substitute s (AppDep' t tm) =
  AppDep' (substitute s t) (substitute s tm)  
substitute s (AppDict t tm) =
  AppDict (substitute s t) (substitute s tm)

substitute s (Lam bind) =
  open bind $
  \ ys m -> Lam (abst ys (substitute s m)) 

substitute s (LamAnn ty bind) =
  open bind $
  \ ys m -> LamAnn (substitute s ty) (abst ys (substitute s m)) 

substitute s (LamAnn' ty bind) =
  open bind $
  \ ys m -> LamAnn' (substitute s ty) (abst ys (substitute s m)) 

substitute s (Lam' bind) =
  open bind $
  \ ys m -> Lam' (abst ys (substitute s m)) 

substitute s (LamType bind) =
  open bind $
  \ ys m -> LamType (abst ys (substitute s m)) 

substitute s (LamTm bind) =
  open bind $
  \ ys m -> LamTm (abst ys (substitute s m)) 

substitute s (LamDict bind) =
  open bind $
  \ ys m -> LamDict (abst ys (substitute s m)) 


substitute s (LamDep bind) =
  open bind $
  \ ys m -> LamDep (abst ys (substitute s m)) 

substitute s (LamDepTy bind) =
  open bind $
  \ ys m -> LamDepTy (abst ys (substitute s m)) 

substitute s (LamDep' bind) =
  open bind $
  \ ys m -> LamDep' (abst ys (substitute s m)) 

substitute s (Pair t tm) =
  Pair (substitute s t) (substitute s tm)

substitute s (Force t) = Force (substitute s t)
substitute s (Force' t) = Force' (substitute s t)
substitute s (Lift t) = Lift (substitute s t) 
substitute s (UnBox) = UnBox
substitute s (Reverse) = Reverse
substitute s (Controlled) = Controlled
substitute s (WithComputed) = WithComputed
substitute s (Dynlift) = Dynlift
substitute s a@(Box) = a
substitute s a@(ExBox) = a
       
substitute s (Let m bd) =
  let m' = substitute s m in
    open bd $ \ y b -> Let m' (abst y (substitute s b)) 

substitute s (LetPair m bd) =
  let m' = substitute s m in
    open bd $ \ ys b -> LetPair m' (abst ys (substitute s b)) 

substitute s (LetPat m bd) =
  let m' = substitute s m in
   open bd $ \ (PApp id ps) b ->
   let ps' = map (helper s) ps in 
   LetPat m' (abst (PApp id ps') (substitute s b))
  where helper s (Left (NoBind t)) = Left (NoBind (substitute s t))
        helper s (Right x) = Right x
        
substitute s (Case tm (B br)) =
  Case (substitute s tm) (B (helper' br))
  where helper' br =
          map (\ b -> open b $
                       \ (PApp id ps) m ->
                       let ps' = map (helper s) ps in 
                       abst (PApp id ps') (substitute s m))
          br

        helper s (Left (NoBind t)) = Left (NoBind (substitute s t))
        helper s (Right x) = Right x

substitute s (Pos p e) = Pos p (substitute s e)
substitute s a = error ("from substitute: " ++ show (disp a))  

-- | Apply a list version of substitution to an expression.
apply :: [(Variable, Exp)] -> Exp -> Exp
apply s t = let s' = Map.fromList s in substitute s' t

-- | Merge two substitutions.
mergeSub :: Map Variable Exp -> Map Variable Exp -> Map Variable Exp
mergeSub new old =
  new `Map.union` Map.map (substitute new) old

      


