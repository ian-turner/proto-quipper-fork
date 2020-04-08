{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
-- | This module defines the 'erasure' function, it erases
-- an annotated expression to a lambda expression without irrelevant annotations.

module Erasure (erasure, countVar) where

import Syntax
import Nominal
import Utils
import TCMonad
import TypeError
import SyntacticOperations

import Control.Monad.Except
import Control.Monad.State
import Debug.Trace
import Text.PrettyPrint
import qualified Data.Set as S
import Data.List
import Debug.Trace



-- | Erase a fully annotated expression to a lambda expression, for
-- runtime evaluation. Provide the variable information for variable bindings.
-- The erasure function also checks if an irrelevant variable
-- is used as an explicit argument. 

erasure :: Exp -> TCMonad EExp
erasure (Pos p a) = erasure a `catchError` \ e -> throwError $ collapsePos p e
erasure Star = return EStar
erasure Unit = return EUnit
erasure a@(Var x) = return (EVar x)
erasure a@(EigenVar x) = return (EVar x)
erasure a@(GoalVar x) = return (EVar x)
erasure a@(Const t) = return (EConst t)
erasure a@(Base t) = return (EBase t)
erasure a@(LBase t) = return (ELBase t)

erasure (App e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ EApp e1' e2'

-- Convert app' to app
erasure (App' e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ EApp e1' e2'

erasure (AppDict e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ EApp e1' e2'

erasure (AppDep e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ EApp e1' e2'

erasure (AppDepTy e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ EApp e1' e2'

erasure (AppDep' e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ EApp e1' e2'

erasure (Pair e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ EPair e1' e2'

erasure (Tensor e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ ETensor e1' e2'


erasure (Arrow e1 e2) =
  do e1' <- erasure e1
     e2' <- erasure e2
     return $ EArrow e1' e2'

erasure (AppType e1 e2) = erasure e1

erasure (AppTm e1 e2) = erasure e1

erasure a@(Lam (Abst xs m)) =
  do m' <- erasure m
     let ns = countVar xs m'
         xs' = zip xs ns
         ws = evars m' \\ xs
     return $ ELam ws (abst xs' m') 

erasure a@(LamAnn _ (Abst xs m)) =
  do m' <- erasure m
     let ns = countVar xs m'
         xs' = zip xs ns
         ws = evars m' \\ xs
     return $ ELam ws (abst xs' m') 

erasure a@(LamAnn' _ (Abst xs m)) =
  do m' <- erasure m
     let ns = countVar xs m'
         xs' = zip xs ns
         ws = evars m' \\ xs
     return $ ELam ws (abst xs' m') 

-- Convert lam' to lam
erasure a@(Lam' (Abst xs m)) =
  do m' <- erasure m
     let ns = countVar xs m'
         xs' = zip xs ns
         ws = evars m' \\ xs
     return $ ELam ws (abst xs' m') 

erasure a@(LamDict (Abst xs m)) =
  do m' <- erasure m
     let ns = countVar xs m'
         xs' = zip xs ns
         ws = evars m' \\ xs
     return $ ELam ws (abst xs' m') 

erasure (WithType ann t) = erasure ann

erasure (LamDep (Abst ys m)) =
  do m' <- erasure m
     let ns = countVar ys m'
         xs' = zip ys ns
         ws = evars m' \\ ys
     return $ ELam ws (abst xs' m') 

erasure (LamDepTy (Abst ys m)) =
  do m' <- erasure m
     let ns = countVar ys m'
         xs' = zip ys ns
         ws = evars m' \\ ys
     return $ ELam ws (abst xs' m') 


erasure (LamDep' (Abst ys m)) =
  do m' <- erasure m
     let ns = countVar ys m'
         xs' = zip ys ns
         ws = evars m' \\ ys
     return $ ELam ws (abst xs' m') 

erasure (LamTm bd) =
  open bd $ \ xs m -> erasure m

erasure (LamType bd) =
  open bd $ \ xs m -> erasure m

erasure (Lift t) =
  do t' <- erasure t
     let fvs = evars t'
     return (ELift fvs t')

erasure (Force t) = EForce <$> erasure t
erasure (Force' t) = EForce <$> erasure t

erasure (UnBox) = return EUnBox

erasure (Reverse) = return EReverse
erasure (Controlled) = return EControlled
erasure (WithComputed) = return EWithComputed
erasure (Dynlift) = return EDynlift

erasure a@(Box) = return EBox
erasure a@(ExBox) = return EExBox

erasure (Let m bd) = open bd $ \ vs b -> 
  do m' <- erasure m

     b' <- erasure b
     let n:[] = countVar [vs] b'
     return $ ELet m' (abst (vs, n) b') 
     
erasure (LetPair m bd) = open bd $ \ xs b ->
  do m' <- erasure m
     b' <- erasure b
     let ns = countVar xs b'
         xs' = zip xs ns
     return $ ELetPair m' (abst xs' b') 

erasure (LetPat m bd) = open bd $ \ pa b ->
  case pa of
    PApp kid args ->
      do b' <- erasure b
         m' <- erasure m
         funP <- lookupId kid
         let ty = classifier funP
         args' <- helper ty args b b'
         return $ ELetPat m' (abst (EPApp kid args') b')
  where
        helper (Mod (Abst _ t)) args b b' = helper t args b b'
        -- The only way a data constructor can have a Pi type
        -- is when it is an existential type.
    
        helper (Pi bds t) args b b' | not (isKind t) =
          open bds $ \ ys m ->
          do let (vs, res) = splitAt (length ys) args
                 vs1 = map (\ (Right x) -> x) vs
                 ns = countVar vs1 b'
                 vs2 = zip vs1 ns
             vs' <- helper m res b b'
             return $ vs2++vs'

        helper (Forall bds t) args b b' =
          open bds $ \ ys m ->
          let (vs, res) = splitAt (length ys) args in
          do checkExplicit vs b
             helper m res b b'

        helper (Arrow t1 t2) (x:xs) b b' =
          do vs' <- helper t2 xs b b'
             let (Right x') = x
                 n:[] = countVar [x'] b'
             return $ (x', n):vs'

        helper (Imply [t1] t2) (x:xs) b b' =
          do vs' <- helper t2 xs b b'
             let (Right x') = x
                 n:[] = countVar [x'] b'
             return $ (x', n):vs'

        helper (Imply (t1:ts) t2) (x:xs) b b' =
          do vs' <- helper (Imply ts t2) xs b b'
             let (Right x') = x
                 n:[] = countVar [x'] b'
             return $ (x', n):vs'

        helper a [] b b' = return []
        helper a _ b b' = error $ "from helper erasure-letPat"


erasure l@(Case e (B br)) =
  do e' <- erasure e
     brs <- mapM helper br
     return $ ECase e' (EB brs)
       where helper bd = open bd $ \ p m ->
               case p of
                 PApp kid args ->
                   do funP <- lookupId kid
                      let ty = classifier funP
                      m' <- erasure m
                      args' <- helper2 ty args m m' 
                      return (abst (EPApp kid args') m')
             helper2 (Mod (Abst _ t)) args b b' = helper2 t args b b'         
             -- The only way a data constructor can have a Pi type
             -- is when it is an existential type. 
                      
             helper2 (Pi bds t) args ann m' | not (isKind t) =
               open bds $ \ ys m ->
               do let (vs, res) = splitAt (length ys) args
                      vs1 = map (\ (Right x) -> x) vs
                      ns = countVar vs1 m'
                      vs2 = zip vs1 ns
                  vs' <- helper2 m res ann m'
                  return $ vs2++vs'

             helper2 (Forall bds t) args ann m' =
               open bds $ \ ys m ->
               let (vs, res) = splitAt (length ys) args
               in do checkExplicit vs ann
                     helper2 m res ann m'
                  
             helper2 (Arrow t1 t2) (x:xs) ann m' =
               do vs' <- helper2 t2 xs ann m'
                  let (Right x') = x
                      n:[] = countVar [x'] m'
                  return $ (x', n):vs'
             helper2 (Imply [t1] t2) (x:xs) ann m' =
               do vs' <- helper2 t2 xs ann m'
                  let (Right x') = x
                      n:[] = countVar [x'] m'
                  return $ (x', n):vs'

             helper2 (Imply (t1:ts) t2) (x:xs) ann m' =
               do vs' <- helper2 (Imply ts t2) xs ann m'
                  let (Right x') = x
                      n:[] = countVar [x'] m'
                  return $ (x', n):vs'
                  
             helper2 a [] _ _ = return []
             helper2 a b _ _ = error $ "from helper2 flag-erasure-case" ++ (show $ disp a)

erasure a = error $ "from erasure: " ++ (show $ disp a)

-- | Check if any irrelavant variables in the list is used explicitly in an expression.
checkExplicit :: [Either (NoBind Exp) Variable] -> Exp -> TCMonad ()
checkExplicit [] ann = return ()
checkExplicit (Left a :xs) ann = checkExplicit xs ann
checkExplicit (Right x :xs) ann =
  do when (isExplicit x ann) $ throwError $ ImplicitCase x ann
     checkExplicit xs ann

-- | Count the number of occurrences for a list of variables. It is only
-- an over-approximation, as there is no way to predict the real uses due to
-- the way closure interacts with recursion and case branching. 
countVar :: [Variable] -> EExp -> [Integer]
countVar xs e =
  map (helper e) xs
  where helper :: EExp -> Variable -> Integer
        helper (EVar y) x | x == y = 1
                          | otherwise = 0
        helper (EConst _) x = 0
        helper (EBase _) x = 0
        helper (ELBase _) x = 0
        helper EUnBox x = 0
        helper EReverse x = 0
        helper EControlled x = 0
        helper EWithComputed x = 0
        helper EDynlift x = 0
        helper EBox x = 0
        helper EExBox x = 0
        helper EStar x = 0
        helper EUnit x = 0
        helper (EApp t1 t2) x = helper t1 x + helper t2 x
        helper (EPair t1 t2) x = helper t1 x + helper t2 x
        helper (ETensor t1 t2) x = helper t1 x + helper t2 x
        helper (EArrow t1 t2) x = helper t1 x + helper t2 x
        helper (ELam _ (Abst _ e)) x = (helper e x)
        helper (ELift _ e) x = (helper e x)
        helper (EForce e) x = helper e x
        helper (ELet e (Abst _ e2)) x =
          helper e x + helper e2 x
        helper (ELetPair e (Abst _ e2)) x =
          helper e x + helper e2 x
        helper (ELetPat e (Abst _ e2)) x =
          helper e x + helper e2 x
        helper (ECase e (EB brs)) x =
          helper e x + helper2 brs x
        helper2 :: [Bind EPattern EExp] -> Variable -> Integer  
        helper2 brs x =
          maximum $ map (\ b -> open b $ \ _ m -> helper m x) brs

