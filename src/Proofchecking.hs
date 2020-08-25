{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
-- | This module implements a proof checker that checks the results
-- produced from the elaborator ("Typechecking" module). The proof checker
-- is also bi-directional. 
  
module Proofchecking (proofCheck) where


import Syntax
import SyntacticOperations
import TCMonad
import Normalize
import TypeError
import Unification
import ModeResolve
import Substitution
import Utils

import Nominal
import Control.Monad.Except
import qualified Data.MultiSet as S
import qualified Data.Map as Map
import Data.Map (Map)
import Debug.Trace


-- | Check an expression against a type. 
-- The flag indicates if it is a parameter type checking.
-- Here parameter type checking means using shape of the context to
-- type check a parameter term.

-- Currently we only use proofCheck to check programs.
proofCheck :: Bool -> Exp -> Exp -> TCMonad ()


-- | Infer a type for an expression. 
proofInfer :: Bool -> Exp -> TCMonad Exp



proofInfer True (LBase kid) =
  lookupId kid >>= \ x -> return $ (classifier x)
proofInfer True (Base kid) =
  lookupId kid >>= \ x -> return $ (classifier x)
proofInfer True Unit = return Set
proofInfer True Set = return Sort
proofInfer True ty@(Arrow t1 t2) =
  do a1 <- proofInfer True t1
     a2 <- proofInfer True t2
     case (a1, a2) of
       (Set, Set) -> return Set
       (Set, Sort) -> return Sort
       (Sort, Sort) -> return Sort
       (b1, b2) -> throwError (NotEq ty Set (Arrow b1 b2))
 
proofInfer True ty@(Circ t1 t2 m) =
  do a1 <- proofInfer True t1
     a2 <- proofInfer True t2
     case (a1, a2) of
       (Set, Set) -> return Set
       (b1, b2) -> throwError (NotEq ty Set (Circ b1 b2 m))

proofInfer True a@(Imply [] t) =
  do ty <- proofInfer True t
     case ty of
       Set -> return Set
       _ -> throwError (NotEq t Set ty)
       
proofInfer True a@(Imply (x:xs) t) =
  do ty <- proofInfer True x
     updateParamInfo [x]
     case ty of
       Set -> proofInfer True (Imply xs t)
       _ -> throwError (NotEq x Set ty)

proofInfer True (Bang ty _) =
  do a <- proofInfer True ty
     case a of
       Set -> return Set
       b -> throwError (NotEq ty Set b)

proofInfer True ty@(Tensor t1 t2) =
  do a1 <- proofInfer True t1
     a2 <- proofInfer True t2
     case (a1, a2) of
       (Set, Set) -> return Set
       (b1, b2) -> throwError (NotEq ty Set (Tensor b1 b2))

proofInfer True ty@(Exists bd t) =
  do a <- proofInfer True t
     case a of
       Set ->
         open bd $ \ x m ->
         do addVar x t
            tm <- proofInfer True m
            removeVar x
            case tm of
              Set -> return Set
              _ -> throwError (NotEq m Set tm)
       _ -> throwError (NotEq t Set a)
       
proofInfer True ty@(Pi bd t) =
  do a <- proofInfer True t
     case a of
       Set ->
         open bd $ \ xs m ->
         do mapM_ (\ x -> addVar x t) xs
            tm <- proofInfer True m
            mapM_ removeVar xs
            case tm of
              Set -> return Set
              _ -> throwError (NotEq m Set tm)
       Sort ->
         open bd $ \ xs m ->
         do mapM_ (\ x -> addVar x t) xs
            tm <- proofInfer True m
            mapM_ removeVar xs
            case tm of
              Set -> return Set
              _ -> throwError (NotEq m Set tm)
       _ -> throwError (NotEq t Set a)

proofInfer True ty@(Forall bd t) =
  do a <- proofInfer True t
     case a of
       Set ->
         open bd $ \ xs m ->
         do mapM_ (\ x -> addVar x t) xs
            tm <- proofInfer True m
            mapM_ removeVar xs
            case tm of
              Set -> return Set
       Sort ->
         open bd $ \ xs m ->
         do mapM_ (\ x -> addVar x t) xs
            tm <- proofInfer True m
            mapM_ removeVar xs
            case tm of
              Set -> return Set


proofInfer flag a@(Var x) =
  do (t, _) <- lookupVar x
     if flag then shape t 
       else
       do updateCount x
          return t

-- proofInfer flag a@(MetaVar x) =
--   do (t, _) <- lookupVar x
--      if flag then shape t 
--        else
--        do updateCount x
--           return t


proofInfer flag a@(Const kid) =
  do funPac <- lookupId kid
     let cl = classifier funPac
     case cl of
       (Mod (Abst _ cl')) -> 
         if flag then shape cl' else return cl'
       _ -> if flag then shape cl else return cl

  
proofInfer False a@(AppDep t1 t2) =
  do t' <- proofInfer False t1
     case t' of
       b@(Pi bd ty) -> open bd $ \ xs m ->
         do proofCheck False t2 ty
            -- let t2' = toEigen t2
            t2' <- shape t2
            m' <- betaNormalize (apply [(head xs, t2')] m) 
            if null (tail xs)
              then return m'
              else return $ Pi (abst (tail xs) m') ty
       b@(PiImp bd ty) -> open bd $ \ xs m ->
         do proofCheck False t2 ty
            -- let t2' = toEigen t2
            t2' <- shape t2
            m' <- betaNormalize (apply [(head xs, t2')] m) 
            if null (tail xs)
              then return m'
              else return $ PiImp (abst (tail xs) m') ty  


proofInfer flag a@(AppDepInt t1 t2) =
  do t' <- proofInfer True t1
     case t' of
       b@(PiInt bd ty) -> open bd $ \ xs m ->
         do proofCheck True t2 ty
            -- let t2' = toEigen t2
            m' <- betaNormalize (apply [(head xs, t2)] m)
            if null (tail xs)
              then return m'
              else return $ PiInt (abst (tail xs) m') ty  

proofInfer flag a@(AppDepTy t1 t2) =
  do t' <- proofInfer flag t1
     case t' of
       (Arrow ty1 ty2) | isKind ty1 ->
         do proofCheck True t2 ty1
            return ty2
       b@(Pi bd ty) | not flag -> open bd $ \ xs m ->
         do proofCheck True t2 ty
            -- let t2' = toEigen t2
            m' <- betaNormalize (apply [(head xs, t2)] m) 
            if null (tail xs)
              then return m'
              else return $ Pi (abst (tail xs) m') ty
       b@(PiImp bd ty) | not flag -> open bd $ \ xs m ->
         do proofCheck True t2 ty
            -- let t2' = toEigen t2
            m' <- betaNormalize (apply [(head xs, t2)] m) 
            if null (tail xs)
              then return m'
              else return $ PiImp (abst (tail xs) m') ty  
       b@(PiInt bd ty) | flag -> open bd $ \ xs m ->
         do proofCheck True t2 ty
            -- let t2' = toEigen t2
            m' <- betaNormalize (apply [(head xs, t2)] m) >>= shape
            if null (tail xs)
              then return m'
              else return $ PiInt (abst (tail xs) m') ty


proofInfer False a@(App t1 t2) =
  do t' <- proofInfer False t1
     case t' of
       Arrow ty m -> proofCheck False t2 ty >> return m
       b -> throwError $ ArrowErr t1 b


proofInfer flag a@(AppP t1 t2) =
  do t' <- proofInfer True t1
     case t' of
       Arrow ty m | isKind t' -> proofCheck True t2 ty >> return m
       ArrowP ty m -> proofCheck True t2 ty >> return m
       b@(Pi bd ty) | isKind b -> open bd $ \ xs m ->
         do
            proofCheck True t2 ty
            -- let t2' = toEigen t2
            m' <- betaNormalize (apply [(head xs, t2)]  m) 
            if null (tail xs)
              then return m'
              else return $ Pi (abst (tail xs) m') ty  
       b -> throwError $ ArrowErr t1 b

proofInfer flag a@(AppDict t1 t2) =
  do t' <- proofInfer flag t1
     case t' of
       Imply (ty:[]) m -> proofCheck True t2 ty >> return m
       Imply (ty:res) m -> proofCheck True t2 ty >> return (Imply res m)
       b -> throwError $ ArrowErr t1 b

proofInfer flag a@(AppType t1 t2) =
  do t' <- proofInfer flag t1
     case erasePos t' of
       b@(Forall bd kd) | isKind kd -> 
             open bd $ \ xs m ->
              do -- let t2' = toEigen t2
                 proofCheck True t2 kd
                 m' <- betaNormalize (apply [(head xs,  t2)] m)
                 m'' <- if flag then shape m' else return m'
                 if null (tail xs)
                   then return m''
                   else return $ Forall (abst (tail xs) m'') kd
       b@(Mod (Abst _ (Forall bd kd))) | isKind kd -> 
             open bd $ \ xs m ->
              do -- let t2' = toEigen t2
                 proofCheck True t2 kd
                 m' <- betaNormalize (apply [(head xs,  t2)] m)
                 m'' <- if flag then shape m' else return m'
                 if null (tail xs)
                   then return m''
                   else return $ Forall (abst (tail xs) m'') kd
                        
       b -> error $ "from proofInfer:" ++ show b
proofInfer flag a@(AppTm t1 t2) =
  do t' <- proofInfer flag t1
     case erasePos t' of
       b@(Forall bd kd) -> 
             open bd $ \ xs m ->
              do -- let t2' = toEigen t2
                 proofCheck True t2 kd
                 m' <- betaNormalize (apply [(head xs,  t2)] m)
                 if null (tail xs)
                   then return m'
                   else return $ Forall (abst (tail xs) m') kd

proofInfer flag Reverse =
  freshNames ["a", "b"] $ \ [a, b] ->
  let va = Var a
      vb = Var b
      simpClass = Id "Simple"
      t1 = Arrow (Circ va vb identityMod) (Circ vb va identityMod)
      t1' = Imply [AppP (Base simpClass) va , AppP (Base simpClass) vb] t1
      ty = Forall (abst [a, b] t1') Set
  in return ty

proofInfer flag Dynlift =
  let ty = Bang (Arrow (LBase (Id "Bit")) (Base (Id "Bool")))
           (M (BConst False) (BConst False) (BConst False))
  in return ty

proofInfer flag a@(WithComputed) =
  freshNames ["a", "b", "c", "d", "e", "x", "y"] $ \ xs@[a, b, c, d, e, x, y] ->
  let vxs@[va, vb, vc, vd, ve, vx, vy] = map Var xs
      simpClass = Id "Simple"
      mod1 = M (BConst True) (BConst False) (BConst True)
      mod2 = M (BConst True) (BVar x) (BVar y)
      t1 = Arrow (Circ va (Tensor vb ve) mod1)
           (Arrow (Circ (Tensor vb vc) (Tensor vb vd) mod2)
            (Circ (Tensor va vc) (Tensor va vd) mod2))
      t1' = Imply (map (AppP (Base simpClass)) (take 5 vxs)) t1
      ty = Forall (abst [a, b,c,d,e] t1') Set
      ty' = abstractMode ty
  in return ty'

proofInfer flag a@(Controlled) =
  freshNames ["a", "b", "s"] $ \ [a, b, s'] ->
  let va = Var a
      s = Var s'
      vb = Var b
      simpClass = Id "Simple"
      t1 = Arrow (Circ va vb identityMod) (Bang (Arrow va (Arrow s (Tensor vb s))) identityMod)
      t1' = Imply [AppP (Base simpClass) s, AppP (Base simpClass) va , AppP (Base simpClass) vb] t1
      ty = Forall (abst [a, b, s'] t1') Set
      ty' = abstractMode ty
  in return ty'

proofInfer flag UnBox =
  freshNames ["a", "b"] $ \ [a, b] ->
  let va = Var a
      vb = Var b
      simpClass = Id "Simple"
      t1 = Arrow (Circ va vb identityMod) (Bang (Arrow va vb) identityMod)
      t1' = Imply [AppP (Base simpClass) va , AppP (Base simpClass) vb] t1
      ty = Forall (abst [a, b] t1') Set
  in return ty

proofInfer flag t@(Box) = freshNames ["a", "b"] $ \ [a, b] ->
  do let va = Var a
         vb = Var b
         simpClass = Id "Simple"
         t1 = Arrow (Bang (Arrow va vb) identityMod) (Circ va vb identityMod)
         t1' = Imply [(AppP (Base simpClass) va), (AppP (Base simpClass) vb)] t1
         boxType = Pi (abst [a] (Forall (abst [b] t1') Set)) Set
     return boxType

proofInfer flag t@(ExBox) =
  freshNames ["a", "b", "p", "n"] $ \ [a, b, p, n] ->
  do let va = Var a
         vb = Var b
         vp = Var p
         vn = Var n
         kp = Arrow vb Set
         simpClass = Id "Simple"
         paramClass = Id "Parameter"
         simpA = AppP (Base simpClass) va
         paramB = AppP (Base paramClass) vb
         simpP = AppP (Base simpClass) (AppP vp vn)
         t1Output = Exists (abst n (AppP vp vn)) (vb)
         t1 = Bang (Arrow va t1Output) identityMod
         output = Exists (abst n $ Imply [simpP] (Circ va (AppP vp vn) identityMod)) (vb)
         beforePi = Arrow t1 output
         r = Pi (abst [a] $
                 Forall (abst [b] (Imply [simpA, paramB] $ Pi (abst [p] $ beforePi) kp)) Set) Set
     return r

proofInfer flag (Star) = return Unit
       
proofInfer False a@(Force t) =
  do ty <- proofInfer False t
     case ty of
       Bang ty' _ -> return ty'
       b -> throwError $ BangErr t b 

proofInfer flag a@(ForceP t) =
  do ty <- proofInfer True t
     case ty of
       Bang ty' _ -> shape ty'
       b -> throwError $ BangErr t b 

proofInfer flag a@(Pair t1 t2) =
  do ty1 <- proofInfer flag t1 
     ty2 <- proofInfer flag t2
     return $ (Tensor ty1 ty2)

proofInfer flag (Pos p e) = 
  proofInfer flag e `catchError` \ e -> throwError $ collapsePos p e

proofInfer False (LamAnn ty (Abst xs m)) =
  do if isKind ty then proofCheck True ty Sort else proofCheck True ty Set
     -- let ty1 = toEigen ty
     mapM_ (\ x -> addVar x (erasePos ty)) xs
     ty' <- proofInfer False m
     p <- isParam ty
     foldM (helper p ty) ty' xs
       where helper p ty1 ty' x =
               if x `S.member` getVars All ty'
               then
                 do removeVar x
                    return $ Pi (abst [x] ty') ty1
               else
                 do when (not p) $ checkUsage x m >> return ()
                    removeVar x
                    return (Arrow ty1 ty')


proofInfer flag (WithType a t) =
  do proofCheck True t Set
     -- let t' = toEigen t
     proofCheck False a t
     return t

proofInfer flag e = throwError $ Unhandle e

proofCheck flag (Pos p e) t = 
  proofCheck flag e t `catchError` \ e -> throwError $ collapsePos p e

proofCheck flag e (Mod (Abst _ t)) = 
  proofCheck flag e t

proofCheck False a@(Lam bd) (Arrow t1 t2) = open bd $ \ xs m ->
  do addVar (head xs) t1
     proofCheck False (if (null $ tail xs) then m else (Lam (abst (tail xs) m))) t2
     checkUsage (head xs) m

proofCheck True a@(LamP bd) (ArrowP t1 t2) = open bd $ \ xs m ->
  do addVar (head xs) t1
     proofCheck True (if (null $ tail xs) then m else (LamP (abst (tail xs) m))) t2

proofCheck True a@(LamP bd) b@(Arrow t1 t2) | isKind b = open bd $ \ xs m ->
  do addVar (head xs) t1
     proofCheck True (if (null $ tail xs) then m else (LamP (abst (tail xs) m))) t2

proofCheck flag a@(LamDict bd) (Imply (t1:[]) t2) = open bd $ \ xs m ->
  do addVar (head xs) t1
     updateParamInfo [t1]
     proofCheck flag (if (null $ tail xs) then m else (LamDict (abst (tail xs) m))) t2

proofCheck flag a@(LamDict bd) (Imply (t1:ts) t2) = open bd $ \ xs m ->
  do addVar (head xs) t1
     updateParamInfo [t1]
     proofCheck flag (if (null $ tail xs) then m else (LamDict (abst (tail xs) m))) (Imply ts t2)


proofCheck False a@(LamDep bd1) exp@(Pi bd2 ty) =
  handleAbs False LamDep Pi bd1 bd2 ty True

proofCheck False a@(LamDep bd1) exp@(PiImp bd2 ty) =
  handleAbs False LamDep PiImp bd1 bd2 ty False

proofCheck True a@(LamDepInt bd1) exp@(PiInt bd2 ty) =
  handleAbs True LamDepInt PiInt bd1 bd2 ty False

proofCheck True a@(LamDepTy bd1) exp@(PiInt bd2 ty) =
  handleAbs True LamDepTy PiInt bd1 bd2 ty False

proofCheck False a@(LamDepTy bd1) exp@(Pi bd2 ty) =
  handleAbs False LamDepTy Pi bd1 bd2 ty False

proofCheck False a@(LamDepTy bd1) exp@(PiImp bd2 ty) =
  handleAbs False LamDepTy PiImp bd1 bd2 ty False

proofCheck flag (LamTm bd1) exp@(Forall bd2 ty) =
  handleAbs flag LamTm Forall bd1 bd2 ty False

proofCheck flag (LamType bd1) exp@(Forall bd2 ty) =
  handleAbs flag LamType Forall bd1 bd2 ty False

proofCheck flag (Lift m) (Bang t _) =
  do checkParamCxt m
     proofCheck flag m t

proofCheck flag a@(Pair t1 t2) (Exists p ty)=
  do proofCheck flag t1 ty
     open p $ \ x t ->
       do -- let --vars = S.toList $ getVars NoEigen t1
              -- sub1 = zip vars (map EigenVar vars)
              -- t1Eigen = apply sub1 t1
          ts <- shape t1
          let t' = apply [(x, ts)] t
          proofCheck flag t2 t'

proofCheck flag (Let m bd) goal = open bd $ \ x t ->
  do t' <- proofInfer flag m
     -- let -- vs = S.toList $ getVars NoEigen m
         -- su = zip vs (map EigenVar vs)
     m'' <- shape m
     addVarDef x t' m''
     r <- proofCheck flag t goal
     when (not flag) $ checkUsage x t
     removeVar x
     return r

proofCheck flag (LetPair m bd) goal = -- open bd $ \ xs t ->
  do t' <- proofInfer flag m
     case t' of
       Exists p t1 ->
         open p $ \ z t2 ->
         open bd $ \ [x, y] t ->
         do addVar x t1
            let t2' = apply [(z, Var x)] t2
            addVar y t2'
            proofCheck flag t goal
            when (not flag) $ checkUsage x t >> checkUsage y t 
            removeVar x
            removeVar y
       _ -> open bd $ \ xs t ->
         case unTensor (length xs) t' of
           Just ts ->
             do let env = zip xs ts
                mapM (\ (x, y) -> addVar x y) env
                res <- proofCheck flag t goal
                when (not flag) $ mapM_ (\x -> checkUsage x t) xs
                mapM removeVar xs
                return res
           Nothing -> throwError $ TensorErr (length xs) m t'
 
proofCheck flag a@(LetPat m bd) goal  = open bd $ \ (PApp kid args) n ->
  do tt <- proofInfer flag m
     funPac <- lookupId kid
     let dt = classifier funPac
     semi <- isSemiSimple kid
     (head, vs) <- inst dt args 
--     let matchEigen = isEigenVar m
         -- eSub = map (\ x -> (x, EigenVar x)) eigen
  --       isDpm = isSemi || matchEigen
     (unifRes, sub') <- dependentUnif semi head tt
     ss <- getSubst
     case unifRes of
       UnifError -> throwError $ (PUnifErr head tt m a)
       DUnifError -> throwError $ (PUnifErr head tt m a)
       Success -> do
            sub1 <- makeSub m sub' $ foldl (\ x y ->
                                           case y of
                                             Right u -> App x (Var u)
                                             Left (NoBind u) -> App x u
                                         ) (Const kid) vs
                         
                    
            let sub'' = sub1 `mergeSub` ss
            updateSubst sub''
            let goal' = substitute sub'' goal
            proofCheck flag n goal'
            subb <- getSubst
            mapM_ (\ v ->
                    case v of
                      Right x ->
                        do when (not flag) $ checkUsage x n 
                           removeVar x
                      _ -> return ()
                  ) vs
            -- b <- varDep (erasePos m) goal
            -- let isDpm = ((fst semi) && (snd semi /= Nothing)) || b
            -- when isDpm $ updateSubst ss
            -- when (not isDpm) $ updateSubst subb'
            updateSubst ss
            
       where makeSub (Var x) s u =
               do u' <- shape $ substitute s u
                  return $ s `Map.union` Map.fromList [(x, u')]
             makeSub (Pos p x) s u = makeSub x s u
             makeSub a s u = return s
             varDep (Var x) goal = isDpmVar x goal
             varDep _ _ = return False

proofCheck flag a@(Case tm (B brs)) goal =
  do t <- proofInfer flag tm
     let t' = flatten t 
     when (t' == Nothing) $ throwError (DataErr t tm)
     let Just (Right id, _) = t'
     id' <- lookupId id
     case identification id' of
          DataType Simple _ _ -> throwError (DataErr t tm)
          DataType _ _ _ -> return ()         
     updateCountWith (\ x -> enterCase x id)
     checkBrs t brs goal
     updateCountWith exitCase
  where 
        makeSub (Var x) s u =
          do u' <- shape $ substitute s u
             return $ s `Map.union` Map.fromList [(x, u')]
        makeSub (Pos p x) s u = makeSub x s u
        makeSub a s u = return s
        varDep (Var x) goal = isDpmVar x goal
        varDep _ _ = return False

        checkBrs t pbs goal = 
          mapM (checkBr t goal) pbs

        checkBr t goal pb = open pb $ \ (PApp kid args) m ->
          do funPac <- lookupId kid
             let dt = classifier funPac
             updateCountWith (\ x -> nextCase x kid)
             semi <- isSemiSimple kid
             (head, vs) <- inst dt args
             --let matchEigen = isEigenVar tm
                 --eSub = map (\ x -> (x, EigenVar x)) eigen
               --  isDpm = isSemi || matchEigen
             ss <- getSubst
             (unifRes, sub') <- dependentUnif semi head t
             case unifRes of
               DUnifError -> throwError $ (PUnifErr head t tm a)
               UnifError -> throwError $ (PUnifErr head t tm a)
               Success -> do
                 sub1 <- makeSub tm sub' $ foldl (\ x y ->
                                               case y of
                                                 Right u -> App x (Var u)
                                                 Left (NoBind u) -> App x u
                                             ) (Const kid) vs
                     
                 let sub'' = sub1 `mergeSub` ss
                 updateSubst sub''
                 let goal' = substitute sub'' goal
                 proofCheck flag m goal'
                 subb <- getSubst
                 -- let subb' = case erasePos m of
                 --               Var y -> Map.delete y subb  
                 --               _ -> subb                 
                 mapM_ (\ v ->
                         case v of
                           Right x ->
                             do when (not flag) $ checkUsage x m 
                                removeVar x
                           _ -> return ()
                       ) vs
                 -- b <- varDep (erasePos tm) goal
                 -- let isDpm = ((fst semi) && (snd semi /= Nothing)) || b
                 -- when isDpm $ trace ("dpm:"++ show (dispRaw ss)) $ updateSubst ss
                 -- when (not isDpm) $ trace ("not dpm:"++ show (dispRaw subb')) $ updateSubst subb'
                 updateSubst ss
               a -> error $ show a
                 -- when isDpm $ updateSubst ss

proofCheck flag a goal =
  do t <- proofInfer flag a
     t1 <- updateWithSubst t
     goal1 <- updateWithSubst goal
     goal' <- normalize goal1
     t' <- normalize t1
     ss <- getSubst
     when (not (noModEq (erasePos goal') (erasePos t'))) $
       throwError (AppendSub ss $ NotEq a goal' t')

-- | Unification for dependent pattern pattern matching.

-- Technical: in the following, "return $ runUnify head t" can be replaced by
-- "if head == t then return $ Just Map.empty else return Nothing", as
 -- these two cases are not dependent pattern matching.
dependentUnif :: (Bool , Maybe Int) -> Exp -> Exp -> TCMonad (UnifResult,Subst)
dependentUnif (isDpm, index) head t =
  if not isDpm then
    if head == t then return (Success, Map.empty)
    else return (UnifError, Map.empty)
    -- do let (res, (sub, _)) = runUnify GEq head t
    --    return (res, sub)
  else case index of
         Nothing ->
            if head == t then return (Success, Map.empty)
            else return (UnifError, Map.empty)
           -- let (res, (sub, _)) = runUnify GEq head t
           -- return (res, sub)
         Just i -> return $ runDUnify head t
            -- u@(res, subst) <- 
            -- case res of
            --   UnifError -> return u
            --   Success 
           -- case flatten t of
           --  Just (Right h, args) -> 
           --    let (bs, a:as) = splitAt i args
           --        vars = S.toList $ getVars OnlyEigen a
           --        eSub = zip vars (map EigenVar vars)
           --        a' = unEigenBound vars a
           --        t' = foldl AppP (LBase h) (bs++(a':as))
           --        u@(res, (subst, bss)) =  runUnify GEq head t'
           --    in case res of
           --         UnifError -> return u
           --         Success -> 
           --           helper subst vars eSub bss
           -- _ -> throwError $ UnifErr head t
--  where -- change relavent variables back into eigenvariables after dependent pattern-matching. 
        -- helper subst (v:vars) eSub bs =
        --   let subst' = Map.mapWithKey (\ k val -> if k == v then toEigen val else val) subst
        --       subst'' = Map.map (\ val -> apply eSub val) subst'
        --   in helper subst'' vars eSub bs
        -- helper subst [] eSub bs = return (Success, (subst, bs)) 

-- | Check lambda abstractions against a type. The argument /fl/ is to indicate
-- whether or not to check usage. 
handleAbs ::  Bool -> (Bind [Variable] Exp -> Exp) ->
                      (Bind [Variable] Exp -> Exp -> Exp) ->
                      Bind [Variable] Exp -> Bind [Variable] Exp -> Exp -> Bool -> TCMonad ()
handleAbs flag lam prefix bd1 bd2 ty fl =
  open bd1 $ \ xs m -> open bd2 $ \ ys b ->
  if length xs <= length ys
  then do let sub = zip ys (map Var xs)
              b' = apply sub b
              --sub2 = zip xs (map EigenVar xs)
              (vs, rs) = splitAt (length xs) ys
              -- m' = apply sub2 m
          mapM_ (\ x -> addVar x ty) xs
          proofCheck flag m (if null rs then b'
                              else prefix (abst rs b') ty)
          when fl $ mapM_ (\ x -> checkUsage x m) xs   
          mapM_ removeVar xs
  else 
    do let sub = zip ys (map Var xs)
           b' = apply sub b
           (vs, rs) = splitAt (length ys) xs
           -- sub2 = zip xs $ take (length ys) (map EigenVar xs)
           -- m' = apply sub2 m
       mapM_ (\ x -> addVar x ty) vs
       proofCheck flag (if null rs then m else lam (abst rs m)) b'
       when fl $ mapM_ (\ x -> checkUsage x m) vs
       mapM_ removeVar vs


-- | Extend the typing environment according to the information available
-- in the pattern expression.
inst ::  Exp -> [Either (NoBind Exp) Variable] ->
         TCMonad (Exp, [Either (NoBind Exp) Variable])
inst (Mod (Abst _ t)) xs = inst t xs         
inst (Arrow t1 t2) (Right x : xs) =
  do addVar x t1
     (h, vs) <- inst t2 xs 
     return (h, Right x : vs)

inst (Imply [t1] t2) (Right x : xs) =
  do addVar x t1
     (h, vs) <- inst t2 xs 
     return (h, Right x : vs)

inst (Imply (t1:ts) t2) (Right x : xs) =
  do addVar x t1
     (h, vs) <- inst (Imply ts t2) xs 
     return (h, Right x : vs)

inst (Pi bd t) (Right x:xs) | not (isKind t) = open bd $ \ ys t' ->
  do let y = head ys
         t'' = apply [(y, Var x)] t' 
     if null (tail ys)
       then do addVar x t
               (h, xs') <- inst t'' xs  
               return (h, Right x:xs')
       else do addVar x t
               (h, xs') <- inst (Pi (abst (tail ys) t'') t) xs 
               return (h, Right x:xs')

inst (Forall bd t) (Right x:xs)  = open bd $ \ ys t' ->
  do let y = head ys
         t'' = apply [(y, Var x)] t'
     if null (tail ys)
       then do addVar x t
               (h, xs') <- inst t'' xs 
               return (h, Right x:xs')
       else do addVar x t
               (h, xs') <- inst (Forall (abst (tail ys) t'') t) xs 
               return (h, Right x:xs')

inst (Forall bd t) (Left (NoBind x):xs) = open bd $ \ ys t' ->
  do let y = head ys
         -- fvs = S.toList $ getVars NoEigen x
         -- fvs' = map EigenVar fvs
         -- sub = zip fvs fvs'
         -- x' = apply sub x
         t'' = apply [(y, x)] t' 
     if null (tail ys)
       then do (h, xs') <- inst t'' xs 
               return (h, Left (NoBind x):xs')
       else do (h, xs') <- inst (Forall (abst (tail ys) t'') t) xs 
               return (h, Left (NoBind x):xs')

inst t [] = return (t, [])            

