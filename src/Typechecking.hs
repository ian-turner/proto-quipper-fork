{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
-- | This module implements a bi-directional algorithm for elaborating
-- the surface language into the core language. The elaborated programs
-- will be checked by the "Proofchecking" module.
-- The elaboration aims for soundness, i.e.,
-- if the elaboration is successful, then it shoud past
-- the proof-checker. Otherwise it
-- means there is a bug in the elaboration. 

 
module Typechecking (typeCheck, typeInfer) where

import Syntax
import SyntacticOperations
import TCMonad
import TypeError
import Utils
import Normalize
import Substitution
import TypeClass
import Unification
import ModeResolve

import Nominal
import qualified Data.MultiSet as S
import qualified Data.Map as Map
import Data.Map (Map)
import Debug.Trace
import Control.Monad.Except
import Control.Monad.State
import Text.PrettyPrint
import Prelude hiding((<>))

-- | Check an expression against a type under a modality assumption,
-- retun the elaborated term and type.
-- When the boolean flag is true, it means
-- it is during kinding or sorting.
-- Otherwise it is during type checking.
-- For simplicity, we do not allow the use 
-- of lambda, box, unbox, reverse, dynlift, runCirc, existsBox in types.


typeCheck :: Bool -> Exp -> Exp -> Modality -> TCMonad (Exp, Exp)

-- | Infer a type, a modality from a term. 
typeInfer :: Bool -> Exp -> TCMonad (Exp, Exp, Modality)

typeInfer flag (Pos p e) = do
  (ty, ann, m) <- typeInfer flag e `catchError`
                  \e -> throwError $ addErrPos p e
  return (ty, (Pos p ann), m)

typeInfer flag Type = return (Sort, Type, identityMod)

typeInfer flag a@(Base kid) =
  lookupId kid >>= \x -> return (classifier x, a, identityMod)

typeInfer flag a@(LBase kid) =
  lookupId kid >>= \x -> return (classifier x, a, identityMod)

typeInfer flag a@(Var x) = do
  (t, _) <- lookupVar x
  if flag
    then do
      t' <- shape t `catchError`
            \ e -> throwError $ AddDoc
                   (text "for the expression" $$ (nest 2 $ disp t)) e
      return (t', a, identityMod)
    else do
      updateCount x
      return (t, a, identityMod)

typeInfer flag RealNum = 
   return (Arrow (Base (Id "Nat")) Type identityMod, RealNum, identityMod)

typeInfer flag a@(WrapR (MR len x)) =
  return (AppP RealNum (toNat len), a, identityMod)
  where  toNat i | i == 0 = Const (Id "Z")
         toNat i | i > 0 =
                   let n = toNat (i-1)
                   in AppP (Const (Id "S")) n

typeInfer flag a@(RealOp x)
  | x == "sin" || x == "exp" || x == "cos" || x == "log" || x == "sqrt" || x == "floor" || x == "ceiling" || x == "round" =
  freshNames ["n"] $ \ [n] -> 
  let arr = Arrow (AppP RealNum (Var n)) (AppP RealNum (Var n)) identityMod
      ty = Forall (abst [n] arr) (Base (Id "Nat")) 
  in return (ty, a, identityMod)

typeInfer flag a@(RealOp x) | x == "cast" =
  freshNames ["n", "m"] $ \ [n, m] -> 
  let arr = Arrow (AppP RealNum (Var m)) (AppP RealNum (Var n)) identityMod
      ty = PiImp (abst [m, n] arr) (Base (Id "Nat")) identityMod
  in return (ty, a, identityMod)

typeInfer flag a@(RealOp x) | x == "pi" =
  freshNames ["n"] $ \ [n] -> 
  let arr = AppP RealNum (Var n)
      ty = PiImp (abst [n] arr) (Base (Id "Nat")) identityMod
  in return (ty, a, identityMod)

typeInfer flag a@(RealOp x) | x == "plusReal" || x == "minusReal" || x == "divReal" || x == "mulReal" =
  freshNames ["n"] $ \ [n] -> 
  let arr = Arrow (AppP RealNum (Var n))
                  (Arrow (AppP RealNum (Var n))
                    (AppP RealNum (Var n)) identityMod) identityMod
      ty = Forall (abst [n] arr) (Base (Id "Nat")) 
  in return (ty, a, identityMod)

typeInfer flag a@(RealOp x) | x == "eqReal" || x == "ltReal" =
  freshNames ["n"] $ \ [n] -> 
  let arr = Arrow (AppP RealNum (Var n))
            (Arrow (AppP RealNum (Var n)) (Base (Id "Bool")) identityMod)
            identityMod
      ty = Forall (abst [n] arr) (Base (Id "Nat")) 
  in return (ty, a, identityMod)
 
typeInfer flag a@(Const kid) = do
  funPac <- lookupId kid
  let cl = classifier funPac
  case cl of
    Mod (Abst _ cl') -> return (cl', a, identityMod)
    _ -> return (cl, a, identityMod)

typeInfer flag a@(App t1 t2) = do
  (t', ann, m) <- typeInfer flag t1
  m' <- updateModality m
  if isKind t'
    then handleTypeApp ann t' t1 t2
    else handleTermApp flag ann t1 t' t1 t2 m'

typeInfer False a@(UnBox) =
  freshNames ["a", "b", "alpha", "beta"] $ \[a, b, alpha, beta] ->
    let va = Var a
        vb = Var b
        simpClass = Id "Simple"
        boxMode = M (BConst True) (BVar alpha) (BVar beta)
        t1 = Arrow (Circ va vb boxMode) (Bang (Arrow va vb boxMode) identityMod) identityMod
        t1' = Imply [AppP (Base simpClass) va,
                     AppP (Base simpClass) vb] t1 identityMod
        ty = Forall (abst [a, b] t1') Type
        ty' = abstractMode ty
     in return (ty', UnBox, identityMod)

typeInfer False a@(RunCirc) =
  freshNames ["a", "b", "alpha", "beta"] $ \[a, b, alpha, beta] ->
    let va = Var a
        vb = Var b
        simpClass = Id "Simple"
        boxMode = M (BConst True) (BVar alpha) (BVar beta)
        t1 = Arrow (Circ va vb boxMode) (Base (Id "Bool")) identityMod
        t1' = Imply [AppP (Base simpClass) va,
                     AppP (Base simpClass) vb] t1 identityMod
        ty = Forall (abst [a, b] t1') Type
        ty' = abstractMode ty
     in return (ty', RunCirc, identityMod)

typeInfer False a@(Reverse) =
  freshNames ["a", "b", "alpha"] $ \[a, b, alpha] ->
    let va = Var a
        vb = Var b
        simpClass = Id "Simple"
        boxMode = M (BConst True) (BVar alpha) (BConst True)
        t1 = Arrow (Circ va vb boxMode) (Circ vb va boxMode) identityMod
        t1' = Imply [AppP (Base simpClass) va,
                     AppP (Base simpClass) vb] t1 identityMod
        ty = Forall (abst [a, b] t1') Type
        ty' = abstractMode ty
     in return (ty', Reverse, identityMod)

typeInfer False a@(Controlled) =
  freshNames ["a", "s"] $ \[a, s'] ->
    let va = Var a
        s = Var s'
        simpClass = Id "Simple"
        t1 =
          Arrow
            (Circ va va identityMod)
            (Bang (Arrow va (Arrow s (Tensor va s) identityMod) identityMod) identityMod) identityMod
        t1' =
          Imply
            [ AppP (Base simpClass) s
            , AppP (Base simpClass) va
            ]
            t1 identityMod
        ty = Forall (abst [a, s'] t1') Type
        ty' = abstractMode ty
     in return (ty', Controlled, identityMod)

typeInfer True Dynlift =
  throwError $ ErrDoc $
  text "dynlift should not be used in a type expression"

typeInfer False Dynlift =
  let ty =
          Arrow (LBase (Id "Bit")) (Base (Id "Bool"))
            (M (BConst False) (BConst False) (BConst False))
   in return (ty, Dynlift, identityMod)

typeInfer False a@(WithComputed) =
  freshNames ["a", "b", "x", "y"] $
   \xs@[a, b, x, y] ->
    let vxs@[va, vb, vx, vy] = map Var xs
        simpClass = Id "Simple"
        mod1 = M (BConst True) (BConst False) (BConst True)
        mod2 = M (BConst True) (BVar x) (BVar y)
        t1 =
          Arrow
            (Circ va vb mod1)
            (Arrow
               (Circ vb vb mod2)
               (Circ va va mod2) identityMod) identityMod
        t1' = Imply (map (AppP (Base simpClass)) (take 2 vxs)) t1 identityMod
        ty = Forall (abst [a, b] t1') Type
        ty' = abstractMode ty
     in return (ty', WithComputed, identityMod)

typeInfer False t@(Box) =
  freshNames ["a", "b", "alpha", "beta"] $ \[a, b, alpha, beta] -> do
    let va = Var a
        vb = Var b
        simpClass = Id "Simple"
        boxMode = M (BConst True) (BVar alpha) (BVar beta)
        t1 = Arrow (Bang (Arrow va vb boxMode) identityMod) (Circ va vb boxMode) identityMod
        t1' = Imply [AppP (Base simpClass) va,
                     AppP (Base simpClass) vb] t1 identityMod
        boxType = Pi (abst [a] (Forall (abst [b] t1') Type)) Type identityMod
        ty' = abstractMode boxType
    return (ty', t, identityMod)

typeInfer False t@(ExBox) =
  freshNames ["a", "b", "p", "n", "alpha", "beta"] $
  \[a, b, p, n, alpha, beta] -> do
    let va = Var a
        vb = Var b
        vp = Var p
        vn = Var n
        simpClass = Id "Simple"
        paramClass = Id "Parameter"
        kp = Arrow vb Type identityMod
        boxMode = M (BConst True) (BVar alpha) (BVar beta)
        simpA = AppP (Base simpClass) va
        paramB = AppP (Base paramClass) vb
        simpP = AppP (Base simpClass) (AppP vp vn)
        t1Output = Exists (abst n (AppP vp vn)) vb
        t1 = Bang (Arrow va t1Output boxMode) identityMod
        output =
          Exists (abst n $ Imply [simpP]
                           (Circ va (AppP vp vn) boxMode) identityMod) vb
        beforePi = Arrow t1 output identityMod
        r =
          Pi
            (abst [a] $
             Forall
               (abst [b] (Imply [simpA, paramB] 
                     (Pi (abst [p] $ beforePi) kp identityMod) identityMod))
               Type)
            Type identityMod
        r' = abstractMode r
    return (r', t, identityMod)

typeInfer flag Star = return (Unit, Star, identityMod)
typeInfer flag Unit = return (Type, Unit, identityMod)

typeInfer flag a@(Pair t1 t2) = do
  (ty1, ann1, mode1) <- typeInfer flag t1
  (ty2, ann2, mode2) <- typeInfer flag t2
  mode1' <- updateModality mode1
  mode2' <- updateModality mode2
  return (Tensor ty1 ty2, Pair ann1 ann2, modalAnd mode1' mode2')

typeInfer False a@(LamAnn ty (Abst xs m)) = do
  (_, tyAnn1) <-
    if isKind ty
      then typeCheck True ty Sort identityMod
      else typeCheck True ty Type identityMod
  mapM_ (\x -> addVar x (erasePos tyAnn1)) xs
  p <- isParam tyAnn1
  (ty', ann, mode) <- typeInfer False m
  mode' <- updateModality mode
  foldM (helper p tyAnn1) (ty', ann, mode') xs
  where
    helper p tyAnn1 (ty', ann, mode') x = do
      when (not p) $ checkUsage x m 
      removeVar x
      let resTy =
            if x `S.member` getVars All ty'
              then Pi (abst [x] ty') tyAnn1 mode'
              else Arrow tyAnn1 ty' mode'
      return (resTy, LamAnn tyAnn1 (abst [x] ann), identityMod)

typeInfer flag (WithType a t) = 
  do (_, tAnn1) <- typeCheck True t Type identityMod
     let tAnn' = erasePos tAnn1
     mod <- newNames ["#alpha", "#beta", "#gamma"] >>= newMode
     (tAnn2, ann) <- typeCheck False a tAnn' mod
     mod' <- updateModality mod
     return (tAnn2, WithType ann tAnn2, mod')

typeInfer flag a@(Case _ _) =
  freshNames ["#case"] $
  \[n] -> do
    mod <- newNames ["#alpha", "#beta", "#gamma"] >>= newMode 
    (t, ann) <- typeCheck flag a (MetaVar n) mod
    mod' <- updateModality mod
    return (t, WithType ann t, mod')

typeInfer flag a@(Let _ _) =
  freshNames ["#let"] $
    \[n] -> do
      mod <- newNames ["#alpha", "#beta", "#gamma"] >>= newMode 
      (t, ann) <- typeCheck flag a (MetaVar n) mod
      mod' <- updateModality mod
      return (t, WithType ann t, mod')

typeInfer flag a@(LetPair _ _) =
  freshNames ["#letPair"] $
  \[n] -> do
    mod <- newNames  ["#alpha", "#beta", "#gamma"] >>= newMode
    (t, ann) <- typeCheck flag a (MetaVar n) mod
    mod' <- updateModality mod
    return (t, WithType ann t, mod')

typeInfer flag a@(Lam _) = throwError $ LamInferErr a

typeInfer flag (Tensor ty1 ty2) =
  do (_, ty1') <- typeCheck flag ty1 Type identityMod
     (_, ty2') <- typeCheck flag ty2 Type identityMod
     return (Type, Tensor ty1' ty2', identityMod)
  
typeInfer flag e = throwError $ Unhandle e

typeCheck flag (Pos p e) ty mod = do
  (ty', ann) <-
    typeCheck flag e ty mod `catchError` \e -> throwError $ addErrPos p e
  return (ty', Pos p ann)

typeCheck flag (Mod (Abst _ e)) ty mod = typeCheck flag e ty mod

-- Sort check
typeCheck True Type Sort _ = return (Sort, Type)

typeCheck True (Arrow ty1 ty2 m) Sort mod = do
  (_, ty1') <-
    if isKind ty1
      then typeCheck True ty1 Sort mod
      else typeCheck True ty1 Type mod
  (_, ty2') <- typeCheck True ty2 Sort mod
  return (Sort, Arrow ty1' ty2' m)

typeCheck True (Pi (Abst xs m) ty mod) Sort cm = do
  (_, ty') <-
    if isKind ty
      then typeCheck True ty Sort cm
      else typeCheck True ty Type cm
  mapM_ (\x -> addVar x (erasePos ty')) xs
  (_, ann2) <- typeCheck True m Sort cm
  let res = Pi (abst xs ann2) ty' mod
  mapM_ removeVar xs
  return (Sort, res)

-- Kind check
typeCheck True Unit Type _ = return (Type, Unit)

typeCheck True (Bang ty m) Type mod = do
  (_, a) <- typeCheck True ty Type mod
  return (Type, Bang a m)

typeCheck True (Arrow ty1 ty2 mod) Type cm = do
  (_, ty1') <-
    if isKind ty1
      then typeCheck True ty1 Sort cm
      else typeCheck True ty1 Type cm
  (_, ty2') <- typeCheck True ty2 Type cm
  return (Type, Arrow ty1' ty2' mod)

typeCheck True (Imply tys ty2 mod) Type m = do
  res <- mapM (\x -> typeCheck True x Type m) tys
  let tys1 = map (\(x, y) -> y) res
  mapM checkClass tys1
  updateParamInfo tys1
  updateSimpleInfo tys1
  (_, ty2') <- typeCheck True ty2 Type m
  return (Type, Imply tys1 ty2' mod)

typeCheck True (Tensor ty1 ty2) Type m = do
  (_, ty1') <- typeCheck True ty1 Type m
  (_, ty2') <- typeCheck True ty2 Type m
  return (Type, Tensor ty1' ty2')

typeCheck True (Circ t u m) Type mod = do
  (_, t') <- typeCheck True t Type mod
  (_, u') <- typeCheck True u Type mod
  return (Type, Circ t' u' m)

typeCheck True (Pi (Abst xs m) ty mod) Type cm = do
  (_, tyAnn) <-
    if isKind ty
      then typeCheck True ty Sort cm
      else typeCheck True ty Type cm
  mapM_ (\x -> addVar x (erasePos tyAnn)) xs
  (_, ann2) <- typeCheck True m Type cm
  ann2' <- updateWithSubst ann2
  ann2'' <- resolveGoals ann2'
  let res = Pi (abst xs ann2'') tyAnn mod
  mapM_ removeVar xs
  return (Type, res)

typeCheck True pty@(PiImp (Abst xs m) ty mod2) Type mod = do
  isP <- isParam ty
  when (not isP) $ throwError $ ForallLinearErr xs ty pty
  (_, tyAnn) <-
    if isKind ty
      then typeCheck True ty Sort mod
      else typeCheck True ty Type mod
  mapM_ (\x -> addVar x (erasePos tyAnn)) xs
  (_, ann2) <- typeCheck True m Type mod
  ann2' <- updateWithSubst ann2
  ann2'' <- resolveGoals ann2'
  let res = PiImp (abst xs ann2'') tyAnn mod2
  mapM_ removeVar xs
  return (Type, res)

typeCheck True (Forall (Abst xs m) ty) a@(Type) mod
  | isKind ty = do
    (_, tyAnn) <- typeCheck True ty Sort mod
    mapM_ (\x -> addVar x (erasePos tyAnn)) xs
    (_, ann) <- typeCheck True m a mod
    ann' <- updateWithSubst ann
    ann'' <- resolveGoals ann'
    let res = Forall (abst xs ann'') tyAnn
    mapM_ (\x -> removeVar x) xs
    return (a, res)

typeCheck True exp@(Forall (Abst xs m) ty) a@(Type) mod
  | otherwise = do
    p <- isParam ty
    b <- getCheckBound
    when (not p && b) $ throwError (ForallLinearErr xs ty exp)
    (_, tyAnn) <- typeCheck True ty a mod
    mapM_ (\x -> addVar x (erasePos tyAnn)) xs
    (_, ann) <- typeCheck True m a mod
    ann' <- updateWithSubst ann
    ann'' <- resolveGoals ann'
    let res = Forall (abst xs ann'') tyAnn
    mapM_ removeVar xs
    return (a, res)

typeCheck True (Exists (Abst xs m) ty) a@(Type) mod
  | not (isKind ty) = do
    (_, ann1) <- typeCheck True ty a mod
    addVar xs (erasePos ann1)
    (_, ann2) <- typeCheck True m a mod
    ann2' <- updateWithSubst ann2
    ann2'' <- resolveGoals ann2'
    let res = Exists (abst xs ann2'') ann1
    removeVar xs
    return (a, res)

typeCheck True a@(Lam (Abst xs m)) t mod
  | isKind t =
    case t of
      Arrow t1 t2 _ -> do
        let x = head xs
            ys = tail xs
        addVar x t1
        (_, ann) <-
          if null ys
            then typeCheck True m t2 mod
            else typeCheck True (Lam (abst ys m)) t2 mod
        ann' <- updateWithSubst ann
        ann'' <- resolveGoals ann'
        let res = LamP (abst [x] ann'')
        removeVar x
        return (t, res)
      b -> throwError $ KArrowErr a t

-- Type check
typeCheck flag a (Forall (Abst xs m) ty) mod = do
  mapM_ (\x -> addVar x ty) xs
  (t, ann) <- typeCheck flag a m mod
  mapM_ removeVar xs
     -- It is important to update the annotation with current
     -- substitution before rebinding xs, so that variables in
     -- xs does not get leaked
     -- into outer environment.
     -- Also, we will have to resolve all the constraint before
     -- going out of this forall environment.
  ann' <- updateWithSubst ann
  t' <- updateWithSubst t
     -- It is necessary to resolve all the goals before going out of
     -- the scope of xs as well.
  ann'' <- resolveGoals ann'
  mapM_ (checkExplicit ann'') xs
  let res =
        if isKind ty
          then (Forall (abst xs $ t') ty,
                LamType (abst xs $ ann''))
          else (Forall (abst xs $ t') ty, LamTm (abst xs $ ann''))
  return res
  where
    -- Make sure the variable \x\ does not leak into runtime.  
    checkExplicit ann'' x =
      when (isExplicit x ann'') $ throwError $ ImplicitVarErr x ann''

-- Only used for checking method declaration.
typeCheck False a@(LamDict (Abst xs e)) (Imply bds ty mod2) mod1 = do
  mod1' <- updateModality mod1
  let lxs = length xs
      lbd = length bds
      msubs = modeResolution GEq identityMod mod1'
  case msubs of
    Nothing -> throwError $ ModalityErr identityMod mod1' a
    Just s' -> do
      updateModeSubst s'
      if lxs <= lbd
        then do
          let (pre, post) = splitAt lxs bds
              ty' =
                if null post
                  then ty
                  else Imply post ty mod2
          mapM (\(x, y) -> addVar x y) (zip xs pre)
          (ty'', a) <- typeCheck False e ty' mod2
          mapM_ removeVar xs
          return (Imply pre ty'' mod2, LamDict (abst xs a))
        else do
          let (pre, post) = splitAt lbd xs
          mapM (\(x, y) -> addVar x y) (zip pre bds)
          (ty', a) <- typeCheck False (LamDict (abst post e)) ty mod2
          mapM_ removeVar pre
          return (Imply bds ty' mod2, LamDict (abst pre a))

typeCheck flag a (Imply bds ty mod2) mod1 = do
  mod1' <- updateModality mod1
  let msubs = modeResolution GEq identityMod mod1'
  case msubs of
    Nothing -> throwError $ ModalityErr identityMod mod1' a
    Just s' -> do
      updateModeSubst s'
      updateParamInfo bds
      updateSimpleInfo bds
      let ns1 = take (length bds) (repeat "#inst")
      ns <- newNames ns1
      freshNames ns $ \ns -> do
        bds' <- mapM normalize bds
        let instEnv = zip ns bds'
        mapM_ (\(x, t) -> insertLocalInst x t) instEnv
        (t, ann) <- typeCheck flag a ty mod2
        ann' <- resolveGoals ann
        mapM_ (\(x, t) -> removeLocalInst x) instEnv
        let res = LamDict (abst ns ann')
        return (Imply bds t mod2, res)

typeCheck flag a@(Const _) (Bang ty m) mod =
  handleBangConstVar flag a (Bang ty m) mod

typeCheck flag a@(Var _) (Bang ty m) mod =
  handleBangConstVar flag a (Bang ty m) mod

-- Inserting lift on Bang.
typeCheck flag a (Bang ty m) mod = do
  handleBangValue flag a (Bang ty m) mod

typeCheck False c@(Lam bind) t mod = do
  mod' <- updateModality mod
  let msubs = modeResolution GEq identityMod mod'
  case msubs of
    Nothing -> throwError $ ModalityErr identityMod mod' c
    Just s' -> do
      updateModeSubst s'
      at <- updateWithSubst t
      handleFunctions at c t
  where
    handleFunctions at _ t
      | not (at == t) = typeCheck False c at mod
    handleFunctions (Arrow t1 t2 mod1) c@(Lam (Abst xs m)) t = do
      let x = head xs
          ys = tail xs
      addVar x t1
      (t2', ann) <-
        if null ys
          then typeCheck False m t2 mod1
          else typeCheck False (Lam (abst ys m)) t2 mod1
      checkUsage x m
      removeVar x
      -- x cannot appear in type annotation, so we do not
      -- need to update the ann with current substitution.
      let res = Lam (abst [x] ann)
      return (Arrow t1 t2' mod1, res)
    handleFunctions (Pi (Abst ys b) ty mod1) (Lam (Abst xs m)) t =
      handleDep (Pi, ys, b, ty) mod1 (xs, m) t
    handleFunctions (PiImp (Abst ys b) ty mod1) (Lam (Abst xs m)) t =
      handleDep (PiImp, ys, b, ty) mod1 (xs, m) t
    handleFunctions ty l t = throwError $ withPosition l $ LamErr l ty
    handleDep (pi, ys, b, ty) mod1 (xs, m) t =
      if length xs <= length ys
        then do
          let sub1 = zip ys (map Var xs)
              b' = apply sub1 b
              (vs, rs) = splitAt (length xs) ys
          mapM_ (\x -> addVar x ty) xs
          (t, ann) <-
            typeCheck
              False
              m
              (if null rs
                 then b'
                 else pi (abst rs b') ty mod1)
              mod1
          mapM (\x -> checkUsage x m) xs
          mapM_ removeVar xs
           -- Since xs may appear in the type annotation in ann,
           -- we have to update ann with current substitution.
           -- before going out of the scope of xs. We also have to
           -- resolve the current goals because current goals may
           -- depend on xs.
          ann2 <- updateWithSubst ann
          ann' <- resolveGoals ann2
          t' <- updateWithSubst t
          mod1' <- updateModality mod1
          let lamDep =
                if isKind ty
                  then LamDepTy
                  else LamDep
              res = lamDep (abst xs ann')
              t'' = pi (abst xs t') ty mod1'
          return (t'', res)
        else do
          let lamDep =
                if isKind ty
                  then LamDepTy
                  else LamDep
              sub1 = zip ys (map Var xs)
              b' = apply sub1 b
              (vs, rs) = splitAt (length ys) xs
          mapM_ (\x -> addVar x ty) vs
          (t, ann) <-
            typeCheck
              False
              (if null rs
                 then m
                 else Lam (abst rs m))
              b'
              mod1
          mapM (\x -> checkUsage x m) vs
          mapM_ removeVar vs
          ann1 <- updateWithSubst ann
          t' <- updateWithSubst t
          ann' <- resolveGoals ann1
          mod1' <- updateModality mod1
          let res = lamDep (abst vs ann')
          return (pi (abst vs t') ty mod1', res)
    
typeCheck flag a@(Pair t1 t2) (Exists (Abst x t) ty) mod = do
  mode1 <- newNames ["y", "z"] >>= newMode2
  mode2 <- newNames ["u", "v", "w"] >>= newMode
  (ty', ann1) <- typeCheck flag t1 ty mode1
  t1 <-
    shape ann1 `catchError` \e ->
      throwError $ AddDoc (text "for the expression" $$ (nest 2 $ disp t1)) e
  let t' = apply [(x, t1)] t
  (p', ann2) <- typeCheck flag t2 t' mode2
  mode1' <- updateModality mode1
  mode2' <- updateModality mode2
  mod' <- updateModality mod
  let s = modeResolution GEq (modalAnd mode1' mode2') mod'
  case s of
    Nothing -> throwError $ ModalityErr (modalAnd mode1' mode2') mod' a
    Just s'@(s1, s2, s3) -> do
      updateModeSubst s'
          -- t' is an instance of t, it does not contain x anymore,
          -- hence the return type should be Exists p ty', not
          -- Exists (abst x p') ty'
      return (Exists (abst x t) ty', Pair ann1 ann2)

 
typeCheck flag a@(Pair t1 t2) d mod =
  do sd <- updateWithSubst d
     mode1 <- newMode ["a", "b", "c"]
     mode2 <- newMode ["a2", "b2", "c2"]
     case erasePos sd of
       Tensor ty1 ty2 ->
         do (ty1', t1') <- typeCheck flag t1 ty1 mode1
            (ty2', t2') <- typeCheck flag t2 ty2 mode2
            mode1' <- updateModality mode1
            mode2' <- updateModality mode2
            mod' <- updateModality mod
            let conj = modalAnd mode1' mode2'
                msubs = modeResolution GEq conj mod'
            case msubs of
              Nothing -> throwError $ ModalityErr conj mod' a
              Just s' -> do
                updateModeSubst s'
                return (Tensor ty1' ty2', Pair t1' t2')
       b -> freshNames ["#unif1", "#unif2"] $ \ (x1:x2:[]) ->
         do let ty = Tensor (MetaVar x1) (MetaVar x2)
                (res, (s, bs)) = runUnify GEq sd ty
            case res of
              Success ->
                do ss <- getSubst
                   let sub' = s `mergeSub` ss
                   updateSubst sub'
                   updateModeSubst bs
                   let x1' = substitute sub' (MetaVar x1)
                       x2' = substitute sub' (MetaVar x2)
                   (x1'', t1') <- typeCheck flag t1 x1' mode1
                   (x2'', t2') <- typeCheck flag t2 x2' mode2
                   mode1' <- updateModality mode1
                   mode2' <- updateModality mode2
                   mod' <- updateModality mod
                   let conj = modalAnd mode1' mode2'
                       msubs = modeResolution GEq conj mod'
                   case msubs of
                     Nothing -> throwError $ ModalityErr conj mod' a
                     Just s' -> do
                       updateModeSubst s'
                       let res = Pair t1' t2'
                       return (Tensor x1'' x2'', res)
              UnifError -> throwError (TensorExpErr a b)
              ModeError p1 p2 ->
                throwError $ ModalityGEqErr a sd ty p1 p2
 
typeCheck flag a@(Let m (Abst x t)) goal mod = do
  (t', ann, mode) <- typeInfer flag m
  mode1@(M alpha beta gamma) <- updateModality mode
  when (not (alpha == BConst True)) (addVar x t')
  when (alpha == BConst True) $ do
    m'' <-
      shape ann `catchError` \e ->
        throwError $ AddDoc (text "for the expression" $$ (nest 2 $ disp m)) e
    addVarDef x t' m''
  mode2 <- newMode ["#alpha", "#beta", "#gamma"]
  (goal', ann2) <- typeCheck flag t goal mode2
  checkUsage x t
  mod' <- updateModality mod
  mode1' <- updateModality mode1
  mode2' <- updateModality mode2
  let s = modeResolution GEq (modalAnd mode1' mode2') mod
  case s of
    Nothing -> throwError $ ModalityErr (modalAnd mode1' mode2') mod' a
    Just s'@(s1, s2, s3) -> do
      updateModeSubst s'
      -- If the goal resolution fails,
      -- delay it for upper level to resolve
      ann2' <-
        (resolveGoals ann2 >>= updateWithSubst) `catchError` \e -> return ann2
      removeVar x
      let res = Let ann (abst x ann2')
      return (goal', res)

typeCheck flag a@(LetPair m (Abst xs b)) goal mod = do
  (t', ann, mode1) <- typeInfer flag m
  at <- updateWithSubst t'
  case at of
    Exists (Abst x1 b') t1 -> do
      when (length xs /= 2) $ throwError $ ArityExistsErr at xs
      let (x:y:[]) = xs
      mode2 <- newMode ["alpha", "beta", "gamma"]
      addVar x t1
      addVar y (apply [(x1, Var x)] b')
      (goal', ann2) <- typeCheck flag b goal mode2
      ann2' <- updateWithSubst ann2
      ann3 <- resolveGoals ann2'
      checkUsage y b
      checkUsage x b
      removeVar x
      removeVar y
      mod' <- updateModality mod
      mode1' <- updateModality mode1
      mode2' <- updateModality mode2
      let s = modeResolution GEq (modalAnd mode1' mode2') mod'
      case s of
        Nothing -> throwError $ ModalityErr (modalAnd mode1' mode2') mod' a
        Just s'@(s1, s2, s3) -> do
          updateModeSubst s'
          let res = LetPair ann (abst [x, y] ann3)
          return (goal', res)
    _ ->
      case unTensor (length xs) at of
        Just ts -> do
          let env = zip xs ts
          mode2 <- newMode ["alpha", "beta", "gamma"]
          mapM (\(x, t) -> addVar x t) env
          (goal', ann2) <- typeCheck flag b goal mode2
          mapM (\(x, t) -> checkUsage x b) env
          ann2' <- updateWithSubst ann2
          mod' <- updateModality mod
          mode1' <- updateModality mode1
          mode2' <- updateModality mode2
          let s = modeResolution GEq (modalAnd mode1' mode2') mod'
          case s of
            Nothing -> throwError $ ModalityErr (modalAnd mode1' mode2') mod' a
            Just s'@(s1, s2, s3) -> do
              updateModeSubst s'
              mapM removeVar xs
              let res = LetPair ann (abst xs ann2')
              return (goal', res)
        Nothing -> do
          nss <- newNames $ map (\x -> "#unif") xs
          freshNames nss $ \(h:ns) -> do
            let newTensor = foldl Tensor (MetaVar h) (map MetaVar ns)
                vars = map MetaVar (h : ns)
                (res, (s, bs)) = runUnify GEq at newTensor
            case res of
              UnifError -> throwError $ TensorErr (length xs) m at
              ModeError p1 p2 ->
                throwError $ ModalityGEqErr m at newTensor p1 p2
              Success -> do
                ss <- getSubst
                let sub' = s `mergeSub` ss
                updateSubst sub'
                updateModeSubst bs
                let ts' = map (substitute sub') vars
                    env' = zip xs ts'
                mode2 <- newMode ["alpha", "beta", "gamma"]
                mapM (\(x, t) -> addVar x t) env'
                (goal', ann2) <-
                  typeCheck flag b (bSubstitute bs $ substitute sub' goal) mode2
                mapM (\x -> checkUsage x b) xs
                mod' <- updateModality mod
                mode1' <- updateModality mode1
                mode2' <- updateModality mode2
                let s = modeResolution GEq (modalAnd mode1' mode2') mod'
                case s of
                  Nothing ->
                    throwError $ ModalityErr (modalAnd mode1' mode2') mod' a
                  Just s'@(s1, s2, s3) -> do
                    updateModeSubst s'
                    ann2' <- updateWithSubst ann2
                    mapM removeVar xs
                    let res = LetPair ann (abst xs ann2')
                    return (goal', res)

                
typeCheck flag a@(LetPat m (Abst (PApp kid vs) n)) goal mod = do
  (t, ann, mode1) <- typeInfer flag m
  at <- updateWithSubst t
  funPac <- lookupId kid
  let dt = classifier funPac
  semi <- isSemiSimple kid
  (head, axs, ins, kid') <- extendEnv vs dt (Const kid)
  ss <- getSubst
  (unifRes, (sub', bs)) <- patternUnif semi m head at
  case unifRes of
      UnifError -> throwError $ withPosition m (UnifErr head at)
      Success -> do
        b <- varDep (erasePos m) goal
        sub1 <-
          if b
            then makeSub m sub' $ foldl (\x (Right y) -> App x (Var y)) kid' vs
            else return sub'
        let sub'' = sub1 `mergeSub` ss
        updateSubst sub''
        updateModeSubst bs
        let goal' = bSubstitute bs (substitute sub'' goal)
        mode2 <- newMode ["alpha", "beta", "gamma"]
        (goal'', ann2) <- typeCheck flag n goal' mode2
        subb <- getSubst
        mapM (\(Right v) -> checkUsage v n >>= \r -> (return (v, r))) vs
        mapM_ (\(Right v) -> removeVar v) vs
        mod' <- updateModality mod
        mode1' <- updateModality mode1
        mode2' <- updateModality mode2
        let s = modeResolution GEq (modalAnd mode1' mode2') mod'
        case s of
          Nothing -> throwError $ ModalityErr (modalAnd mode1' mode2') mod' a
          Just s'@(s1, s2, s3) -> do
            updateModeSubst s'
            -- It is important to update the environment before
            -- going out of a dependent pattern matching
            updateLocalInst subb
            ann2' <- resolveGoals (substitute subb ann2)
            mapM removeLocalInst ins
            let axs' = map (substVar subb) axs
                goal''' = substitute subb goal''
                res = LetPat ann (abst (PApp kid axs') ann2')
            return (goal''', res)
  where
    varDep (Var x) goal = isDpmVar x goal
    varDep _ _ = return False
    makeSub (Var x) s u = do
      let m = substitute s u
      u' <-
        shape m `catchError` \e ->
          throwError $ AddDoc (text "for the expression" $$ (nest 2 $ disp m)) e
      return $ Map.union s (Map.fromList [(x, u')])
    makeSub (Pos p x) s u = makeSub x s u
    makeSub a s u = return s
    substVar ss (Right x) =
      let r = substitute ss (Var x)
       in case erasePos r of
            Var y
              | x == y -> Right y
            _ -> Left (NoBind r)


typeCheck flag a@(Case tm (B brs)) goal mod =
  do (t, ann, mode1) <- typeInfer flag tm
     at <- updateWithSubst t
     let t' = flatten at
     when (t' == Nothing) $ throwError (DataErr at tm)
     let Just (Right id, _) = t'
     id' <- lookupId id
     case identification id' of
          DataType Simple _ _ -> throwError (DataErr at tm)
          DataType _ _ _ -> return ()
     updateCountWith (\ c -> enterCase c id)
     r <- checkBrs at brs goal
     let brss = map (\ (x, y, z) -> y) r
         ms = map (\ (x, y, z) -> z) r
     updateCountWith exitCase
     mode1' <- updateModality mode1
     mod' <- updateModality mod
     let mode'' = foldr modalAnd mode1' ms
     let s = modeResolution GEq mode'' mod' 
     when (s == Nothing) $ 
       throwError $
        ModalityErr mode'' mod' a
     let Just s'@(s1, s2, s3) = s
     updateModeSubst s'     
     let res = Case ann (B brss)
     return (goal, res)
  where makeSub (Var x) s u =
          do let m = substitute s u
             u' <- shape m  `catchError`
                   \ e -> throwError $ AddDoc
                          (text "for the expression" $$ (nest 2 $ disp m)) e
             return $ s `Map.union` Map.fromList [(x, u')]
        makeSub (Pos p x) s u = makeSub x s u
        makeSub a s u = return s
        varDep (Var x) goal = isDpmVar x goal
        varDep _ _ = return False
        
        substVar ss (Right x) =
             let r = substitute ss (Var x)
             in case erasePos r of
                 Var y | x == y -> Right y
                 _ -> Left (NoBind r)

        checkBrs t pbs goal =
          mapM (checkBr t goal) pbs
          
        checkBr t goal pb =
          open pb $ \ p m ->
           case p of
             PApp kid vs ->
               do funPac <- lookupId kid
                  let dt = classifier funPac
                  semi <- isSemiSimple kid
                  updateCountWith (\ c -> nextCase c kid)
                  (head, axs, ins, kid') <- extendEnv vs dt (Const kid)
                  ss <- getSubst
                  (unifRes, (sub', bs)) <- patternUnif semi m head t
                  case unifRes of
                    UnifError ->
                      throwError $ withPosition tm (UnifErr head t)
                      
                    ModeError p1 p2 ->
                      throwError $ ModalityGEqErr tm head t p1 p2
                    Success -> do
                      b <- varDep (erasePos tm) goal
                      sub1 <- if b then
                               makeSub tm sub' $
                                 foldl (\ x (Right y) ->
                                          App x (Var y)) kid' vs
                               else return sub'           
                      let sub'' = sub1 `mergeSub` ss
                      updateSubst sub''
                      updateModeSubst bs
                      let goal' = bSubstitute bs (substitute sub'' goal)
                      mode <- newMode ["a", "b", "c"]
                      (goal'', ann2) <- typeCheck flag m goal' mode
                      subb <- getSubst 
                      mapM (\ (Right v) -> checkUsage v m >>=
                                           \ r -> return (v, r)) vs
                      updateLocalInst subb
                      -- we need to restore the substitution to ss
                      -- because subb may be influenced
                      -- by dependent pattern matching.
                      ann2' <- resolveGoals (substitute subb ann2)
                               `catchError` \ e -> return ann2
                      infer <- getInfer
                      let isDpm = ((fst semi) && (snd semi /= Nothing))
                                    || b
                      when (isDpm && infer) $ throwError $
                         withPosition tm $ DpmInferErr tm
                      when isDpm $ updateSubst ss
                      when (not isDpm) $ updateSubst subb
                      let goal''' = substitute subb goal''
                      -- because the variable axs may be in the domain
                      -- of the substitution, hence it is necessary
                      -- to update axs as well before binding.
                         
                      let axs' = map (substVar subb) axs
                      mapM_ (\ (Right v) -> removeVar v) vs
                      mapM removeLocalInst ins
                      mode' <- updateModality mode
                      return (goal''', abst (PApp kid axs') ann2', mode')

typeCheck flag a@(Const x) ty mod = inferAddAnn flag a ty mod
typeCheck flag a@(RealOp _) ty mod = inferAddAnn flag a ty mod
typeCheck flag a@(Var x) ty mod = inferAddAnn flag a ty mod
typeCheck flag a@(App _ _) ty mod = inferAddAnn flag a ty mod
typeCheck flag a ty mod
  | isBuildIn a = inferAddAnn flag a ty mod
typeCheck flag tm ty mod = equality flag tm ty mod

equality :: Bool -> Exp -> Exp -> Modality -> TCMonad (Exp, Exp)
equality flag tm ty mod =
  do ty' <- updateWithSubst ty
     if not (ty == ty')
       then typeCheck flag tm ty' mod
       else 
       do (tym, ann, mode) <- typeInfer flag tm
          mode' <- updateModality mode
          mod' <- updateModality mod
          let s = modeResolution GEq mode' mod' 
          when (s == Nothing) $ throwError $
              ModalityErr mode' mod' tm
          let Just s'@(s1, s2, s3) = s
          updateModeSubst s'     
          tym1 <- updateWithSubst tym
          ty1 <- updateWithSubst ty'
          tym1' <- updateWithModeSubst tym1
          ty1' <-  updateWithModeSubst ty1
          (unifRes, (sub, bs)) <- normalizeUnif GEq tym1' ty1'
          case unifRes of
             UnifError ->
               throwError $ withPosition tm (UnifErr tym1 ty1)
             ModeError p1 p2 ->
               throwError $ ModalityGEqErr tm ty1 tym1 p1 p2
             Success -> do
               ss <- getSubst
               let ss' = sub `mergeSub` ss 
               updateSubst ss'
               updateModeSubst bs
               ty1' <- updateWithModeSubst ty1 >>= updateWithSubst
               return (ty1', ann)

          
          
-- | Normalize and unify two expressions (/head/ and /t/),
-- used by dependent pattern matching.

patternUnif :: (Bool, Maybe Int) ->
                 Exp -> Exp -> Exp ->
                  TCMonad (UnifResult, (Subst, BSubst))
patternUnif (isDpm, index) m head t =
  if isDpm then
    case index of
        Nothing -> normalizeUnif GEq head t 
        Just i ->
          case (flatten head, flatten t) of
            (Just (Right h1, args1), Just (Right h2, args2))
              | h1 == h2 && length args1 == length args2 ->
              let (bs1, a1:as1) = splitAt i args1
                  (bs2, a2:as2) = splitAt i args2
              in do (r1, subst1) <- normalizeDUnif a1 a2
                    case r1 of
                      Success ->
                        do let a1' = substitute subst1 a1
                               a2' = substitute subst1 a2
                               head' = foldl AppP (Base h1)
                                         (bs1++a1':as1)
                               t' = foldl AppP (Base h2) (bs2++a2':as2)
                           (res, (sub, bs)) <- normalizeUnif GEq head' t'
                           return (res, (sub `mergeSub` subst1, bs))
                      _ -> throwError $ withPosition m (UnifErr head t)
            _ -> throwError $ withPosition m (UnifErr head t)
  else normalizeUnif GEq head t
          
      
-- | Normalize two expressions and then unify them.  
-- There is a degree of freedom in implementing normalizeUnif function.
-- It could be further improved.
normalizeUnif :: InEquality -> Exp -> Exp ->
                 TCMonad (UnifResult, (Subst, BSubst))
normalizeUnif b t1 t2 = do
  t1' <- resolveGoals t1
  t2' <- resolveGoals t2
  let a@(res, (s, bs)) = runUnify b t1' t2'
  case res of
    Success -> return a
    _ -> do
      t1'' <- normalize t1'
      t2'' <- normalize t2'
      return $ runUnify b t1'' t2''

-- | Normalize two expressions and then unify them.  The unification
-- here is using dependent unification dUnify. 
normalizeDUnif :: Exp -> Exp ->
                 TCMonad (UnifResult, Subst)
normalizeDUnif t1 t2 = do
  t1' <- resolveGoals t1
  t2' <- resolveGoals t2
  let a@(res, _) = runDUnify t1' t2'
  case res of
    Success -> return a
    _ -> do
      t1'' <- normalize t1'
      t2'' <- normalize t2'
      return $ runDUnify t1'' t2''

-- | Extend the typing environment with
-- the environment induced by a pattern.
-- Its first argument is the argument list from 'Pattern'.
-- Its second argument is the type of the constructor,
-- its third argument is the constructor
-- of the pattern. It will return the following,
-- 'Exp': head of the type expression,
-- ['Either' a 'Variable']: essentially an extended list
-- of pattern variables,
-- ['Variable']: a list of dictionary variables,
-- 'Exp': annotated version of the constructor,
extendEnv ::
     [Either (NoBind Exp) Variable]
  -> Exp
  -> Exp
  -> TCMonad (Exp, [Either a Variable], [Variable], Exp)

extendEnv xs (Mod (Abst _ ty)) kid = extendEnv xs ty kid

extendEnv xs (Forall bind ty) kid
  | isKind ty =
    open bind $ \ys t' -> do
      mapM_ (\x -> addVar x ty) ys
      let mvars = map MetaVar ys
          kid' = foldl AppType kid mvars
          t'' = apply (zip ys mvars) t'
      (h, vs, ins, kid'') <- extendEnv xs t'' kid'
      let vs' = map Right ys ++ vs
      return (h, vs', ins, kid'')

extendEnv xs (Forall bind ty) kid
  | otherwise =
    open bind $ \ys t' -> do
      mapM_ (\x -> addVar x ty) ys
      let mvars = map MetaVar ys
          kid' = foldl AppTm kid mvars
          t'' = apply (zip ys mvars) t'
      (h, vs, ins, kid'') <- extendEnv xs t'' kid'
      let vs' = (map Right ys) ++ vs
      return (h, vs', ins, kid'')

extendEnv xs (Imply bds ty _) kid = do
  let ns1 = take (length bds) (repeat "#inst")
  ns <- newNames ns1
  freshNames ns $ \ns -> do
    mapM_ (\(x, y) -> insertLocalInst x y) (zip ns bds)
    let kid' = foldl AppDict kid (map MetaVar ns)
    (h, vs, ins, kid'') <- extendEnv xs ty kid'
    return (h, (map Right ns) ++ vs, ns ++ ins, kid'')

extendEnv [] t kid = return (t, [], [], kid)

extendEnv (Right x:xs) (Arrow t1 t2 _) kid = do
  addVar x t1
  (h, ys, ins, kid') <- extendEnv xs t2 kid
  return (h, Right x : ys, ins, kid')

extendEnv (Right x:xs) (Pi bind ty mod) kid
  | not (isKind ty) =
    open bind $ \ys t' -> do
      let y = head ys
          t'' = apply [(y, Var x)] t'
           -- note that Pi is existential
      addVar x ty
      if null (tail ys)
        then do
          (h, ys, ins, kid') <- extendEnv xs t'' kid
          return (h, (Right x : ys), ins, kid')
        else do
          (h, ys, ins, kid') <- extendEnv xs (Pi (abst (tail ys) t'') ty mod) kid
          return (h, (Right x : ys), ins, kid')

extendEnv a b kid = throwError $ ExtendEnvErr a b

-- | Infer a type for a type application.
handleTypeApp ::
     Exp -> Exp -> Exp -> Exp -> TCMonad (Exp, Exp, Modality)
handleTypeApp ann t' t1 t2 =
  case erasePos t' of
    Arrow k1 k2 _ -> do
      (_, ann2) <- typeCheck True t2 k1 identityMod
      return (k2, AppP ann ann2, identityMod)
    Pi (Abst vs b') ty mod -> do
        (_, ann2) <- typeCheck True t2 ty identityMod
        let t2' = erasePos ann2
        b'' <- betaNormalize (apply [(head vs, t2')] b')
        let k2 =
              if null (tail vs)
                then b''
                else Pi (abst (tail vs) b'') ty mod
        return (k2, AppP ann ann2, identityMod)
    a -> throwError $ KAppErr t1 (App t1 t2) a

-- | Infer a type for a term application.
handleTermApp ::
     Bool
  -> Exp
  -> Exp
  -> Exp
  -> Exp
  -> Exp
  -> Modality
  -> TCMonad (Exp, Exp, Modality)

handleTermApp flag ann pos t' t1 t2 mode1 = do
  (a1', rt, anEnv, mode1') <- addAnn flag mode1 pos ann t' []
  mapM (\(x, t) -> addVar x t) anEnv
  rt' <- updateWithSubst rt
  case rt' of
    Arrow ty1 ty2 mode2
      | isKind ty1 -> do
        (_, ann2) <- typeCheck True t2 ty1 identityMod
        let res = AppDepTy a1' ann2
        mode2' <- updateModality mode2
        return (ty2, res, modalAnd mode1' mode2')
    Arrow ty1 ty2 mode2 -> do
      mode3 <- newMode ["a", "b", "c"]
      (_, ann2) <- typeCheck flag t2 ty1 mode3
      mode3' <- updateModality mode3
      mode2' <- updateModality mode2
      let newMode = modalAnd (modalAnd mode1' mode2') mode3'
          res =
            if flag
              then AppP a1' ann2
              else App a1' ann2
      return (ty2, res, newMode)
    ArrowP ty1 ty2 -> do
      (_, ann2) <- typeCheck True t2 ty1 identityMod
      let res = AppP a1' ann2
      return (ty2, res, identityMod)
    b@(Pi (Abst xs m) ty mode2) -> do
        let flag' = isKind ty
        mode3 <- newMode2 ["a", "b"]
        (_, kann) <- typeCheck flag' t2 ty mode3
        let t2' = erasePos kann
        t2'' <-
          if not flag'
            then shape t2' `catchError`
                 \ e -> throwError $ AddDoc
                        (text "for the expression" $$ (nest 2 $ disp t2')) e
            else return t2'
        m' <- betaNormalize (apply [(head xs, t2'')] m)
        mode2' <- updateModality mode2
        mode3' <- updateModality mode3
        let res =
              case (flag, flag') of
                (False, False) -> AppDep a1' kann
                (False, True) -> AppDepTy a1' kann
                (True, False) -> AppDepInt a1' kann
                (True, True) -> AppDepTy a1' kann
        if null (tail xs)
          then
            return (m', res, modalAnd (modalAnd mode2' mode1') mode3')
          else
            return (Pi (abst (tail xs) m') ty mode2', res,
                     modalAnd (modalAnd mode2' mode1') mode3')
    b -> throwError $ ArrowErr t1 b

-- | Insert missing annotations to the term /a/ according to
-- its type when /a/ is applied to some other terms.
addAnn ::
     Bool
  -> Modality
  -> Exp
  -> Exp
  -> Exp
  -> [(Variable, Exp)]
  -> TCMonad (Exp, Exp, [(Variable, Exp)], Modality)
addAnn flag mode e a (Pos _ t) env = addAnn flag mode e a t env
addAnn flag mode e a (Mod (Abst _ t)) env = addAnn flag mode e a t env
addAnn flag mode e a (Bang t m) env = do
  let force =
        if flag
          then ForceP
          else Force
  t' <-
    if flag
      then shape t `catchError`
           \ e -> throwError $
                   AddDoc (text "for the expression" $$ (nest 2 $ disp t)) e
      else return t
  if flag
    then
    addAnn flag mode e (force a) t' env
    else
    do m' <- updateModality m
       let newMode = modalAnd mode m'
       addAnn flag newMode e (force a) t' env

addAnn flag mode e a (Forall (Abst xs t) ty) env = 
      let mvars = map MetaVar xs
          app = if isKind ty then AppType else AppTm
          a' = foldl app a mvars
          new = map (\x -> (x, ty)) xs
          t' = apply (zip xs mvars) t
       in addAnn flag mode e a' t' (new ++ env)

addAnn flag mode e a (PiImp (Abst xs t) ty mode2) env = do
  let app =
        if isKind ty
          then AppDepTy
          else if flag
                 then AppDepInt
                 else AppDep
      mvars = map MetaVar xs
      a' = foldl app a mvars
      new = map (\x -> (x, ty)) xs
      t' = apply (zip xs mvars) t
  mode2' <- updateModality mode2
  addAnn flag (modalAnd mode mode2') e a' t' (new ++ env)

addAnn flag mode e a (Imply bds ty mod) env = do
  let names = map (\ x -> "#goalinst") bds
  names' <- newNames names
  freshNames names' $ \ns -> do
    let instEnv = map (\x -> (x, e)) (zip ns bds)
    mapM_ (\((x, t), e) -> addGoalInst x t e) instEnv
    let a' = foldl AppDict a (map MetaVar ns)
    mod' <- updateModality mod
    addAnn flag (modalAnd mod' mode) e a' ty env

addAnn flag mode e a t env = return (a, t, env, mode)

-- expecting a to be either a Const or Var
handleBangConstVar flag a (Bang ty2 m2) mod = do
  mod' <- updateModality mod
  let msubs = modeResolution GEq identityMod mod'
  case msubs of
    Nothing -> throwError $ ModalityErr identityMod mod' a
    Just s' -> do
      updateModeSubst s'
      (ty', _, _) <- typeInfer flag a
      case ty' of
         Bang ty1 m1 -> equality flag a (Bang ty2 m2) mod
         _ -> handleBangValue flag a (Bang ty2 m2) mod

handleBangValue flag a ty1@(Bang ty m) mod = do
  r <- isValue a
  mod' <- updateModality mod
  if r then do
     let s = modeResolution GEq identityMod mod' 
     case s of
       Nothing -> throwError $ ModalityErr identityMod mod' a
       Just s'@(s1, s2, s3) -> do
         updateModeSubst s'
         m' <- updateModality m
         checkParamCxt a
         (t, ann) <- typeCheck flag a ty m'
         t' <- updateWithModeSubst t
         return (Bang t' (simplify m'), Lift ann)
  else do
      (tym, ann, cMode) <- typeInfer flag a
      cMode' <- updateModality cMode
      let s = modeResolution GEq cMode' mod'
      case s of
        Nothing -> throwError $ ModalityErr cMode' mod' a
        Just s'@(s1, s2, s3) -> do
          updateModeSubst s'     
          tym' <- updateWithSubst tym
          case erasePos tym' of
               tym1@(Bang _ _) -> do
                    tym1' <- updateWithModeSubst tym1
                    ty1' <- updateWithModeSubst ty1
                    (unifRes, (s, bs)) <- normalizeUnif GEq tym1' ty1'
                    case unifRes of
                      UnifError -> throwError $ NotEq a ty1' tym1'
                      ModeError p1 p2 ->
                        throwError $ ModalityGEqErr a ty1 tym1 p1 p2
                      Success -> do
                        ss <- getSubst
                        let sub' = s `mergeSub` ss
                        updateSubst sub'
                        updateModeSubst bs
                        ty1'' <- updateWithModeSubst ty1' >>= updateWithSubst
                        return (ty1'', ann)
               _ -> throwError $ BangValue a (Bang ty m)

-- note that ty1 is prefix free.
-- inferAddAnn flag a ty mod | trace ("inferAnn:"++ (show $ disp a) ++ ":" ++ (show $ disp ty)) $ False = undefined 
inferAddAnn flag a ty mod = do
  ty2 <- updateWithSubst ty
  if not (ty2 == ty)
    then typeCheck flag a ty2 mod
    else do
      (tym, ann, mode) <- typeInfer flag a
      tym1 <- updateWithSubst tym >>= updateWithModeSubst
      ty1 <- updateWithSubst ty2  >>= updateWithModeSubst
      (a2, tym1', anEnv, mode') <- addAnn flag mode a ann tym1 []
      mapM (\(x, t) -> addVar x t) anEnv
      mod' <- updateModality mod
      mode'' <- updateModality mode'
      let s = modeResolution GEq mode'' mod' 
      when (s == Nothing) $ throwError $
              ModalityErr mode'' mod' a
      let Just s'@(s1, s2, s3) = s
      updateModeSubst s'     
      tym1'' <- updateWithModeSubst tym1'
      ty1' <- updateWithModeSubst ty1
      (unifRes, (s, bs)) <- normalizeUnif GEq tym1'' ty1'
      case unifRes of
        UnifError -> -- error $ "tym:" ++ (show $ tym) ++ show flag
          throwError $ NotEq a ty1' tym1'' 
        ModeError p1 p2 ->
          throwError $ ModalityGEqErr a ty1' tym1'' p1 p2
        Success -> do
          ss <- getSubst
          let sub' = s `mergeSub` ss
          updateSubst sub'
          updateModeSubst bs
          ty1'' <- updateWithModeSubst ty1' >>= updateWithSubst
          return (ty1'', a2)


