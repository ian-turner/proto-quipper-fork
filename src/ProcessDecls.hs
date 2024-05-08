{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module processes Proto-Quipper-D declarations. For object and simple type declarations,
-- the type checker will generate instances for 'Simple', 'Parameter' and 'SimpParam' classes.
-- Each simple type
-- declaration also gives rise to a function that turns the simple type into a simple term.
-- We support two kinds of gate declarations, an ordinary gate declaration and a generic
-- control gate declaration. We support Haskell 98 style data type declaration with type class
-- constraint. Moreover, we support existential dependent data type in this
-- format. All top level functions must be of parameter types. Functions can be defined
-- by first giving its type annotation, or one can just annotate the types
-- for its arguments (in that case dependent pattern matching is not supported).
module ProcessDecls
  ( process
  , elaborateInstance
  ) where

import ModeResolve
import SyntacticOperations
import Syntax
import TCMonad
import TypeError
import Typechecking
import Utils

import Erasure

import Proofchecking
import Evaluation hiding (genNames)
import Nominal hiding ((.))
import Simplecheck
import Substitution
import TopMonad
import TypeClass

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.MultiSet as S
import Debug.Trace
import Text.PrettyPrint

-- | Process a top-level declaration
process :: Decl -> Top ()
process (Class pos d kd dict dictType mths) = do
  let methodNames = map (\(_, s, _) -> s) mths
      tp =
        Info
          { classifier = erasePos kd
          , identification = DictionaryType dict methodNames
          }
  tcTop $ addNewId d tp
  tcTop $ checkVacuous pos dictType
  (_, dictTypeAnn) <- tcTop $ typeChecking True dictType Type identityMod
  
  let fp =
        Info
          { classifier = abstractMode $ erasePos $ removeVacuousPi dictTypeAnn
          , identification = DataConstr d
          }
  tcTop $ addNewId dict fp
  mapM_ (makeMethod dict methodNames) mths
  where
    makeMethod constr methodNames (pos, mname, mty) = do
      let names = map getName methodNames
          Just i = elemIndex (getName mname) names
          mth =
            freshNames ("x" : names) $ \(x:mVars) ->
              LamDict
                (abst [x] $
                 LetPat
                   (Var x)
                   (abst (PApp constr (map Right mVars)) (Var $ mVars !! i)))
          tyy = erasePos $ removeVacuousPi mty
      tcTop $ checkVacuous pos tyy
      (_, tyy') <- tcTop $ typeChecking True tyy Type identityMod
      (tyy'', a) <- tcTop $ do
                      m <- newMode ["a", "b", "c"]
                      typeChecking False (Pos pos mth) tyy' m
      tcTop $ proofChecking False a tyy''        
      v <- evaluation a False
      let fp =
            Info
              { classifier = abstractMode tyy'
              , identification = DefinedMethod a v
              }
      tcTop $ addNewId mname fp
                  
process (Instance pos f ty mths) = do
  tcTop $ checkVacuous pos ty
  let (env, ty') = removePrefixes False ty
      (bds, h) = flattenArrows ty'
      d = flatten h
  tcTop $ checkOverlap h `catchError` \e -> throwError $ ErrPos pos e
  case d of
    Nothing -> throwError $ CompileErr $ ErrPos pos $ TypeClassNotValid h
    Just (Right d', args)
      | getName d' == "Simple" ->
        throwError $
        CompileErr $
        ErrPos pos $
        ErrDoc $ text "Simple class instance is not user-definable."
    Just (Right d', args)
      | getName d' == "SimpParam" ->
        throwError $
        CompileErr $
        ErrPos pos $
        ErrDoc $ text "SimpParam class instance is not user-definable."
    Just (Right d', args)
      | getName d' == "Parameter" ->
        throwError $
        CompileErr $
        ErrPos pos $
        ErrDoc $ text "Parameter class instance is not user-definable."
    Just (Right d', args) ->
      elaborateInstance pos f ty mths `catchError`
      \ e -> case e of
              CompileErr e' -> throwError $ CompileErr (ErrPos pos e')
              _ -> throwError e

process (Def pos f' ty' def' isClifford) = do
  tcTop $ checkVacuous pos ty'
  (_, ty) <- tcTop $ typeChecking True ty' Type identityMod
  let ty1 = erasePos $ removeVacuousPi ty
  p <- tcTop $ isParam ty1
  when (not p) $ throwError $ CompileErr $
    ErrPos pos (NotParam (Const f') ty')
  let info1 = Info {classifier = ty1,
                    identification = DefinedFunction Nothing}
  tcTop $ addNewId f' info1
  (ty1', ann) <- tcTop $ do
                   mode <- newMode ["a", "b", "c"]
                   typeChecking False (Pos pos def') ty1 mode
     -- note: need to do an erasure check before proof checking
  tcTop $ proofChecking False ann ty1'     
  v <- evaluation ann isClifford
  b <- tcTop $ isBasicValue v
  v' <-
    if b
      then do
        x <- tcTop $ typeChecking False (toExp v) ty1' identityMod
        return $ Just (snd x)
      else if isCirc v
             then return $ Just (Const f')
             else return Nothing
  let info2 =
        Info
          { classifier = ty1'
          , identification = DefinedFunction (Just (ann, v, v'))
          }
  tcTop $ addNewId f' info2
     

-- This definition without arguments can not be recursive.
process (Defn pos f Nothing def isClifford) = do
  (ty, a) <- tcTop $ typeInfering False (Pos pos def)
  let fvs = getVars All ty
  when (not $ S.null fvs) $
    throwError $ CompileErr $ ErrPos pos $ TyAmbiguous (Just f) ty
  tcTop $ checkVacuous pos ty
  p <- tcTop $ isParam ty
  when (not p && not (isConst def)) $
    throwError $ CompileErr (ErrPos pos $ NotParam (Const f) ty)
  tcTop $ proofChecking False a ty    
  v <- evaluation a isClifford
  b <- tcTop $ isBasicValue v
  v' <-
    if b
      then do
        x <- tcTop $ typeChecking False (toExp v) ty identityMod
        return $ Just (snd x)
      else return Nothing
  let fp =
        Info
          { classifier = erasePos $ removeVacuousPi ty
          , identification = DefinedFunction (Just (a, v, v'))
          }
  tcTop $ addNewId f fp
  where
    typeInfering b exp = do
      (ty', exp', _) <- typeInfer b exp
      exp'' <- resolveGoals exp'
      r <- updateWithSubst exp''
      ty'' <- resolveGoals ty' >>= updateWithSubst
      ty2 <- updateWithModeSubst ty''
      r' <- deMeta [] r `catchError` \ e -> throwError $ withPosition r e 
      return (abstractMode $ booleanVarElim ty2, r')
     
process (Defn pos f (Just tt) def isClifford) = do
  (_, tt') <-
    tcTop $
    typeChecking True tt Type identityMod `catchError`
       \e -> throwError $ ErrPos pos e
  let (Forall (Abst [r] ty') Type) = tt'
      ty'' = erasePos $ apply [(r, MetaVar r)] ty'
  let info1 = Info {classifier = ty'', identification = DefinedFunction Nothing}
  tcTop $ addNewId f info1
     -- the first check obtain the type information
  (tk', def0, s) <- tcTop $ 
                       typeChecking''' False (Pos pos def) ty'' 
  
  let tk1 = erasePos $ removeVacuousPi tk'
  let fvs = getVars All tk1
  when (not $ S.null fvs) $
    throwError $ CompileErr $ ErrPos pos $ AppendSub s $ TyAmbiguous (Just f) tk1
  tcTop $ checkVacuous pos tk1
  p <- tcTop $ isParam tk1
  when (not p && not (isConst def)) $
    throwError $ CompileErr (ErrPos pos $ NotParam (Const f) tk1)
  let info2 = Info {classifier = tk1, identification = DefinedFunction Nothing}
  tcTop $ addNewId f info2
     -- the second check
  (tk', def') <- tcTop $ do
                   mode <- newMode ["a", "b", "c"]
                   typeChecking False (Pos pos def) tk1 mode
  tcTop $ proofChecking False def' tk'  
  v <- evaluation def' isClifford
  b <- tcTop $ isBasicValue v
  v' <-
    if b
      then do
        x <- tcTop $ typeChecking False (toExp v) tk1 identityMod
        return $ Just (snd x)
      else return Nothing
  let fp =
        Info
          { classifier = tk'
          , identification = DefinedFunction (Just (def', v, v'))
          }
  tcTop $ addNewId f fp
  where
    typeChecking''' b exp ty = do
      setInfer True
      mode <- newMode ["a", "b", "c"]
      (ty', exp') <- typeCheck b exp ty mode
      setInfer False
      exp'' <- updateWithSubst exp'
      r <- resolveGoals exp''
      ty'' <- resolveGoals ty' >>= updateWithSubst
      s <- getSubst
      return (ty'', r, s)
     
process (Data pos d kd cons) = do
  let constructors = map (\(_, id, _) -> id) cons
      types = map (\(_, _, t) -> t) cons
  (_, kd') <- tcTop $ typeChecking True kd Sort identityMod
  dc <- tcTop $ determineClassifier d kd' constructors types
  let tp =
        Info
          {classifier = kd', identification = DataType dc constructors Nothing}
  tcTop $ addNewId d tp
  res <- tcTop $ mapM (\t -> typeChecking True (Pos pos t) Type identityMod) types
  let types' = map snd res
  let funcs =
        map
          (\t ->
             Info
               { classifier = erasePos $ removeVacuousPi t
               , identification = DataConstr d
               })
          types'
  tcTop $ zipWithM_ addNewId constructors funcs
  generateParamInstance pos dc (Base d) kd'
  where
    genEnv :: Int -> [(Maybe Variable, Exp)] -> [(Variable, Exp)]
    genEnv n ((Nothing, e):res) =
      let env = genEnv (n + 1) res
       in freshNames [("x" ++ show n)] $ \[x] -> (x, e) : env
    genEnv n ((Just a, e):res) =
      let env = genEnv n res
      in (a, e) : env
    genEnv n [] = []
    generateParamInstance pos Param d kd' =
      let (bds, _) = flattenArrows kd'
          env = genEnv 0 bds
          ns = map fst env
          head = foldl App d (map Var ns)
          s = Base (Id "Parameter")
          ty1 = foldr (\(x, t) y -> Forall (abst [x] y) t) (App s head) env
       in do let instId = Id $ "instAt" ++ hashPos pos ++ "Parameter"
             elaborateInstance pos instId ty1 []
    generateParamInstance pos SemiParam d kd' =
      let (bds, _) = flattenArrows kd'
          s = Base (Id "Parameter")
          env = genEnv 0 bds
          env' = filter (\(x, t) -> isKind t) env
          ns = map fst env
          vars = map Var ns
          head = App s (foldl App d vars)
          instId = Id $ "instAt" ++ hashPos pos ++ "Param"
          bodies = map (\v -> App s v) (map (\x -> Var (fst x)) env')
          ty1 =
            foldr (\(x, t) y -> Forall (abst [x] y) t) (Imply bodies head identityMod) env
       in elaborateInstance pos instId ty1 []
    generateParamInstance _ _ d kd' = return ()

process (Object pos id) = do
  let tp =
        Info
          { classifier = Type
          , identification = DataType Simple [] (Just (ELBase id))
          }
  tcTop $ addNewId id tp
  let s = Base (Id "Simple")
      sp = Base (Id "SimpParam")
      instId = Id $ "instAt" ++ hashPos pos ++ "Simple"
      instPS = Id $ "instAt" ++ hashPos pos ++ "SimpParam"
  elaborateInstance pos instId (App s (LBase id)) []

process (GateDecl pos id par t inv flag) = do
  let (quans, params) =
        case par of
          Nothing -> ([], [])
          Just x ->
            let (ps, x') = removePrefixes False x 
                ps' = [ (x, ty) | (Just x, ty) <- ps]
                x'' = flattenTensor x' 
            in (ps', x'')
  tcTop $ mapM_ checkParam params
  let (bds, h) = flattenArrows t
      t' = erasePos t
      bds' = map snd bds
      params' = map erasePos params
  tcTop $ mapM_ checkStrictSimple (h : bds')
  when (null bds) $ throwError $ CompileErr (GateErr pos id)
  let ty = Bang (foldr (\ (x, ty) y -> Forall (abst [x] y) ty) (foldr (\ x y -> Arrow x y identityMod) t params) quans) identityMod 
  (_, tk) <- tcTop $ typeChecking True ty Type identityMod
  let tk' = erasePos tk
  case inv of
    Nothing ->
      do  gate <- makeGate id params' t' flag Nothing
          let fp = Info {classifier = tk',
                         identification = DefinedGate gate}
          tcTop $ addNewId id fp
    Just (id', t'') -> 
      do  gate <- makeGate id params' t' flag (Just id')
          let fp = Info {classifier = tk',
                         identification = DefinedGate gate}
          tcTop $ addNewId id fp
          let t_inv = erasePos t''
              t_inv' = Bang (foldr (\ (x, ty) y -> Forall (abst [x] y) ty) (foldr (\ x y -> Arrow x y identityMod) t_inv params) quans) identityMod 
          gate' <- makeGate id' params' t_inv flag (Just id)
          let fp' = Info {classifier = t_inv', identification = DefinedGate gate'}
          tcTop $ addNewId id' fp'
  where
    checkParam t = do
      p <- isParam t
      when (not p) $ throwError $ ErrPos pos (NotAParam t)
    checkStrictSimple (Pos p e) =
      checkStrictSimple e `catchError` \e -> throwError $ ErrPos p e
    checkStrictSimple (LBase x) = return ()
    checkStrictSimple (Unit) = return ()
    checkStrictSimple (Tensor a b) = do
      checkStrictSimple a
      checkStrictSimple b
    checkStrictSimple a = throwError (NotStrictSimple a)

process (SimpData pos d n k0 eqs) = do
  (_, k2) <-
    tcTop $
    (typeChecking True k0 Sort identityMod
       `catchError` \e -> throwError $ collapsePos pos e)
  let k = foldr (\x y -> Arrow Type y identityMod) k2 (take n [0 ..])
  let constructors = map (\(_, _, c, _) -> c) eqs
      pretypes = map (\(_, _, _, t) -> t) eqs
      inds = map (\(_, i, _, _) -> i) eqs
  indx <-
    tcTop $
    checkIndices n d inds `catchError` \e -> throwError $ collapsePos pos e
  info <-
    tcTop $
    mapM
      (\(i, t) ->
         (preTypeToType n k2 i t) `catchError` \e ->
           throwError $ collapsePos pos e)
      (zip inds pretypes)
  let (cs, tys) = unzip info
  tcTop $ (checkCoverage d cs `catchError` \e -> throwError $ collapsePos pos e)
  let tp1 =
        Info
          { classifier = erasePos k
          , identification = DataType (SemiSimple indx) constructors Nothing
          }
  tcTop $ addNewId d tp1
  p <- tcTop $ mapM (\ty -> typeChecking True ty Type identityMod) tys
  let tys' = map snd p
  let funcs =
        map
          (\t -> Info {classifier = erasePos t, identification = DataConstr d})
          tys'
  tcTop $ zipWithM_ addNewId constructors funcs
  let s = Base $ Id "Simple"
      s1 = Base $ Id "Parameter"
  tvars <- tcTop $ newNames $ take n (repeat "a")
  tvars' <- tcTop $ newNames $ take n (repeat "b")
  let (bds1, _) = flattenArrows k2
      bds = map snd bds1
  tmvars <- tcTop $ newNames $ take (length bds) (repeat "x")
  let insTy =
        freshNames tvars $ \tvs ->
          freshNames tmvars $ \tmvs ->
            let env = map (\t -> (t, Type)) tvs ++ (zip tmvs bds)
                pre = map (\x -> App s (Var x)) tvs
                hd =
                  App s $
                  foldl App (foldl App (LBase d) (map Var tvs)) (map Var tmvs)
                ty =
                  foldr (\(x, t) y -> Forall (abst [x] y) t) (Imply pre hd identityMod) env
             in ty
  let insTy' =
        freshNames tvars $ \tvs ->
          freshNames tmvars $ \tmvs ->
            let env = map (\t -> (t, Type)) tvs ++ (zip tmvs bds)
                pre = map (\x -> App s1 (Var x)) tvs
                hd =
                  App s1 $
                  foldl App (foldl App (LBase d) (map Var tvs)) (map Var tmvs)
                ty =
                  foldr (\(x, t) y -> Forall (abst [x] y) t) (Imply pre hd identityMod) env
             in ty
  let instSimp = Id $ "instAt" ++ hashPos pos ++ "Simp"
      instParam = Id $ "instAt" ++ hashPos pos ++ "Parameter"
  elaborateInstance pos instSimp insTy []
  elaborateInstance pos instParam insTy' []
  tfunc <- tcTop $ makeTypeFun n k2 (zip constructors (zip inds tys))
  tfunc' <- tcTop $ erasure tfunc
  let tp =
        Info
          { classifier = erasePos k
          , identification =
              DataType (SemiSimple indx) constructors (Just tfunc')
          }
  tcTop $ addNewId d tp
process (OperatorDecl pos op level fixity) = return ()
process (ImportDecl p mod) = return ()

-- | Check if the defined instance head is overlapping with
-- existing type class instances.
-- checkOverlap :: Exp -> TCMonad ()
checkOverlap h = do
  es <- get
  let gs = globalInstance $ instanceContext es
  mapM_ helper gs
  where
    helper (id, exp) =
      let (vs, exp') = removePrefixes False exp
          sub = map (\ (Just x, t) -> (x, MetaVar x)) vs
          exp'' = apply sub exp'
          (_, head) = flattenArrows exp''
          (r, _) = runMatch head h
       in if r
            then throwError $ InstanceOverlap h id exp
            else return ()

-- | Construct an instance function. The argument /f'/ is
-- the name of the instance function and /ty/ is its type. The
-- arguments /mths/ are the method definitions.

elaborateInstance :: Position -> Id -> Exp -> [(Position, Id, Exp)] -> Top ()
elaborateInstance pos f' ty mths = do
  annTy <- tcTop $ typeChecking' True ty Type identityMod
  let (env, ty') = removePrefixes False annTy
      vars =
        map
          (\x ->
             case x of
               (Just y, _) -> y)
          env
      sub0 = zip vars (map Var vars)
      (bds0, h) = flattenArrows (apply sub0 ty')
      names = zipWith (\i b -> "inst" ++ (show i)) [0 ..] bds0
  case flatten h of
    Just (Right d', args) -> do
      dconst <- tcTop $ lookupId d'
      let DictionaryType c mm = identification dconst
          mm' = map (\(_, x, _) -> x) mths
      when (mm /= mm') $
        throwError $ CompileErr $ ErrPos pos (MethodsErr mm mm')
      funPac <- tcTop $ lookupId c
      let constTy = classifier funPac
      let constTy' = instantiateWith constTy args
      let (bds, _) = flattenArrows constTy'
      freshNames names $ \ns -> do
        let instEnv = zip ns (map snd bds0)
                 -- add the name of instance function and its type to the
                 -- global instance context, this enable recursive dictionary
                 -- construction.
        tcTop $ addGlobalInst f' annTy
                 -- Type check and elaborate each method
        ms' <- tcTop $ zipWithM (helper env instEnv) mths (map snd bds)
                 -- construct the annotated version of the instance function.
        let def = foldl App (foldl AppType (Const c) args) ms'
            def' =
              if null ns
                then rebind env def
                else rebind env $ LamDict (abst ns def)
            annTy' = erasePos annTy
        
        v <- evaluation def' False
        let fp =
              Info
                { classifier = annTy'
                , identification = DefinedInstFunction def' v
                }
        tcTop $ addNewId f' fp
        tcTop $ proofChecking False def' annTy'            
    _ -> throwError $ CompileErr $ ErrPos pos $ TypeClassNotValid h
  where
    instantiateWith (Forall (Abst vs b') t) xs =
      let xs' = drop (length vs) xs
          b'' = apply (zip vs xs) b'
       in instantiateWith b'' xs'
    instantiateWith (Mod (Abst _ t)) xs = instantiateWith t xs
    instantiateWith t xs = t
    helper env instEnv (p, _, m) t =
      let env' =
            map
              (\x ->
                 case x of
                   (Just y, a) -> (y, a))
              env
       in do mapM_ (\(x, t) -> addVar x t) env'
             mapM_ (\(x, t) -> insertLocalInst x t) instEnv
             updateParamInfo (map snd instEnv)
             mode <- newMode ["a", "b", "c"]
             (t', a) <-
               typeChecking'' (map fst env') False (Pos p m)
                   (erasePos t) mode
             mapM_ (\(x, t) -> removeVar x) env'
             mapM_ (\(x, t) -> removeLocalInst x) instEnv
             return a
    rebind [] t = t
    rebind ((Just x, ty):res) t
      | isKind ty = LamType (abst [x] (rebind res t))
    rebind ((Just x, ty):res) t
      | otherwise = LamTm (abst [x] (rebind res t))
    -- A version of type checking that avoids checking forall param.
    typeChecking' b exp ty mod = do
      setCheckBound False
      (ty', exp') <- typeCheck b exp ty mod
      setCheckBound True
      exp'' <- updateWithSubst exp'
      r <- resolveGoals exp''
      deMeta [] r `catchError` \ e -> throwError $ withPosition r e 
    -- a version of typeChecking that uses unEigenBound instead of unEigen
    typeChecking'' vars b exp ty mod = do
      (ty', exp') <- typeCheck b exp ty mod
      exp'' <- resolveGoals exp'
      r <- updateWithSubst exp''
      ty'' <- resolveGoals ty' >>= updateWithSubst
      r' <- deMeta [] r `catchError` \ e -> throwError $ withPosition r e 
      return (ty'', r')

                 
-- | Determine the classifier for a data type declaration.
determineClassifier :: Id -> Exp -> [Id] -> [Exp] -> TCMonad DataClassifier
determineClassifier d kd constructors types = do
  f <- queryParam d kd constructors types
  if f
    then return Param
    else do
      g <- querySemiParam d kd constructors types
      if g
        then return SemiParam
        else return Unknown
  where
    queryParam d kd constructors types = do
      let tp =
            Info
              { classifier = kd
              , identification = DataType Param constructors Nothing
              }
      addNewId d tp
      r <- mapM helper types
      return $ and r
      where
        helper ty = do
          let (_, ty') = removePrefixes True ty
              (args, h) = flattenArrows ty'
          r <- mapM isParam (map snd args)
          return $ and r
    querySemiParam d kd constructors types = do
      let tp =
            Info
              { classifier = kd
              , identification = DataType SemiParam constructors Nothing
              }
      addNewId d tp
      r <- mapM helper types
      return $ and r
      where
        helper ty = do
          let (_, ty') = removePrefixes True ty
              (args, h) = flattenArrows ty'
          r <-
            mapM
              (\a -> do
                 r1 <- isParam a
                 r2 <- isSemiParam a
                 return (r1 || r2))
              (map snd args)
          return $ and r

-- | Construct a gate from a gate declaration.
makeGate :: Id -> [Exp] -> Exp -> Bool -> Maybe Id -> Top Value
makeGate id ps t flag inv =
  let lp = length ps + 1
      ns = getName "x" lp
      (inss, outExp) = makeInOut t
      outNames = size outExp
      inExp =
        if null inss
          then VUnit
          else foldl VTensor (head inss) (tail inss)
      inNames = size inExp
   in freshNames ns $ \(y:xs) ->
        freshLabels inNames $ \ins ->
          freshLabels outNames $ \outs ->
            let params = map VVar xs
                inExp' = toVal inExp ins
                outExp' = toVal outExp outs
                g = Gate id params inExp' outExp' VStar flag inv ins outs
                morph = Wired $ abst (ins ++ outs) (Circuit inExp' [g] outExp' ins outs VStar)
                env = Map.fromList [(y, morph)]
                unbox_morph =
                  ELam $ etaPair y (length inss) (EForce $ EApp EUnBox (EVar y))
                res = VLiftCirc (abst xs (abst env unbox_morph))
             in return res
  where
    makeInOut (Arrow t t' _) =
      let (ins, outs) = makeInOut t'
       in (toV t : ins, outs)
    makeInOut (Pos p e) = makeInOut e
    makeInOut a = ([], toV a)
    toV Unit = VUnit
    toV (Tensor a b) = VTensor (toV a) (toV b)
    toV (LBase x) = VLBase x
    getName x lp =
      let xs = x : xs
       in zipWith (\x y -> x ++ show y) (take lp xs) [0 ..]
    etaPair x n e
      | n == 0 = error "from etaPair"
    etaPair x n e =
      freshNames (getName "y" n) $ \xs ->
        let xs' = map EVar xs
            pairs = foldl EPair (head xs') (tail xs')
         in abst xs (EApp e pairs)

-- | Make a type function for runtime labels generation. The input /n/
-- is the number of type variables, /k0/ is the kind annotation.
makeTypeFun :: Int -> Exp -> [(Id, (Maybe Int, Exp))] -> TCMonad Exp
makeTypeFun n k0 ((c, (Nothing, ty)):[]) =
  let (env, m) = removePrefixes False ty
      vars = map (\(Just x, _) -> x) env
      (bds, h) = flattenArrows m
      bds' = map snd bds
      exp = foldl App (Const c) bds'
      t =
        if null vars
          then exp
          else Lam (abst vars exp)
   in return t
makeTypeFun n k0 xs@((_, (Just i, _)):_) = do
  tyvars <- newNames $ take n (repeat "a")
  let (bds, _) = flattenArrows k0
  tmvars <- newNames $ take (length bds) (repeat "x")
  freshNames tyvars $ \tvars ->
    freshNames tmvars $ \mvars ->
      let (tmv1, cv:tmv2) = splitAt i mvars
          bindings = map (helper $ tvars ++ tmv1 ++ tmv2) xs
          vs = tvars ++ tmv1 ++ (cv : tmv2)
          exp = Lam (abst vs $ Case (Var cv) (B bindings))
       in return exp
  where
    helper vss (c, (Just i, ty)) =
      let (env, m) = removePrefixes False ty
          (bds, h) = flattenArrows m
       in case flatten h of
            Just (Right w, args) ->
              let (ttvars, pat:mmvars) = splitAt (n + i) args
                  renamings =
                    zip (map getVar ttvars ++ map getVar mmvars) (map Var vss)
                  rhs = apply renamings $ foldl App (Const c) (map snd bds)
                  r = abst (toPat pat) rhs
               in r
            Nothing -> error $ show (text "from makeTypeFun helper:" <+> disp h)
    getVar (Var x) = x
    getVar (Pos p e) = getVar e
    getConst (Const x) = x
    getConst (Pos p e) = getConst e
    toPat p =
      let (h, as) = unwind AppFlag p
       in PApp (getConst h) (map (\a -> Right (getVar a)) as)

-- | Check an expression against a type. It is a wrapper on the 'typeCheck' function.
typeChecking :: Bool -> Exp -> Exp -> Modality -> TCMonad (Exp, Exp)
typeChecking b exp ty mod = do
  (ty', exp') <- typeCheck b exp ty mod
  exp'' <- resolveGoals exp'
  r <- updateWithSubst exp'' >>= updateWithModeSubst
  ty'' <- resolveGoals ty' >>= updateWithSubst
  ty2 <- updateWithModeSubst ty''
  r' <- deMeta [] r `catchError` \ e -> throwError $ withPosition r e 
  return (abstractMode $ booleanVarElim ty2, r')

-- | Check an annotated expression against a type. It is a wrapper on 'proofCheck' function.
proofChecking :: Bool -> Exp -> Exp -> TCMonad ()
proofChecking b exp ty =
  proofCheck b exp ty `catchError` \ e -> throwError  $ PfErrWrapper exp e ty
