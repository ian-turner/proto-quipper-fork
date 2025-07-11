{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | This module defines various of utility functions for the 'TCMonad'.
module TCMonad where

import Syntax
import TypeError
import Utils

import ModeResolve
import Nominal
import Substitution
import SyntacticOperations

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State

import Data.List
import qualified Data.MultiSet as S
import Data.MultiSet (MultiSet)

import qualified Data.Map as Map
import Data.Map (Map)
import Debug.Trace
import Text.PrettyPrint

-- | Global context.
type Context = Map Id Info

-- | A data type that captures all the information
-- about a top-level identifier.
data Info =
  Info
    { classifier :: Exp
    , identification :: Identification
    }

-- | Identification for top-level identifiers. 
data Identification
  = DataConstr Id  -- ^ Data constructor, 'Id' is its type constructor.
  | DefinedGate Value -- ^ Gate, and its representation .
  | DefinedFunction (Maybe (Exp, Value, Maybe Exp))
  -- ^ Defined function. Exp : its annotated version, Value: function value,
  -- and Maybe Exp: an expression of a basic value.
  | DefinedMethod Exp Value
  -- ^ Method, its annotated version and value.
  | DefinedInstFunction Exp Value
  -- ^ Instance function, its annotated version and value.
  | DataType DataClassifier [Id] (Maybe EExp)
  -- ^ A data type, its classifier and 
  -- constructors. If it is a simple type, then its corresponding runtime
  -- function.
  | DictionaryType Id [Id]
  -- ^ Dictionary type-constructor and all of its method ids.
  deriving (Show)

-- | Data type classifier.
data DataClassifier
  = Param -- ^ Parameter data type.
  | SemiParam -- ^ Semi-parameter data type, e.g., List a.
  | Simple -- ^ Types defined by the 'object' keyword. e.g. Qubit
  | SemiSimple (Maybe Int)
  -- ^ Data types defined by the /simple/ keyword. E.g. @Vec a n@.
  | Unknown -- ^ None of the above.
  deriving (Show, Eq)

-- | Local type checking context.
data LContext =
  LContext
    { localCxt :: Map Variable VarInfo -- ^ Local variable information.
    , globalCxt :: Context -- ^ Global typing context.
    }

-- | A record that captures all the information about a variable
-- during type checking.
data VarInfo =
  VarInfo
    { varClassifier :: Exp
    , varIdentification :: VarIdentification
    }

-- | Information about a term variable or a type variable.
data VarIdentification
  = TermVar ZipCount (Maybe Exp)
                         -- ^ Term variable, its count and its definition if it is defined
                         -- by let expression.
  | TypeVar Bool Bool-- ^ Type variable. The first 'Bool' indicates
                         -- whether a type variable is a parameter variable.
                         -- The second 'Bool' indicates if it is a simple type variable.

-- | Convert a global context to a local one.
fromGlobal :: Context -> LContext
fromGlobal gl = LContext {localCxt = Map.empty, globalCxt = gl}

type GlobalInstanceCxt = [(Id, Exp)]

-- | A record for local type class instance context.
data InstanceContext =
  IC
    { localInstance :: [(Variable, Exp)]
  -- ^ Local instance assumptions.
    , globalInstance :: GlobalInstanceCxt
  -- ^ Global instance declarations.
    , goalInstance :: [(Variable, (Exp, Exp))]
  -- ^ Current goal (constraint) variables that
  -- needed to be resolved. It has the format:
  -- (variable, (type, original-term-for-error-info)).
    }

-- | Convert a global instance context into a local one.
makeInstanceCxt :: GlobalInstanceCxt -> InstanceContext
makeInstanceCxt gl =
  IC {localInstance = [], globalInstance = gl, goalInstance = []}

-- | The type checking monad transformer.
newtype TCMonadT m a =
  TC
    { runTC :: ExceptT TypeError (StateT TypeState m) a
    }
  deriving ( Functor
           , Monad
           , Applicative
           , MonadError TypeError
           , MonadState TypeState
           )

instance MonadTrans TCMonadT where
  lift ma = TC (lift (lift ma))

-- | The type checking monad.
type TCMonad a = TCMonadT Identity a

-- | A state for 'TCMonad'.
data TypeState =
  TS
    { lcontext :: LContext -- ^ Current local typing context.
    , subst :: Subst -- ^ Substitution generated during type checking.
    , clock :: Int -- ^ A counter.
    , instanceContext :: InstanceContext -- ^ A local instance context.
    , checkForallBound :: Bool
    -- ^ Whether or not to check if a Forall variable
    -- is well-quantified. It is unchecked when the
    -- type is intended to be used as an instance type.
    , infer :: Bool -- ^ If it is in infer mode.
    , modeSubstitution :: (ModeSubst, ModeSubst, ModeSubst)
    -- ^ Mode substitution generated during type checking.
    }

-- | Initial type state from a global typing context and a
-- global type class instance context.
initTS :: Map Id Info -> GlobalInstanceCxt -> TypeState
initTS gl inst =
  TS (fromGlobal gl) Map.empty 0 (makeInstanceCxt inst) True False ([], [], [])

-- | A run function for 'TCMonadT'.
runTCMonadT ::
     Context
  -> GlobalInstanceCxt
  -> TCMonadT m a
  -> m (Either TypeError a, TypeState)
runTCMonadT env inst m = runStateT (runExceptT $ runTC m) (initTS env inst)

-- | Set whether or not to check the type of a forall-quantified variable is
-- a parameter type.
setCheckBound x = do
  st <- get
  put st {checkForallBound = x}

-- | Set current mode to infer mode if input is True.
setInfer x = do
  st <- get
  put st {infer = x}

-- | Obtain the 'checkForallBound' flag.
getCheckBound :: TCMonad Bool
getCheckBound = get >>= \x -> return $ checkForallBound x

-- | Obtain the 'infer' flag.
getInfer :: TCMonad Bool
getInfer = get >>= \x -> return $ infer x

-- | Look up an identifier for information.
lookupId :: Id -> TCMonad Info
lookupId x = do
  ts <- get
  let gamma = lcontext ts
  case Map.lookup x (globalCxt gamma) of
    Nothing -> throwError (NoDef x)
    Just tup -> return tup

-- | Look up a variable from the typing context.
-- Note that type variable does not have count.
lookupVar :: Variable -> TCMonad (Exp, Maybe ZipCount)
lookupVar x = do
  ts <- get
  let gamma = lcontext ts
      lg = localCxt gamma
      s = subst ts
      m = modeSubstitution ts
  case Map.lookup x lg of
    Nothing -> throwError $ UnBoundErr x
    Just lp -> do
      let a = substitute s $ bSubstitute m $ varClassifier lp
          varid = varIdentification lp
      case varid of
        TermVar c _ -> return (a, Just c)
        _ -> return (a, Nothing)

-- | Determine if a constructor is a constructor of a semi-simple type,
-- or a type constructor is a semi-simple type.
isSemiSimple :: Id -> TCMonad (Bool, Maybe Int)
isSemiSimple id = do
  tyinfo <- lookupId id
  case identification tyinfo of
    DataConstr dt -> do
      info <- lookupId dt
      case identification info of
        DataType (SemiSimple b) _ _ -> return (True, b)
        _ -> return (False, Nothing)
    DataType (SemiSimple b) _ _ -> return (True, b)
    _ -> return (False, Nothing)

-- | Determine if a type expression is a parameter type.
isParam :: Exp -> TCMonad Bool
isParam a
  | isKind a = return True
isParam (Unit) = return True
isParam (LBase id) = return False
isParam (Var x) = do
  ts <- get
  let gamma = lcontext ts
      lg = localCxt gamma
  case Map.lookup x lg of
    Nothing -> return False
    Just lti ->
      case varIdentification lti of
        TypeVar b _ -> return b
        _ -> return False
isParam (Base id) = do
  pac <- lookupId id
  case identification pac of
    DataType Param _ _ -> return True
    DataType _ _ _ -> return False
isParam t@(App x _) =
  if erasePos x == RealNum then return True else  
  case flatten t of
    Nothing -> return False
    Just (Right id, args) -> do
      tyinfo <- lookupId id
      case identification tyinfo of
        DataType Param _ _ -> return True
        DataType Simple _ _ -> return False
        DataType Unknown _ _ -> return False
        DataType _ _ _ -> helper tyinfo args
        DictionaryType _ _ -> return True
    _ -> error $ "isParam " ++ (show $ disp t)
  where
    helper tyinfo args = do
      let k = classifier tyinfo
          (inds, h) = flattenArrows k
          m = zip (map snd inds) args
      s <-
        mapM
          (\(i, a) ->
             if i == Type
               then isParam a
               else if isKind i
                      then return False
                      else return True)
          m
      return $ and s


isParam t@(AppP x _) =
  if erasePos x == RealNum then return True else
  case flatten t of
    Nothing -> return False
    Just (Right id, args) -> do
      tyinfo <- lookupId id
      case identification tyinfo of
        DataType Param _ _ -> return True
        DataType Simple _ _ -> return False
        DataType Unknown _ _ -> return False
        DataType _ _ _ -> helper tyinfo args
        DictionaryType _ _ -> return True
    _ -> error $ "isParam " ++ (show $ disp t)
  where
    helper tyinfo args = do
      let k = classifier tyinfo
          (inds, h) = flattenArrows k
          m = zip (map snd inds) args
      s <-
        mapM
          (\(i, a) ->
             if i == Type
               then isParam a
               else if isKind i
                      then return False
                      else return True)
          m
      return $ and s
isParam (Tensor t t') = do
  r1 <- isParam t
  r2 <- isParam t'
  return $ r1 && r2
isParam (ArrowP t t') = return True
isParam (PiInt (Abst x t) ty) = return True
isParam (Imply xs t _) = isParam t
isParam (Bang q _) = return True
isParam (Circ t1 t2 _) = return True
isParam (Pos _ e) = isParam e
isParam (Exists (Abst x t) ty) = do
  x <- isParam t
  y <- isParam ty
  return $ x && y
isParam a
  | otherwise = return False

-- | Check if an expression is a semi-parameter type. For example,
-- @List a@ and @Vec a@ are both semi-parameter types because if @a@ is a parameter type,
-- then both @List a@ and @Vec a@ are parameter types.
isSemiParam :: Exp -> TCMonad Bool
isSemiParam a
  | isKind a = return True
isSemiParam (Unit) = return True
isSemiParam (LBase id) = return False
isSemiParam (Base id) = return False
isSemiParam (Var _) = return True
isSemiParam t@(App _ _) =
  case flatten t of
    Nothing -> return False
    Just (Right id, args) -> do
      tyinfo <- lookupId id
      case identification tyinfo of
        DataType Param _ _ -> return True
        DataType Simple _ _ -> return False
        DataType Unknown _ _ -> return False
        DataType (SemiSimple _) _ _ -> helper tyinfo args
        DataType SemiParam _ _ -> helper tyinfo args
        DictionaryType _ _ -> return True
  where
    helper tyinfo args = do
      let k = classifier tyinfo
          (inds, h) = flattenArrows k
          m = zip (map snd inds) args
      s <-
        mapM
          (\(i, a) ->
             if i == Type
               then isSemiParam a
               else if isKind i
                      then return False
                      else return True)
          m
      return $ and s
isSemiParam (Tensor t t') = do
  r1 <- isSemiParam t
  r2 <- isSemiParam t'
  return $ r1 && r2
isSemiParam (Bang q _) = return True
isSemiParam (Circ t1 t2 _) = return True
isSemiParam (Exists (Abst x t) ty) = do
  r1 <- isSemiParam t
  r2 <- isSemiParam ty
  return $ r1 && r2
isSemiParam (Pos _ e) = isSemiParam e
isSemiParam a = return False

-- | Increment the count of a variable by one.
updateCount :: Variable -> TCMonad ()
updateCount x = do
  ts <- get
  let gamma = lcontext ts
      lty = localCxt gamma
  case Map.lookup x lty of
    Nothing -> error "from updateCount."
    Just lpkg ->
      case varIdentification lpkg of
        TypeVar b _ -> return ()
        TermVar c d -> do
          let lty' =
                Map.insert x (lpkg {varIdentification = TermVar (incr c) d}) lty
              gamma' = gamma {localCxt = lty'}
          put ts {lcontext = gamma'}

-- | Get the shape of an expression. It does not transform a kind expression.
-- shape a | trace ("shape:" ++ show ( a)) False = undefined
shape a
  | isKind a = return a
shape Unit = return Unit
shape a@(RealOp _) = return a
shape a@(WrapR _) = return a
shape (LBase x)
  | getName x == "Qubit" = return Unit
shape a@(LBase x)
  | otherwise = return a
shape Star = return Star
shape a@(Base _) = return a
shape a@(Const _) = return a
shape a@(Var x) = do
  ts <- get
  let gamma = lcontext ts
      lty = localCxt gamma
  case Map.lookup x lty of
    Nothing -> return a
    Just lpkg ->
      case varIdentification lpkg of
        TermVar _ _ -> return a
        TypeVar _ s
          | s -> return Unit
          | otherwise -> return a

shape a@(MetaVar x) = do
  ts <- get
  let gamma = lcontext ts
      lty = localCxt gamma
  case Map.lookup x lty of
    Nothing -> return a
    Just lpkg ->
      case varIdentification lpkg of
        TermVar _ _ -> return a
        TypeVar _ s
          | s -> return Unit
          | otherwise -> return a
shape a@(Bang _ (M (BConst False) _ _)) = throwError ShapeErr
shape a@(Bang _ _) = return a
shape a@(Lift _) = return a
shape a@(Circ _ _ _) = return a
shape a@(ForceP m) = return a
shape (Force m) = do
  m' <- shape m
  return (ForceP m)
shape a@(App t1 t2) = do
  t1' <- shape t1
  t2' <- shape t2
  return $ AppP t1' t2'
shape a@(WithType t1 t2) = do
  t1' <- shape t1
  t2' <- shape t2
  return $ WithType t1' t2'

shape a@(AppP t1 t2) =
  case flatten a of
    Just (Right k, _) -> do
      p <- isParam a
      if p
        then return a
        else shapeApp t1 t2
    _ -> shapeApp t1 t2
  where
    shapeApp t1 t2 = do
      t1' <- shape t1
      t2' <- shape t2
      return (AppP t1' t2')
shape a@(AppDep t1 t2) =
  case erasePos t1 of
    Box -> return $ AppDepInt Box t2
    _ -> do
      t1' <- shape t1
      t2' <- shape t2
      return (AppDepInt t1' t2')
shape (AppDepTy t t') = do
  t1 <- shape t
  return (AppDepTy t1 t')
shape (LamDepTy (Abst xs t)) = do
  t' <- shape t
  return $ LamDepTy (abst xs t')
shape (AppDict t1 t2) = do
  t1' <- shape t1
  return $ AppDict t1' t2
shape (AppType t1 t2) = do
  t1' <- shape t1
  return $ AppType t1' t2
shape (AppTm t1 t2) = do
  t1' <- shape t1
  return $ AppTm t1' t2
shape (Tensor t1 t2) = Tensor <$> shape t1 <*> shape t2
shape (Pair t1 t2) = Pair <$> shape t1 <*> shape t2
shape (Arrow t1 t2 (M (BConst False) _ _)) =
  throwError ShapeErr
shape (Arrow t1 t2 _) =   ArrowP <$> shape t1 <*> shape t2
shape (Imply bds h (M (BConst False) _ _)) =
  throwError ShapeErr
shape (Imply bds h m) = Imply <$> return bds <*> shape h <*> return m

shape (Exists (Abst x t) t2) = do
  t' <- shape t
  t2' <- shape t2
  return $ Exists (abst x t') t2'
shape (Forall (Abst x t) t2) = do
  t' <- shape t
  return $ Forall (abst x t') t2
shape a@(ArrowP a1 a2) = ArrowP <$> shape a1 <*> shape a2

shape (Pi (Abst x t) t2 (M (BConst False) _ _)) = throwError ShapeErr

shape (Pi (Abst x t) t2 _) = 
  do t' <- shape t
     t2' <- shape t2
     return $ PiInt (abst x t') t2'

shape (PiImp (Abst x t) t2 (M (BConst False) _ _)) = throwError ShapeErr
shape (PiImp (Abst x t) t2 m) = do
  t' <- shape t
  t2' <- shape t2
  return $ PiInt (abst x t') t2' 

shape (Lam (Abst x t)) = do
  t' <- shape t
  return $ LamP (abst x t')
shape (LamAnn ty (Abst x t)) = do
  t' <- shape t
  ty' <- shape ty
  return $ LamAnnP ty' (abst x t')
shape (LamDep (Abst x t)) = do
  t' <- shape t
  return $ LamDepInt (abst x t')
shape (LamType (Abst x t)) = do
  t' <- shape t
  return $ LamType (abst x t')
shape (LamTm (Abst x t)) = do
  t' <- shape t
  return $ LamTm (abst x t')
shape (LamDict (Abst x t)) = do
  t' <- shape t
  return $ LamDict (abst x t')
shape Box = return Box
shape UnBox = return UnBox
shape Reverse = return Reverse
shape Controlled = return Controlled
shape WithComputed = return WithComputed
shape Dynlift = throwError ShapeErr
shape (Case tm (B br)) = do
  tm' <- shape tm
  br' <- helper' br
  return $ Case tm' (B br')
  where
    helper' ps =
      mapM
        (\b ->
           open b $ \ys m -> do
             m' <- shape m
             return $ abst ys m')
        ps
shape (Let m bd) = do
  m' <- shape m
  open bd $ \y b -> do
    b' <- shape b
    return $ Let m' (abst y b')
shape (LetPair m bd) = do
  m' <- shape m
  open bd $ \y b -> do
    b' <- shape b
    return $ LetPair m' (abst y b')
shape (LetPat m (Abst (PApp id vs) b)) = do
  m' <- shape m
  b' <- shape b
  return $ LetPat m' (abst (PApp id vs) b')
shape (Pos _ a) = shape a
shape a = error $ "from shape: " ++ (show $ disp a)

-- | Update an expression with the current substitution generated by the unification.
updateWithSubst :: Exp -> TCMonad Exp
updateWithSubst e = do
  ts <- get
  return $ substitute (subst ts) e

-- | Determine if a matching on a variable is dependent pattern matching.
isDpmVar :: Variable -> Exp -> TCMonad Bool
isDpmVar x e = do
  let fvs = getVars All e
      b = x `S.member` fvs
  s <- get
  ss <- getSubst
  let lenv = Map.toList $ localCxt $ lcontext s
      bs = or $ map (\ (y, varinfo) -> x `S.member` (getVars All $ substitute ss $ varClassifier varinfo)) lenv
  return (b || bs)

-- | Add a variable into the typing context.
addVar :: Variable -> Exp -> TCMonad ()
-- addVar x t | trace ("adding:"++ show (disp x) ++ ":" ++ show (disp t) ) $ False = undefined
addVar x t = do
  ts <- get
  let b = isKind t
      env = lcontext ts
      pkg =
        if b
          then VarInfo t (TypeVar False False)
          else VarInfo t (TermVar initCount Nothing)
      gamma' = Map.insert x pkg (localCxt env)
      env' = env {localCxt = gamma'}
  put ts {lcontext = env'}

-- | Add a variable and its definition into the typing context.
addVarDef :: Variable -> Exp -> Exp -> TCMonad ()
addVarDef x t m = do
  ts <- get
  let env = lcontext ts
      gamma' =
        Map.insert x (VarInfo t (TermVar initCount (Just m))) (localCxt env)
      env' = env {localCxt = gamma'}
  put ts {lcontext = env'}

-- | Add a goal variable, its type and its origin into the type class context.
addGoalInst :: Variable -> Exp -> Exp -> TCMonad ()
addGoalInst x t e = do
  ts <- get
  let env = instanceContext ts
      gamma' = (x, (t, e)) : goalInstance env
      env' = env {goalInstance = gamma'}
  put ts {instanceContext = env'}

-- | Remove a variable from the local typing environment.
removeVar :: Variable -> TCMonad ()
removeVar x = do
  ts <- get
  let gamma = lcontext ts
      lt = Map.delete x (localCxt gamma)
      gamma' = gamma {localCxt = lt}
  put ts {lcontext = gamma'}

-- | Check if a type class is well-formed.
checkClass :: Exp -> TCMonad ()
checkClass h =
  case flatten h of
    Nothing -> throwError $ NotAValidClass h
    Just (Right d', args) -> do
      dconst <- lookupId d'
      let dict = identification dconst
      ensureDict dict h
  where
    ensureDict (DictionaryType _ _) _ = return ()
    ensureDict x h = throwError $ NotAValidClass h

-- | Update parameter info if a type variable has
-- a 'Parameter' assumption
updateParamInfo :: [Exp] -> TCMonad ()
updateParamInfo [] = return ()
updateParamInfo (p:ps) =
  case flatten p of
    Just (Right i, [arg])
      | getName i == "Parameter" ->
        case erasePos arg of
          Var x -> updateParam x >> updateParamInfo ps
          _ -> updateParamInfo ps
    _ -> updateParamInfo ps
  where
    updateParam :: Variable -> TCMonad ()
    updateParam x = do
      ts <- get
      let gamma = lcontext ts
          lty = localCxt gamma
      case Map.lookup x lty of
        Nothing -> error "from updateParam."
        Just lpkg ->
          case varIdentification lpkg of
            TermVar c _ ->
              error
                "from updateParam, unexpected term variable when updating param info."
            TypeVar _ s -> do
              let lti' =
                    Map.insert x (lpkg {varIdentification = TypeVar True s}) lty
                  gamma' = gamma {localCxt = lti'}
              put ts {lcontext = gamma'}

-- | Update simple info if a type variable has a 'Simple' assumption
updateSimpleInfo :: [Exp] -> TCMonad ()
updateSimpleInfo [] = return ()
updateSimpleInfo (p:ps) =
  case flatten p of
    Just (Right i, [arg])
      | getName i == "Simple" ->
        case erasePos arg of
          Var x -> updateSimple x >> updateSimpleInfo ps
          _ -> updateSimpleInfo ps
    _ -> updateSimpleInfo ps
  where
    updateSimple :: Variable -> TCMonad ()
    updateSimple x = do
      ts <- get
      let gamma = lcontext ts
          lty = localCxt gamma
      case Map.lookup x lty of
        Nothing -> error "from updateSimple."
        Just lpkg ->
          case varIdentification lpkg of
            TermVar c _ ->
              error
                "from updateSimple, unexpected term variable when updating simple info."
            TypeVar p _ -> do
              let lti' =
                    Map.insert x (lpkg {varIdentification = TypeVar p True}) lty
                  gamma' = gamma {localCxt = lti'}
              put ts {lcontext = gamma'}

-- | Add a local instance assumption for instance resolution.
insertLocalInst :: Variable -> Exp -> TCMonad ()
insertLocalInst x t = do
  ts <- get
  let env = instanceContext ts
      gamma' = (x, t) : localInstance env
      env' = env {localInstance = gamma'}
  put ts {instanceContext = env'}

-- | Remove a local instance assumption.
removeLocalInst :: Variable -> TCMonad ()
removeLocalInst x = do
  ts <- get
  let env = instanceContext ts
      gamma' = deleteBy (\a b -> fst a == fst b) (x, Unit) $ localInstance env
      env' = env {localInstance = gamma'}
  put ts {instanceContext = env'}

-- | Generate a list of names that is relatively fresh using the
-- clock value. 
newNames :: [String] -> TCMonad [String]
newNames ns = do
  ts <- get
  let i = clock ts
      ns' = zipWith (\j n -> n ++ show j) [i ..] ns
      j = i + length ns
  put ts {clock = j}
  return ns'

-- | Generate a fresh modality
newMode :: [String] -> TCMonad Modality
newMode ns =
  do ns' <- newNames ns
     return $ freshMode ns'

-- | Generate a fresh modality, but
-- with boxing modality set to 1
newMode2 :: [String] -> TCMonad Modality
newMode2 ns =
  do ns' <- newNames ns
     return $ freshMode2 ns'

-- | Check if a term is in value form.
isValue (Pos p e) = isValue e
isValue (Var _) = return True
isValue Star = return True
isValue (Const _) = return True
isValue (Lam _) = return True
isValue (LamAnn _ _) = return True
isValue (LamAnnP _ _) = return True
isValue (LamP _) = return True
isValue (Lift _) = return True
isValue (LamDepTy _) = return True
isValue (LamDep _) = return True
isValue (LamDepInt _) = return True
isValue (LamType (Abst xs m)) = isValue m
isValue (LamTm (Abst xs m)) = isValue m
isValue (LamDict _) = return True
isValue (Pair x y) = do
  x' <- isValue x
  y' <- isValue y
  return $ x' && y'
isValue (Force (App UnBox t)) = isValue t
isValue (ForceP (AppP UnBox t)) = isValue t
isValue a@(App UnBox t) = isValue t
isValue a@(AppP UnBox t) = isValue t
isValue a@(App t t') = checkApp a
isValue a@(AppP t t') = checkApp a
isValue a@(AppDep t t') = checkApp a
isValue a@(AppDepInt t t') = checkApp a
isValue a@(AppDict t t') = checkApp a
isValue a@(AppType t t') = isValue t
isValue a@(AppTm t t') = isValue t
isValue (RealOp _) = return True
isValue (WrapR _) = return True
isValue _ = return False

-- | Check if an application is a value.
checkApp :: Exp -> TCMonad Bool
checkApp a =
  case flatten a of
    Just (h, args) -> do
      pc <- lookupId (fromEither h)
      case identification pc of
        DataConstr _ -> do
          rs <- mapM isValue args
          return $ and rs
        DataType _ _ _ -> do
          rs <- mapM isValue args
          return $ and rs
        DictionaryType _ _ -> do
          rs <- mapM isValue args
          return $ and rs
        _ -> return False
      where fromEither (Left x) = x
            fromEither (Right x) = x
    _ -> return False

-- | Check if the expression is a basic value (i.e., things that can be displayed in an interpreter), note that function and circuit is not a basic value.
isBasicValue :: Value -> TCMonad Bool
isBasicValue (VConst k) = do
  pac <- lookupId k
  case identification pac of
    DataConstr _ -> return True
    _ -> return False
isBasicValue (VPair x y) = do
  r1 <- isBasicValue x
  r2 <- isBasicValue y
  return (r1 && r2)
isBasicValue a@(VApp t t') = do
  r1 <- isBasicValue t
  r2 <- isBasicValue t'
  return (r1 && r2)
isBasicValue (VStar) = return True
isBasicValue _ = return False

-- | Check if the current context is a parameter context, this is
-- used for checking a lift term.
checkParamCxt :: Exp -> TCMonad ()
checkParamCxt t =
  let fvars = getVars All t
   in do env <- get >>= \x -> return (lcontext x)
         mapM_ (checkFVars env) fvars
  where
    checkFVars env x =
      let lvars = localCxt env
       in case Map.lookup x lvars of
            Nothing -> throwError $ UnBoundErr x
            Just lpkg -> do
              let t' = varClassifier lpkg
              case varIdentification lpkg of
                TypeVar _ _ -> return ()
                TermVar c _ -> do
                  tt <- updateWithSubst t'
                  p <- isParam tt
                  when (not p) $ throwError $ LiftErrVar x t tt

-- | Check if a variable is used according to linearity
-- in an expression.
checkUsage :: Variable -> Exp -> TCMonad ()
checkUsage x m = do
  (t', count) <- lookupVar x
  case count of
    Nothing -> return ()
    Just c -> do
      p <- isParam t'
      if p
        then return ()
        else case evalCount c of
               Nothing -> throwError $ CaseErr (Var x) (Just m) c
               Just v
                 | v == 1 -> return ()
                 | otherwise -> throwError $ (LVarErr x m c t')

-- | update the current substitution.
updateSubst :: Subst -> TCMonad ()
updateSubst ss = do
  ts <- get
  put ts {subst = ss}

-- | Get the current substitution.
getSubst :: TCMonad Subst
getSubst = do
  ts <- get
  return $ subst ts

-- | Add a position information of an expression to the error message without duplicating
-- position.
withPosition :: Exp -> TypeError -> TypeError
withPosition (Pos p e) er@(ErrPos _ _) = er
withPosition (Pos p e) er = ErrPos p er
withPosition _ er = er

-- | Apply the current substitution to the local instance assumptions.
updateLocalInst :: Subst -> TCMonad ()
updateLocalInst sub = do
  ts <- get
  let tc = instanceContext ts
      gi = localInstance tc
      gi' = map (\(x, t) -> (x, substitute sub t)) gi
  put ts {instanceContext = tc {localInstance = gi'}}

-- | Update the count information according to the input function.
updateCountWith :: (ZipCount -> ZipCount) -> TCMonad ()
updateCountWith update = do
  ts <- get
  let env = lcontext ts
      localVars = localCxt env
      localVars' = Map.map helper localVars
      res = env {localCxt = localVars'}
  put ts {lcontext = res}
  where
    helper lpkg =
      case varIdentification lpkg of
        TypeVar _ _ -> lpkg
        TermVar n d ->
          let n' = update n
           in lpkg {varIdentification = TermVar n' d}

-- | Add a new Id into the typing context
addNewId :: Id -> Info -> TCMonad ()
addNewId x t = do
  ts <- get
  let l = lcontext ts
      env = globalCxt l
      env' = Map.insert x t env
      l' = l {globalCxt = env'}
  put ts {lcontext = l'}

-- | Check whether a type contains any vacuous forall quantification.
checkVacuous :: Position -> Exp -> TCMonad ()
checkVacuous pos ty =
  case vacuousForall ty of
    Nothing -> return ()
    Just (Nothing, vs, ty, m) -> throwError (Vacuous pos vs ty m)
    Just (Just p, vs, ty, m) -> throwError (Vacuous p vs ty m)

-- | Add an instance function to the global instance context.
addGlobalInst :: Id -> Exp -> TCMonad ()
addGlobalInst x t = do
  ts <- get
  let env = instanceContext ts
      gamma' = (x, t) : globalInstance env
      env' = env {globalInstance = gamma'}
  put ts {instanceContext = env'}

-- | Add an error position when possible.
collapsePos :: Position -> TypeError -> TypeError
collapsePos p a@(ErrPos _ _) = a
collapsePos p a = ErrPos p a

-- | Update the current mode substitution.
updateModeSubst :: (ModeSubst, ModeSubst, ModeSubst) -> TCMonad ()
updateModeSubst s@(s1, s2, s3) = do
  ts <- get
  let (s1', s2', s3') = modeSubstitution ts
      s1'' = mergeModeSubst s1 s1'
      s2'' = mergeModeSubst s2 s2'
      s3'' = mergeModeSubst s3 s3'
  put ts {modeSubstitution = (s1'', s2'', s3'')}

-- | Update an expression with mode substitution.
updateWithModeSubst :: Exp -> TCMonad Exp
updateWithModeSubst e = do
  ts <- get
  let s@(s1, s2, s3) = modeSubstitution ts
  return $ bSubstitute s e

-- | Update a given modality with current substitution.
updateModality :: Modality -> TCMonad Modality
updateModality m = do
  ts <- get
  let s@(s1, s2, s3) = modeSubstitution ts
  return $ modeSubst s m


deMeta :: [Variable] -> Exp -> TCMonad Exp
deMeta vars (Pos p e) = Pos p <$> (deMeta vars e)
deMeta vars (Unit) = return Unit
deMeta vars (Type) = return Type
deMeta vars Star = return Star
deMeta vars Sort = return Sort
deMeta vars a@(Var x) = return a
deMeta vars a@(MetaVar x) =
  if x `elem` vars then return $ Var x
  else throwError $ UnBoundMetaVar x
deMeta vars a@(Base x) = return a
deMeta vars a@(LBase x) = return a
deMeta vars a@(Const x) = return a

deMeta vars (App e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in App <$> e1' <*> e2'

deMeta vars (AppP e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppP <$> e1' <*> e2'

deMeta vars (WithType e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in WithType <$> e1' <*> e2'

deMeta vars (AppType e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppType <$> e1' <*> e2'  

deMeta vars (AppTm e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppTm <$> e1' <*> e2'  

deMeta vars (AppDep e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppDep <$> e1' <*> e2'  

deMeta vars (AppDepInt e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppDepInt <$> e1' <*> e2'  

deMeta vars (AppDepTy e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppDepTy <$> e1' <*> e2'  

deMeta vars (AppDict e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppDict <$> e1' <*> e2'  

deMeta vars (Tensor e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in Tensor <$> e1' <*> e2'
  
deMeta vars (Pair e1 e2) = 
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in  Pair <$> e1' <*> e2'

deMeta vars (Arrow e1 e2 m) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in Arrow <$> e1' <*> e2' <*> return m

deMeta vars (ArrowP e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in ArrowP <$> e1' <*> e2'

deMeta vars (Imply e1 e2 m) =
  let e1' = mapM (deMeta vars) e1
      e2' = deMeta vars e2
  in Imply <$> e1' <*> e2' <*> return m

deMeta vars (Bang e m) = Bang <$> (deMeta vars e) <*> return m
deMeta vars (UnBox) = return UnBox
deMeta vars (RunCirc) = return RunCirc
deMeta vars (Reverse) = return Reverse
deMeta vars (Controlled) = return Controlled
deMeta vars (WithComputed) = return WithComputed
deMeta vars (Dynlift) = return Dynlift
deMeta vars (Box) = return Box 
deMeta vars (ExBox) = return ExBox
deMeta vars a@(WrapR _) = return a
deMeta vars (RealNum) = return RealNum
deMeta vars a@(RealOp _) = return a

deMeta vars (Lift e) = Lift <$> (deMeta vars e) 
deMeta vars (Force e) = Force <$> (deMeta vars e)
deMeta vars (ForceP e) = ForceP <$> (deMeta vars e)

deMeta vars (Circ e1 e2 m) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in Circ <$> e1' <*> e2' <*> return m

deMeta vars (LetPair m bd) = open bd $ \ xs b ->
  do m' <- (deMeta vars m)
     b' <- (deMeta (xs ++ vars) b)
     return $ LetPair m' (abst xs b') 

deMeta vars (LetPat m bd) = open bd $ \ (PApp id vs) b ->
  do m' <- deMeta vars m
     (bvs, vs') <- pvar vs
     b' <- deMeta (bvs ++ vars) b 
     return $ LetPat m' (abst (PApp id vs') b')
 where  pvar ([]) = return ([], [])

        pvar (Right x : xs) =
          do (bv, fv) <- pvar xs
             return (x:bv, Right x : fv)

        pvar (Left (NoBind (MetaVar x)):xs) =
          do (bv, fv) <- pvar xs 
             if x `elem` vars then
               return (bv, Left (NoBind (Var x)):fv)
               else return (x:bv, Right x : fv)

        pvar ((Left (NoBind x)):xs) =
          do (bv, fv) <- pvar xs
             x' <- deMeta vars x
             return (bv, Left (NoBind x'):fv)
   
deMeta vars (Let m bd) = open bd $ \ p b ->
  do m' <- (deMeta vars m)
     b' <- (deMeta (p:vars) b)
     return $ Let m' (abst p b') 

deMeta vars (LamTm bd) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      return $ LamTm $ abst xs m'

deMeta vars (LamDep bd) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      return $ LamDep (abst xs m') 

deMeta vars (LamDepTy bd) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      return $ LamDepTy (abst xs m') 

deMeta vars (LamDepInt bd) =
  open bd $ \ xs m ->
  do m' <- deMeta (xs ++ vars) m
     return $ LamDepInt (abst xs m') 

deMeta vars (Lam bd) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      return $ Lam (abst xs m') 

deMeta vars (LamAnn ty bd) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      ty' <- deMeta vars ty
      return $ LamAnn ty' (abst xs m') 

deMeta vars (LamAnnP ty bd) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      ty' <- deMeta vars ty
      return $ LamAnnP ty' (abst xs m') 

deMeta vars (LamP bd) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      return $ LamP (abst xs m') 

deMeta vars (LamType bd) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      return $ LamType $ abst xs m'

deMeta vars (LamDict bd) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      return $ LamDict $ abst xs m'

deMeta vars (Pi bd ty mod) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      ty' <- deMeta vars ty
      return $ Pi (abst xs m') ty' mod

deMeta vars (PiImp bd ty mod) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      ty' <- deMeta vars ty
      return $ PiImp (abst xs m') ty' mod

deMeta vars (PiInt bd ty) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      ty' <- deMeta vars ty
      return $ PiInt (abst xs m') ty'

deMeta vars (Exists bd ty) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs:vars) m
      ty' <- deMeta vars ty
      return $ Exists (abst xs m') ty'

deMeta vars (Forall bd ty) =
  open bd $ \ xs m ->
   do m' <- deMeta (xs ++ vars) m
      ty' <- deMeta vars ty
      return $ Forall (abst xs m') ty'

      
deMeta vars a@(Case e (B br)) =
  do e' <- deMeta vars e
     br' <- mapM helper br
     return $ Case e' (B br')
  where helper b = open b $ \ (PApp id vs) b ->
          do (bvs, vs') <- pvar vs
             b' <- (deMeta (bvs ++vars) b)
             return $ abst (PApp id vs') b'

        pvar ([]) = return ([], [])

        pvar ((Right x):xs) =
          do (bv, fv) <- pvar xs
             return (x:bv, (Right x):fv)

        pvar ((Left (NoBind (MetaVar x))):xs) =
          do (bv, fv) <- pvar xs
             if x `elem` vars then
               return (bv, (Left (NoBind (Var x))):fv)
               else return (x:bv, (Right x):fv)

        pvar ((Left (NoBind x)):xs) =
          do (bv, fv) <- pvar xs
             x' <- deMeta vars x
             return (bv, (Left (NoBind x')):fv)

deMeta vars (Mod (Abst vs b)) =
  (deMeta vars b) >>= \ y -> return $  Mod (abst vs y)
deMeta vars a = error $ "from deMeta" ++ (show $ disp a)
