{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}

-- | This module implements a closure-based call-by-value evaluation.
-- It can run into memory problem when generating super-large circuits (e.g., 1 millions gates).
module Evaluation
  ( eval
  , initES
  , size
  , toVal
  ) where

import Erasure
import Simulation
import SyntacticOperations
import Syntax
import Utils

import Nominal
import Control.Exception
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Identity
import TCMonad
import Text.PrettyPrint
import Data.List
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Tuple
import Debug.Trace
import Data.Number.CReal

-- * The Eval monad and eval function.

-- | The evaluation monad combines the ReadWrite monad
-- and carried an EvalState.
type Eval a = StateT EvalState ReadWrite a

-- | The evaluator state, it contains an underlying circuit and
-- a global context.
data EvalState =
  ES
    { evalEnv :: Context -- ^ The global evaluation context.
    , labels :: [Label] -- ^ A list of labels that are generated during evaluation 
    }

-- | Initialize an EvalState from a global context.
initES :: Context -> EvalState
initES gl = ES {evalEnv = gl, labels = []}

-- | Lifting a label to a boolean. 
dynamicLift :: Label -> Eval Bool
dynamicLift l = lift $ dynliftRW l

-- | Append a list of gates to the underlying ReadWrite state. 
addGates :: [Gate] -> Eval ()
addGates gs = lift $ mapM_ gateRW gs

-- | Evaluate an expression to a value in the value domain.
-- The eval function also takes a local environment
-- as argument and form closures when evaluating lambda abstractions
-- or lifted terms.
eval :: LEnv -> EExp -> Eval Value
eval !lenv (EVar x) = return $ lookupLEnv x lenv
eval !lenv EStar = return VStar
eval !lenv EUnit = return VUnit
eval !lenv a@(EConst k) = do
  st <- get
  let genv = evalEnv st
  case Map.lookup k genv of
    Nothing -> error $ "undefined" ++ (show $ disp k)
    Just e ->
      case identification e of
        DataConstr _ -> return (VConst k)
        DefinedGate v -> return v
        DefinedFunction (Just (_, v, _)) -> return v
        DefinedFunction Nothing ->
          throw $ userError ("undefined: " ++ (show $ disp k))
        DefinedMethod _ v -> return v
        DefinedInstFunction _ v -> return v

eval !lenv (EBase k) = return $ VBase k

eval !lenv a@(ELBase k) = do
  st <- get
  let genv = evalEnv st
  case Map.lookup k genv of
    Nothing -> throw $ userError ("undefined: " ++ (show $ disp k))
    Just e ->
      case identification e of
        DataType Simple _ (Just (ELBase id)) -> return (VLBase id)
        DataType (SemiSimple _) _ (Just d) -> eval lenv d
        DataType _ _ Nothing -> return (VBase k)

eval !lenv (EForce m) = do
  m' <- eval lenv m
  case m' of
    VLift (Abst lenv e) -> eval lenv e
    w@(VLiftCirc _) -> return w
    v@(VApp VUnBox _) -> return $ VForce v
    a -> error $ "from eval(EForce):" ++ (show $ disp a)

eval !lenv (ETensor e1 e2) = do
  e1' <- eval lenv e1
  e2' <- eval lenv e2
  return $ VTensor e1' e2'

eval !lenv a@(ELam body) = return (VLam (abst lenv body))
eval !lenv a@(ELift body) = return (VLift (abst lenv body))
eval !lenv EUnBox = return VUnBox
eval !lenv EReverse = return VReverse
eval !lenv EDynlift = return VDynlift
eval !lenv EControlled = return VControlled
eval !lenv EWithComputed = return VWithComputed
eval !lenv a@(EBox) = return VBox
eval !lenv a@(EExBox) = return VExBox
eval !lenv a@(ERealOp x) = return (VRealOp x)
eval !lenv a@(EWrapR m) = return (VWrapR m)

eval !lenv (EApp m n) = do
  v <- eval lenv m
  w <- eval lenv n
  evalApp v w

eval !lenv (EPair m n) = do
  v <- eval lenv m
  w <- eval lenv n
  return (VPair v w)

eval !lenv (ELet m (Abst x n)) = do
  m' <- eval lenv m
  let lenv' = addDefinition x m' lenv
  eval lenv' n

eval !lenv (ELetPair m (Abst xs n)) = do
  m' <- eval lenv m
  let r = unVPair (length xs) m'
  case r of
    Just vs ->
      let lenv' = foldl (\a (x, y) -> addDefinition x y a) lenv
                  (zip xs vs)
      in eval lenv' n
    Nothing -> error "unpair error, from eval ELetPair."
    
eval !lenv (ELetPat m (Abst (EPApp kid vs) n)) = do
  m' <- eval lenv m
  case vflatten m' of
    Nothing -> error ("from LetPat" ++ (show $ disp m'))
    Just (Left id, args) | kid == id -> 
         do let vs' = vs
                subs = (zip vs' args)
                lenv' = foldl (\a (x, v) -> addDefinition x v a)
                        lenv subs
            eval lenv' n
    Just (Left id, args) | otherwise -> 
         error "pattern mismatch, from eval ELetPat"

eval !lenv b@(ECase m (EB bd)) = do
  m' <- eval lenv m
  case vflatten m' of
    Nothing -> error ("from eval (Case):" ++ (show $ dispRaw m'))
    Just (Left id, args) -> reduce id args bd
  where
    reduce id args ((Abst (EPApp kid vs) m):bds) | kid == id =
      do let vs' = vs
             subs = zip vs' args
             lenv' = foldl' (\a (x, v) -> addDefinition x v a)
                     lenv subs
         eval lenv' m
    reduce id args ((Abst (EPApp kid vs) m):bds) | otherwise =
          reduce id args bds
    reduce id args [] =
      throw $ userError ("missing a branch for: " ++ show (disp id))

eval !lenv a = error $ "from eval: " ++ (show $ disp a)

-- * Helper functions for eval.
-- | Look up a value from the local environment.
lookupLEnv :: Variable -> LEnv -> Value
lookupLEnv x lenv =
  case Map.lookup x lenv of
    Nothing -> error $ "undefined variable from lookupLEnv:" ++ show x
    Just v -> v

-- | Add a value to the environment.
addDefinition :: Variable -> Value -> LEnv -> LEnv
addDefinition x m lenv = Map.insert x m lenv

-- | Evaluate various of applications.
evalApp :: Value -> Value -> Eval Value
evalApp VUnBox v =
  case v of
    (Wired _) -> return $ VApp VUnBox v
    _ -> return VUnBox

-- Note that (VRealOp pi) is a function.
evalApp (VRealOp x) n | x == "pi" =
  case toInt n of
    Nothing -> error "from pi n"
    Just n' -> return $ VWrapR $ MR n' pi
    
evalApp (VRealOp x) (VWrapR (MR l r)) | x == "sin" =
  return $ VWrapR $ MR l (sin r)

evalApp (VRealOp x) (VWrapR (MR l r)) | x == "ceiling" =
  return $ VWrapR $ MR l (fromIntegral (ceiling r :: Integer))

evalApp (VRealOp x) (VWrapR (MR l r)) | x == "round" =
  return $ VWrapR $ MR l (fromIntegral (round r :: Integer))

evalApp (VRealOp x) (VWrapR (MR l r)) | x == "floor" =
  return $ VWrapR $ MR l (fromIntegral (floor r :: Integer))

evalApp (VRealOp x) (VWrapR (MR l r)) | x == "exp" =
  return $ VWrapR $ MR l (exp r)

evalApp (VRealOp x) (VWrapR (MR l r)) | x == "cos" =
  return $ VWrapR $ MR l (cos r)

evalApp (VRealOp x) (VWrapR (MR l r)) | x == "log" = do
  when (r < 0) $ error "applying log a negative real"
  return $ VWrapR $ MR l (log r)

evalApp (VRealOp x) (VWrapR (MR l r)) | x == "sqrt" = do
  when (r < 0) $ error "squaring a negative real"
  return $ VWrapR $ MR l (sqrt r)

evalApp (VApp (VApp (VRealOp x) _) n) (VWrapR (MR l r)) | x == "cast" =
  case toInt n of
    Nothing -> error "from evalVApp: toInt"
    Just l' -> return $ VWrapR $ MR l' r

evalApp (VApp (VRealOp x) (VWrapR (MR l' r'))) (VWrapR (MR l r)) | x == "plusReal" =
  if l' == l then return $ VWrapR $ MR l' (r' + r)
  else error "length mismatch from plusReal, when evaluating evalVApp."

evalApp (VApp (VRealOp x) (VWrapR (MR l' r'))) (VWrapR (MR l r)) | x == "minusReal" =
  if l' == l then return $ VWrapR $ MR l' (r' - r)
  else error "length mismatch from minusReal, when evalutating evalVApp."

evalApp (VApp (VRealOp x) (VWrapR (MR l' r'))) (VWrapR (MR l r)) | x == "divReal" =
  if l' == l then
    do when (r == 0) $ error "divided by zero"
       return $ VWrapR $ MR l' (r' / r)
  else error "length mismatch from evalVApp: divReal"

evalApp (VApp (VRealOp x) (VWrapR (MR l' r'))) (VWrapR (MR l r)) | x == "mulReal" =
  if l' == l then return $ VWrapR $ MR l' (r' * r)
  else error "length mismatch from mulReal, when evaluating evalVApp."

evalApp (VApp (VRealOp x) (VWrapR (MR l' r'))) (VWrapR (MR l r)) | x == "eqReal" =
  if l' == l then
    if showCReal l' r' == showCReal l' r then
      return $ VConst (Id "True")
    else return $ VConst (Id "False")
  else error "length mismatch from eqReal, when evaluating evalVApp."

evalApp (VApp (VRealOp x) (VWrapR (MR l' r'))) (VWrapR (MR l r)) | x == "ltReal" =
  if l' == l then
    let r1 = (read $ showCReal l' r') :: CReal
        r2 = (read $ showCReal l' r) :: CReal in
    if r1 > r2 then
      return $ VConst (Id "True")
    else return $ VConst (Id "False")
  else error "length mismatch from ltReal, when evaluating evalApp."

evalApp (VDynlift) (VLabel v) = do
  b <- dynamicLift v
  if b
    then return $ VConst (Id "True")
    else return $ VConst (Id "False")

-- append gates
evalApp (VForce (VApp VUnBox (Wired (Abst wires morph)))) w = do
  let binding = makeBinding (input morph) w
  let morph' = rename morph binding
      gs = gates morph'
      outs = output morph'
  addGates gs
  let wires' = wires \\ (Map.keys binding)
  modify (\ st -> st{labels = labels st ++ wires'})
  return outs

evalApp (VApp (VApp (VApp VBox q) _) _) v =
  case v of
    VLift (Abst lenv m) -> evalBox lenv (Right m) q
    VApp VUnBox w -> return w
    m@(VLiftCirc _) -> evalBox Map.empty (Left m) q
    a -> error $ "unexpected value" ++ (show $ disp a) ++ " , from evalApp VBox."
  where
    evalBox :: LEnv -> Either Value EExp -> Value -> Eval Value
    evalBox lenv body uv = freshLabels (size uv) $ \vs -> do
      b <-
        case body of
             Right body' -> eval lenv body'
             Left v -> return v
      st <- get             
      let uv' = toVal uv vs
          bgs = boxGates $ runStateT (evalApp b uv') (initES (evalEnv st))
          gs = fst bgs
          res = fst $ snd bgs
          st' = snd $ snd bgs
          vs' = labels st'
          newMorph = Morphism uv' gs res
          morph' = Wired (abst (vs ++ vs') newMorph)
      return morph'

evalApp (VApp (VApp (VApp (VApp VExBox uv) _) _) _) v =
  case v of
    VLift (Abst lenv body) ->
      freshLabels (size uv) $ \vs -> do
        st <- get
        b <- eval lenv body
        let uv' = toVal uv vs
            bgs = boxGates $ runStateT (evalApp b uv') st
            gs = fst bgs
            res = fst $ snd bgs
            n = fstVPair res
            res' = sndVPair res
            st' = snd $ snd bgs
            vs' = labels st'
            newMorph = Morphism uv' gs res'
            morph' = Wired (abst (vs ++ vs') newMorph)
        return (VPair n morph')
  where
    fstVPair (VPair a _) = a
    sndVPair (VPair _ b) = b

evalApp (VApp (VApp VReverse _) _) (Wired (Abst ws (Morphism ins gs outs))) = do
  let gs' = revGates gs
  return $ Wired (abst ws $ Morphism outs gs' ins)

evalApp (VApp (VApp (VApp VControlled _) _) _) (Wired (Abst ws m)) =
  freshNames ["#ctrl", "#input", "#circ"] $ \([ctrl, inp, circ]) -> do
    let ins = input m
        gs = gates m
        outs = output m
        mycirc = Wired (abst ws $ Morphism ins (controlledGates ctrl gs) outs)
        env = Map.fromList [(circ, mycirc)]
        exp =
          EPair (EApp (EForce $ EApp EUnBox (EVar circ)) (EVar inp))
          (EVar ctrl)
    return $ VLiftCirc (abst [inp, ctrl] $ abst env exp)
  where
    controlledGates a gs = map (helper a) gs
    helper a (Gate id ps ins outs b False inv) = Gate id ps ins outs b False inv
    helper a (Gate id ps ins outs VStar flag inv) =
      Gate id ps ins outs (VVar a) flag inv
    helper a (Gate id ps ins outs b flag inv) =
      Gate id ps ins outs (VPair b (VVar a)) flag inv

evalApp (VApp (VApp (VApp (VApp (VApp VWithComputed _) _) _) _) _) m =
  return $ VComputed m

-- Congugate the circ1 : Circ(a, b*e) to circ2 : Circ(b * c, b * d),
-- return a circuit of type Circ(a*c, a*d). The resulting circuit
-- can be controlled via circ2 (not circ1). 
evalApp (VComputed (Wired (Abst ws1 circ1))) (Wired (Abst ws2 circ2)) = 
  let gs1 = gates circ1
      a = input circ1
      b1 = fstVPair $ output circ1
      e = sndVPair $ output circ1
      gs1' = map disableCtrl gs1
      gs1'' = revGates gs1'
      circ1' = Morphism (VPair b1 e) gs1'' a
      b2 = fstVPair $ input circ2
      binding = makeBinding b2 b1
      circ2' = rename circ2 binding
      gs2 = gates circ2'
      c = sndVPair $ input circ2'
      b3 = fstVPair $ output circ2'
      d = sndVPair $ output circ2'
      binding2 = makeBinding b1 b3
      circ3 = rename circ1' binding2
      gs1''' = gates circ3
      a' = output circ3
      res =
        Wired $
        abst
          (ws1 ++ ws2)
          (Morphism (VPair a c) (gs1' ++ gs2 ++ gs1''') (VPair a' d))
  in return res
  where
    disableCtrl (Gate e1 e2 e3 e4 e5 b inv) = Gate e1 e2 e3 e4 e5 False inv
    fstVPair (VPair a _) = a
    sndVPair (VPair _ b) = b

evalApp a@(Wired _) w = return a

evalApp v w =
  let (h, res) = unwindVal v
  in case h of
        VLam (Abst lenv bd) -> handleBody lenv (res ++ [w]) bd
        VLiftCirc (Abst vs (Abst lenv e)) -> do
          let args = res ++ [w]
              lvs = length vs
          if lvs > (length args)
            then return $ VApp v w
            else do
              let sub' = zip vs args
                  ws = drop lvs args
                  lenv' = updateCirc sub' lenv
                  lenv'' = Map.fromList (lenv' ++ sub')
              e' <- eval lenv'' e
              case e' of
                VLam (Abst lenv''' bd) -> handleBody lenv''' ws bd
                _ -> return $ foldl (\x y -> VApp x y) e' ws
        _ -> return $ VApp v w
  where -- Handle beta reduction
    handleBody lenv args bd =
      open bd $ \vs m ->
        let lvs = length vs
         in if lvs > length args
              then return $ VApp v w
              else do
                let sub = zip vs args
                    ws = drop lvs args
                    lenv' = foldl' (\a (x, v) -> addDefinition x v a) lenv sub
                if null ws
                  then eval lenv' m
                  else do
                    m' <- eval lenv' m
                    return $ foldl (\x y -> VApp x y) m' ws
        -- Perform substitution on the variables in a circuit.
    updateCirc :: [(Variable, Value)] -> LEnv -> [(Variable, Value)]
    updateCirc sub lenv =
      let [(x, Wired (Abst wires (Morphism ins gs outs)))] = Map.toList lenv
          params1 = map params gs
          ctrls = map ctrl gs
          params' = map (\p -> helper p sub) params1
          ctrls' = helper ctrls sub
          gs' =
            zipWith3
              (\p c g ->
                 Gate
                   (gateName g)
                   p
                   (inputVal g)
                   (outputVal g)
                   c
                   (ctrlFlag g)
                   (inv g))
              params'
              ctrls'
              gs
          circ' = Wired (abst wires (Morphism ins gs' outs))
       in [(x, circ')]
        -- Perfrom substitution.
    helper :: [Value] -> [(Variable, Value)] -> [Value]
    helper [] lc = []
    helper (b:xs) lc =
      let b' = applyValSubst b lc
          res = helper xs lc
       in b' : res
    applyValSubst VStar lc = VStar
    applyValSubst a@(VConst _) lc = a
    applyValSubst l@(VLabel _) lc = l
    applyValSubst (VVar x) lc =
      case lookup x lc of
        Just v -> v
        Nothing -> error $ "can't find variable " ++ (show $ disp x)
    applyValSubst (VPair a b) lc =
      let a' = applyValSubst a lc
          b' = applyValSubst b lc
       in VPair a' b'
    applyValSubst (VApp a b) lc =
      let a' = applyValSubst a lc
          b' = applyValSubst b lc
       in VApp a' b'
    applyValSubst c lc = error $ "from applyValSubst:" ++ (show $ disp c)


-- | A binding is a map of labels.
type Binding = Map Label Label

-- | Obtain a binding from two simple terms.
makeBinding :: Value -> Value -> Binding
makeBinding w v =
  let ws = getWires w
      vs = getWires v
   in Map.fromList (zip ws vs)

-- | Reverse a list of gates. 
-- It also changes the name of a gate to its adjoint. 
revGates :: [Gate] -> [Gate]
revGates xs = map invertGateName $ reverse xs
  where
    invertGateName (Gate id params ins outs ctrls flag (Just g)) =
      Gate g params outs ins ctrls flag (Just id)
    invertGateName (Gate id params ins outs ctrls flag Nothing) =
      error $ "non-invertable gate: " ++ getName id

-- | Obtain a fresh value of type /uv/ using fresh labels draw from /vs/.
toVal :: Value -> [Label] -> Value
toVal uv vs = evalState (templateToVal uv) vs

-- | Obtain a fresh template inhabitant of a simple type, with wirenames
-- drawn from the state. The input is a simple data type, the output is a
-- simple data value.
templateToVal :: Value -> State [Label] Value
templateToVal (VLBase _) = do
  x <- get
  let (v:vs) = x
  put vs
  return (VLabel v)
templateToVal a@(VConst _) = return a
templateToVal a@(VUnit) = return VStar
templateToVal (VApp e1 e2) = do
  e1' <- templateToVal e1
  e2' <- templateToVal e2
  return $ VApp e1' e2'
templateToVal (VTensor e1 e2) = do
  e1' <- templateToVal e1
  e2' <- templateToVal e2
  return $ VPair e1' e2'
templateToVal a =
  error "applying templateToVal function to an ill-formed template"

-- | Get the size of a simple data type.
size :: Value -> Int
size (VLBase x) = 1
size (VLabel x) = 1
size (VConst _) = 0
size VUnit = 0
size VStar = 0
size (VApp e1 e2) = size e1 + size e2
size (VTensor e1 e2) = size e1 + size e2
size (VPair e1 e2) = size e1 + size e2
size a =
  error $ "applying size function to an ill-formed template:" ++ (show $ disp a)

-- | Convert applicative natural number into the haskell int type.
toInt :: Value -> Maybe Int
toInt (VApp (VConst id) t') =
  if getName id == "S" then
    do n <- toInt t'
       return $ 1+ n
  else Nothing

toInt (VConst id) = 
  if getName id == "Z" then
    return 0
  else Nothing

toInt _ = Nothing
