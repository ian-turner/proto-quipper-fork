{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}



-- | This module implements a closure-based call-by-value evaluation.
-- It still has memory problem when generating super-large circuits.

module Evaluation 
       (eval, getSt, initES, size, toVal) where

import Syntax
import Erasure
import SyntacticOperations
import Utils
import Nominal
import Simulation

import Control.Exception 
import Control.Monad.State (State)
import qualified Control.Monad.State as S
import Control.Monad.Identity
import Control.Monad.Except
import Text.PrettyPrint
import TCMonad 

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set (Set)
import Data.List
import qualified Data.Set as S
import Debug.Trace


-- * The Eval monad and eval function.

-- | The evaluation monad.
type Eval a = QuantumState a


-- | Evaluator state, it contains an underlying circuit and
-- a global context. 
data EvalState =
  ES { evalEnv :: Context,  -- ^ The global evaluation context.
       localEvalEnv :: Map Variable (Value, Integer, Integer, [Variable]),
       -- ^ The heap for evaluation, represented by a map.
       -- The first 'Integer' represents the approximate number of occurrences,
       -- the second 'Integer' represents its accurate reference count,
       -- the ['Variable'] is the variables that it refers to.
       wires :: [Label]

     }

newtype QuantumState a = QS {getSt :: EvalState -> ReadWrite (EvalState, a)}

initES gl = ES{evalEnv = gl, localEvalEnv = Map.empty, wires = []}

get :: Eval EvalState
get = QS $ \ s -> return (s, s)

put :: EvalState -> Eval ()
put s' = QS $ \ s -> return (s', ())

dynamicLift :: Label -> Eval Bool
dynamicLift l = QS $ \ s ->
  do b <- dynliftRW l
     return (s, b)


addGates :: [Gate] -> Eval ()
addGates gs =
  QS $ \ s -> mapM_ gateRW gs >> return (s, ())
                         
addWires ws =
  do s <- get
     let ws1 = wires s
     put s{wires = ws ++ ws1}


instance Monad QuantumState where
  return a = QS $ \ s -> return (s, a)
  f >>= g = QS h
    where h s = do
            (st, v) <- getSt f s
            getSt (g v) st
          

instance Applicative QuantumState where
  pure = return
  (<*>) = ap

instance Functor QuantumState where
  fmap = liftM

-- | Evaluate an expression to
-- a value in the value domain. The eval function also takes an environment
-- as argument and form a closure when evaluating a lambda abstraction or a lifted term.

eval :: EExp -> Eval Value
eval (EVar x) = do
  v <- lookupLEnv x 
  return v

eval EStar = return VStar
eval EUnit = return VUnit
eval a@(EConst k) =
  do st <- get
     let genv = evalEnv st
     case Map.lookup k genv of
       Nothing -> error $ "undefined" ++ (show $ disp k) -- throwError $ UndefinedId k
       Just e ->
         case identification e of
           DataConstr _ -> return (VConst k)
           DefinedGate v -> return v
           DefinedFunction (Just (_, v, _)) -> return v
           DefinedFunction Nothing -> throw $ userError ("undefined: " ++ (show $ disp k))
           DefinedMethod _ v -> return v
           DefinedInstFunction _ v -> return v

eval (EBase k) = return $ VBase k

eval a@(ELBase k) =
  do st <- get
     let genv = evalEnv st
     case Map.lookup k genv of
       Nothing -> throw $ userError ("undefined: " ++ (show $ disp k))
       Just e ->
         case identification e of
           DataType Simple _ (Just (ELBase id)) -> return (VLBase id)
           DataType (SemiSimple _) _ (Just d) -> eval d
           DataType _ _ Nothing -> return (VBase k)

eval (EForce m) =
  do m' <- eval m
     case m' of
       VLift _ e -> eval e
       VDynlift -> return $ VForce VDynlift
       w@(VLiftCirc _) -> return w
       v@(VApp VUnBox _) -> return $ VForce v
       a -> error $ "from eval(EForce):" ++ (show $ disp a)
       
eval (ETensor e1 e2) =
  do e1' <- eval e1
     e2' <- eval e2
     return $ VTensor e1' e2'

eval a@(ELam ws body) = return (VLam ws body)
     
eval a@(ELift ws body) = return (VLift ws body)
     
eval EUnBox = return VUnBox
eval EReverse = return VReverse
eval EDynlift = return VDynlift
eval EControlled = return VControlled
eval EWithComputed = return VWithComputed
eval a@(EBox) = return VBox
eval a@(EExBox) = return VExBox

eval (EApp m n) =
  do v <- eval m
     w <- eval n
     evalApp v w

eval (EPair m n) = 
  do v <- eval m
     w <- eval n
     return (VPair v w)

eval (ELet m bd) =
  do m' <- eval m
     open bd $ \ x n ->
       do addDefinition x m'
          eval n


eval (ELetPair m (Abst xs n)) =
  do m' <- eval m
     let r = unVPair (length xs) m'
     case r of
       Just vs -> do
         mapM_ (\ (x, y) -> addDefinition x y)
                        (zip xs vs)
         eval n

eval (ELetPat m bd) =
  do m' <- eval m
     case vflatten m' of
       Nothing -> error ("from LetPat" ++ (show $ disp m'))
       Just (Left id, args) ->
         open bd $ \ p m ->
         case p of
           EPApp kid vs
             | kid == id ->
               do let vs' = vs 
                      subs = (zip vs' args)
                  mapM_ (\ (x, v) -> addDefinition x v) subs
                  eval m
           p -> error "pattern mismatch, from eval ELetPat" 

eval b@(ECase m (EB bd)) =
  do m' <- eval m
     case vflatten m' of
       Nothing -> error ("from eval (Case):")
       Just (Left id, args) ->
         reduce id args bd
  where reduce id args (bd:bds) =
          open bd $ \ p m ->
          case p of
             EPApp kid vs
               | kid == id -> 
               do st <- get
                  let vs' = vs
                      subs = zip vs' args
                  mapM_ (\ (x, v) -> addDefinition x v) subs
                  eval m
               | otherwise -> reduce id args bds
        reduce id args [] = throw $ userError ("missing a branch for: " ++ show (disp id))

eval a = error $ "from eval: " ++ (show $ disp a)


-- * Helper functions for eval.

-- | Look up a value from the local environment.
-- It also implements a nonstop GC. Compared to stop-the-world-gc,
-- The CONS is that if the garbage is not access
-- anymore, there is no way to collect them. The
-- PROS is that it runs faster than stop-the-world-gc and it does not
-- stop anything. 
lookupLEnv :: Variable -> Eval Value
lookupLEnv x =
  do st <- get
     let lenv = localEvalEnv st
     case Map.lookup x lenv of
       Nothing -> error $ "from lookupLEnv:" ++ show x
       Just (v, n, ref, ps) ->
         if (n-1 <= 0) && ref == 0 then
           do let lenv' = decrRef ps (Map.delete x lenv)
              put st{localEvalEnv = lenv'}
              return v
         else
           do let lenv' = Map.insert x (v, n-1, ref, ps) lenv
              put st{localEvalEnv = lenv'}
              return v

-- | Add a value to the environment.
addDefinition (x, n) m =
  do st <- get
     let vs = vars m
         lenv = localEvalEnv st
         lenv' = if n == 0 then lenv
                 else Map.insert x (m, n, 0, vs) (addRef vs lenv) 
     put st{localEvalEnv = lenv'}

-- | Increase the reference count for given variables.
addRef :: [Variable] -> Map Variable (Value, Integer, Integer, [Variable]) ->
           Map Variable (Value, Integer, Integer, [Variable])               
addRef [] lenv = lenv
addRef (v:vs) lenv =
  case Map.lookup v lenv of
    Nothing -> error $ "from addRef:" ++ show v
    Just (val, n, ref, ps) ->
      let lenv' = Map.insert v (val, n , ref+1, ps) lenv
      in addRef vs lenv' 
  
-- | A helper function for evaluating various of applications.
evalApp :: Value -> Value -> Eval Value
evalApp VUnBox v | Wired _ <- v = return $ VApp VUnBox v
evalApp VUnBox v | otherwise = return VUnBox
evalApp (VForce VDynlift) (VLabel v) =
  do b <- dynamicLift v
     if b then return $ VConst (Id "True") else return $ VConst (Id "False")
evalApp (VForce (VApp VUnBox v)) w =
  case v of
    Wired bd ->
      open bd $ \ wiress m ->
      case m of
        f@(VCircuit (Morphism ins gs outs)) ->
          do let binding = makeBinding ins w
                 wires' = wiress \\ getWires ins
             addWires wires'
             appendMorph binding (Morphism ins gs outs)
    a -> error $ "evalApp(Unbox ..) " ++ (show $ disp a)

evalApp (VApp (VApp (VApp VBox q) _) _) v =
  case v of
    VLift _ m -> evalBox (Right m) q
    VApp VUnBox w -> return w
    m@(VLiftCirc _) -> evalBox (Left m) q
    a -> error $ "evalApp VBox:" ++ (show $ disp a)

evalApp (VApp (VApp (VApp (VApp VExBox q) _) _) _) v =  
  case v of
    VLift _ body ->
      evalExbox body q


evalApp (VApp (VApp VReverse _) _) m' =
  case m' of
    Wired bd ->
      open bd $ \ ws (VCircuit (Morphism ins gs outs)) ->
      let gs' = revGates gs in
        return $ Wired (abst ws (VCircuit $ Morphism outs gs' ins))

evalApp (VApp (VApp (VApp VControlled _) _) _) m =
  case m of
    Wired bd ->
      open bd $ \ ws (VCircuit (Morphism ins gs outs)) ->
      freshNames ["#ctrl", "#input", "#circ"] $ \ (ctrl:input:circ:[]) -> 
      let mycirc = Wired $ abst ws (VCircuit $ Morphism ins (controlledGates ctrl gs) outs)
          env = Map.fromList [(circ, (mycirc, 1))] 
          exp = EPair (EApp (EForce $ EApp EUnBox (EVar circ)) (EVar input)) (EVar ctrl)
      in return $ VLiftCirc (abst [input, ctrl] $ abst env exp)
  where controlledGates a gs = map (helper a) gs
        helper a (Gate id ps ins outs b False) = Gate id ps ins outs b False
        helper a (Gate id ps ins outs VStar flag) = Gate id ps ins outs (VVar a) flag
        helper a (Gate id ps ins outs b flag) = Gate id ps ins outs (VPair b (VVar a)) flag

evalApp (VApp (VApp (VApp (VApp (VApp VWithComputed _) _) _)_)_) m =
  return $ VComputed m 

evalApp (VComputed m1) m2 =
  let (Wired (Abst ws1 (VCircuit (Morphism a gs1 (VPair b1 e))))) = m1
      (Wired (Abst ws2 (VCircuit circ2@(Morphism (VPair b2 _) _ (VPair _ _))))) = m2
      gs1' = map negateCtrl gs1
      gs1'' = revGates gs1'
      circ1' = (Morphism (VPair b1 e) gs1'' a)
      binding = makeBinding b2 b1
      circ2' = rename circ2 binding
      (Morphism (VPair _ c) gs2 (VPair b3 d)) = circ2'
      binding2 = makeBinding b1 b3
      (Morphism (VPair _ _) gs1''' a') = rename circ1' binding2
      res = Wired (abst (ws1 ++ ws2) $ VCircuit (Morphism (VPair a c) (gs1' ++ gs2 ++ gs1''') (VPair a' d)))
  in return res
  where negateCtrl (Gate e1 e2 e3 e4 e5 b) = Gate e1 e2 e3 e4 e5 False
  
evalApp a@(Wired _) w = return a

evalApp v w = 
  let (h, res) = unwindVal v
  in case h of
    VLam _ bd -> handleBody (res ++ [w]) bd
    VLiftCirc (Abst vs (Abst lenv e)) -> 
        do let args = res ++ [w]
               lvs = length vs
           if lvs > (length args) then
             return $ VApp v w
             else do let ns = countVar vs e
                         sub = filter (\ (_ , (v, n)) -> n /= 0) $ zip vs (zip args ns)
                         sub' = zip vs args
                         ws = drop lvs args
                         lenv' = updateCirc sub' lenv
                     mapM_ (\(x, (v, n)) -> addDefinition (x, n) v) (lenv' ++ sub)
                     e' <- eval e
                     case e' of
                       VLam _ bd -> handleBody ws bd
                       _ -> return $ foldl VApp e' ws
        
    _ -> return $ VApp v w
          
  where unwindVal (VApp t1 t2) =
          let (h, args) = unwindVal t1
          in (h, args++[t2])
        unwindVal a = (a, [])
        -- Handle beta reduction
        handleBody args bd = open bd $ \ vs m ->
             let lvs = length vs
             in
              if lvs > length args
              then return $ VApp v w
              else do let sub = zip vs args
                          ws = drop lvs args
                      mapM_ (\ (x,v) -> addDefinition x v) sub
                      if null ws then eval m
                        else 
                        do m' <- eval m
                           return $ foldl VApp m' ws
        -- Perform substitution on the variables in a circuit.
        updateCirc :: [(Variable, Value)] -> LEnv -> [(Variable, (Value, Integer))]
        updateCirc sub lenv =
             let (x, (circ, n)):[] = Map.toList lenv
                 Wired (Abst wires (VCircuit (Morphism ins
                                               gs outs)))
                   = circ
                 params = map (\ (Gate _ p _ _ _ _) -> p) gs
                 ctrls = map (\ (Gate _ _ _ _ c _) -> c) gs
                 params' = map (\ p -> helper p sub) params
                 ctrls' = helper ctrls sub
                 gs' = zipWith3 (\ p c (Gate id _ inn oot _ flag) -> Gate id p inn oot c flag)
                       params' ctrls' gs
                 circ' = Wired (abst wires
                                 (VCircuit (Morphism ins
                                             gs' outs))) 
             in [(x, (circ', n))]
        -- Perfrom substitution.             
        helper :: [Value] -> [(Variable, Value)] -> [Value]
        helper [] lc = []
        helper (b:xs) lc =
          let b' = applyValSubst b lc
              res = helper xs lc
          in b':res
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
        applyValSubst c lc = 
          error $ "from applyValSubst" ++ (show $ disp c)

-- | Evaluate a box term.
evalBox :: Either Value EExp -> Value -> Eval Value               
evalBox body uv =
  freshLabels (size uv) $ \ vs ->
   do addWires vs
      st <- get
      b <- case body of
                Right body' -> eval body'
                Left v -> return v
      let uv' = toVal uv vs
          bgs = boxGates $ getSt (evalApp b uv') st
          gs = fst bgs
          res = snd $ snd bgs
          st' = fst $ snd bgs
          newMorph = Morphism uv' gs res
          wires' = wires st'
          morph' = Wired $ abst wires' (VCircuit newMorph)
      return morph'

-- | Evaluate an existsBox term. Note that
-- it is tempting to combine 'evalExbox' and 'evalBox' into one function,
-- but this will introduce bug, because we do not distinguish existential
-- pair and the usual tensor pair at runtime, the evaluator may confuse
-- the tensor pair with existential pair, thus making the wrong decision.
-- So we define 'evalExbox' and 'evalBox' separately to enforce the assumptions.
evalExbox :: EExp -> Value -> Eval Value        
evalExbox body uv =
  freshLabels (size uv) $ \ vs ->
   do addWires vs
      st <- get
      b <- eval body
      let uv' = toVal uv vs
          d = Morphism uv' [] uv'
          bgs = boxGates $ getSt (evalApp b uv') st
          gs = fst bgs
          res = snd $ snd bgs
          ws = wires $ fst $ snd bgs
          (VPair n res') = res
          newMorph = Morphism uv' gs res'
          morph' = Wired $ abst ws (VCircuit newMorph)
      return (VPair n morph')        




-- | Append a circuit to the underline circuit state according to a binding.
-- For efficiency reason we try prepend instead of append, so 'evalBox' and 'evalExbox'
-- have to reverse the list of gates as part of the post-processing. 
appendMorph :: Binding -> Morphism -> Eval Value
appendMorph binding f@(Morphism fins fs fouts) =
  do let (Morphism fins' fs' fouts') = rename f binding
     addGates fs'
     return fouts'



-- | A binding is a map of labels. 
type Binding = Map Label Label

-- | Obtain a binding from two simple terms. 
makeBinding :: Value -> Value -> Binding
makeBinding w v =
  let ws = getWires w
      vs = getWires v
  in if length ws /= length vs
     then 
       error ("binding mismatch!\n" ++ (show $ disp w) ++
               "\n" ++ (show $ disp v))
       else Map.fromList (zip ws vs)



   
-- | Reverse a list of gate in theory, in reality it only
-- changes the name of a gate to its adjoint, the gates are
-- already stored in reverse order due to the way we implement 'appendMorph'.
revGates :: [Gate] -> [Gate]
revGates xs = revGatesh xs [] 
  where revGatesh [] gs = gs
        revGatesh ((Gate id params ins outs ctrls flag):res) gs =
          let id' = invertName id
          in revGatesh res ((Gate id' params outs ins ctrls flag):gs)

-- | Change the name of a gate to its adjoint
invertName :: Id -> Id             
invertName id | getName id == "Init0" =  Id "Term0"
invertName id | getName id == "Init1" =  Id "Term1"
invertName id | getName id == "Term1" =  Id "Init1"
invertName id | getName id == "Term0" =  Id "Init0"
invertName id | getName id == "H" =  Id "H"
invertName id | getName id == "CNot" =  Id "CNot"
invertName id | getName id == "Not_g" =  Id "Not_g"
invertName id | getName id == "C_Not" =  Id "C_Not"
invertName id | getName id == "QNot" =  Id "QNot"
invertName id | getName id == "CNotGate" =  Id "CNotGate"
invertName id | getName id == "ToffoliGate_10" =  Id "ToffoliGate_10"
invertName id | getName id == "ToffoliGate_01" =  Id "ToffoliGate_01"
invertName id | getName id == "ToffoliGate" =  Id "ToffoliGate"
invertName id | getName id == "Mea" = error "cannot invert Mea gate"
invertName id | getName id == "Discard" = error "cannot invert Discard gate"
invertName id | last (getName id) /= '*' =  Id $ getName id ++ "*"
              | otherwise = Id $ init (getName id)


-- | Rename /uv/ using fresh labels draw from /vs/.
toVal :: Value -> [Label] -> Value
toVal uv vs = S.evalState (templateToVal uv) vs

-- | Obtain a fresh template inhabitant of a simple type, with wirenames
-- drawn from the state. The input is a simple data type.
templateToVal :: Value -> State [Label] Value
templateToVal (VLBase _) =
  do x <- S.get
     let (v:vs) = x
     S.put vs
     return (VLabel v)
templateToVal a@(VConst _) = return a
templateToVal a@(VUnit) = return VStar
templateToVal (VApp e1 e2) =
  do e1' <- templateToVal e1
     e2' <- templateToVal e2
     return $ VApp e1' e2'

templateToVal (VTensor e1 e2) =
  do e1' <- templateToVal e1
     e2' <- templateToVal e2
     return $ VPair e1' e2'

templateToVal a = error "applying templateToVal function to an ill-formed template"

-- | Get the size of a simple data type.
size :: Num a => Value -> a
size (VLBase x) = 1
size (VConst _) = 0
size VUnit = 0
size (VApp e1 e2) = size e1 + size e2
size (VTensor e1 e2) = size e1 + size e2
size a = error $ "applying size function to an ill-formed template:" ++ (show $ disp a)     

-- | Obtain all the labels from the circuit.

-- getAllWires :: Morphism -> [Label]
-- getAllWires (Morphism ins gs outs) =
--   let inWires = S.fromList $ getWires ins
--       outWires = S.fromList $ getWires outs
--       gsWires = S.unions $ map getGateWires gs
--   in S.toList (inWires `S.union` outWires `S.union` gsWires)
--   where getGateWires (Gate _ _ ins outs ctrls _) =
--           S.fromList (getWires ins) `S.union`
--           S.fromList (getWires outs) `S.union`
--           S.fromList (getWires ctrls)


-- | Decrease the reference count for a list of variables.
decrRef :: [Variable] -> Map Variable (Value, Integer, Integer, [Variable]) ->
           Map Variable (Value, Integer, Integer, [Variable])          
decrRef [] m = m
decrRef (v:vs) m =
  case Map.lookup v m of
    Nothing -> error "from decrRef"
    Just (val, n, ref, ps) ->
      let m' = Map.insert v (val, n, ref-1, ps) m
      in decrRef vs m'
        

  



