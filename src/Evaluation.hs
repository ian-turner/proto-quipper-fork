{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}


-- | This module implements a closure-based call-by-value evaluation.
-- It still has memory problem when generating super-large circuits.

module Evaluation 
       (eval, initES, size, toVal) where

import Syntax
import Erasure
import SyntacticOperations
import Utils
import Nominal
import Simulation

import Control.Exception 
import Control.Monad.State 

import Control.Monad.Identity
import Control.Monad.Except
import Text.PrettyPrint
import TCMonad 

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.List
import Data.Tuple
import qualified Data.Set as S
import Debug.Trace


-- * The Eval monad and eval function.

-- | The evaluation monad.
type Eval a = StateT EvalState ReadWrite a


-- | Evaluator state, it contains an underlying circuit and
-- a global context. 
data EvalState =
  ES { evalEnv :: Context,  -- ^ The global evaluation context.
       labels :: [Label]
     }

initES gl = ES{evalEnv = gl, labels = []}

     
dynamicLift :: Label -> Eval Bool
dynamicLift l = lift $ dynliftRW l

addGates :: [Gate] -> Eval ()
addGates gs = lift $ mapM_ gateRW gs


-- | Evaluate an expression to
-- a value in the value domain. The eval function also takes an environment
-- as argument and form a closure when evaluating a lambda abstraction or a lifted term.

eval :: LEnv -> EExp -> Eval Value
eval !lenv (EVar x) = 
  return $ lookupLEnv x lenv


eval !lenv EStar = return VStar
eval !lenv EUnit = return VUnit
eval !lenv a@(EConst k) =
  do st <- get
     let genv = evalEnv st
     case Map.lookup k genv of
       Nothing -> error $ "undefined" ++ (show $ disp k) 
       Just e ->
         case identification e of
           DataConstr _ -> return (VConst k)
           DefinedGate v -> return v
           DefinedFunction (Just (_, v, _)) -> return v
           DefinedFunction Nothing -> throw $ userError ("undefined: " ++ (show $ disp k))
           DefinedMethod _ v -> return v
           DefinedInstFunction _ v -> return v

eval !lenv (EBase k) = return $ VBase k

eval !lenv a@(ELBase k) =
  do st <- get
     let genv = evalEnv st
     case Map.lookup k genv of
       Nothing -> throw $ userError ("undefined: " ++ (show $ disp k))
       Just e ->
         case identification e of
           DataType Simple _ (Just (ELBase id)) -> return (VLBase id)
           DataType (SemiSimple _) _ (Just d) -> eval lenv d
           DataType _ _ Nothing -> return (VBase k)

eval !lenv (EForce m) =
  do m' <- eval lenv m
     case m' of
       VLift (Abst lenv e) -> eval lenv e
       VDynlift -> return $ VForce VDynlift
       w@(VLiftCirc _) -> return w
       v@(VApp VUnBox _) -> return $ VForce v
       a -> error $ "from eval(EForce):" ++ (show $ disp a)
       
eval !lenv (ETensor e1 e2) =
  do e1' <- eval lenv e1
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

-- Note that because QuantumState is an example
-- of state monad, sequencing is enforced. So each
-- statement will be evaluated to weak head normal form in sequence.
-- This means /w/ below will be evaluated to weak head normal form,
-- hence making the implementation conforming the eager evaluation
-- strategy. As a result, we do not get lazy circuit in the sense of Quipper.

eval !lenv (EApp m n) =
  do v <- eval lenv m
     w <- eval lenv n
     evalApp v w

eval !lenv (EPair m n) = 
  do v <- eval lenv m
     w <- eval lenv n
     return (VPair v w)

eval !lenv (ELet m bd) =
  do m' <- eval lenv m
     open bd $ \ x n ->
       let lenv' = addDefinition x m' lenv
       in eval lenv' n


eval !lenv (ELetPair m (Abst xs n)) =
  do m' <- eval lenv m
     let r = unVPair (length xs) m'
     case r of
       Just vs -> 
         let lenv' = foldl (\ a (x, y) -> addDefinition x y a) lenv
                     (zip xs vs)
         in eval lenv' n

eval !lenv (ELetPat m bd) =
  do m' <- eval lenv m
     case vflatten m' of
       Nothing -> error ("from LetPat" ++ (show $ disp m'))
       Just (Left id, args) ->
         open bd $ \ p n ->
         case p of
           EPApp kid vs
             | kid == id ->
               do let vs' = vs 
                      subs = (zip vs' args)
                      lenv' = foldl (\ a (x, v) -> addDefinition x v a) lenv subs
                  eval lenv' n
           p -> error "pattern mismatch, from eval ELetPat" 

eval !lenv b@(ECase m (EB bd)) =
  do m' <- eval lenv m
     case vflatten m' of
       Nothing -> error ("from eval (Case):")
       Just (Left id, args) ->
         reduce id args bd
  where reduce id args (bd:bds) =
          open bd $ \ p m ->
          case p of
             EPApp kid vs
               | kid == id -> 
               do -- st <- get
                  let vs' = vs
                      subs = zip vs' args
                      lenv' = foldl' (\ a (x, v) -> addDefinition x v a) lenv subs
                  eval lenv' m
               | otherwise -> reduce id args bds
        reduce id args [] = throw $ userError ("missing a branch for: " ++ show (disp id))

eval !lenv a = error $ "from eval: " ++ (show $ disp a)


-- * Helper functions for eval.

-- | Look up a value from the local environment.
-- It also implements a nonstop GC. Compared to stop-the-world-gc,
-- The CONS is that if the garbage is not access
-- anymore, there is no way to collect them. The
-- PROS is that it runs faster than stop-the-world-gc and it does not
-- stop anything. 
lookupLEnv :: Variable -> LEnv -> Value
lookupLEnv x lenv =
     case Map.lookup x lenv of
       Nothing -> error $ "from lookupLEnv:" ++ show x
       Just v -> v
           
-- | Add a value to the environment.
addDefinition x m lenv =
     Map.insert x m lenv


  
-- | A helper function for evaluating various of applications.
evalApp :: Value -> Value -> Eval Value
evalApp VUnBox v =
  case v of
    (Wired _) -> return $ VApp VUnBox v
    _ -> return VUnBox


evalApp (VForce VDynlift) (VLabel v) =
  do b <- dynamicLift v
     if b then
       return $ VConst (Id "True")
       else return $ VConst (Id "False")

-- append gates
evalApp (VForce (VApp VUnBox (Wired (Abst wires morph)))) w =
 do let binding = makeBinding (input morph) w
    appendMorph binding morph

evalApp (VApp (VApp (VApp VBox q) _) _) v =
  case v of
    VLift (Abst lenv m) -> evalBox lenv (Right m) q
    VApp VUnBox w -> return w
    m@(VLiftCirc _) -> evalBox Map.empty (Left m) q
    a -> error $ "evalApp VBox:" ++ (show $ disp a)

evalApp (VApp (VApp (VApp (VApp VExBox q) _) _) _) v =  
  case v of
    VLift (Abst lenv body) ->
      evalExbox lenv body q


evalApp (VApp (VApp VReverse _) _) (Wired (Abst ws (Morphism ins gs outs))) = do
  let gs' = revGates gs
  return $ Wired (abst ws $ Morphism outs gs' ins)



evalApp (VApp (VApp (VApp VControlled _) _) _) (Wired (Abst ws m)) = 
  freshNames ["#ctrl", "#input", "#circ"] $ \ (ctrl:inp:circ:[]) -> do
      let ins = input m
          gs = gates m
          outs = output m
          mycirc = Wired (abst ws $ Morphism ins (controlledGates ctrl gs) outs)
          env = Map.fromList [(circ, mycirc)] 
          exp = EPair (EApp 
                       (EForce $ EApp EUnBox (EVar circ)) (EVar inp)) (EVar ctrl)
      return $ VLiftCirc (abst [inp, ctrl] $ abst env exp)
  where controlledGates a gs = map (helper a) gs
        helper a (Gate id ps ins outs b False inv) = Gate id ps ins outs b False inv
        helper a (Gate id ps ins outs VStar flag inv) = Gate id ps ins outs (VVar a) flag inv
        helper a (Gate id ps ins outs b flag inv) =
          Gate id ps ins outs (VPair b (VVar a)) flag inv

evalApp (VApp (VApp (VApp (VApp (VApp VWithComputed _) _) _)_)_) m =
  return $ VComputed m 

evalApp (VComputed (Wired (Abst ws1 m1'))) (Wired (Abst ws2 circ2)) = do
  -- evalApp (VComputed (VCircuit m1)) (VCircuit m2) = do
--  m1' <- refresh m1
  let gs1 = gates m1'
      a = input m1'
      b1 = fstVPair $ output m1'
      e = sndVPair $ output m1'
--  circ2 <- refresh m2
  let b2 = fstVPair $ input circ2
  let gs1' = map negateCtrl gs1
      gs1'' = revGates gs1'
      circ1' = (Morphism (VPair b1 e) gs1'' a)
--  circ1' <- refresh (Morphism (VPair b1 e) gs1'' a) 
  let -- (Morphism (VPair b1' _) _ _) = circ1'
      b1' = b1
      binding = makeBinding b2 b1
      circ2' = rename circ2 binding
      gs2 = gates circ2'
      c = sndVPair $ input circ2'
      b3 = fstVPair $ output circ2'
      d = sndVPair $ output circ2'
      binding2 = makeBinding b1' b3
      circ3 = rename circ1' binding2
      gs1''' = gates circ3
      a' = output circ3
      res = Wired $ abst (ws1++ws2) (Morphism (VPair a c) (gs1' ++ gs2 ++ gs1''') (VPair a' d))
        -- VCircuit (Morphism (VPair a c) (gs1' ++ gs2 ++ gs1''') (VPair a' d))
  return res
  where negateCtrl (Gate e1 e2 e3 e4 e5 b inv) = Gate e1 e2 e3 e4 e5 False inv
        fstVPair (VPair a _) = a
        sndVPair (VPair _ b) = b

evalApp a@(Wired _) w = return a

evalApp v w = 
  let (h, res) = unwindVal v
  in case h of
    VLam (Abst lenv bd) -> handleBody lenv (res ++ [w]) bd
    VLiftCirc (Abst vs (Abst lenv e)) -> 
        do let args = res ++ [w]
               lvs = length vs
           if lvs > (length args) then
             return $ VApp v w
             else do let sub' = zip vs args
                         ws = drop lvs args
                         lenv'= updateCirc sub' lenv
                         lenv'' = Map.fromList (lenv' ++ sub')
                     e' <- eval lenv'' e
                     case e' of
                       VLam (Abst lenv''' bd) -> handleBody lenv''' ws bd
                       _ ->
                         return $ foldl (\ x y -> VApp x y) e' ws
        
    _ -> return $ VApp v w
          
  where
        -- Handle beta reduction
        handleBody lenv args bd = open bd $ \ vs m ->
             let lvs = length vs
             in
              if lvs > length args
              then return $ VApp v w
              else do let sub = zip vs args
                          ws = drop lvs args
                          lenv' = foldl' (\ a (x,v) -> addDefinition x v a) lenv sub
                      if null ws then eval lenv' m
                        else 
                        do m' <- eval lenv' m
                           return $ foldl (\ x y -> VApp x y) m' ws
        -- Perform substitution on the variables in a circuit.
        updateCirc :: [(Variable, Value)] -> LEnv -> [(Variable, Value)]
        updateCirc sub lenv =
             let [(x, Wired (Abst wires (Morphism ins gs outs)))] = Map.toList lenv
                 params1 = map params gs
                 ctrls = map ctrl gs
                 params' = map (\ p -> helper p sub) params1
                 ctrls' = helper ctrls sub
                 gs' = zipWith3 (\ p c g ->
                                  Gate (gateName g) p (inputVal g)
                                  (outputVal g) c (ctrlFlag g) (inv g))
                       params' ctrls' gs
                 circ' = Wired (abst wires (Morphism ins gs' outs))
             in [(x, circ')]
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

-- evalBox :: Either Value EExp -> Value -> Eval Value               
evalBox lenv body uv = freshLabels (size uv) $ \ vs ->
   do st <- get
      b <- case body of
                Right body' -> eval lenv body'
                Left v -> return v
      let uv' = toVal uv vs
          bgs = boxGates $ runStateT (evalApp b uv') st
          gs = fst bgs
          res = fst $ snd bgs
          st' = snd $ snd bgs
          vs' = labels st'
          newMorph = Morphism uv' gs res
          morph' = Wired (abst (vs++vs') newMorph)
      return morph'

-- | Evaluate an existsBox term. Note that
-- it is tempting to combine 'evalExbox' and 'evalBox' into one function,
-- but this will introduce bug, because we do not distinguish existential
-- pair and the usual tensor pair at runtime, the evaluator may confuse
-- the tensor pair with existential pair, thus making the wrong decision.
-- So we define 'evalExbox' and 'evalBox' separately to enforce the assumptions.
   
-- evalExbox :: EExp -> Value -> Eval Value        
evalExbox lenv body uv = freshLabels (size uv) $ \ vs ->
   do st <- get
      b <- eval lenv body
      let uv' = toVal uv vs
          d = Morphism uv' [] uv'
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
  where fstVPair (VPair a _) = a
        sndVPair (VPair _ b) = b



-- | Append a circuit to the underline circuit state according to a binding.
-- For efficiency reason we try prepend instead of append, so 'evalBox' and 'evalExbox'
-- have to reverse the list of gates as part of the post-processing. 
appendMorph :: Binding -> Morphism -> Eval Value
appendMorph binding f = 
  do let f' = rename f binding
         gs = gates f'
         outs = output f'
     addGates gs
     return outs



-- | A binding is a map of labels. 
type Binding = Map Label Label

-- | Obtain a binding from two simple terms. 
makeBinding :: Value -> Value -> Binding
makeBinding w v =
  let ws = getWires w
      vs = getWires v
  in Map.fromList (zip ws vs)
     



   
-- | Reverse a list of gate in theory, in reality it only
-- changes the name of a gate to its adjoint, the gates are
-- already stored in reverse order due to the way we implement 'appendMorph'.
revGates :: [Gate] -> [Gate]
revGates xs = map invertGateName $ reverse xs
  where invertGateName (Gate id params ins outs ctrls flag (Just g)) =
          Gate g params outs ins ctrls flag (Just id)
        invertGateName (Gate id params ins outs ctrls flag Nothing) =
          error $ "non-invertable gate:" ++ getName id
-- | Rename /uv/ using fresh labels draw from /vs/.
toVal :: Value -> [Label] -> Value
toVal uv vs = evalState (templateToVal uv) vs

-- | Obtain a fresh template inhabitant of a simple type, with wirenames
-- drawn from the state. The input is a simple data type.
templateToVal :: Value -> State [Label] Value
templateToVal (VLBase _) =
  do x <- get
     let (v:vs) = x
     put vs
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
size :: Value -> Int
size (VLBase x) = 1
size (VLabel x) = 1
size (VConst _) = 0
size VUnit = 0
size VStar = 0
size (VApp e1 e2) = size e1 + size e2
size (VTensor e1 e2) = size e1 + size e2
size (VPair e1 e2) = size e1 + size e2
size a = error $ "applying size function to an ill-formed template:" ++ (show $ disp a)     

