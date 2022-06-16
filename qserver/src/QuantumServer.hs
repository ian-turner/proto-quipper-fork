{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}

-- | A simple and inefficient reference implementation of the quantums
-- server protocol, version 0.

module QuantumServer (
  server
  ) where

import ParseCommand


import Ring
import Stabilizer hiding (H, S, Z, X, Y, StabilizerState)
import qualified Stabilizer as Stable
import qualified Data.Map as Map
import Data.Map (Map)

import Control.Exception
import Data.Typeable
import Control.Applicative
import Control.Monad
import Data.String
import Data.List
import Debug.Trace

import System.Exit
import System.Random
import System.IO
import System.IO.Error

-- ----------------------------------------------------------------------
-- * Types


-- | A context is a list of registers.
type Context = [Register]


-- | A complex number is a member of 'DOmega'.

type Complex = DOmega

-- | A state for a bit context is a bit vector.
type BitVector = [Bit]

-- | A state for a qubit context is a map from bitvectors to
-- amplitudes.
type QubitVector = Map BitVector Complex

-- | A classical state.
type BState = (Context, BitVector)

-- | A quantum state.
type QState = (Context, Map BitVector Complex)

-- | A type is either 'Bit' or 'Qubit'.
data Type = Bit | Qubit
                  deriving (Show, Eq)

-- | A type environment is a map from registers to types.
type Typing = Map Register Type

-- | Exceptions resulting from incorrect usage.
data UsageException =
  NoSuchRegister Register   -- ^ Attempted to access an unallocated register.
  | RegisterExists Register -- ^ Attempted to initialize an allocated register.
  | NonLinear Register      -- ^ Attempted to access the register non-linearly.
  | TypeCheck Register Type -- ^ Attempted to access a register of wrong type.
  deriving (Typeable)

instance Exception UsageException

instance Show UsageException where
  show (NoSuchRegister x) = "No such register: " ++ show x
  show (RegisterExists x) = "Register exists: " ++ show x
  show (NonLinear x) = "Non-linear access: " ++ show x
  show (TypeCheck x t) = "Type mismatch: register " ++ show x ++ " has type " ++ show t

-- | Exception resulting from an internal error, i.e., a violation of
-- a program invariant. These should not happen.
data InternalException =
  Internal String           -- ^ Invariant violated. Should not happen.
  deriving (Typeable)

instance Exception InternalException

instance Show InternalException where
  show (Internal s) = "Internal error: " ++ s

-- ----------------------------------------------------------------------
-- * Operations on typing contexts

-- | Return the type of the given register, or Nothing if undefined.
get_type :: Typing -> Register -> Maybe Type
get_type gamma n = Map.lookup n gamma

-- | Check whether the given register is allocated.
is_free :: Typing -> Register -> Bool
is_free gamma n = not (Map.member n gamma)

-- | Find a free register.
freereg :: Typing -> Register
freereg gamma = aux 0 where
  aux n
    | is_free gamma n = n
    | otherwise = aux (n+1)

-- | Reserve a new register of the given type.
lockreg :: Typing -> Register -> Type -> Typing
lockreg gamma n t
  | is_free gamma n = Map.insert n t gamma
  | otherwise = throw (RegisterExists n)

-- | Remove the given register.
delreg :: Typing -> Register -> Typing
delreg gamma n
  | Map.member n gamma = Map.delete n gamma
  | otherwise = throw (NoSuchRegister n)

-- | The empty context.
empty_typing :: Typing
empty_typing = Map.empty

-- ----------------------------------------------------------------------
-- * Operations on bit states

-- | The empty bit state.
empty_bstate :: BState
empty_bstate = ([], [])

-- | Add a new bit to a classical state.
newbit :: BState -> Register -> Bit -> BState
newbit (ctxt, vec) n b = (n : ctxt, b : vec)

-- | Read the given bit from the classical state.
readbit :: BState -> Register -> Bool
readbit (m : ctxt, b : vec) n
  | m == n = b
  | otherwise = readbit (ctxt, vec) n
readbit (ctxt, vec) n = throw (Internal "readbit")


-- | The underlying register of a control.
unCtrl :: Ctrl -> Register
unCtrl (Pos x) = x
unCtrl (Neg x) = x

-- | Read the given control from the classical state.
readctrl :: BState -> Ctrl -> Bool
readctrl s (Pos x) = readbit s x
readctrl s (Neg x) = not (readbit s x)

-- | Delete the given bit from the classical state.
delbit :: BState -> Register -> BState
delbit (m : ctxt, b : vec) n
  | m == n = (ctxt, vec)
  | otherwise = (m : ctxt', b : vec') where
  (ctxt', vec') = delbit (ctxt, vec) n
delbit (ctxt, vec) n = throw (Internal "delbit")

-- | Check the given list of classical controls.
andbits :: BState -> [Ctrl] -> Bool
andbits st [] = True
andbits st (h:t) = readctrl st h && andbits st t

-- | Negate the given bit in a 'BitVector'.
negate_bv :: Context -> BitVector -> Register -> BitVector
negate_bv (m : ctxt) (b : vec) n
  | m == n = not b : vec
  | otherwise = b : negate_bv ctxt vec n
negate_bv ctxt vec n = throw (Internal "negate_bv")                

-- | Negate the given bit.
negatebit :: BState -> Register -> BState
negatebit (ctxt, vec) n = (ctxt, negate_bv ctxt vec n)

-- ----------------------------------------------------------------------
-- * Auxiliary operations for matrix manipulations

-- | Increase the value for key /k/ by a given numerical amount. This
-- will erase the key (basis state) if the result is 0.
map_add :: (Ord k, Eq a, Num a) => a -> k -> Map k a -> Map k a
map_add a k m = Map.alter (g . f) k m where
  f Nothing = a
  f (Just b) = a+b
  g 0 = Nothing
  g b = Just b

-- | Linearly extend a map from basis states to all states. For example,
-- suppose \f\ = H = (0 |-> (0 |-> 1/sqrt(2), 1 |-> 1/sqrt(2)),
--                  1 |-> (0 |-> 1/sqrt(2), 1 |-> -1/sqrt(2)))
-- initial qubit state \m\ is (0 |-> alpha1, 1 |-> alpha2).
-- `extend_linearly` will map \m\ to \m'\, where \m'\ =
-- (0 |-> 1/sqrt(2)(alpha1 + alpha2),
--  1 |-> 1/sqrt(2)(alpha1 - alpha2)).  
extend_linearly :: (BitVector -> Map BitVector Complex) ->
                    Map BitVector Complex ->
                    Map BitVector Complex
extend_linearly f m = m'
  where
    m' = Map.foldrWithKey g Map.empty m
    g k alpha map = Map.foldrWithKey (\ k beta m -> map_add (alpha*beta) k m) map (f k)

      
-- ----------------------------------------------------------------------
-- * Operations on qubit states

-- | The empty quantum state.
empty_qstate :: QState
empty_qstate = ([], Map.singleton [] 1)

-- | Add a new qubit to a quantum state.
newqubit :: QState -> Register -> Bit -> QState
newqubit (ctxt, qvec) n b = (n : ctxt, extend_linearly f qvec)
  where
    f vec = Map.singleton (b : vec) 1

-- | Negate the given qubit.
gateX :: QState -> Register -> QState
gateX (ctxt, qvec) n = (ctxt, extend_linearly f qvec)
  where
    f vec = Map.singleton (negate_bv ctxt vec n) 1
        
-- | Apply the Pauli /Z/-gate to the given qubit.
gateZ :: QState -> Register -> QState
gateZ (ctxt, qvec) n = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) n == True = Map.singleton vec (-1)
      | otherwise = Map.singleton vec 1

gateDiag :: Double -> Double -> QState -> Register -> QState
gateDiag a b (ctxt, qvec) n = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) n == True = Map.singleton vec (fromDyadic $  to_dyadic (realToFrac b :: Rational))
      | otherwise = Map.singleton vec (fromDyadic $ to_dyadic (realToFrac a :: Rational))

-- | Apply the Pauli /Y/-gate to the given qubit.
gateY :: QState -> Register -> QState
gateY (ctxt, qvec) n = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) n == True = Map.singleton vec' (-i)
      | otherwise = Map.singleton vec' i
      where
        vec' = negate_bv ctxt vec n

-- | Apply a Hadamard gate to the given qubit.
gateH :: QState -> Register -> QState
gateH (ctxt, qvec) n = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) n == False = -- plus
          Map.fromList [(vec, roothalf), (vec', roothalf)]
      | otherwise = -- minus
          Map.fromList [(vec, -roothalf), (vec', roothalf)]
        where
          vec' = negate_bv ctxt vec n

-- | Apply an /S/-gate to the given qubit.
gateS :: QState -> Register -> QState
gateS (ctxt, qvec) n = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) n == True = Map.singleton vec i
      | otherwise = Map.singleton vec 1

-- | Apply a rotation r of type double to the given qubit. Note that since DOmega (D[omega]) does not
-- contain Euler's constant e, so here we use e^{i*r} = cos r + i * sin r for the calculation.
gateRot :: Double -> QState -> Register -> QState
gateRot r (ctxt, qvec) n = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) n == True =
          Map.singleton vec
          ((fromDyadic $ to_dyadic $ (realToFrac (cos r) :: Rational)) + i * (fromDyadic $ to_dyadic $ (realToFrac (sin r) :: Rational))) 
      | otherwise = Map.singleton vec 1

-- | Apply a /T/-gate to the given qubit.
gateT :: QState -> Register -> QState
gateT (ctxt, qvec) n = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) n == True = Map.singleton vec omega
      | otherwise = Map.singleton vec 1

gateTInv :: QState -> Register -> QState
gateTInv (ctxt, qvec) n = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) n == True = Map.singleton vec (adj omega)
      | otherwise = Map.singleton vec 1

gateSInv :: QState -> Register -> QState
gateSInv (ctxt, qvec) n = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) n == True = Map.singleton vec (adj i)
      | otherwise = Map.singleton vec 1

-- | Apply a /CNOT/-gate to the given pair of qubits.
gateCNOT :: QState -> Register -> Register -> QState
gateCNOT (ctxt, qvec) x y = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) y == True =
      Map.singleton (negate_bv ctxt vec x) 1
      | otherwise = Map.singleton vec 1

-- | Apply a /Toffoli/-gate to the given pair of qubits.
gateTOF :: QState -> Register -> Register -> Register -> QState
gateTOF (ctxt, qvec) x y z = (ctxt, extend_linearly f qvec)
  where
    f vec
      | (readbit (ctxt, vec) y && readbit (ctxt, vec) z)  == True =
        Map.singleton (negate_bv ctxt vec x) 1
      | otherwise = Map.singleton vec 1

-- | Apply a controlled-/Y/-gate to the given pair of qubits.
gateCY :: QState -> Register -> Register -> QState
gateCY (ctxt, qvec) x y = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) y == True &&
        readbit (ctxt, vec) x == True =
        Map.singleton vec' (-i)
      | readbit (ctxt, vec) y == True &&
        readbit (ctxt, vec) x == False =
        Map.singleton vec' i
      | otherwise = Map.singleton vec 1
     where
          vec' = negate_bv ctxt vec x
          
-- | Apply a controlled-/Z/-gate to the given pair of qubits.
gateCZ :: QState -> Register -> Register -> QState
gateCZ (ctxt, qvec) x y = (ctxt, extend_linearly f qvec)
  where
    f vec
      | readbit (ctxt, vec) x == True
      && readbit (ctxt, vec) y == True = Map.singleton vec (-1)
      | otherwise = Map.singleton vec 1

-- | Compute the probability corresponding to a given qubit being 0.
compute_probability :: QState -> Register -> QRootTwo
compute_probability (ctxt, qvec) x
  | p + q == 0 = throw (Internal "compute_probability")
  | otherwise = fromDRootTwo p / fromDRootTwo (p + q)
  where
    (p, q) = Map.foldrWithKey g (0, 0) qvec
    g vec alpha (p, q)
      | readbit (ctxt, vec) x == False = (p + prob, q)
      | otherwise = (p, q + prob)
      where
        prob :: DRootTwo
        prob = real (alpha * adj alpha)

-- | Collapse the given qubit to the given bit.
collapse :: QState -> Register -> Bit -> QState
collapse (ctxt, qvec) x b = (aux ctxt, extend_linearly f qvec)
  where
    aux (m : ctxt)
      | m == x = ctxt
      | otherwise = m : aux ctxt
    aux [] = throw (Internal "collapse")
    f vec
      | readbit (ctxt, vec) x == b = Map.singleton vec' 1
      | otherwise = Map.empty
      where
        (_, vec') = delbit (ctxt, vec) x

-- | Randomly choose 0 with probability /p/ and 1 with probability
-- 1-/p/.
random_choice :: (RandomGen g) => QRootTwo -> g -> Bit
random_choice 0 g = True
random_choice 1 g = False
random_choice p g = b
  where
    (x, _) = randomR (0.0, 1.0 :: Double) g
    b | x < fromQRootTwo p = False
      | otherwise = True
             
-- | Measurement.
measure_qstate :: (RandomGen g) => QState -> Register -> g -> (Bit, QState)
measure_qstate gamma x g = (b, gamma')
  where
    b = random_choice (compute_probability gamma x) g
    gamma' = collapse gamma x b

-- ----------------------------------------------------------------------
-- * Monadic interface

-- ----------------------------------------------------------------------
-- ** A state monad

-- | A high-level state consists of a typing context, a compatible
-- classical state, and a compatible quantum state.
newtype State = State (Typing, BState, QState)
                deriving (Show)

-- | Strictly evaluate the first part of the state.
strict :: State -> a -> a
strict (State (t, b, q)) x = t `seq` x

-- | The initial state.
initial_state :: State
initial_state = State (empty_typing, empty_bstate, empty_qstate)

-- | The 'Quantum' monad is a state monad for 'State'.
newtype Quantum a = Quantum { run :: State -> (State, a) }

instance Monad Quantum where
  return a = Quantum (\s -> (s, a))
  (Quantum f) >>= g = Quantum (\s -> let (s', a) = f s in let Quantum h = g a in h s')

instance Applicative Quantum where
  pure = return
  (<*>) = ap

instance Functor Quantum where
  fmap = liftM

-- | Get the current state.
get :: Quantum State
get = Quantum (\s -> (s, s))

-- | Set the current state.
set :: State -> Quantum ()
set s = Quantum (\t -> (s, ()))

get_typing :: Quantum Typing
get_typing = do
  State (gamma, _, _) <- get
  return gamma

get_bstate :: Quantum BState
get_bstate = do
  State (_, bst, _) <- get
  return bst

get_qstate :: Quantum QState
get_qstate = do
  State (_, _, qst) <- get
  return qst

set_typing :: Typing -> Quantum ()
set_typing gamma = do
  State (gamma', bst, qst) <- get
  set (State (gamma, bst, qst))

set_bstate :: BState -> Quantum ()
set_bstate bst = do
  State (gamma, bst', qst) <- get
  set (State (gamma, bst, qst))

set_qstate :: QState -> Quantum ()
set_qstate qst = do
  State (gamma, bst, qst') <- get
  set (State (gamma, bst, qst))

-- ----------------------------------------------------------------------
-- ** Auxiliary functions

-- | Check that the given register is defined with the current
-- type. Raise an appropaite exception otherwise.
typecheck :: Register -> Type -> Quantum ()
typecheck n t = do
  gamma <- get_typing
  case get_type gamma n of
   Nothing -> throw (NoSuchRegister n)
   Just t' | t /= t' -> throw (TypeCheck n t')
   _ -> return ()

-- | Apply classical bits to control a computation.
with_controls :: [Ctrl] -> Quantum () -> Quantum ()
with_controls ctrls body = do
  gamma <- get_typing
  sequence_ [typecheck x Bit | x <- map unCtrl ctrls]
  bst <- get_bstate
  let c = andbits bst ctrls
  if c then body else return ()

-- ----------------------------------------------------------------------
-- ** API functions

-- | Find a free register. Note: this is not allocated.
alloc :: Quantum Register
alloc = do
  gamma <- get_typing
  return (freereg gamma)

-- | Initialize a new bit register.
binit :: Register -> Bit -> Quantum ()
binit n b = do
  gamma <- get_typing
  let gamma' = lockreg gamma n Bit
  set_typing gamma'
  bst <- get_bstate
  let bst' = newbit bst n b
  set_bstate bst'
  return ()

-- | Apply a controlled-/X/ gate to a classical bit.
bnot :: Register -> [Ctrl] -> Quantum ()
bnot x ctrls = do
  typecheck x Bit
  when (x `elem` map unCtrl ctrls) $ throw (NonLinear x)
  with_controls ctrls $ do
    bst <- get_bstate
    let bst' = negatebit bst x
    set_bstate bst'

-- | Read the value of the register, which must be a bit. The register
-- is deallocated.
bread :: Register -> Quantum Bit
bread x = do
  gamma <- get_typing
  typecheck x Bit
  let gamma' = delreg gamma x
  set_typing gamma'
  bst <- get_bstate
  let b = readbit bst x
  let bst' = delbit bst x
  set_bstate bst'
  return b

-- | Initialize a new qubit register.
qinit :: Register -> Bit -> Quantum ()
qinit n b = do
  gamma <- get_typing
  let gamma' = lockreg gamma n Qubit
  set_typing gamma'
  qst <- get_qstate
  let qst' = newqubit qst n b
  set_qstate qst'
  return ()

-- | Initialize a qubit register from a bit register.
qnew :: Register -> Quantum ()
qnew x = do
  b <- bread x
  qinit x b

-- | Apply a unary gate to a quantum bit.
unary_gate :: (QState -> Register -> QState) -> Register -> [Ctrl] -> Quantum ()
unary_gate gate x ctrls = do
  typecheck x Qubit
  when (x `elem` map unCtrl ctrls) $ throw (NonLinear x)
  with_controls ctrls $ do
    qst <- get_qstate
    let qst' = gate qst x
    set_qstate qst'

-- | Apply a binary gate to a quantum bit.
binary_gate :: (QState -> Register -> Register -> QState) -> Register -> Register -> [Ctrl] -> Quantum ()
binary_gate gate x y ctrls = do
  typecheck x Qubit
  typecheck y Qubit
  when (x == y) $ throw (NonLinear x)
  when (x `elem` map unCtrl ctrls) $ throw (NonLinear x)
  with_controls ctrls $ do
    qst <- get_qstate
    let qst' = gate qst x y
    set_qstate qst'

ternary_gate :: (QState -> Register -> Register -> Register -> QState) -> Register -> Register -> Register -> [Ctrl] -> Quantum ()
ternary_gate gate x y z ctrls = do
  typecheck x Qubit
  typecheck y Qubit
  typecheck z Qubit
  when (x == y || y == z || x == z) $ throw (NonLinear x)
  when (x `elem` map unCtrl ctrls || y `elem` map unCtrl ctrls || z `elem` map unCtrl ctrls) $ throw (NonLinear x)
  with_controls ctrls $ do
    qst <- get_qstate
    let qst' = gate qst x y z
    set_qstate qst'

-- | Apply an /X/ gate to a classical or quantum bit.
apply_X :: Register -> [Ctrl] -> Quantum ()
apply_X x ctrls = do
  gamma <- get_typing
  case get_type gamma x of
   Nothing -> throw (NoSuchRegister x)
   Just Qubit -> unary_gate gateX x ctrls
   Just Bit -> bnot x ctrls

measure :: (RandomGen g) => Register -> g -> Quantum ()
measure x g = do
  gamma <- get_typing
  typecheck x Qubit
  let gamma' = delreg gamma x
  set_typing gamma'
  qst <- get_qstate
  let (b, qst') = measure_qstate qst x g
  set_qstate qst'
  binit x b

-- | Read the value of a register. If it is a qubit, it is measured 
-- first. The register is deallocated.
qbread :: (RandomGen g) => Register -> g -> Quantum Bit
qbread x g = do
  gamma <- get_typing
  case get_type gamma x of
   Nothing -> throw (NoSuchRegister x)
   Just Bit -> bread x
   Just Qubit -> do
     measure x g
     bread x

-- ----------------------------------------------------------------------
-- * Interpreter

-- | Usage information.
usage :: String
usage = ""
  ++ "Control commands:\n"
  ++ " help             - print usage information\n"
  ++ " reset            - reset the machine to the initial state\n"
  ++ " quit             - quit\n"
  ++ " fresh            - return the address of a free register\n"
  ++ "\n"
  ++ "QRAM commands:\n"
  ++ " Q x              - initialize qubit x to |0>\n"
  ++ " Q x b            - initialize qubit x to |b>\n"
  ++ " B x              - initialize bit x to 0\n"
  ++ " B x b            - initialize bit x to b\n"
  ++ " N x              - initialize qubit x from bit x\n"
  ++ " M x              - measure qubit x into bit x\n"
  ++ " D x              - discard bit or qubit x\n"
  ++ " R x              - read and discard bit or qubit x\n"
  ++ "\n"  
  ++ " X x [ctrls]      - apply X-gate to bit or qubit x\n"
  ++ " Y x [ctrls]      - apply Y-gate to qubit x\n"
  ++ " Z x [ctrls]      - apply Z-gate to qubit x\n"
  ++ " H x [ctrls]      - apply H-gate to qubit x\n"
  ++ " S x [ctrls]      - apply S-gate to qubit x\n"
  ++ " T x [ctrls]      - apply T-gate to qubit x\n"
  ++ " CNOT x y [ctrls] - apply CNOT-gate to qubits x and y (x is the target)\n"
  ++ " CZ x y [ctrls]   - apply CZ-gate to qubits x and y\n"
  ++ "\n"  
  ++ " [ctrls] is an optional space-separated list of signed classical control bits\n"



-- | Interpret a command. Return a new state if any (or 'Nothing' on
-- QUIT), and a response if any.

  
interpret_command :: Command -> State -> IO (Maybe State, Response)
interpret_command Empty st = 
  return (Just st, Null)
interpret_command (Q b x) st =
  case run (qinit x b) st of
   (st', ()) -> return (Just st', OK)
interpret_command (B b x) st =
  case run (binit x b) st of
   (st', ()) -> return (Just st', OK)
interpret_command (N x) st = 
  case run (qnew x) st of
   (st', ()) -> return (Just st', OK)
interpret_command (X x xs) st =
  case run (apply_X x xs) st of
    (st', ()) -> return (Just st', OK)
interpret_command (Y x xs) st =
  case run (unary_gate gateY x xs) st of
    (st', ()) -> return (Just st', OK)
interpret_command (Z x xs) st =
  case run (unary_gate gateZ x xs) st of
    (st', ()) -> return (Just st', OK)
interpret_command (H x xs) st =
  case run (unary_gate gateH x xs) st of
    (st', ()) -> return (Just st', OK)
interpret_command (S x xs) st =
  case run (unary_gate gateS x xs) st of
    (st', ()) -> return (Just st', OK)
interpret_command (T x xs) st =
  case run (unary_gate gateT x xs) st of
    (st', ()) -> return (Just st', OK)

interpret_command (Rot r x xs) st =
  case run (unary_gate (gateRot r) x xs) st of
    (st', ()) -> return (Just st', OK)
interpret_command (Diag a b x xs) st =
  case run (unary_gate (gateDiag a b) x xs) st of
    (st', ()) -> return (Just st', OK)

interpret_command (TInv x xs) st =
  case run (unary_gate gateTInv x xs) st of
    (st', ()) -> return (Just st', OK)
interpret_command (SInv x xs) st =
  case run (unary_gate gateSInv x xs) st of
    (st', ()) -> return (Just st', OK)        
interpret_command (CNOT x y xs) st = 
  case run (binary_gate gateCNOT x y xs) st of
    (st', ()) -> return (Just st', OK)
interpret_command (TOF x y z xs) st = 
  case run (ternary_gate gateTOF x y z xs) st of
    (st', ()) -> return (Just st', OK)    
interpret_command (CZ x y xs) st = 
  case run (binary_gate gateCZ x y xs) st of
    (st', ()) -> return (Just st', OK)
interpret_command (CY x y xs) st = 
  case run (binary_gate gateCY x y xs) st of
    (st', ()) -> return (Just st', OK)    
interpret_command (M x) st = do
  g <- newStdGen
  case run (measure x g) st of
    (st', ()) -> return (Just st', OK)
interpret_command (D x) st = do
  g <- newStdGen
  case run (qbread x g) st of
    (st', b) -> return (Just st', OK)

interpret_command (R x) st = do
  g <- newStdGen
  let (st', b) = run (qbread x g) st
  let response = if b then "1" else "0"
  return (Just st', Reply response)

interpret_command (Help) st = 
  return (Just st, Reply usage)
interpret_command (Quit) st = 
  return (Nothing, Terminate)
interpret_command (Reset) st =
  return (Just initial_state, OK)
interpret_command (Fresh) st = do
  let (st', x) = run alloc st
  return (Just st', Reply (show x))
interpret_command Dump st = 
  return (Just st, Reply (show st))

-- | Interpreter.
interpreter :: Handle -> Handle -> (String -> IO ()) -> State -> IO State
interpreter hin hout log st =
  body `catches` [Handler handle_usage_exception,
                  Handler handle_parse_error,
                  Handler handle_internal_exception,
                  Handler handle_eof_exception]
  where
    body = do
        line <- hGetLine hin
        log line
        let cmd = parse_command line
        res <- interpret_command cmd st
        case res of
          (Just st, r) | Reply _ <- r ->
               st `strict` ((output $ show r) >> interpreter hin hout log st)
          (Just st, r) | OK <- r ->
               st `strict` (interpreter hin hout log st)
          (Just st, r) | Null <- r ->
               st `strict` (interpreter hin hout log st)
          (Nothing, Terminate) -> return st
          (Nothing, r) ->
            do output $ show r
               return st

    handle_parse_error :: ParseError -> IO State
    handle_parse_error e = do
      output $ show $ Error ("! " ++ show e ++ ". Try help.")
      interpreter hin hout log st

    handle_usage_exception :: UsageException -> IO State
    handle_usage_exception e = do
      output $ show $ Error ("! " ++ show e)
      interpreter hin hout log st

    handle_internal_exception :: InternalException -> IO State
    handle_internal_exception e = do
      output $ show $ InternalError ("! " ++ show e)
      exitFailure

    handle_eof_exception :: IOError -> IO State
    handle_eof_exception e
      | isEOFError e =
        do output $ show $ InternalError ("! " ++ show e)
           return st
      | otherwise =
        do output $ show $ InternalError ("! " ++ show e)          
           throw e

    output :: String -> IO ()
    output s = do
      hPutStrLn hout s
      log s

data Options = Universal | Stabilizer deriving (Show, Eq, Read)

server :: Handle -> Handle -> (String -> IO ()) -> IO ()
server hin hout log = do
  hPutStrLn hout "# quantum server, version 0.1."
  msg <- hGetLine hin
  case read msg of
    Universal -> do
      interpreter hin hout log initial_state
      return ()
    Stabilizer -> do
      runStabilizer hin hout log (initStabilizerState, ([], []))
      return ()

runStabilizer :: Handle -> Handle -> (String -> IO ()) -> StabilizerState -> IO StabilizerState
runStabilizer hin hout log st =
  body `catches` [Handler handle_usage_exception,
                  Handler handle_parse_error,
                  Handler handle_internal_exception,
                  Handler handle_eof_exception]
  where
    body = do
        line <- hGetLine hin
        log line
        let cmd = parse_command line
        res <- interpretStabilizer cmd st
        case res of
          (Just st, r) | Reply _ <- r ->
            (output $ show r) >> runStabilizer hin hout log st
          (Just st, r) | OK <- r ->
            runStabilizer hin hout log st
          (Just st, r) | Null <- r ->
            runStabilizer hin hout log st
          (Nothing, Terminate) -> return st
          (Nothing, r) ->
            do output $ show r
               return st

    handle_parse_error :: ParseError -> IO StabilizerState
    handle_parse_error e = do
      output $ show $ Error ("! " ++ show e ++ ". Try help.")
      runStabilizer hin hout log st

    handle_usage_exception :: UsageException -> IO StabilizerState
    handle_usage_exception e = do
      output $ show $ Error ("! " ++ show e)
      runStabilizer hin hout log st

    handle_internal_exception :: InternalException -> IO StabilizerState
    handle_internal_exception e = do
      output $ show $ InternalError ("! " ++ show e)
      exitFailure

    handle_eof_exception :: IOError -> IO StabilizerState
    handle_eof_exception e
      | isEOFError e =
        do output $ show $ InternalError ("! " ++ show e)
           return st
      | otherwise =
        do output $ show $ InternalError ("! " ++ show e)          
           throw e

    output :: String -> IO ()
    output s = do
      hPutStrLn hout s
      log s

type StabilizerState = (Stable.StabilizerState, ([Int], [Bool]))

interpretStabilizer :: Command -> StabilizerState ->
                       IO (Maybe StabilizerState, Response)
-- interpretStabilizer s st | trace ("interpreting:"++ show s ++ "state:" ++ show (disp (fst st)) ++ "\n" ++ show (snd st)) $ False = undefined
interpretStabilizer Empty st = return (Just st, Null)
        
interpretStabilizer (Q b x) st =
  if b then
    let s' = initialize' x (fst st)
        st' = (s', snd st)
    in return (Just st', OK)
  else
    let s' = initialize x (fst st)
        st' = (s', snd st)
    in return (Just st', OK)

interpretStabilizer (X b []) st =
  let s' = applyUnary b (Stable.P (Stable.Plus, Stable.X)) (fst st)
      st' = (s', snd st)
  in return (Just st', OK)

interpretStabilizer (Y b []) st =
  let s' = applyUnary b (Stable.P (Stable.Plus, Stable.Y)) (fst st)
      st' = (s', snd st)
  in return (Just st', OK)

interpretStabilizer (Z b []) st =
  let s' = applyUnary b (Stable.P (Stable.Plus, Stable.Z)) (fst st)
      st' = (s', snd st)
  in return (Just st', OK)

interpretStabilizer (H b []) st =
  let s' = applyUnary b Stable.H (fst st)
      st' = (s', snd st)
  in return (Just st', OK)

interpretStabilizer (S b []) st =
  let s' = applyUnary b Stable.S (fst st)
      st' = (s', snd st)
  in return (Just st', OK)

interpretStabilizer (CNOT x y []) st =
  let s' = applyBinary y x (fst st)
      st' = (s', snd st)
  in return (Just st', OK)

interpretStabilizer (M x) st = do
  g <- newStdGen
  let s' = measurement g x (fst st)
      st' = (s', snd st)
  return (Just st', OK)

interpretStabilizer (R x) st = 
  let (ps, bs) = snd st
  in if null ps then do
       let (ps', bs') = getBits (fst st)
           Just p = elemIndex x ps'
           response = if bs' !! p then "1" else "0"
       return (Just (fst st, (ps', bs')), Reply response)
     else do
       let Just p = elemIndex x ps
           response = if bs !! p then "1" else "0"
       return (Just (fst st, (ps, bs)), Reply response)

interpretStabilizer (Reset) st =
  return (Just (initStabilizerState, ([], [])), OK)

interpretStabilizer (Quit) st = return (Nothing, Terminate)

interpretStabilizer c st = error $ "unsupport comand when running the stabilizer formalism:" ++ show c
