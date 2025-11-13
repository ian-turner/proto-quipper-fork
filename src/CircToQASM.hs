module CircToQASM where

import Syntax
import Utils
import SyntacticOperations
import Nominal
import Simulation

import Data.Number.CReal
import System.IO
import Text.PrettyPrint
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List as List
import Text.Printf
import Control.Monad.State.Strict (State, execState, get, put, modify)


-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | An unsafe version of 'Map.lookup'. This should only be used for
-- keys that are guaranteed to be in the map. It is an error to call
-- this function otherwise.
mapLookup :: (Ord a, Disp a) => Map a b -> a -> b
mapLookup ds x = case Map.lookup x ds of
                      Nothing -> error $ "can't find " ++ show (disp x)
                      Just v -> v


-- Converts Quipper gate Ids to OpenQASM gate names
to_qasm_gate "H"          = "h"
to_qasm_gate "SGate"      = "s"
to_qasm_gate "SGate_Inv"  = "sdg"
to_qasm_gate "TGate"      = "t"
to_qasm_gate "TGate_Inv"  = "tdg"
to_qasm_gate "QNot"       = "x"
to_qasm_gate "ZGate"      = "z"
to_qasm_gate "YGate"      = "y"
to_qasm_gate "Rot"        = "rz"
to_qasm_gate "Toffoli"    = "ccx"
to_qasm_gate "CNot"       = "cx"
to_qasm_gate "CZ"         = "cz"
to_qasm_gate "CY"         = "cy"
to_qasm_gate "C_Z"        = "z"
to_qasm_gate "C_Y"        = "y"
to_qasm_gate "C_X"        = "x"

qasm_header :: String
qasm_header = "OPENQASM 3.0; \n\
              \include \"stdgates.inc\";"


-- ----------------------------------------------------------------------
-- * Resource counting

-- Determines number of qubit and bit registers needed for circuit
get_resource_count_rec [] curr_bits curr_qubits max_bits max_qubits =
    (max_bits, max_qubits)
get_resource_count_rec (g:gs) curr_bits curr_qubits max_bits max_qubits =
    case g of
        (Gate (Id gateName) _ _ _ VStar _ _ _ _) | gateName == "Init0" || gateName == "Init1" ->
            get_resource_count_rec gs curr_bits (curr_qubits + 1) max_bits (max max_qubits (curr_qubits + 1))

        (Gate (Id gateName) _ _ _ VStar _ _ _ _) | gateName == "Meas" ->
            get_resource_count_rec gs (curr_bits + 1) (curr_qubits - 1) (max max_bits (curr_bits + 1)) max_qubits

        (Gate (Id gateName) _ _ _ VStar _ _ _ _) | gateName == "Term0" ->
            get_resource_count_rec gs curr_bits (curr_qubits - 1) max_bits max_qubits

        (Gate (Id gateName) _ _ _ VStar _ _ _ _) | gateName == "Discard" ->
            get_resource_count_rec gs (curr_bits - 1) curr_qubits max_bits max_qubits

        _ -> get_resource_count_rec gs curr_bits curr_qubits max_bits max_qubits

get_resource_count gs = get_resource_count_rec gs 0 0 0 0


-- ----------------------------------------------------------------------
-- * State monad for QASM conversion

-- | Internal state threaded through the QASM conversion.
--   'l' is the type of the Proto-Quipper labels (the thing inside VLabel).
data QasmState l = QasmState
  { qsFreeBits   :: [Int]
  , qsFreeQubits :: [Int]
  , qsBits       :: Map l Int
  , qsQubits     :: Map l Int
  , qsLines      :: [String]   -- accumulated QASM lines, stored in reverse
  }

type QasmM l = State (QasmState l)

emit :: String -> QasmM l ()
emit line = modify $ \s -> s { qsLines = line : qsLines s }

takeFreeBit :: QasmM l Int
takeFreeBit = do
  s <- get
  case qsFreeBits s of
    []     -> error "No free classical bits left in QASM converter"
    (b:bs) -> do
      put s { qsFreeBits = bs }
      return b

takeFreeQubit :: QasmM l Int
takeFreeQubit = do
  s <- get
  case qsFreeQubits s of
    []     -> error "No free qubits left in QASM converter"
    (q:qs) -> do
      put s { qsFreeQubits = qs }
      return q

addFreeBit :: Int -> QasmM l ()
addFreeBit b = modify $ \s -> s { qsFreeBits = b : qsFreeBits s }

addFreeQubit :: Int -> QasmM l ()
addFreeQubit q = modify $ \s -> s { qsFreeQubits = q : qsFreeQubits s }

lookupBit :: (Ord l, Disp l) => l -> QasmM l Int
lookupBit l = do
  s <- get
  return $ mapLookup (qsBits s) l

lookupQubit :: (Ord l, Disp l) => l -> QasmM l Int
lookupQubit l = do
  s <- get
  return $ mapLookup (qsQubits s) l

setBitLabel :: Ord l => l -> Int -> QasmM l ()
setBitLabel l b = modify $ \s ->
  s { qsBits = Map.insert l b (qsBits s) }

setQubitLabel :: Ord l => l -> Int -> QasmM l ()
setQubitLabel l q = modify $ \s ->
  s { qsQubits = Map.insert l q (qsQubits s) }


-- ----------------------------------------------------------------------
-- * Gate -> QASM (monadic)

-- | Process a single gate, updating the QasmState and possibly emitting QASM.
gateToQasm g =
  case g of
    -- Init gates
    (Gate (Id gateName) _ _ (VLabel l) VStar _ _ _ _)
      | gateName == "Init0" -> do
          fq <- takeFreeQubit
          setQubitLabel l fq
          emit ("reset qubits[" ++ show fq ++ "];")

    (Gate (Id gateName) _ _ (VLabel l) VStar _ _ _ _)
      | gateName == "Init1" -> do
          fq <- takeFreeQubit
          setQubitLabel l fq
          emit ("reset qubits[" ++ show fq ++ "];\n"
                ++ "x qubits[" ++ show fq ++ "];")

    -- Measurement gate
    (Gate (Id gateName) _ (VLabel li) (VLabel lo) VStar _ _ _ _)
      | gateName == "Meas" -> do
          fb    <- takeFreeBit
          qubit <- lookupQubit li
          setBitLabel lo fb
          addFreeQubit qubit
          emit ("bits[" ++ show fb ++ "] = measure qubits[" ++ show qubit ++ "];")

    -- Term gates
    (Gate (Id gateName) _ (VLabel li) VStar VStar _ _ _ _)
      | gateName == "Term0" -> do
          qubit <- lookupQubit li
          addFreeQubit qubit

    -- Discard gate
    (Gate (Id gateName) _ (VLabel l) _ VStar _ _ _ _)
      | gateName == "Discard" -> do
          bit <- lookupBit l
          addFreeBit bit

    -- Single qubit gate - no params
    (Gate (Id gateName) [] (VLabel li) (VLabel lo) VStar _ _ _ _) -> do
          qubit <- lookupQubit li
          setQubitLabel lo qubit
          emit (to_qasm_gate gateName ++ " qubits[" ++ show qubit ++ "];")

    -- Single qubit rotation gates
    (Gate (Id gateName) [VWrapR (MR len r)] (VLabel li) (VLabel lo) VStar _ _ _ _)
      | gateName == "Rot" -> do
          qubit <- lookupQubit li
          setQubitLabel lo qubit
          emit ("rz(" ++ showCReal len r ++ ") qubits[" ++ show qubit ++ "];")

    -- Classically controlled X, Y, Z gates
    (Gate (Id gateName) [] (VPair (VLabel l1i) (VLabel l2i))
                           (VPair (VLabel l1o) (VLabel l2o)) VStar _ _ _ _)
      | gateName == "C_X" || gateName == "C_Y" || gateName == "C_Z" -> do
          qubit <- lookupQubit l1i
          bit   <- lookupBit l2i
          setQubitLabel l1o qubit
          setBitLabel   l2o bit
          emit ("if (bits[" ++ show bit ++ "]) "
                ++ to_qasm_gate gateName
                ++ " qubits[" ++ show qubit ++ "];")

    -- CNot gates
    (Gate (Id gateName) [] (VPair (VLabel l1i) (VLabel l2i))
                           (VPair (VLabel l1o) (VLabel l2o)) VStar _ _ _ _)
      | gateName == "CNot" -> do
          q1 <- lookupQubit l1i
          q2 <- lookupQubit l2i
          setQubitLabel l1o q1
          setQubitLabel l2o q2
          -- Keeping the original control/target ordering:
          emit ("cx qubits[" ++ show q2 ++ "], qubits[" ++ show q1 ++ "];")

    -- Controlled rotation gate
    (Gate (Id gateName) [a]
          (VPair (VLabel l1i) (VLabel l2i))
          (VPair (VLabel l1o) (VLabel l2o)) VStar _ _ _ _)
      | gateName == "R" ->
          case toInt a of
            Nothing -> error "Error parsing R gate in qasm converter"
            Just n  -> do
              q1 <- lookupQubit l1i
              q2 <- lookupQubit l2i
              setQubitLabel l1o q1
              setQubitLabel l2o q2
              emit ("ctrl @ rz(" ++ show (pi / (2^n)) ++ ") qubits["
                    ++ show q2 ++ "], qubits[" ++ show q1 ++ "];")

    -- Diagonal gates
    (Gate (Id gateName)
          [VWrapR (MR len  r), VWrapR (MR len' r')]
          (VLabel li) (VLabel lo) VStar _ _ _ _)
      | gateName == "Diag" ->
          error "Diagonal gates not currently supported for QASM conversion"

    -- Toffoli gate
    (Gate (Id gateName) []
          (VPair (VPair (VLabel la_in) (VLabel lb_in)) (VLabel lc_in))
          (VPair (VPair (VLabel la_out) (VLabel lb_out)) (VLabel lc_out))
          VStar _ _ _ _)
      | gateName == "Toffoli" -> do
          qa <- lookupQubit la_in
          qb <- lookupQubit lb_in
          qc <- lookupQubit lc_in
          -- Note: this maps the outputs la_out, lb_out, lc_out to qa, qb, qc.
          setQubitLabel la_out qa
          setQubitLabel lb_out qb
          setQubitLabel lc_out qc
          emit ("ccx qubits[" ++ show qc ++ "], qubits[" ++ show qb
                ++ "], qubits[" ++ show qa ++ "];")

    -- Any gate we don’t handle explicitly: do nothing
    _ -> return ()


-- | Monadic version of 'gates_to_qasm' using 'State' to carry maps and free lists.
gates_to_qasm gs free_bits free_qubits bits qubits =
    let initialState = QasmState
          { qsFreeBits   = free_bits
          , qsFreeQubits = free_qubits
          , qsBits       = bits
          , qsQubits     = qubits
          , qsLines      = []
          }

        finalState = execState (mapM_ gateToQasm gs) initialState
    in ( reverse (qsLines finalState)
       , qsBits   finalState
       , qsQubits finalState
       )


-- ----------------------------------------------------------------------
-- * Utilities

string_join :: String -> [String] -> String
string_join _ []     = ""
string_join _ [x]    = x
string_join s (x:xs) = x ++ s ++ string_join s xs


-- ----------------------------------------------------------------------
-- * Circuit -> QASM

-- Converts `Wired` circuit objects to QASM circuit
circ_to_qasm circ =
    open circ $ \ _ morph ->
        -- Getting gates from circuit
        let gs = gates morph
            -- Calculating how many bit and qubit register to use
            (nbits, nqubits) = get_resource_count gs

            reg_init =
                case (nbits, nqubits) of
                    (0, nq) ->
                        "qreg qubits[" ++ show nqubits ++ "];"
                    (nb, nq) ->
                        "qreg qubits[" ++ show nq ++ "]; \n\
                        \creg bits[" ++ show nb ++ "];"

            -- Converting gates to qasm
            free_bits   = [0..(nbits-1)]
            free_qubits = [0..(nqubits-1)]
            (gates_qasm, _, _) =
              gates_to_qasm gs free_bits free_qubits Map.empty Map.empty

        in string_join "\n" (qasm_header : reg_init : gates_qasm)


-- Runs the OpenQASM converter and stores result to text file
save_circ_as_qasm (Wired circ) s =
    do  h <- openFile s WriteMode
        hPutStr h (circ_to_qasm circ)
        hClose h
