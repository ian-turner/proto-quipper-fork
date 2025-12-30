module CircToQASM (saveCircAsQasm) where

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

-- String join utility function
stringJoin :: String -> [String] -> String
stringJoin _ []     = ""
stringJoin _ [x]    = x
stringJoin s (x:xs) = x ++ s ++ stringJoin s xs

-- | An unsafe version of 'Map.lookup'. This should only be used for
-- keys that are guaranteed to be in the map. It is an error to call
-- this function otherwise.
mapLookup :: (Ord a, Disp a) => Map a b -> a -> b
mapLookup ds x = case Map.lookup x ds of
                      Nothing -> error $ "can't find " ++ show (disp x)
                      Just v -> v

-- Converts Quipper gate Ids to OpenQASM gate names
toQasmGate "H"          = "h"
toQasmGate "SGate"      = "s"
toQasmGate "SGate_Inv"  = "sdg"
toQasmGate "TGate"      = "t"
toQasmGate "TGate_Inv"  = "tdg"
toQasmGate "QNot"       = "x"
toQasmGate "ZGate"      = "z"
toQasmGate "YGate"      = "y"
toQasmGate "Rot"        = "rz"
toQasmGate "Toffoli"    = "ccx"
toQasmGate "CNot"       = "cx"
toQasmGate "CZ"         = "cz"
toQasmGate "CY"         = "cy"
toQasmGate "C_Z"        = "z"
toQasmGate "C_Y"        = "y"
toQasmGate "C_X"        = "x"


-- OpenQASM syntax tree
data QasmStmt = QasmVersion String
                | QasmImport String
                | QubitDecl String Int
                | BitDecl String Int
                | QubitVar String Int
                | BitVar String Int
                | GateApp String [String] [QasmStmt]
                | CtrlMod QasmStmt QasmStmt
                | QasmMeas QasmStmt QasmStmt
                | QasmIf QasmStmt [QasmStmt]
                deriving (Show, Eq)


qasmStmtToString (QasmVersion x) = "OPENQASM " ++ x ++ ";"
qasmStmtToString (QasmImport x) = "include \"" ++ x ++ "\";"
qasmStmtToString (QubitDecl name size) = "qubit[" ++ (show size) ++ "] " ++ name ++ ";"
qasmStmtToString (BitDecl name size) = "bit[" ++ (show size) ++ "] " ++ name ++ ";"
qasmStmtToString (QubitVar name idx) = name ++ "[" ++ (show idx) ++ "]"
qasmStmtToString (BitVar name idx) = name ++ "[" ++ (show idx) ++ "]"
qasmStmtToString (GateApp name params inps) =
    let inpString = stringJoin "," $ map qasmStmtToString inps
        paramString = case params of
            [] -> ""
            params -> "(" ++ (stringJoin ", " params) ++ ")"
    in name ++ paramString ++ " " ++ inpString ++ ";"
qasmStmtToString (QasmMeas left right) =
    let leftStr = qasmStmtToString left
        rightStr = qasmStmtToString right
    in leftStr ++ " = measure " ++ rightStr ++ ";"
qasmStmtToString (QasmIf cond stmts) =
    let condString = "if (" ++ (qasmStmtToString cond) ++ ") {"
        stmtStrings = map qasmStmtToString stmts
        trueBlock = stringJoin "\n" $ map (\x -> "\t" ++ x) stmtStrings
    in stringJoin "\n" $ condString : trueBlock : "}" : []


-- State monad for QASM conversion
data QasmState l = QasmState
  { qsNumBits    :: Int
  , qsNumQubits  :: Int
  , qsFreeBits   :: [Int]
  , qsFreeQubits :: [Int]
  , qsBits       :: Map l Int
  , qsQubits     :: Map l Int
  , qsLines      :: [QasmStmt]   -- accumulated QASM statements, stored in reverse
  }

type QasmM l = State (QasmState l)

emit :: QasmStmt -> QasmM l ()
emit line = modify $ \s -> s { qsLines = line : qsLines s }

addFreeBit :: Int -> QasmM l ()
addFreeBit b = modify $ \s -> s { qsFreeBits = b : qsFreeBits s }

addFreeQubit :: Int -> QasmM l ()
addFreeQubit q = modify $ \s -> s { qsFreeQubits = q : qsFreeQubits s }

allocBit :: QasmM l Int
allocBit = do
    s <- get
    case qsFreeBits s of
        (b:bs) -> do
            put s { qsFreeBits = bs }
            return b
        [] -> do
            let b = qsNumBits s
            put s { qsNumBits = b + 1 }
            return b

allocQubit :: QasmM l Int
allocQubit = do
    s <- get
    case qsFreeQubits s of
        (q:qs) -> do
            put s { qsFreeQubits = qs }
            return q
        [] -> do
            let q = qsNumQubits s
            put s { qsNumQubits = q + 1 }
            return q

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


-- | Process a single gate, updating the QasmState and possibly emitting a QASM line
gateToQasm g =
  case g of
    -- Init gates
    (Gate (Id gateName) _ _ (VLabel l) VStar _ _ _ _)
      | gateName == "Init0" -> do
          q <- allocQubit
          setQubitLabel l q
          emit $ GateApp "reset" [] [QubitVar "qubits" q]

    (Gate (Id gateName) _ _ (VLabel l) VStar _ _ _ _)
      | gateName == "Init1" -> do
          q <- allocQubit
          setQubitLabel l q
          emit $ GateApp "reset" [] [QubitVar "qubits" q]
          emit $ GateApp "x" [] [QubitVar "qubits" q]

    -- Measurement gate
    (Gate (Id gateName) _ (VLabel li) (VLabel lo) VStar _ _ _ _)
      | gateName == "Meas" -> do
          b <- allocBit
          qubit <- lookupQubit li
          setBitLabel lo b
          addFreeQubit qubit
          emit $ QasmMeas (BitVar "bits" b) (QubitVar "qubits" qubit)

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
          emit $ GateApp (toQasmGate gateName) [] [QubitVar "qubits" qubit]

    -- Single qubit rotation gates
    (Gate (Id gateName) [VWrapR (MR len r)] (VLabel li) (VLabel lo) VStar _ _ _ _)
      | gateName == "Rot" -> do
          qubit <- lookupQubit li
          setQubitLabel lo qubit
          emit $ GateApp "rz" [showCReal len r] [(QubitVar "qubits" qubit)]

    -- Classically controlled X, Y, Z gates
    (Gate (Id gateName) [] (VPair (VLabel l1i) (VLabel l2i))
                           (VPair (VLabel l1o) (VLabel l2o)) VStar _ _ _ _)
      | gateName == "C_X" || gateName == "C_Y" || gateName == "C_Z" -> do
          qubit <- lookupQubit l1i
          bit   <- lookupBit l2i
          setQubitLabel l1o qubit
          setBitLabel   l2o bit
          let qasmGateName = toQasmGate gateName
          emit $ QasmIf (BitVar "bits" bit) [GateApp qasmGateName [] [(QubitVar "qubits" qubit)]]

    -- CNot gates
    (Gate (Id gateName) [] (VPair (VLabel l1i) (VLabel l2i))
                           (VPair (VLabel l1o) (VLabel l2o)) VStar _ _ _ _) -> do
          q1 <- lookupQubit l1i
          q2 <- lookupQubit l2i
          setQubitLabel l1o q1
          setQubitLabel l2o q2
          -- Keeping the original control/target ordering:
          emit $ GateApp (toQasmGate gateName) [] [(QubitVar "qubits" q2), (QubitVar "qubits" q1)]

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
              emit $ GateApp "cp" [show (pi / (2^n))] [(QubitVar "qubits" q2), (QubitVar "qubits" q2)]

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
          emit $ GateApp "ccx" [] [(QubitVar "qubits" qa), (QubitVar "qubits" qb), (QubitVar "qubits" qc)]

    -- Any gate we don’t handle explicitly: do nothing
    _ -> return ()


-- Converts `Wired` circuit objects to QASM circuit
circToQasm circ =
    open circ $ \ _ morph ->
        -- Getting gates from circuit
        let gs = gates morph

            -- Setting up initial state for monadic computation
            initialState = QasmState
              { qsNumBits    = 0
              , qsNumQubits  = 0
              , qsFreeBits   = []
              , qsFreeQubits = []
              , qsBits       = Map.empty
              , qsQubits     = Map.empty
              , qsLines      = []
              }

            -- Running OpenQASM conversion
            finalState = execState (mapM_ gateToQasm gs) initialState
            qasmLines = reverse $ qsLines finalState

            -- Header
            qasmVersion = QasmVersion "3.0"
            importGates = QasmImport "stdgates.inc"

            -- Register initialization code
            nbits = qsNumBits finalState
            nqubits = qsNumQubits finalState
            bitInit = BitDecl "bits" nbits
            qubitInit = QubitDecl "qubits" nqubits
            
            -- Full program
            qasmProgram = qasmVersion : importGates : qubitInit : bitInit : qasmLines

        -- All lines of QASM together with newline characters in between
        in stringJoin "\n" $ map qasmStmtToString qasmProgram


-- Runs the OpenQASM converter and stores result to text file
saveCircAsQasm circ s =
    do  h <- openFile s WriteMode
        hPutStr h (circToQasm circ)
        hClose h
