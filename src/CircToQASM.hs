module CircToQASM where

import Syntax
import Utils
import SyntacticOperations
import Nominal
import Simulation

import System.IO
import Text.PrettyPrint
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List as List


-- | A wire in a circuit is the same thing as a label in
-- Proto-Quipper.
type Wire = Label


-- | Compute the set of all gates in a circuit (but do not necessarily
-- delete duplicates).
wirelist :: [Gate] -> [Wire]
wirelist [] = []
wirelist (Gate _ _ input output ctrl _ _ _ _: gs) =
    (getWires input) ++ (getWires output) ++ (getWires ctrl) ++ (wirelist gs)


-- Converts Quipper gate Ids to OpenQASM gate names
to_qasm_gate :: String -> String
to_qasm_gate "H" = "h"
to_qasm_gate "SGate" = "s"
to_qasm_gate "SGate_Inv" = "sdg"
to_qasm_gate "TGate" = "t"
to_qasm_gate "TGate_Inv" = "tdg"
to_qasm_gate "QNot" = "x"
to_qasm_gate "ZGate" = "z"
to_qasm_gate "YGate" = "y"
to_qasm_gate "Rot" = "rz"
to_qasm_gate "Toffoli" = "ccx"
to_qasm_gate "CNot" = "cx"
to_qasm_gate "CZ" = "cz"
to_qasm_gate "CY" = "cy"

qasm_header = "OPENQASM 3.0;\ninclude \"stdgates.inc\";"


-- Query map object for qubit label
label_to_qubit m l =
    case Map.lookup l m of
        Nothing -> error "QASM converter error"
        Just y -> "qubits[" ++ (show y) ++ "]"
        

-- Converts gate to QASM format

-- Init gates
gate_to_qasm (Gate (Id gateName) _ (VStar) (VLabel l) _ _ _ _ _)
    | gateName == "Init0" =
        "qubit " ++ (show l) ++ ";\nreset " ++ (show l) ++ ";"

gate_to_qasm (Gate (Id gateName) _ (VStar) (VLabel l) _ _ _ _ _)
    | gateName == "Init1" =
        "qubit " ++ (show l) ++ ";\nreset " ++ (show l) ++ ";\nx " ++ (show l) ++ ";"

-- Measurement and discard gates
gate_to_qasm (Gate (Id gateName) _ (VLabel l) output _ _ _ _ _)
    | (gateName == "Meas" || gateName == "Discard") =
        "bit b_" ++ (show l) ++ ";\nb_" ++ (show l) ++ " = measure " ++ (show l) ++ ";"
    
-- Single qubit gates - no params
gate_to_qasm (Gate (Id gateName) [] (VLabel l) output ctrl _ _ _ _) =
    (to_qasm_gate gateName) ++ " " ++ (show l) ++ ";"
    
-- Single qubit gates - with params
gate_to_qasm (Gate (Id gateName) params (VLabel l) output ctrl _ _ _ _) =
    (to_qasm_gate gateName) ++ "(" ++ (show params) ++ ") " ++ (show l) ++ ";"

-- Two qubit gates - no params
gate_to_qasm (Gate (Id gateName) [] (VPair (VLabel l1) (VLabel l2)) output ctrl _ _ _ _) =
    (to_qasm_gate gateName) ++ " " ++ (show l2) ++ ", "
        ++ (show l1) ++ ";"

-- Two qubit gates - with params
gate_to_qasm (Gate (Id gateName) [a] (VPair (VLabel l1) (VLabel l2)) output ctrl _ _ _ _)
    | gateName == "R" =
        -- Parsing input param as int
        case (toInt a) of
            Nothing -> error "Error parsing R gate during QASM conversion"
            Just n ->
                "ctrl @ rz(" ++ (show n) ++ ") " ++ (show l2) ++ ", "
                        ++ (show l1) ++ ";"


string_join :: String -> [String] -> String
string_join s [] = ""
string_join s (x:[]) = x
string_join s (x:xs) = x ++ s ++ (string_join s xs)


-- Converts `Wired` circuit objects to QASM circuit
circ_to_qasm circ =
    open circ $ \ _ morph ->
        let q1 = input morph
            -- Parsing circuit object to extract gates
            ocirc = gates morph
            (gs, _) = refresh_gates Map.empty ocirc []
            ws = getWires q1 `List.union` wirelist gs

            -- Mapping over gates to convert each to qasm
            gates_qasm = map gate_to_qasm gs

        -- Joining all gate strings together with header
        in (string_join "\n" (qasm_header : gates_qasm))


-- Runs the OpenQASM converter and stores result to text file
save_circ_as_qasm (Wired circ) s =
    do
        h <- openFile s WriteMode
        hPutStr h (circ_to_qasm circ)
        hClose h