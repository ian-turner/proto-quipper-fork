module CircToQASM where

import Syntax
import Utils
import SyntacticOperations
import Nominal

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
to_qasm_gate "S" = "s"
to_qasm_gate "S*" = "sdg"
to_qasm_gate "T" = "t"
to_qasm_gate "T*" = "tdg"
to_qasm_gate "CNot" = "cx"
to_qasm_gate "Rot" = "rz"

qasm_header = "OPENQASM 3.0;\ninclude \"qelib1.inc\";"


-- Query map object for qubit label
label_to_qubit m l =
    case Map.lookup l m of
        Nothing -> error "QASM converter error"
        Just y -> "qubits[" ++ (show y) ++ "]"
        

-- Converts gate to QASM format

-- Init gates
gate_to_qasm qubit_map (Gate (Id gateName) _ (VStar) (VLabel l) _ _ _ _ _)
    | gateName == "Init0" =
        "qubit " ++ (show l) ++ ";\nreset " ++ (show l) ++ ";"

gate_to_qasm qubit_map (Gate (Id gateName) _ (VStar) (VLabel l) _ _ _ _ _)
    | gateName == "Init1" =
        "qubit " ++ (show l) ++ ";\nreset " ++ (show l) ++ ";\nx " ++ (show l) ++ ";"

-- Single qubit gates
gate_to_qasm qubit_map (Gate (Id gateName) _ (VLabel l) output ctrl _ _ _ _)
    | (gateName == "Meas" || gateName == "Discard") =
        "bit b_" ++ (show l) ++ ";\nb_" ++ (show l) ++ " = measure " ++ (show l) ++ ";"
    
gate_to_qasm qubit_map (Gate (Id gateName) _ (VLabel l) output ctrl _ _ _ _) =
    (to_qasm_gate gateName) ++ " " ++ (label_to_qubit qubit_map l) ++ ";"

-- Two qubit gates
gate_to_qasm qubit_map (Gate (Id gateName) _ (VPair (VLabel l1) (VLabel l2)) output ctrl _ _ _ _) =
    (to_qasm_gate gateName) ++ " " ++ (label_to_qubit qubit_map l2) ++ ", "
        ++ (label_to_qubit qubit_map l1) ++ ";"


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
            num_qubits = fromIntegral $ List.length ws
            qubit_map = Map.fromList $ zip ws [0..(num_qubits-1)]

            -- Mapping over gates to convert each to qasm
            gates_qasm = map (gate_to_qasm qubit_map) gs
            qreg_init = "qreg qubits[" ++ (show num_qubits) ++ "];"

        -- Joining all gate strings together with header
        in (string_join "\n" (qasm_header : qreg_init : gates_qasm))


-- Runs the OpenQASM converter and stores result to text file
save_circ_as_qasm (Wired circ) s =
    do
        h <- openFile s WriteMode
        hPutStr h (circ_to_qasm circ)
        hClose h