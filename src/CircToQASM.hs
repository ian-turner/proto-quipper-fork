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


-- ----------------------------------------------------------------------
-- * Auxiliary functions

-- | An unsafe version of 'Map.lookup'. This should only be used for
-- keys that are guaranteed to be in the map. It is an error to call
-- this function otherwise.

mapLookup :: (Ord a, Disp a) => Map a b -> a -> b
mapLookup ds x = case Map.lookup x ds of
                      Nothing -> error $ "can't find " ++ show (disp x)
                      Just v -> v


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
to_qasm_gate "C_Z" = "z"
to_qasm_gate "C_Y" = "y"
to_qasm_gate "C_X" = "x"

qasm_header = "OPENQASM 3.0; \n\
              \include \"stdgates.inc\";"


-- Determines number of qubit and bit registers needed for circuit
get_resource_count_rec [] curr_bits curr_qubits max_bits max_qubits =
    (max_bits, max_qubits)
get_resource_count_rec (g:gs) curr_bits curr_qubits max_bits max_qubits =
    case g of
        (Gate (Id gateName) _ _ _ _ _ _ _ _) | (gateName == "Init0" || gateName == "Init1") ->
            get_resource_count_rec gs curr_bits (curr_qubits + 1) max_bits (max max_qubits (curr_qubits + 1))
        (Gate (Id gateName) _ _ _ _ _ _ _ _) | (gateName == "Meas") ->
            get_resource_count_rec gs (curr_bits + 1) (curr_qubits - 1) (max max_bits (curr_bits + 1)) max_qubits
        (Gate (Id gateName) _ _ _ _ _ _ _ _) | (gateName == "Discard") ->
            get_resource_count_rec gs (curr_bits - 1) curr_qubits max_bits max_qubits
        _ -> get_resource_count_rec gs curr_bits curr_qubits max_bits max_qubits

get_resource_count gs = get_resource_count_rec gs 0 0 0 0


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
    | (gateName == "Meas") =
        "bit b_" ++ (show l) ++ ";\nb_" ++ (show l) ++ " = measure " ++ (show l) ++ ";"

gate_to_qasm (Gate (Id gateName) _ (VLabel l) output _ _ _ _ _)
    | (gateName == "Discard") = ""
    
-- Single qubit gates - no params
gate_to_qasm (Gate (Id gateName) [] (VLabel l) output ctrl _ _ _ _) =
    (to_qasm_gate gateName) ++ " " ++ (show l) ++ ";"
    
-- Single qubit rotation gate
gate_to_qasm (Gate (Id gateName) [VWrapR (MR len r)] (VLabel l) output ctrl _ _ _ _)
    | gateName == "Rot" =
        "rz(" ++ (showCReal len r) ++ ") " ++ (show l) ++ ";"

-- Classical controlled X and Y gates
gate_to_qasm (Gate (Id gateName) [] (VPair (VLabel l1) (VLabel l2)) output ctrl _ _ _ _)
    | (gateName == "C_X" || gateName == "C_Z" || gateName == "C_Y") =
        "if (b_" ++ (show l2) ++ ") " ++ (to_qasm_gate gateName) ++ " " ++ (show l1) ++ ";"

-- Two qubit gates - no params
gate_to_qasm (Gate (Id gateName) [] (VPair (VLabel l1) (VLabel l2)) output ctrl _ _ _ _) =
    (to_qasm_gate gateName) ++ " " ++ (show l2) ++ ", " ++ (show l1) ++ ";"

-- Controlled rotation gate
gate_to_qasm (Gate (Id gateName) [a] (VPair (VLabel l1) (VLabel l2)) output ctrl _ _ _ _)
    | gateName == "R" =
        -- Parsing input param as int
        case (toInt a) of
            Nothing -> error "Error parsing R gate during QASM conversion"
            Just n ->
                "ctrl @ rz(" ++ (show n) ++ ") " ++ (show l2) ++ ", "
                    ++ (show l1) ++ ";"


-- Recursive function that maps list of gates to their QASM representation
gates_to_qasm [] _ _ _ _ = []
gates_to_qasm (g:gs) free_bits free_qubits bits qubits =
    case g of
        -- Init gates
        (Gate (Id gateName) _ _ (VLabel l) _ _ _ _ _) | gateName == "Init0" ->
            let (fq:fqs) = free_qubits
                new_qubits = Map.insert l fq qubits
            in (("reset qubits[" ++ (show fq) ++ "];") : (gates_to_qasm gs free_bits fqs bits new_qubits))
        (Gate (Id gateName) _ _ (VLabel l) _ _ _ _ _) | gateName == "Init1" ->
            let (fq:fqs) = free_qubits
                new_qubits = Map.insert l fq qubits
            in (("reset qubits[" ++ (show fq) ++ "];\nx qubits[" ++ (show fq) ++ "];") :
                (gates_to_qasm gs free_bits fqs bits new_qubits))


string_join :: String -> [String] -> String
string_join s [] = ""
string_join s (x:[]) = x
string_join s (x:xs) = x ++ s ++ (string_join s xs)


-- Converts `Wired` circuit objects to QASM circuit
circ_to_qasm circ =
    open circ $ \ _ morph ->
        -- let q1 = input morph
        --     -- Parsing circuit object to extract gates
        --     ocirc = gates morph
        --     (gs, _) = refresh_gates Map.empty ocirc []
        --     ws = getWires q1 `List.union` wirelist gs

        --     -- Mapping over gates to convert each to qasm
        --     gates_qasm = map gate_to_qasm gs

        -- -- Joining all gate strings together with header
        -- in (string_join "\n" (qasm_header : gates_qasm))

        -- Getting gates from circuit
        let gs = gates morph
            -- Calculating how many bit and qubit register to use
            (nbits, nqubits) = get_resource_count gs

            -- Initializing registers
            reg_init = "qreg qubits[" ++ (show nqubits) ++ "]; \n\
                       \creg bits[" ++ (show nbits) ++ "];"

            -- Converting gates to qasm
            free_bits = [0..(nbits-1)]
            free_qubits = [0..(nqubits-1)]
            gates_qasm = gates_to_qasm gs free_bits free_qubits Map.empty Map.empty

        in (string_join "\n" (qasm_header : reg_init : gates_qasm))


-- Runs the OpenQASM converter and stores result to text file
save_circ_as_qasm (Wired circ) s =
    do
        h <- openFile s WriteMode
        hPutStr h (circ_to_qasm circ)
        hClose h