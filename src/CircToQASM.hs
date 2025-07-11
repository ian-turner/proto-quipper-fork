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
        (Gate (Id gateName) _ _ _ _ _ _ _ _) | (gateName == "Term0") ->
            get_resource_count_rec gs curr_bits (curr_qubits - 1) max_bits max_qubits
        (Gate (Id gateName) _ _ _ _ _ _ _ _) | (gateName == "Discard") ->
            get_resource_count_rec gs (curr_bits - 1) curr_qubits max_bits max_qubits
        _ -> get_resource_count_rec gs curr_bits curr_qubits max_bits max_qubits

get_resource_count gs = get_resource_count_rec gs 0 0 0 0


-- Recursive function that maps list of gates to their QASM representation
gates_to_qasm [] _ _ b q = ([], b, q)
gates_to_qasm (g:gs) free_bits free_qubits bits qubits =
    case g of
        -- Init gates
        (Gate (Id gateName) _ _ (VLabel l) VStar _ _ _ _) | gateName == "Init0" ->
            let (fq:fqs) = free_qubits
                new_qubits = Map.insert l fq qubits
                qasm_str = "reset qubits[" ++ (show fq) ++ "];"
                (gates_rec, bits', qubits') = gates_to_qasm gs free_bits fqs bits new_qubits
            in ((qasm_str : gates_rec), bits', qubits')

        (Gate (Id gateName) _ _ (VLabel l) VStar _ _ _ _) | gateName == "Init1" ->
            let (fq:fqs) = free_qubits
                new_qubits = Map.insert l fq qubits
                qasm_str = "reset qubits[" ++ (show fq) ++ "];\nx qubits[" ++ (show fq) ++ "];"
                (gates_rec, bits', qubits') = gates_to_qasm gs free_bits fqs bits new_qubits
            in ((qasm_str : gates_rec), bits', qubits')

        -- Measurement gate
        (Gate (Id gateName) _ (VLabel li) (VLabel lo) VStar _ _ _ _) | gateName == "Meas" ->
            let (fb:fbs) = free_bits
                qubit = qubits `mapLookup` li
                new_bits = Map.insert lo fb bits
                new_free_qubits = (qubit:free_qubits)
                qasm_str = "bits[" ++ (show fb) ++ "] = measure qubits[" ++ (show qubit) ++ "];"
                (gates_rec, bits', qubits') = gates_to_qasm gs fbs new_free_qubits new_bits qubits
            in ((qasm_str : gates_rec), bits', qubits')

        -- Term gates
        (Gate (Id gateName) _ (VLabel li) VStar VStar _ _ _ _) | gateName == "Term0" ->
            let qubit = qubits `mapLookup` li
                new_free_qubits = (qubit:free_qubits)
                (gates_rec, bits', qubits') = gates_to_qasm gs free_bits new_free_qubits bits qubits
            in (gates_rec, bits', qubits')

        -- Discard gate
        (Gate (Id gateName) _ (VLabel l) _ VStar _ _ _ _) | gateName == "Discard" ->
            let bit = bits `mapLookup` l
                new_free_bits = (bit:free_bits)
                (gates_rec, bits', qubits') = gates_to_qasm gs new_free_bits free_qubits bits qubits
            in (gates_rec, bits', qubits')

        -- Single qubit gate - no params
        (Gate (Id gateName) [] (VLabel li) (VLabel lo) VStar _ _ _ _) ->
            let qubit = qubits `mapLookup` li
                new_qubits = Map.insert lo qubit qubits
                qasm_str = (to_qasm_gate gateName) ++ " qubits[" ++ (show qubit) ++ "];"
                (gates_rec, bits', qubits') = gates_to_qasm gs free_bits free_qubits bits new_qubits
            in ((qasm_str : gates_rec), bits', qubits')

        -- Single qubit rotation gates
        (Gate (Id gateName) [VWrapR (MR len r)] (VLabel li) (VLabel lo) VStar _ _ _ _) | gateName == "Rot" ->
            let qubit = qubits `mapLookup` li
                new_qubits = Map.insert lo qubit qubits
                qasm_str = "rz(" ++ (showCReal len r) ++ ") qubits[" ++ (show qubit) ++ "];"
                (gates_rec, bits', qubits') = gates_to_qasm gs free_bits free_qubits bits new_qubits
            in ((qasm_str : gates_rec), bits', qubits')

        -- Classically controlled X, Y, Z gates
        (Gate (Id gateName) [] (VPair (VLabel l1i) (VLabel l2i)) (VPair (VLabel l1o) (VLabel l2o)) VStar _ _ _ _)
            | (gateName == "C_X" || gateName == "C_Y" || gateName == "C_Z") ->
                let qubit = qubits `mapLookup` l1i
                    new_qubits = Map.insert l1o qubit qubits
                    bit = bits `mapLookup` l2i
                    new_bits = Map.insert l2o bit bits
                    qasm_str = "if (bits[" ++ (show bit) ++ "]) " ++ (to_qasm_gate gateName)
                        ++ " qubits[" ++ (show qubit) ++ "];"
                    (gates_rec, bits', qubits') = gates_to_qasm gs free_bits free_qubits new_bits new_qubits
                in ((qasm_str : gates_rec), bits', qubits')
        
        -- CNot gates
        (Gate (Id gateName) [] (VPair (VLabel l1i) (VLabel l2i)) (VPair (VLabel l1o) (VLabel l2o)) VStar _ _ _ _)
            | gateName == "CNot" ->
                let q1 = qubits `mapLookup` l1i
                    q2 = qubits `mapLookup` l2i
                    new_qubits = Map.insert l1o q1 qubits
                    new_qubits' = Map.insert l2o q2 new_qubits
                    qasm_str = "cx qubits[" ++ (show q2) ++ "], qubits[" ++ (show q1) ++ "];"
                    (gates_rec, bits', qubits') = gates_to_qasm gs free_bits free_qubits bits new_qubits'
                in ((qasm_str : gates_rec), bits', qubits')

        -- Controlled rotation gate
        (Gate (Id gateName) [a] (VPair (VLabel l1i) (VLabel l2i)) (VPair (VLabel l1o) (VLabel l2o)) VStar _ _ _ _)
            | gateName == "R" ->
                case toInt a of
                    Nothing -> error "Error parsing R gate in qasm converter"
                    Just n ->
                        let q1 = qubits `mapLookup` l1i
                            q2 = qubits `mapLookup` l2i
                            new_qubits = Map.insert l1o q1 qubits
                            new_qubits' = Map.insert l2o q2 new_qubits
                            qasm_str = "ctrl @ rz(" ++ (show (pi / (2^n))) ++ ") qubits["
                                ++ (show q2) ++ "], qubits[" ++ (show q1) ++ "];"
                            (gates_rec, bits', qubits') = gates_to_qasm gs free_bits free_qubits bits new_qubits'
                        in ((qasm_str : gates_rec), bits', qubits')
        
        -- Diagonal gates (not currently supported)
        -- TODO: add support for Diagonal gates
        (Gate (Id gateName) [VWrapR (MR len r), VWrapR (MR len' r')] (VLabel li) (VLabel lo) VStar _ _ _ _)
            | gateName == "Diag" -> error "Diagonal gates not currently supported for QASM conversion"

        -- Toffoli gate
        (Gate (Id gateName) [] (VPair (VPair (VLabel la_in) (VLabel lb_in)) (VLabel lc_in))
            (VPair (VPair (VLabel la_out) (VLabel lb_out)) (VLabel lc_out)) VStar _ _ _ _)
            | gateName == "Toffoli" ->
                let qa = qubits `mapLookup` la_in
                    qb = qubits `mapLookup` lb_in
                    qc = qubits `mapLookup` lc_in
                    qubits' = Map.insert la_out qa qubits
                    qubits'' = Map.insert la_out qb qubits'
                    qubits''' = Map.insert la_out qb qubits''
                    qasm_string = "ccx qubits[" ++ (show qc) ++ "], qubits[" ++ (show qb) ++ "], qubits[" ++ (show qa) ++ "];"
                    (gates_rec, bits', qubits'''') = gates_to_qasm gs free_bits free_qubits bits qubits'''
                in ((qasm_string : gates_rec), bits', qubits'''')


string_join :: String -> [String] -> String
string_join s [] = ""
string_join s (x:[]) = x
string_join s (x:xs) = x ++ s ++ (string_join s xs)


-- Converts `Wired` circuit objects to QASM circuit
circ_to_qasm circ =
    open circ $ \ _ morph ->
        -- Getting gates from circuit
        let gs = gates morph
            -- Calculating how many bit and qubit register to use
            (nbits, nqubits) = get_resource_count gs

            reg_init =
                case (nbits, nqubits) of
                    (0, nq) -> "qreg qubits[" ++ (show nqubits) ++ "];"
                    (nb, nq) -> "qreg qubits[" ++ (show nq) ++ "]; \n\
                                \creg bits[" ++ (show nb) ++ "];"

            -- Converting gates to qasm
            free_bits = [0..(nbits-1)]
            free_qubits = [0..(nqubits-1)]
            (gates_qasm, _, _) = gates_to_qasm gs free_bits free_qubits Map.empty Map.empty

        in (string_join "\n" (qasm_header : reg_init : gates_qasm))


-- Runs the OpenQASM converter and stores result to text file
save_circ_as_qasm (Wired circ) s =
    do
        h <- openFile s WriteMode
        hPutStr h (circ_to_qasm circ)
        hClose h