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
toQASMGate :: String -> String
toQASMGate "H" = "h"
toQASMGate "S" = "s"
toQASMGate "S*" = "sdg"
toQASMGate "T" = "t"
toQASMGate "T*" = "tdg"
toQASMGate "CNot" = "cx"
toQASMGate "Rot" = "rz"


-- Converts gate to QASM format

-- Init gates
gateToQASM (Gate (Id gateName) _ (VStar) (VLabel l) _ _ _ _ _)
    | gateName == "Init0" =
        "qubit " ++ (show l) ++ ";\nreset " ++ (show l) ++ ";"

gateToQASM (Gate (Id gateName) _ (VStar) (VLabel l) _ _ _ _ _)
    | gateName == "Init1" =
        "qubit " ++ (show l) ++ ";\nreset " ++ (show l) ++ ";\nx " ++ (show l) ++ ";"

-- Single qubit gates
gateToQASM (Gate (Id gateName) _ (VLabel l) output ctrl _ _ _ _)
    | (gateName == "Meas" || gateName == "Discard") =
        "bit b_" ++ (show l) ++ ";\nb_" ++ (show l) ++ " = measure " ++ (show l) ++ ";"
    
gateToQASM (Gate (Id gateName) _ (VLabel l) output ctrl _ _ _ _) =
    (toQASMGate gateName) ++ " " ++ (show l) ++ ";"

-- Two qubit gates
gateToQASM (Gate (Id gateName) _ (VPair (VLabel l1) (VLabel l2)) output ctrl _ _ _ _) =
    (toQASMGate gateName) ++ " " ++ (show l2) ++ ", " ++ (show l1) ++ ";"


joinStrings :: [String] -> String -> String
joinStrings [] s = ""
joinStrings (x:[]) s = x
joinStrings (x:xs) s = x ++ s ++ (joinStrings xs s)


-- Converts `Wired` circuit objects to QASM circuits
saveCircAsQASM (Wired circ) s =
    open circ $ \ _ morph ->
        let q1 = input morph
            ocirc = gates morph
            (gs, _) = refresh_gates Map.empty ocirc []
        in do
            h <- openFile s WriteMode
            hPutStrLn h "OPENQASM 2.0;"
            hPutStrLn h "include \"qelib1.inc\";"
            hPutStr h $ joinStrings (map gateToQASM gs) "\n"
            hClose h