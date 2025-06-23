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


-- Converts gate to QASM format

-- Init gates
gateToQASM (Gate (Id name) _ (VStar) (VLabel l) _ _ _ _ _) =
    "qubit " ++ (show l) ++ ";"

-- Single qubit gates
gateToQASM (Gate (Id name) _ (VLabel l) output ctrl _ _ _ _) =
    (toQASMGate name) ++ " " ++ (show l) ++ ";"

-- Two qubit gates
gateToQASM (Gate (Id name) _ (VPair (VLabel l1) (VLabel l2)) output ctrl _ _ _ _) =
    (toQASMGate name) ++ " " ++ (show l1) ++ ", " ++ (show l2) ++ ";"


joinStrings :: [String] -> String -> String
joinStrings [] s = ""
joinStrings (x:[]) s = x
joinStrings (x:xs) s = x ++ s ++ (joinStrings xs s)


-- Converts `Wired` circuit objects to QASM circuits
saveCircAsQASM (Wired circ) s =
    open circ $ \ ws morph ->
        let q1 = input morph
            ocirc = gates morph
            (gs, _) = refresh_gates Map.empty ocirc []
        in do
            h <- openFile s WriteMode
            hPutStrLn h "OPENQASM 2.0;"
            hPutStrLn h "include \"qelib1.inc\";"
            hPutStrLn h $ joinStrings (map gateToQASM gs) "\n"
            hClose h