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


-- Converts `Wired` circuit objects to QASM circuits
saveCircAsQASM (Wired circ) s =
    open circ $ \ ws morph ->
        let q1 = input morph
            ocirc = gates morph
            (gs, _) = refresh_gates Map.empty ocirc []
            ws = getWires q1 `List.union` wirelist gs
        in do
            putStrLn $ show gs
            putStrLn $ show ws
            h <- openFile s WriteMode
            hPutStrLn h "OPENQASM 2.0;"
            hPutStrLn h "include \"qelib1.inc\";"
            hClose h