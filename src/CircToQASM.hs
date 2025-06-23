module CircToQASM where

import Syntax
import Utils
import Nominal

import System.IO
import Text.PrettyPrint


saveCircAsQASM (Wired circ) s =
    open circ $ \ ws morph ->
        let q1 = input morph
        in do
            putStrLn $ show q1
            h <- openFile s WriteMode
            hPutStrLn h "OPENQASM 2.0;"
            hPutStrLn h "include \"qelib1.inc\";"
            hClose h