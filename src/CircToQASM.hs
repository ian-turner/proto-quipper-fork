module CircToQASM where

import Syntax

import System.IO
import Text.PrettyPrint


saveCircAsQASM circ s = do
  h <- openFile s WriteMode
  hPutStrLn h "OPENQASM 2.0;"
  hPutStrLn h "include \"qelib1.inc\";"
  putStrLn (show circ)
  hClose h