module QasmLoader where

import System.IO
import qualified QasmParser as QASM

import Syntax


loadQasmFile :: String -> IO QASM.Program
loadQasmFile file = do
    prg <- QASM.parseQasmFile file
    return prg
