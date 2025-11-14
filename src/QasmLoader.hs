module QasmLoader where

import System.IO
import QasmParser

import Syntax


loadQasmFile :: String -> Top String
loadQasmFile file = do
    (Program _ stmts) <- parseQasmFile file
    let stmts_str = map show stmts
    ioTop $ putStr (unlines stmts_str)
    return "test"
