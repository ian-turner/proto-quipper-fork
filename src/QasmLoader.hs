module QasmLoader where

import System.IO
import QasmParser


loadQasmFile file = do
    (Program _ stmts) <- parseQasmFile file
    let stmts_str = map show stmts
    putStr (unlines stmts_str)
