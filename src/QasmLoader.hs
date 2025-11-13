module QasmLoader where

import Text.Parsec
import Text.Parsec.Char (char, string, digit, letter, space, newline)
import Control.Applicative ((<|>), many, some)

import System.IO
import QasmParser


loadQasmFile file = do
    (Program _ stmts) <- parseQasmFile file
    let stmts_str = map show stmts
    putStr (unlines stmts_str)
