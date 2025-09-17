module QasmParser where

import Text.Parsec
import Text.Parsec.Char (char, string, digit, letter, space, newline)
import Control.Applicative ((<|>), many, some)

import System.IO


loadQasmFile file = do
  contents <- readFile file
  putStrLn contents
