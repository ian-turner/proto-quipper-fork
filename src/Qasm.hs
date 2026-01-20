module Qasm where

import Syntax
import Utils
import SyntacticOperations
import Nominal
import Simulation
import TopMonad

import Data.Number.CReal
import System.IO
import Text.PrettyPrint
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List as List
import Text.Printf
import Control.Monad.State.Strict (State, execState, get, put, modify)


compileToQasm mainExp outfile = do
    st <- getInterpreterState
    ioTop $ putStrLn $ show $ context st
    return ()
