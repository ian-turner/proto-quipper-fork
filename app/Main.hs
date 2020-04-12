module Main where
import ReadEvalPrint
import Utils
import Dispatch
import TopMonad
import ConcreteSyntax
import System.Environment
import System.Exit
import Control.Exception hiding (TypeError)
import System.FilePath

main :: IO ()
main =
  do p <- getEnv "DPQ" `catch` handler
     runTop p $ read_eval_print 1
     return ()
          
   where mesg = "please set the environment variable DPQ to the DPQ installation directory.\n"
         -- | Handle IO exception and exit.
         handler :: IOException -> IO String
         handler ex = do
           putStrLn $ mesg ++ show ex
           exitWith (ExitFailure 1)

