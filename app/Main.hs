module Main where
import ReadEvalPrint
import Dispatch
import TopMonad
import ConcreteSyntax
import System.Environment
import System.Exit
import Control.Exception hiding (TypeError)
import System.FilePath

main :: IO ()
main =
  do p <- getEnv "DPQ" `catches` handlers 
     runTop p $ read_eval_print 1
     return ()
          
   where mesg = "please set the environment variable DPQ to the DPQ installation directory.\n"
         handlers = [Handler handle1]
         handle1 :: IOException -> IO String
         handle1 = (\ ex  -> do {putStrLn $ mesg ++ show ex; exitWith (ExitFailure 1)})
         error_handler e = 
          do top_display_error e
             return ()
         loadPrelude =
           do p <- getPath
              dispatch (Load True $ p </> "lib/Prelude.dpq")
              return ()

