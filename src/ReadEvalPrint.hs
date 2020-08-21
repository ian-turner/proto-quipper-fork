-- | This module implements the top-level read eval print loop.
-- We use <https://hackage.haskell.org/package/haskeline Haskeline library> for
-- command line handling. The main function calls the 'dispatch' function to handle
-- user input commands. We allow multiline input, as programmer can use ";" to indicate a newline.
-- The interface can also auto-complete names that are in scope.
module ReadEvalPrint where

import ConcreteSyntax as C
import Dispatch
import Parser hiding (const)
import Resolve
import Syntax as A
import TopMonad
import Utils

import Control.Monad.Except
import Control.Monad.State
import Data.Char
import Data.List
import qualified Data.Map as Map
import System.Console.Haskeline hiding (catch, display)
import System.IO
import Text.Parsec
import Text.PrettyPrint

-- | Boilerplate due to the Haskeline lib does not implement enough freaking
-- MonadException instances.
instance MonadException m => MonadException (StateT s m) where
  controlIO f =
    StateT $ \s ->
      controlIO $ \(RunIO run) ->
        let run' = RunIO (fmap (StateT . const) . run . flip runStateT s)
         in fmap (flip runStateT s) $ f run'

instance MonadException m => MonadException (ExceptT e m) where
  controlIO f =
    ExceptT $
    controlIO $ \(RunIO run) ->
      let run' = RunIO (fmap ExceptT . run . runExceptT)
       in fmap runExceptT $ f run'

instance MonadException Top where
  controlIO f =
    T $
    controlIO $ \(RunIO run) ->
      let run' = RunIO (fmap T . run . runT)
       in fmap runT $ f run'

-- | Parse and dispatch a command.
-- It is one iteration of the read-eval-print loop. Return False to quit,
-- otherwise True.
read_eval_print_line :: Num b => b -> String -> InputT Top (Bool, b)
read_eval_print_line lineno initString = do
  s <- getInputLine "> "
  case s of
    Just line
      | all isSpace line ->
        if null initString
          then return (True, lineno)
          else do
            pst <- lift getPState
            case parseCommand initString pst of
              Left e -> lift $ throwError (ParseErr e)
              Right a -> do
                r <- lift $ dispatch a
                return (r, lineno)
      | otherwise ->
        if last line == ';'
          then if length line == 1
                 then read_eval_print_line (lineno + 1) initString
                 else do
                   let s' = initString ++ init line ++ "\n"
                   read_eval_print_line (lineno + 1) s'
          else do
            pst <- lift getPState
            case parseCommand (initString ++ line) pst of
              Left e -> lift $ throwError (ParseErr e)
              Right a -> do
                r <- lift $ dispatch a
                return (r, lineno)
    Nothing -> return (False, lineno)

-- | Read eval print loop.
read_eval_print :: Integer -> Top ()
read_eval_print lineno = do
  more <-
    catchTop
      error_handler
      (runInputTWithPrefs
         defaultPrefs
         dpqSettings
         (read_eval_print_line lineno ""))
  case more of
    (True, ln) -> read_eval_print (ln + 1)
    (False, _) -> return ()
  where
    error_handler e = do
      top_display_error True e
      return (True, lineno)

-- | Print an error.
top_display_error :: Bool -> Error -> Top ()
top_display_error flag e = do
  ioTop $ putStrLn ("error: " ++ show (display flag e))

-- | Restore the interpreter state when
-- an error occur.
catchTop :: (Error -> Top a) -> Top a -> Top a
catchTop k x = do
  s <- get
  x `catchError` (\e -> put s >> k e)

-- | A customize setting that record the command line history in
-- ``dpq-histfile.txt'', so don't type your password in the command line.
dpqSettings :: Settings Top
dpqSettings = Settings dpqCompletion (Just "dpq-histfile.txt") True

-- | Completion by the strings in the scope.
scopeCompletion :: CompletionFunc Top
scopeCompletion = completeWordWithPrev Nothing [' '] helper
  where
    helper :: String -> String -> Top [Completion]
    helper lc word = do
      sc <- getScope
      let keys = Map.keys (scopeMap sc)
          comps = [k | k <- keys, word `isPrefixOf` k]
          res = map simpleCompletion comps
      return res

-- | Set scope completion.
dpqCompletion :: CompletionFunc Top
dpqCompletion = completeQuotedWord Nothing ['"'] listFiles scopeCompletion
