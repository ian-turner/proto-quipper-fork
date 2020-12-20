module Main where

import ConcreteSyntax
import Resolve
import Dispatch
import Parser
import Printcircuits
import ReadEvalPrint
import SyntacticOperations (gateCount)
import Syntax as A
import TopMonad
import Utils

import Control.Exception
import Control.Monad.Except
import System.Environment
import System.Exit
import Text.PrettyPrint

main :: IO ()
main = do
  args <- getArgs
  p <- getEnv "DPQ" `catches` handlers
  case args of
    [filename, option]
      | option == "-m" -> do
        runTop p $ catchTop error_handler (printMain filename)
        return ()
    [filename, option]
      | option == "-v" -> do
        runTop p $ catchTop error_handler_verbose  (load filename)
        return ()
        
    [filename, option]
      | option == "-s" -> do
        runTop p $ catchTop error_handler (printTopLevel Nothing filename)
        return ()
    [filename, option]
      | option == "-g" -> do
        runTop p $ catchTop error_handler (gateCountMain Nothing filename)
        return ()
    [filename, option]
      | option == "-tg" -> do
        runTop p $
          catchTop error_handler (topGateCount Nothing filename Nothing)
        return ()
    [filename, option, name]
      | option == "-g" -> do
        runTop p $ catchTop error_handler (gateCountMain (Just name) filename)
        return ()
    [filename, option, target]
      | option == "-p" -> do
        runTop p $ catchTop error_handler $ (printToFile filename target)
        return ()
    [filename, option, name]
      | option == "-tg" -> do
        runTop p $
          catchTop error_handler (topGateCount (Just name) filename Nothing)
        return ()
    [filename, option, name]
      | option == "-s" -> do
        runTop p $ catchTop error_handler (printTopLevel (Just name) filename)
        return ()
    [filename, option, option2, exp]
      | (option == "-tg") && (option2 == "-e") -> do
        runTop p $
          catchTop error_handler (topGateCount Nothing filename (Just exp))
        return ()
    [filename, option, name, option2, exp]
      | (option == "-tg") && (option2 == "-e") -> do
        runTop p $
          catchTop error_handler (topGateCount (Just name) filename (Just exp))
        return ()
    [filename] -> do
      runTop p $ catchTop error_handler (load filename)
      return ()
    _ -> do
      print $ text "unknown command option"
      print $ text cmdUsage
  where
    printMain fn = do
      dispatch (Load False fn)
      circ <- getMain
      case circ of
        Just (c, _) -> ioTop (print $ dispRaw c)
        Nothing ->
          throwError $
          Mess (text "cannot find the main function in:" <+> text fn)
    printTopLevel e fn = do
      dispatch (Load False fn)
      case e of
        Nothing -> do
          gs <- getGates
          ioTop (print $ vcat $ map dispRaw gs)
        Just str -> do
          pst <- getPState
          exp' <- parserTop $ parseExp str pst
          e <- topResolve Pure exp'
          (_, e'') <- topTypeInfer e
          gs <- evaluation' e'' False
          ioTop (print $ vcat $ map dispRaw gs)
    load fn = dispatch (Load False fn) >> return ()
    topGateCount name file Nothing = do
      dispatch (Load False file)
      gs <- getGates
      case name of
        Nothing -> liftIO $ print (length gs)
        Just n -> do
          let rs = [g | g <- gs, (getName $ gateName g) == n]
          liftIO $ putStrLn (n ++ ":\n" ++ show (length rs))
    topGateCount name file (Just exp) = do
      dispatch (Load False file)
      pst <- getPState
      exp' <- parserTop $ parseExp exp pst
      e <- topResolve Pure exp'
      (_, e'') <- topTypeInfer e
      gs <- evaluation' e'' False
      case name of
        Nothing -> liftIO $ print (length gs)
        Just n -> do
          let rs = [g | g <- gs, (getName $ gateName g) == n]
          liftIO $ putStrLn (n ++ ":\n" ++ show (length rs))
    gateCountMain name file = do
      dispatch (Load False file)
      circ <- getMain
      case circ of
        Nothing ->
          throwError $
          Mess (text "cannot find the main function in:" <+> text file)
        Just (circ', t) ->
          case t of
            A.Circ _ _ _ -> do
              let n = gateCount name circ'
              liftIO $ print n
            A.Exists (Abst m (A.Circ _ _ _)) _ ->
              case circ' of
                A.VPair _ res -> do
                  let n = gateCount name res
                  liftIO $ print n
            ty -> liftIO $ print (text "main is not a circuit")
    printToFile file target = do
      dispatch (Load False file) 
      circ <- getMain
      case circ of
        Nothing ->
          throwError $
          Mess (text "cannot find the main function in:" <+> text file)
        Just (circ', t) ->
          case t of
            A.Circ _ _ _ -> ioTop $ printCirc circ' target
            A.Exists (Abst n (A.Circ _ _ _)) _ ->
              case circ' of
                A.VPair n res -> ioTop $ printCirc res target
            ty -> liftIO $ print (text "main is not a circuit")
    error_handler e = do
      top_display_error True e
      return ()
    error_handler_verbose e = do
      top_display_error False e
      return ()
      
    mesg =
      "please set the environment variable DPQ to the DPQ installation directory.\n"
    handlers = [Handler handle1]
    handle1 :: IOException -> IO String
    handle1 =
      \ex -> do
        putStrLn $ mesg ++ show ex
        exitWith $ ExitFailure 1
    cmdUsage =
      "usage: dpq <dpq-file> [-options]\n\n" ++
      "option: none             -- type check and evaluate given dpq file\n" ++
      "option: -v             -- verbose mode, showing unique names\n" ++
      "option: -p <pdf-file>    -- print the main circuit to a pdf-file\n" ++
      "option: -m               -- print the value of main function\n" ++
      "option: -g [name]        -- print the gate count of main function\n" ++
      "option: -tg [name] [-e exp] -- print the gate count of the expression, if the expression is empty, then print the last definition. \n" ++
      "option: -s [exp] -- print the gates generated by the expresion, if the expression is empty, then print the gates generated by the last definition. \n"
