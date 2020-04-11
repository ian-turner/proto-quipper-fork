{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | This module defines various utility functions for the 'TopMonad'. 
module TopMonad where


import Syntax as A
import ConcreteSyntax as C
import Parser
import TCMonad
import TypeClass
import ProcessDecls
import Typechecking
import Resolve
import TypeError
import Utils
import SyntacticOperations


import Nominal

import Control.Monad.Except
import Control.Monad.Identity
import Control.Exception hiding (TypeError)
import Text.Parsec hiding (count)
import Text.PrettyPrint
import Control.Monad.State
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)


-- | Top-level error data type. 
data Error =
  NoReloadError  
  | IOError IOError -- ^ A wrapper for IO error.
  | ScopeErr ScopeError -- ^ A wrapper for scope error.
  | Mess Position Doc  -- ^ A wrapper for a message.
  | Cyclic Position [String] String -- ^ Cyclic importation error.
  | ParseErr ParseError -- ^ A wrapper for parsing error.
  | CompileErr TypeError -- ^ A wrapper for typing error.


instance Disp Error where
  display flag (IOError e) = (text $ show e)

  display flag NoReloadError = text "There is no file to reload"
  display flag (Mess p s) = display flag p $$ display flag s
  display flag (Cyclic p sources target) = display flag p $$
                                  text "cyclic importing detected" $$
                                  text "when importing:" <+> text target $$
                                  text "current importation chain:" $$
                                  (vcat $ map text sources)
  display flag (ParseErr e) = display flag e
  display flag (ScopeErr e) = display flag e
  display flag (CompileErr (PfErrWrapper a e t)) =
    text "proof checking error:" $$
    disp e $$
    text "when checking the following annotated term:" $$
    dispRaw a $$
    text "against the type:" $$
    dispRaw t $$
    text "*************************" $$
    text "this is a bug, please send bug report. Thanks!"
    

  display flag (CompileErr e) = display flag e
    

-- | A top-level monad. It wraps on top of IO monad, and maintains
-- a 'TopState'. 
newtype Top a = T {runT :: ExceptT Error (StateT TopState IO) a }
              deriving (Monad, Applicative, Functor,
                        MonadState TopState, MonadError Error, MonadIO)

-- | A 'TopState' contains an interpreter state and a file name. 
data TopState = TopState {
  interpreterstate :: InterpreterState,
  filename :: Maybe String
  }

-- | Initial top-level state.
initTopState p = TopState {
  interpreterstate = emptyState p,
  filename = Nothing
  }

-- | A run function for the 'Top' monad.
runTop :: String -> Top a -> IO (Either Error a, TopState)
runTop p body = runStateT (runExceptT (runT body)) (initTopState p)
  -- do (r, s') <- 
  --    case r of
  --      Right a -> return a
  --      Left e -> error ("from runTop: " ++ (show $ disp e)) 


-- | Interpreter's state.
data InterpreterState = InterpreterState {
  scope :: Scope,   -- ^ Scope information.
  context :: Context,  -- ^ Typing context.
  mainExp :: Maybe (A.Value, A.Exp),  -- ^ Main value and its type.
  instCxt :: GlobalInstanceCxt, -- ^ Type class instance context.
  parserState :: ParserState,   -- ^ Infix operators table.
  parentFiles :: [String], -- ^ Parent files, for
                    -- preventing cyclic importing.
  importedFiles :: [String], -- ^ Imported files, for preventing double importing.
  counter :: Int, -- ^ A counter. 
  path :: String -- ^ DPQ project path.
  }


-- | Lift 'IO' to 'Top'.
ioTop :: IO a -> Top a
ioTop x = T $ ExceptT $ lift (caught x)
  where caught :: IO a -> IO (Either Error a)
        caught x = catch (x >>= \y -> return (return y))
                   (\e -> return (Left (IOError e)))

-- | Get current file name. 
getFilename :: Top (Maybe String)
getFilename = do
  s <- get
  return (filename s)

-- | Get the interpreter state.
getInterpreterState :: Top InterpreterState
getInterpreterState = do
  s <- get
  return (interpreterstate s)

-- | Get current scope information.
getScope :: Top Scope
getScope = do
  s <- getInterpreterState
  return (scope s)

-- | Resolve an expression at top-level.
topResolve :: C.Exp -> Top A.Exp
topResolve t =
  do scope <- getScope
     scopeTop $ resolve (toLScope scope) t

-- | Lift the 'Resolve' monad to 'Top' monad. 
scopeTop :: Resolve a -> Top a
scopeTop x = case runResolve x of
                 Left e -> throwError (ScopeErr e)
                 Right a -> return a

-- | Perform an 'TCMonad' action, will update 'Top'. 
tcTop :: Simulation a -> Top a
tcTop m = 
  do st <- getInterpreterState
     let cxt = context st
         inst = instCxt st
     handle $ ioTop $ runTCMonadT cxt inst m
     -- (res, s) <- ioTop $ runTCMonadT cxt inst m
  where handle m =
          do (res, s) <- m
             case res of
               Left e -> throwError $ CompileErr e
               Right e ->
                 do let cxt' = globalCxt $ lcontext s
                        inst' = globalInstance $ instanceContext s
                    putCxt cxt'
                    putInstCxt inst'
                    return e

-- | Infer a type at top-level. It is a wrapper for 'typeInfer'.    
topTypeInfer :: A.Exp -> Top (A.Exp, A.Exp)
topTypeInfer def = tcTop $
  do (ty, tm, _) <- liftS $ typeInfer (isKind def) def
     ty' <- liftS $ updateWithSubst ty
     tm' <- liftS $ updateWithSubst tm
     (ann1, rt) <- liftS $ elimConstraint def tm' ty'
     let ann' = unEigen ann1
     rt' <- liftS $ resolveGoals rt `catchError` \ e -> throwError $ withPosition def e
     ann'' <- liftS $ resolveGoals ann' `catchError` \ e -> throwError $ withPosition def e
     return $ (rt', ann'')     
       where elimConstraint e a (A.Imply (b:bds) ty) = 
                 do ns <- newNames ["#outergoalinst"]
                    freshNames ns $ \ [n] ->
                      do addGoalInst n b e
                         let a' = A.AppDict a (GoalVar n)
                         elimConstraint e a' (A.Imply bds ty)
             elimConstraint e a (A.Imply [] ty) = elimConstraint e a ty
             elimConstraint e a (A.Pos _ ty) = elimConstraint e a ty    
             elimConstraint e a t = return (a, t)

-- | Get the current typing context.
getCxt :: Top Context
getCxt = do
  s <- getInterpreterState
  return (context s)

-- | Reset the interpreter state to the empty state. 
clearInterpreterState :: Top ()
clearInterpreterState =
  do p <- getPath
     putInterpreterState $ emptyState p

-- | The empty interpreter state.
emptyState p = InterpreterState {
  scope = emptyScope,
  context = Map.empty,
  mainExp = Nothing,
  instCxt = [],
  parserState = initialParserState,
  parentFiles = [],
  importedFiles = [],
  counter = 0,
  path = p
  }

-- | Get the DPQ path.
getPath :: Top String
getPath =
  do s <- get
     let intp = interpreterstate s
     return (path intp)

-- | Update the interpreter state.
putInterpreterState :: InterpreterState -> Top ()
putInterpreterState is = do
  s <- get
  put $ s{interpreterstate = is}

-- | Get counter.
getCounter :: Top Int
getCounter = do
  s <- getInterpreterState
  return (counter s)

-- | Add a build in identifier according to the third argument.
-- For example, @addBuiltin (BuiltIn i) "Simple" A.Base@.
addBuiltin :: Position -> String -> (Id -> A.Exp) -> Top Id  
addBuiltin p x f =
  do scope <- getScope
     case lookupScope scope x of
       Just (_, oldp) -> error $ "internal error: from addBuiltin"
       Nothing ->
         let 
             id = Id x
             exp = f id
             newMap = Map.insert x (exp, p) $ scopeMap scope
             scope' = scope{scopeMap = newMap}
         in putScope scope' >> return id

-- | Update scope.
putScope :: Scope -> Top ()
putScope scope = do
  s <- getInterpreterState
  let s' = s { scope = scope }
  putInterpreterState s'

  
-- | Update counter.
putCounter :: Int -> Top ()
putCounter i = do
  s <- getInterpreterState
  let s' = s {counter = i}
  putInterpreterState s'

-- | Update current file name.
putFilename :: String -> Top ()
putFilename x = do
  s <- get
  let s' = s{filename = Just x }
  put s'

-- | Get infix operator table.
getPState :: Top ParserState
getPState = do
  s <- getInterpreterState
  return (parserState s)

-- | Update infix operator table.
putPState :: ParserState -> Top ()
putPState x = do
  s <- getInterpreterState
  let s' = s { parserState = x }
  putInterpreterState s'

-- | Update the typing context.
putCxt :: Map Id Info -> Top ()
putCxt cxt = do
  s <- getInterpreterState
  let s' = s { context = cxt }
  putInterpreterState s'

-- | Update the instance context.
putInstCxt :: [(Id, A.Exp)] -> Top ()
putInstCxt cxt = do
  s <- getInterpreterState
  let s' = s { instCxt = cxt }
  putInterpreterState s'


-- | Make a built-in class of the form @C x1 ... xn@. The input /d/
-- is the class name,  /n/ is the number of arguments for /c/. 
makeBuiltinClass :: Id -> Int -> Top ()
makeBuiltinClass d n | n > 0 =
  do i <- getCounter
     dict <- addBuiltin (BuiltIn (i+1)) (getName d ++"Dict") A.Const
     putCounter (i+3)
     let names = map (\ i -> "x"++ show i) $ take n [0 .. ]
         dictType = freshNames names $
                    \ ns -> A.Forall (abst ns $ foldl A.App (A.Base d) (map A.Var ns)) A.Set
         kd = foldr (\ x y -> A.Arrow A.Set y) A.Set names
     tcTop $ process (A.Class (BuiltIn (i+2)) d kd dict dictType [])

-- | Lift a parsing result to 'Top' monad.
parserTop :: Either ParseError a -> Top a
parserTop (Left e) = throwError (ParseErr e)
parserTop (Right a) = return a

-- | Remember an imported file.
addImported :: String -> Top ()
addImported x = do
  s <- get
  let inS = interpreterstate s
      inS' = inS{importedFiles = x:(importedFiles inS)}
      s' = s{interpreterstate = inS'}
  put s'

-- | Remember an parent file.
addParentFile :: String -> Top ()
addParentFile x = do
  s <- get
  let inS = interpreterstate s
      inS' = inS{parentFiles = x:(parentFiles inS)}
      s' = s{interpreterstate = inS'}
  put s'

-- | Retrieve the parent files.
getParentFiles :: Top [String]
getParentFiles =
  do s <- get
     let intp = interpreterstate s
     return (parentFiles intp)

-- | Retrieve current imported files.
getCurrentImported :: Top [String]
getCurrentImported =
  do s <- get
     let intp = interpreterstate s
     return (importedFiles intp)

-- | Get the main function's information.
getMain :: Top (Maybe (Value, A.Exp))
getMain = do
  s <- getInterpreterState
  return (mainExp s)

-- | Update main function.
putMain :: Value -> A.Exp -> Top ()
putMain v t = do
  s <- getInterpreterState
  let s' = s {mainExp = Just (v, t)}
  putInterpreterState s'
