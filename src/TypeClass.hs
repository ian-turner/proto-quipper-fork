-- | This module implements a simple type class resolution. There is no supper class
-- or cyclic detection. Our type class can work with dependent data types such as Vector.
module TypeClass
  ( resolveGoals
  , runMatch
  ) where

import Nominal
import Normalize
import Substitution
import SyntacticOperations
import Syntax
import TCMonad
import TypeError
import Utils

import Control.Monad.Except
import Control.Monad.State
import Data.List
import qualified Data.MultiSet as S

-- | Resolve all the goals in an expression, this will substitute
-- all the goal variables in an expression with the corresponding
-- evidence (dictionary).
resolveGoals :: Exp -> TCMonad Exp
resolveGoals a = do
  ts <- get
  let env = instanceContext ts
      goals = goalInstance env
      subs = subst ts
      goals' = map (\(x, (t, e)) -> (x, (substitute subs t, e))) goals
      vars = getVars All a
      goals'' = [(x, (t, e)) | (x, (t, e)) <- goals', x `S.member` vars]
  helper a goals''
  where
    helper ann [] = return ann
    helper ann ((x, (t, e)):xs) = do
      t' <- resolveInst t `catchError`
            \ er -> throwError (Originated e er)
      let ann' = apply [(x, t')] ann
      helper ann' xs
    resolveInst e = do
      ts <- get
      let env = instanceContext ts
          local = localInstance env
          gl = globalInstance env
      resolution e local gl

-- | Construct an evidence for a goal expression automatically
-- using the existing global instance context and
-- local type class assumptions.
resolution :: Exp -> [(Variable, Exp)] -> [(Id, Exp)] -> TCMonad Exp
resolution goal localEnv globalEnv = do
  (t, newGoals) <- rewrite goal localEnv globalEnv
  helper t newGoals
  where
    helper t [] = return t
    helper t ((x, subGoal):res) = do
      t' <- resolution subGoal localEnv globalEnv
      let t'' = apply [(x, t')] t
      helper t'' res

-- | Implement resolution by rewriting, it uses matching to drive the resolution process.
rewrite ::
     Exp -> [(Variable, Exp)] -> [(Id, Exp)] ->
     TCMonad (Exp, [(Variable, Exp)])
rewrite goal localEnv globalEnv = do
  r <- tryLocal goal localEnv
  case r of
    Just (x, t) -> return (Var x, [])
    Nothing -> tryGlobal goal globalEnv
  where
    tryLocal goal [] = return Nothing
    tryLocal goal ((x, t):xs) = do
      let (res, _) = runMatch t goal
      if res
        then return $ Just (x, t)
        else tryLocal goal xs
    tryGlobal goal [] = throwError $ ResolveErr goal
    tryGlobal goal ((k, t):xs) = do
      let (vs, t') = removePrefixes False t
          sub = map (\ (Just x, t) -> (x, MetaVar x)) vs
          t'' = apply sub t'
          (bds1, h) = flattenArrows t''
          bds = map snd bds1
          (r, subs) = runMatch h goal
      if r
        then do
          let bds' = map (apply subs) bds
              vs' =
                map
                  (\a ->
                     case a of
                       (Just x, t) -> (apply subs (Var x), t))
                  vs
              e = makeApp (Const k) vs'
          ns <- mapM (\x -> newName "newGoal") bds'
          let newGoals = zip ns bds'
              e' = foldl AppDict e (map Var ns)
          return (e', newGoals)
        else tryGlobal goal xs
    makeApp h ((t, ty):res)
      | isKind ty = makeApp (AppType h t) res
    makeApp h ((t, ty):res)
      | otherwise = makeApp (AppTm h t) res
    makeApp h [] = h
    newName :: String -> TCMonad Variable
    newName s = do
      r <- newNames [s]
      freshNames r $ \(s':[]) -> return s'

-- | A run function for 'match'.
runMatch :: Exp -> Exp -> (Bool, [(Variable, Exp)])
runMatch e1 e2 = runState (match (erasePos e1) (erasePos e2)) []

-- | Match the first expression against the second, return the result (success or fail) and
-- accumulating substitution.
match :: Exp -> Exp -> State [(Variable, Exp)] Bool
match Unit Unit = return True
match (Base x) (Base y)
  | x == y = return True
  | otherwise = return False
match (LBase x) (LBase y)
  | x == y = return True
  | otherwise = return False
match (Const x) (Const y)
  | x == y = return True
  | otherwise = return False
match (Var x) (Var y)
  | x == y = return True
  | otherwise = return False
-- Note that matching will need to check consistency of the substitution.
match (MetaVar x) t = do
  s <- get
  case lookup x s of
    Nothing -> modify (\s -> (x, t) : s) >> return True
    Just t'
      | t == t' -> return True
      | otherwise -> return False
match (ForceP t) (ForceP t') = match t t'
match (Lift t) (Lift t') = match t t'
match (Bang t _) (Bang t' _) = match t t'
match (App t1 t2) (App t3 t4) = do
  r <- match t1 t3
  if r
    then match t2 t4
    else return False
match (AppP t1 t2) (AppP t3 t4) = do
  r <- match t1 t3
  if r
    then match t2 t4
    else return False
match (AppType t1 t2) (AppType t3 t4) = do
  r <- match t1 t3
  if r
    then match t2 t4
    else return False
match (AppDep t1 t2) (AppDep t3 t4) = do
  r <- match t1 t3
  if r
    then match t2 t4
    else return False
match (AppDict t1 t2) (AppDict t3 t4) = do
  r <- match t1 t3
  if r
    then match t2 t4
    else return False
match (AppTm t1 t2) (AppTm t3 t4) = do
  r <- match t1 t3
  if r
    then match t2 t4
    else return False
match (Tensor t1 t2) (Tensor t3 t4) = do
  r <- match t1 t3
  if r
    then match t2 t4
    else return False
match (Circ t1 t2 _) (Circ t3 t4 _) = do
  r <- match t1 t3
  if r
    then match t2 t4
    else return False
match a b = return False
