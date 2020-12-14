{-# LANGUAGE FlexibleInstances #-}
module ModeResolve where

import Syntax
import SyntacticOperations
import Utils
import Substitution
import Debug.Trace
import Control.Monad
import Nominal
import Text.PrettyPrint
import Data.List
import Prelude hiding((<>))
import qualified Data.MultiSet as S

modeResolution b (M x1 x2 x3) (M y1 y2 y3) =
  let s1 = modeResolve b x1 y1 
      s2 = modeResolve b x2 y2
      s3 = modeResolve b x3 y3
  in if null s1 then Nothing
     else if null s2 then Nothing
          else if null s3 then Nothing
               else Just (head s1, head s2, head s3)
  
  

modeSubst (s1, s2, s3) (M e1 e2 e3) = M e1' e2' e3'
  where e1' = bSubst s1 e1
        e2' = bSubst s2 e2
        e3' = bSubst s3 e3

bSubst s a@(BConst _) = a

bSubst s (BVar x) =
  case lookup x s of
    Nothing -> BVar x
    Just e -> e

bSubst s (BAnd e1 e2) = BAnd (bSubst s e1) (bSubst s e2)

type ModeSubst = [(Variable, BExp)]

type BSubst = (ModeSubst, ModeSubst, ModeSubst)

instance Disp [(Variable, BExp)] where
  display flag l = vcat $ map (\ (x, b) -> (dispRaw x <> text "|->" <> dispRaw b)) l

-- | Resolve two simplified boolean expressions. 
modeResolve :: InEquality -> BExp -> BExp -> [ModeSubst]
modeResolve b e1 e2 = modeResolve' b (simplifyB e1) (simplifyB e2)

data InEquality = Equal | GEq | LEq deriving (Show, Eq)

-- | Reverse the direction of the inequality.
flipSide :: InEquality -> InEquality
flipSide Equal = Equal
flipSide GEq = LEq
flipSide LEq = GEq

-- | Resolve two boolean expressions. The first boolean argument is a flag
-- indicating if it is an inequality >=. 
modeResolve' :: InEquality -> BExp -> BExp -> [ModeSubst]
modeResolve' Equal (BConst x) (BConst y) | x == y = return []
modeResolve' Equal (BConst x) (BConst y) | otherwise = mzero
modeResolve' GEq (BConst x) (BConst y)  =
  if x then return [] else if y then mzero else return []

modeResolve' Equal (BVar x) e = return [(x, e)]
modeResolve' GEq (BVar x) e =
   return [(x, e)] `mplus` return [(x, BConst True)]

modeResolve' Equal e (BVar x) = return [(x, e)]
modeResolve' GEq e (BVar x) =
  return [(x, e)] `mplus` return [(x, BConst False)]

modeResolve' Equal (BConst True) (BAnd e1 e2) =
  do s1 <- modeResolve' Equal (BConst True) e1
     s2 <- modeResolve' Equal (BConst True) (bSubst s1 e2)
     return $ mergeModeSubst s2 s1

modeResolve' GEq (BConst True) (BAnd e1 e2) = return []

modeResolve' b (BAnd e1 e2) (BConst True) =
  do s1 <- modeResolve' Equal (BConst True) e1
     s2 <- modeResolve' Equal (BConst True) (bSubst s1 e2)
     return $ mergeModeSubst s2 s1


modeResolve' Equal (BAnd e1 e2) (BConst False) =
  modeResolve' Equal (BConst False) e1 `mplus` modeResolve' Equal (BConst False) e2

modeResolve' GEq (BAnd e1 e2) (BConst False) = return []


modeResolve' Equal (BConst False) (BAnd e1 e2) =
  modeResolve' Equal (BConst False) e1 `mplus` modeResolve' Equal (BConst False) e2

modeResolve' GEq (BConst False) (BAnd e1 e2) =
  do s1 <- modeResolve' Equal (BConst False) e1
     s2 <- modeResolve' Equal (BConst False) (bSubst s1 e2)
     return $ mergeModeSubst s2 s1


modeResolve' b (BAnd e1 e2) (BAnd e1' e2') =
  do{ s1 <- modeResolve' b e1 e1';
      s2 <- modeResolve' b (bSubst s1 e2) (bSubst s1 e2');
      return $ mergeModeSubst s2 s1} `mplus`
  do{ s1 <- modeResolve' b e1 e2';
      s2 <- modeResolve' b (bSubst s1 e2) (bSubst s1 e1');
      return $ mergeModeSubst s2 s1}

modeResolve' LEq e1 e2 = modeResolve' GEq e2 e1

-- mergeModeSubst s1 s2 | trace ("merging:" ++ (show s1) ++ "with "++ (show s2)) $ False = undefined
mergeModeSubst s1 s2 =
  unionBy (\ (a, _) (b, _) -> a == b) s1
  [(x, bSubst s1 t) | (x, t) <- s2 ]


bSubstitute :: (ModeSubst, ModeSubst, ModeSubst) -> Exp -> Exp           
bSubstitute s a@(Var y) = a
bSubstitute s a@(MetaVar y) = a
bSubstitute s a@(Base _) = a
bSubstitute s a@(LBase _) = a      
bSubstitute s a@(Unit) = a
bSubstitute s a@(Set) = a
bSubstitute s a@(Sort) = a
bSubstitute s a@(Star) = a
bSubstitute s a@(Const _) = a
bSubstitute s (Arrow t t' m) =
  let t1' = bSubstitute s t
      t2' = bSubstitute s t'
  in Arrow t1' t2' (modeSubst s m)
bSubstitute s (WithType t t') =
  let t1' = bSubstitute s t
      t2' = bSubstitute s t'
  in WithType t1' t2'     
bSubstitute s (ArrowP t t') =
  let t1' = bSubstitute s t
      t2' = bSubstitute s t'
  in ArrowP t1' t2'  

bSubstitute s (Imply t t') =
  let t1' = map (bSubstitute s) t
      t2' = bSubstitute s t'
  in Imply t1' t2' 
  
bSubstitute s (Tensor t t') =
  let t1' = bSubstitute s t
      t2' = bSubstitute s t'
  in Tensor t1' t2'

bSubstitute s (Circ t t' m) =
  let t1' = bSubstitute s t
      t2' = bSubstitute s t'
      m' = modeSubst s m
  in Circ t1' t2' m'

bSubstitute s (Bang t m) =
  Bang (bSubstitute s t) (modeSubst s m)

bSubstitute s (Pi bind t mod) =
  open bind $
  \ ys m -> Pi (abst ys (bSubstitute s m))
           (bSubstitute s t) (modeSubst s mod)

bSubstitute s (PiImp bind t mod) =
  open bind $
  \ ys m -> PiImp (abst ys (bSubstitute s m))
           (bSubstitute s t) (modeSubst s mod)

bSubstitute s (PiInt bind t) =
  open bind $
  \ ys m -> PiInt (abst ys (bSubstitute s m))
            (bSubstitute s t) 

bSubstitute s (Exists bind t) =
  open bind $
  \ ys m -> Exists (abst ys (bSubstitute s m))
           (bSubstitute s t) 

bSubstitute s (Forall bind t) =
  open bind $
  \ ys m -> Forall (abst ys (bSubstitute s m))
           (bSubstitute s t) 

bSubstitute s (Mod bind) =
  open bind $
  \ ys m -> Mod (abst ys (bSubstitute s m))


bSubstitute s (App t tm) =
  App (bSubstitute s t) (bSubstitute s tm)

bSubstitute s (AppP t tm) =
  AppP (bSubstitute s t) (bSubstitute s tm)
  
bSubstitute s (AppType t tm) =
  AppType (bSubstitute s t) (bSubstitute s tm)

bSubstitute s (AppTm t tm) =
  AppTm (bSubstitute s t) (bSubstitute s tm)

bSubstitute s (AppDep t tm) =
  AppDep (bSubstitute s t) (bSubstitute s tm)

bSubstitute s (AppDepTy t tm) =
  AppDepTy (bSubstitute s t) (bSubstitute s tm)
  
bSubstitute s (AppDepInt t tm) =
  AppDepInt (bSubstitute s t) (bSubstitute s tm)  
bSubstitute s (AppDict t tm) =
  AppDict (bSubstitute s t) (bSubstitute s tm)


bSubstitute s (Pair t tm) =
  Pair (bSubstitute s t) (bSubstitute s tm)

bSubstitute s (ForceP t) = ForceP (bSubstitute s t)
bSubstitute s (Lift t) = Lift (bSubstitute s t) 

bSubstitute s (Pos p e) = Pos p (bSubstitute s e)
bSubstitute s a@(Case _ _) = a
bSubstitute s a = error ("from bSubstitute: " ++ show (disp a))  


flattenB a@(BConst x) = [a]
flattenB a@(BVar x) = [a]
flattenB (BAnd x y) = flattenB x ++ flattenB y

-- | Simplify the boolean constraint.
simplify (M e1 e2 e3) = M (simplifyB e1) (simplifyB e2) (simplifyB e3)

simplifyB :: BExp -> BExp
simplifyB e =
  let bs = filter (\ x -> x /= BConst True) $ flattenB e
  in if null bs then BConst True else
       case find (\ x -> x == BConst False) bs of
         Just _ -> BConst False
         Nothing -> 
           let bs' = nub bs
               e' = foldr BAnd (head bs') (tail bs')
           in e'

-- | Eliminate excessive boolean mode variables, i.e., replace all the variables that
-- occur once by 0/1 (depending on polarity).
booleanVarElim :: Exp -> Exp
booleanVarElim e =
  let s = getVars ModVars e
      s1 = S.filter (\ x -> S.occur x s == 1) s
  in helper True s1 e
  where elim b s e =
          let evars = flattenB e
              evars' = filter (\ x ->
                                case x of
                                  BVar y -> not (y `S.member` s)
                                  BConst _ -> True
                              ) evars
          in if null evars' then
               BConst b
             else foldr BAnd (head evars') (tail evars')

        helper b s1 (Bang ty (M e1 e2 e3)) =
          let e1' = elim b s1 e1
              e2' = elim b s1 e2
              e3' = elim b s1 e3
              ty' = helper b s1 ty
          in Bang ty' (M e1' e2' e3')
        helper b s1 (Circ s u (M e1 e2 e3)) =
          let e1' = elim b s1 e1
              e2' = elim b s1 e2
              e3' = elim b s1 e3
          in Circ s u (M e1' e2' e3')
        helper b s1 (Arrow t1 t2 (M e1 e2 e3)) =
          let t1' = helper (not b) s1 t1
              t2' = helper b s1 t2
              e1' = elim b s1 e1
              e2' = elim b s1 e2
              e3' = elim b s1 e3
          in Arrow t1' t2' (M e1' e2' e3')
        helper b s1 (Pos e t) =
          let t' = helper b s1 t
          in Pos e t'
        helper b s1 (Tensor t1 t2) =
          let t1' = helper b s1 t1
              t2' = helper b s1 t2
          in Tensor t1' t2'
        helper b s1 (Exists (Abst xs t1) t2) =
          let t1' = helper b s1 t1
              t2' = helper b s1 t2
          in Exists (abst xs t1') t2'
        helper b s1 (Pi (Abst xs t1) t2 (M e1 e2 e3)) =
          let t1' = helper b s1 t1
              t2' = helper (not b) s1 t2
              e1' = elim b s1 e1
              e2' = elim b s1 e2
              e3' = elim b s1 e3
          in Pi (abst xs t1') t2' (M e1' e2' e3')

        helper b s1 (PiImp (Abst xs t1) t2 (M e1 e2 e3)) =
          let t1' = helper b s1 t1 
              t2' = helper (not b) s1 t2
              e1' = elim b s1 e1
              e2' = elim b s1 e2
              e3' = elim b s1 e3
          in PiImp (abst xs t1') t2' (M e1' e2' e3')
        helper b s1 (Forall (Abst xs t1) t2) =
          let t1' = helper b s1 t1
              t2' = helper (not b) s1 t2
          in Forall (abst xs t1') t2'

        helper b s1 (Imply t1 t2) =
          let t2' = helper b s1 t2
          in Imply t1 t2' 
        helper b s1 t = t
        
            
                

