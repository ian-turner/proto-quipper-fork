-- | This module defines various of syntactic operations on the abstract syntax.

module SyntacticOperations where

import Syntax
import Utils
import Substitution

import Nominal
import Data.List

import qualified Data.MultiSet as S
import Data.MultiSet (MultiSet)
import qualified Data.Set as Set
import Data.Set (Set)
import Text.PrettyPrint
import Prelude hiding((<>))
import Data.Map (Map)
import qualified Data.Map as Map

-- | Calculate the set difference of two multi-sets. 
difference' s1 s2 =
  let s2' = S.distinctElems s2
  in helper s1 s2'
   where helper s1 [] = s1
         helper s1 (x:xs) =
           helper (S.deleteAll x s1) xs
                    

-- | Remove vacuous Pi quantifiers.

removeVacuousPi :: Exp -> Exp
removeVacuousPi (Pos p e) = removeVacuousPi e

removeVacuousPi (Forall (Abst xs m) ty) =
  Forall (abst xs $ removeVacuousPi m) (removeVacuousPi ty)

-- Currently there should be no way to construct a vacuous
-- implicit Pi. 
removeVacuousPi (PiImp (Abst xs m) ty mod) =
 PiImp (abst xs $ removeVacuousPi m) (removeVacuousPi ty) mod

removeVacuousPi (Pi (Abst xs m) ty mod) =
  let fvs = getVars All m
      xs' = map (\ x ->
                  if S.member x fvs then
                    Just x
                  else Nothing
                ) xs
      ty' = removeVacuousPi ty
      m' = removeVacuousPi m 
  in foldr (\ x y ->
               case x of
                 Nothing -> Arrow ty' y mod
                 Just x' -> Pi (abst [x'] y) ty' mod) 
     m' xs'
     
removeVacuousPi (Arrow ty1 ty2 mod) =
  Arrow (removeVacuousPi ty1) (removeVacuousPi ty2) mod

removeVacuousPi (Imply ps ty2 mod) =
  Imply ps (removeVacuousPi ty2) mod

removeVacuousPi (Bang ty m) = Bang (removeVacuousPi ty) m
removeVacuousPi a = a

-- | Detect vacuous forall and implicit quantifications,
-- return a list of vacuous variables, their type
-- and the expression that they should occur in. 
vacuousForall :: Exp -> Maybe (Maybe Position, [Variable], Exp, Exp)
vacuousForall (Arrow t1 t2 m) =
  case vacuousForall t1 of
    Nothing -> vacuousForall t2
    Just p -> Just p

vacuousForall (Pi (Abst vs m) ty mod) | isKind ty = vacuousForall m
vacuousForall (Pi (Abst vs m) ty mod) | otherwise = 
  case vacuousForall ty of
    Nothing -> vacuousForall m
    Just p -> Just p

vacuousForall (PiImp bds ty mod) =
  open bds $ \ vs m ->
   let fvs = getVars NoImply m
       vs' = S.fromList vs
       p = S.isSubsetOf vs' fvs
   in if p then
        case vacuousForall ty of
          Nothing -> vacuousForall m
          Just p -> Just p
      else let diff = S.distinctElems $ difference' vs' fvs in
             Just (Nothing, diff, ty, m)

vacuousForall (Imply ts t2 _) = vacuousForall t2
vacuousForall (Bang t2 _) = vacuousForall t2
vacuousForall (Forall bds ty) =
  open bds $ \ vs m ->
   let fvs = getVars NoImply m
       vs' = S.fromList vs
       p = S.isSubsetOf vs' fvs
   in if p then
        case vacuousForall ty of
          Nothing -> vacuousForall m
          Just p -> Just p
      else let diff = S.distinctElems $ difference' vs' fvs in
             Just (Nothing, diff, ty, m)

vacuousForall (Pos p e) =
  case vacuousForall e of
    Nothing -> Nothing
    Just (Nothing, vs, t, m) -> Just (Just p, vs, t, m)
    Just r -> Just r

vacuousForall a = Nothing

-- | Flags for getting various of variables.
data VarSwitch =
  All -- ^ Get all the variables. 
  | NoImply
  -- ^ Does not include the variables that occur
  -- in the type class constraints. 
  | ModVars -- ^ Get modality variables.
  deriving (Show, Eq)

-- | Get a set of variables from an expression according to the flag.
getVars :: VarSwitch -> Exp -> MultiSet Variable
getVars All a@(Var x) = S.insert x S.empty
getVars All a@(MetaVar x) = S.insert x S.empty

getVars NoImply a@(Var x) = S.insert x S.empty
getVars NoImply a@(MetaVar x) = S.insert x S.empty

getVars ModVars (Var x) = S.empty
getVars ModVars (MetaVar x) = S.empty

getVars b (Base _) = S.empty
getVars b (LBase _) = S.empty
getVars b (Const _) = S.empty
getVars b (Unit) = S.empty
getVars b (Star) = S.empty
getVars b (Sort) = S.empty
getVars b (Set) = S.empty
getVars b (UnBox) = S.empty
getVars b (Reverse) = S.empty
getVars b (Controlled) = S.empty
getVars b (WithComputed) = S.empty
getVars b (Dynlift) = S.empty
getVars b (App t t') =
  getVars b t `S.union` getVars b t'
getVars b (AppP t t') =
  getVars b t `S.union` getVars b t'  
getVars b (AppType t t') =
  getVars b t `S.union` getVars b t'
getVars b (AppDep t t') =
  getVars b t `S.union` getVars b t'
getVars b (AppDepTy t t') =
  getVars b t `S.union` getVars b t'  
getVars b (AppDepInt t t') =
  getVars b t `S.union` getVars b t'  
getVars b (AppDict t t') =
  getVars b t `S.union` getVars b t'    
getVars b (AppTm t t') =
  getVars b t `S.union` getVars b t'

getVars b (WithType t t') =
  getVars b t `S.union` getVars b t'

getVars b (Tensor ty tm) =
  getVars b ty `S.union` getVars b tm

getVars ModVars (Arrow ty tm m) =
  getBVars m `S.union` getVars ModVars ty `S.union` getVars ModVars tm

getVars b (Arrow ty tm mod) =
  getVars b ty `S.union` getVars b tm

getVars b (ArrowP ty tm) =
  getVars b ty `S.union` getVars b tm  

getVars NoImply (Imply ty tm _) = getVars NoImply tm
getVars ModVars (Imply ty t m) =
  getBVars m `S.union`
  (S.unions $ map (getVars ModVars) ty) `S.union` getVars ModVars t

getVars b (Imply ty tm _) =
  (S.unions $ map (getVars b) ty) `S.union` getVars b tm

getVars ModVars (Bang t m) =
  getBVars m `S.union` getVars ModVars t
  
getVars b (Bang t _) = getVars b t

getVars b@ModVars (Pi bind t mod) =
  getBVars mod `S.union` getVars b t `S.union`
  (open bind $ \ xs m -> getVars b m)

getVars b (Pi bind t _) =
  getVars b t `S.union`
  (open bind $ \ xs m -> getVars b m `difference'` S.fromList xs)

getVars b@ModVars (PiImp bind t mod) =
  getBVars mod `S.union` getVars b t `S.union`
  (open bind $ \ xs m -> getVars b m)

getVars b (PiImp bind t _) =
  getVars b t `S.union`
  (open bind $ \ xs m -> getVars b m `difference'` S.fromList xs)
  
getVars b (PiInt bind t) =
  getVars b t `S.union`
  (open bind $ \ xs m -> getVars b m `difference'` S.fromList xs)  

getVars b (Exists bind t) =
  getVars b t `S.union`
  (open bind $ \ xs m -> getVars b m `difference'` S.fromList [xs])

getVars b (Lam bind) =
  open bind $ \ xs m -> getVars b m `difference'` S.fromList xs
  
getVars b (LamAnn ty bind) =
  open bind $ \ xs m -> (getVars b m `difference'` S.fromList xs)
  `S.union` getVars b ty
                        
getVars b (LamAnnP ty bind) =
  open bind $ \ xs m -> (getVars b m `difference'` S.fromList xs)
  `S.union` getVars b ty                        
                        
getVars b (LamP bind) =
  open bind $ \ xs m -> getVars b m `difference'` S.fromList xs  

getVars b (LamType bind) =
  open bind $ \ xs m -> getVars b m `difference'` S.fromList xs

getVars b (LamDep bind) =
  open bind $ \ xs m -> getVars b m `difference'` S.fromList xs

getVars b (LamDepTy bind) =
  open bind $ \ xs m -> getVars b m `difference'` S.fromList xs
  
getVars b (LamDepInt bind) =
  open bind $ \ xs m -> getVars b m `difference'` S.fromList xs
  
getVars b (LamTm bind) =
  open bind $ \ xs m -> getVars b m `difference'` S.fromList xs
getVars b (LamDict bind) =
  open bind $ \ xs m -> getVars b m `difference'` S.fromList xs
  
                        
getVars b (Forall bind ty) =
  open bind $ \ xs m -> S.union (getVars b m `difference'` S.fromList xs) (getVars b ty)

getVars b (Mod bind) =
  open bind $ \ xs m -> getVars b m `difference'` S.fromList xs

getVars ModVars (Circ t u m) = getBVars m
getVars b (Circ t u m) = S.union (getVars b t) (getVars b u)
getVars b (Pair ty tm) =
  getVars b ty `S.union` getVars b tm

getVars b (Let t bind) =
  getVars b t `S.union`
  (open bind $ \ x m -> S.deleteAll x (getVars b m))

getVars b (LetPair t bind) =
  getVars b t `S.union`
  (open bind $ \ xs m -> (difference' (getVars b m) (S.fromList xs)))


getVars b (LetPat t (Abst ps m)) =
  let (bvs, fvs) = pvar ps in
  (getVars b t `S.union` fvs `S.union` getVars b m)
  `difference'` bvs
  where pvar (PApp _ []) = (S.empty, S.empty)
        pvar (PApp k ((Right x):xs)) =
          let (bv, fv) = pvar (PApp k xs) in
          (S.insert x bv, fv)
        pvar (PApp k ((Left (NoBind x)):xs)) =
          let (bv, fv) = pvar (PApp k xs)
              fbv = getVars b x
          in (bv, S.union fbv fv)

getVars b (Force t) = getVars b t
getVars b (ForceP t) = getVars b t
getVars b (Box) = S.empty
getVars b (ExBox) = S.empty
getVars b (Lift t) = getVars b t
getVars b (Case t (B brs)) =
  getVars b t `S.union` S.unions (map helper brs)
  where helper bind = open bind $ \ ps m ->
          let (bvs, fvs) = pvar ps in
          (fvs `S.union` getVars b m) `difference'` bvs
        pvar (PApp _ []) = (S.empty, S.empty)
        pvar (PApp k ((Right x):xs)) =
          let (bv, fv) = pvar (PApp k xs) in
          (S.insert x bv, fv)
        pvar (PApp k ((Left (NoBind x)):xs)) =
          let (bv, fv) = pvar (PApp k xs)
              fbv = getVars b x
          in (bv, S.union fbv fv)
getVars b (Pos p e) = getVars b e
getVars b a = error $ "from getVars  " ++ show a

-- | Get the modality variables.

getBVars (M e1 e2 e3) =
  getBVars' e1 `S.union` getBVars' e2 `S.union` getBVars' e3
  where 
    getBVars' (BVar x) = S.insert x S.empty
    getBVars' (BConst _) = S.empty
    getBVars' (BAnd e1 e2) = S.union (getBVars' e1) (getBVars' e2)



-- | Flatten a n-tuple into a list.
unPair :: (Num a, Ord a) => a -> Exp -> Maybe [Exp]
unPair n (Pos _ e) = unPair n e
unPair n (Pair x y) | n == 2 = Just [x, y]
unPair n (Pair x y) | n > 2 =
  do r <- unPair (n-1) x
     return (r++[y])
unPair _ _ = Nothing

-- | Flatten a n-value-tuple into a list.
unVPair :: (Num t, Ord t) => t -> Value -> Maybe [Value]
unVPair n (VPair x y) | n == 2 = Just [x, y]
unVPair n (VPair x y) | n > 2 =
  do r <- unVPair (n-1) x
     return (r++[y])
unVPair _ _ = Nothing

-- | Flatten a multi-tensor into a list.
unTensor :: (Num a, Ord a) => a -> Exp -> Maybe [Exp]
unTensor n (Pos _ e) = unTensor n e
unTensor n (Tensor x y) | n == 2 = Just [x, y]
unTensor n (Tensor x y) | n > 2 =
  do r <- unTensor (n-1) x
     return (r++[y])
unTensor _ _ = Nothing

flattenTensor (Pos _ e) = flattenTensor e
flattenTensor (Tensor x y) = 
  flattenTensor x ++ flattenTensor y
flattenTensor a = [a]

-- | Flatten a type expression into bodies and head,
-- with variables intact.
-- e.g. @flattenArrows ((x : A1) -> A2 -> (P) => H)@ produces
-- @([(Just x, A1), (Nothing, A2), (Nothing, P)], H)@

flattenArrows :: Exp -> ([(Maybe Variable, Exp)], Exp)
flattenArrows (Pos p a) = flattenArrows a
flattenArrows (Mod (Abst vs a)) = flattenArrows a
flattenArrows (Arrow t1 t2 _) =
  let (res, h) = flattenArrows t2 in
  ((Nothing, t1):res, h)
flattenArrows (ArrowP t1 t2) =
  let (res, h) = flattenArrows t2 in
  ((Nothing, t1):res, h)  
flattenArrows (Pi (Abst vs t2) t1 _) = 
  let (res, h) = flattenArrows t2 in
  (map (\ x -> (Just x, t1)) vs ++ res, h)
flattenArrows (PiImp (Abst vs t2) t1 _) = 
  let (res, h) = flattenArrows t2 in
  (map (\ x -> (Just x, t1)) vs ++ res, h)
  
flattenArrows (PiInt (Abst vs t2) t1) = 
  let (res, h) = flattenArrows t2 in
  (map (\ x -> (Just x, t1)) vs ++ res, h)  

flattenArrows (Imply t1 t2 _) =
  let (res, h) = flattenArrows t2 in
  ((map (\ x -> (Nothing, x)) t1) ++ res, h)  
 
flattenArrows a = ([], a)  

  
-- | Remove the leading forall quantifiers,
-- and class quantifiers if flag is True.
removePrefixes :: Bool -> Exp -> ([(Maybe Variable, Exp)], Exp)
removePrefixes flag (Forall bd ty) =
  open bd $ \ vs m ->
  let vs' = map (\ x -> (Just x, ty)) vs
      (xs, m') = removePrefixes flag m
  in (vs' ++ xs, m')
removePrefixes flag (Imply bd ty _) | flag =
  let vs' = map (\ x -> (Nothing, x)) bd
      (xs, m') = removePrefixes flag ty
  in (vs' ++ xs, m')
removePrefixes flag (Pos _ a) = removePrefixes flag a
removePrefixes flag a = ([], a)

-- | Flatten an applicative expression. It can
-- be applied to both type and term expressions.
-- It returns 'Nothing' if the input is not
-- in applicative form. 'Left' indicates the identifier is
-- a term constructor, 'Right' 
-- indicates the identifier is a type constructor.
-- It also returns a list of arguments.

flatten :: Exp -> Maybe (Either Id Id, [Exp])
flatten (Base id) = return (Right id, [])
flatten (LBase id) = return (Right id, [])
flatten (Const id) = return (Left id, [])
flatten (App t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])
flatten (AppP t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])     
flatten (AppDep t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])
flatten (AppDepTy t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])     
flatten (AppDict t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])          
flatten (AppType t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])          
flatten (AppTm t1 t2) =
  do (id, args) <- flatten t1
     return (id, args ++ [t2])          
flatten (Pos p e) = flatten e
flatten _ = Nothing

-- | Flatten an applicative value. 
vflatten :: Value -> Maybe (Either Id Id, [Value])
vflatten (VBase id) = return (Right id, [])
vflatten (VLBase id) = return (Right id, [])
vflatten (VConst id) = return (Left id, [])
vflatten (VApp t1 t2) =
  do (id, args) <- vflatten t1
     return (id, args ++ [t2])
vflatten _ = Nothing

unwindVal (VApp t1 t2) =
          let (h, args) = unwindVal t1
          in (h, args++[t2])
unwindVal a = (a, [])

-- | Determine whether an expression is a kind expression.
-- Note that we allow
-- dependent kind such as: @(a : Type) -> a -> Type@.
isKind :: Exp -> Bool
isKind (Set) = True
isKind (Arrow k1 k2 _) = isKind k2
isKind (Pi b ty _) = open b $ \ vs b' -> isKind b'
isKind (Forall b ty) = open b $ \ vs b' -> isKind b'
isKind (Pos _ e) = isKind e
isKind _ = False

-- | Erase the positions from an expression.
erasePos :: Exp -> Exp
erasePos (Pos _ e) = erasePos e
erasePos (Unit) = Unit
erasePos (Set) = Set
erasePos (Sort) = Sort
erasePos Star = Star
erasePos a@(Var x) = a
erasePos a@(MetaVar x) = a
erasePos a@(Base x) = a
erasePos a@(LBase x) = a
erasePos a@(Const x) = a
erasePos (App e1 e2) = App (erasePos e1) (erasePos e2)
erasePos (AppP e1 e2) = AppP (erasePos e1) (erasePos e2)
erasePos (AppType e1 e2) = AppType (erasePos e1) (erasePos e2)
erasePos (AppTm e1 e2) = AppTm (erasePos e1) (erasePos e2)
erasePos (AppDep e1 e2) = AppDep (erasePos e1) (erasePos e2)
erasePos (AppDepTy e1 e2) = AppDepTy (erasePos e1) (erasePos e2)
erasePos (AppDepInt e1 e2) = AppDepInt (erasePos e1) (erasePos e2)
erasePos (AppDict e1 e2) = AppDict (erasePos e1) (erasePos e2)
erasePos (Tensor e1 e2) = Tensor (erasePos e1) (erasePos e2)
erasePos (WithType e1 e2) = WithType (erasePos e1) (erasePos e2)
erasePos (Pair e1 e2) = Pair (erasePos e1) (erasePos e2)
erasePos (Arrow e1 e2 m) = Arrow (erasePos e1) (erasePos e2) m
erasePos (ArrowP e1 e2) = ArrowP (erasePos e1) (erasePos e2)
erasePos (Imply e1 e2 m) = Imply (map erasePos e1) (erasePos e2) m
erasePos (Bang e m) = Bang (erasePos e) m
erasePos (UnBox) = UnBox
erasePos (Reverse) = Reverse
erasePos (Controlled) = Controlled
erasePos (WithComputed) = WithComputed
erasePos (Dynlift) = Dynlift
erasePos (Box) = Box
erasePos a@(ExBox) = a
erasePos (Lift e) = Lift (erasePos e) 

erasePos (Force e) = Force $ erasePos e
erasePos (ForceP e) = ForceP $ erasePos e
erasePos (Circ e1 e2 m) = Circ (erasePos e1) (erasePos e2) m
erasePos (Pi (Abst vs b) e m) = Pi (abst vs (erasePos b)) (erasePos e) m
erasePos (PiImp (Abst vs b) e m) =
  PiImp (abst vs (erasePos b)) (erasePos e) m

erasePos (PiInt (Abst vs b) e) =
  PiInt (abst vs (erasePos b)) (erasePos e)
erasePos (Exists (Abst vs b) e) =
  Exists (abst vs (erasePos b)) (erasePos e)
erasePos (Forall (Abst vs b) e) =
  Forall (abst vs (erasePos b)) (erasePos e)
erasePos (Mod (Abst vs b)) = Mod (abst vs (erasePos b))
erasePos (Lam (Abst vs b)) = Lam (abst vs (erasePos b))

erasePos (LamAnn ty (Abst vs b)) =
  LamAnn (erasePos ty) (abst vs (erasePos b))

erasePos (LamAnnP ty (Abst vs b)) =
  LamAnnP (erasePos ty) (abst vs (erasePos b))
  
erasePos (LamP (Abst vs b)) = LamP (abst vs (erasePos b)) 
erasePos (LamTm (Abst vs b)) = LamTm (abst vs (erasePos b))
erasePos (LamDep (Abst vs b)) = LamDep (abst vs (erasePos b))
erasePos (LamDepTy (Abst vs b)) = LamDepTy (abst vs (erasePos b)) 
erasePos (LamType (Abst vs b)) = LamType (abst vs (erasePos b))
erasePos (LamDict (Abst vs b)) = LamDict (abst vs (erasePos b))

erasePos (Let m (Abst vs b)) = Let (erasePos m) (abst vs (erasePos b)) 
erasePos (LetPair m (Abst xs b)) =
  LetPair (erasePos m) (abst xs (erasePos b)) 
erasePos (LetPat m (Abst (PApp id vs) b)) =
  LetPat (erasePos m) (abst (PApp id vs) (erasePos b))
erasePos (Case e (B br)) = Case (erasePos e) (B (map helper br))
  where helper (Abst p m) = abst p (erasePos m)
erasePos e = error $ "from erasePos " ++ (show $ disp e)


-- | Determine if an expression is a constructor.
isConst :: Exp -> Bool
isConst (Const _) = True
isConst (Pos p e) = isConst e
isConst _ = False

-- | Determine if a value is a circuit.
isCirc :: Value -> Bool
isCirc (Wired _) = True
isCirc _ = False


-- | Flags for the 'unwind' function.
data UnwindFlag = AppFlag | AppPFlag | AppDepIntFlag
                | AppDepFlag | AppDictFlag 
  deriving (Show, Eq)


-- | Unwind an applicative depending on the 'UnwindFlag'.
unwind a (Pos _ e) = unwind a e

unwind a@(AppFlag) (App t1 t2) =
  unwindHelper a t1 t2

unwind a@(AppPFlag) (AppP t1 t2) =
  unwindHelper a t1 t2

unwind a@(AppDepIntFlag) (AppDepInt t1 t2) =
  unwindHelper a t1 t2

unwind a@(AppDepFlag) (AppDep t1 t2) =
  unwindHelper a t1 t2

unwind a@(AppDictFlag) (AppDict t1 t2) =
  unwindHelper a t1 t2

unwind _ b = (b, [])

-- | Unwind application. A helper function for 'unwind'.
unwindHelper :: UnwindFlag -> Exp -> Exp -> (Exp, [Exp])
unwindHelper a t1 t2 =
  let (h, args) = unwind a t1
   in (h, args++[t2])
      

-- | Obtain a position information if the expression has one at the top level.
obtainPos :: Exp -> Maybe Position
obtainPos (Pos p e) = Just p
obtainPos _ = Nothing

-- | Obtain the labels from a simple term.
getWires :: Value -> [Label]
getWires (VLabel x) = [x]
getWires (VConst _) = []
getWires VStar = []
getWires (VApp e1 e2) = getWires e1 ++ getWires e2
getWires (VPair e1 e2) = getWires e1 ++ getWires e2
getWires a =
  error $ "applying getWires function to an ill-formed template:" ++
  (show $ disp a)


-- | Check if a variable is used explicitly for runtime evaluation.
isExplicit :: Variable -> Exp -> Bool
isExplicit s (App t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (WithType t tm) =
  (isExplicit s t) 

isExplicit s (Arrow t tm _) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (AppP t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (AppType t tm) =
  (isExplicit s t)
isExplicit s (AppTm t tm) =
   (isExplicit s t)

isExplicit s (AppDep t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (AppDepTy t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (AppDepInt t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (AppDict t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (Lam bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamAnn ty bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamAnnP ty bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamDict bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamP bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamType bind) =
  open bind $
  \ ys m -> isExplicit s m 

isExplicit s (LamTm bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamDep bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (LamDepTy bind) =
  open bind $
  \ ys m -> isExplicit s m

isExplicit s (Pair t tm) =
   (isExplicit s t) || (isExplicit s tm)

isExplicit s (Tensor t tm) =
   (isExplicit s t) || (isExplicit s tm)
   
isExplicit s (Force t) = (isExplicit s t)
isExplicit s (ForceP t) = (isExplicit s t)
isExplicit s (Lift t) = (isExplicit s t)
       
isExplicit s (Let m bd) =
  if isExplicit s m then True
  else open bd $ \ y b -> isExplicit s b

isExplicit s (LetPair m bd) =
  if isExplicit s m then True
  else 
    open bd $ \ ys b -> isExplicit s b

isExplicit s (LetPat m bd) =
  if isExplicit s m then True
  else open bd $ \ ps b ->  isExplicit s b

isExplicit s (Case tm (B br)) =
  if isExplicit s tm then True
  else or (helper' br)
  where helper' ps =
          map (\ b -> open b $
                       \ ys m ->
                        (isExplicit s m))
          ps

isExplicit s (Pos p e) = isExplicit s e
isExplicit s (Var x) = s == x
isExplicit s (MetaVar x) = s == x 
isExplicit s Star = False
isExplicit s Box = False
isExplicit s UnBox = False
isExplicit s ExBox = False
isExplicit s Reverse = False
isExplicit s Controlled = False
isExplicit s WithComputed = False
isExplicit s Dynlift = False
isExplicit s Unit = False
isExplicit s Set = False
isExplicit s (Base _) = False
isExplicit s (LBase _) = False
isExplicit s (Const _) = False

isExplicit s a = error $ "from isExplicit:" ++ (show $ disp a)


-- | Count the number of gates in a circuit.
gateCount :: Maybe String -> Value -> Int
gateCount Nothing (Wired (Abst _ morph)) = length (gates morph)
gateCount (Just n) (Wired (Abst _ morph)) =
  helper n (gates morph) 0
  where helper n [] m = m
        helper n (Gate d _ _ _ _ _ _:s) m
          | getName d == n = helper n s (m+1)
          | otherwise = helper n s m
        

-- | Relabel each gate to ensure the input and output
-- wires have the same label names.  It assumes each gate is regular,
-- i.e., input and output should have the same arity for all the
-- non-terminal and non-initial gates. It tries to re-use the label
-- names once a label is terminated, this is reflected in the input ['Label']. 

refresh_gates :: Map Label Label -> [Gate] -> [Label] ->
                 ([Gate], Map Label Label)
refresh_gates m [] s = ([], m)
refresh_gates m (Gate name [] input VStar VStar b inv: gs) s
  | getName name == "Term0" || getName name == "Term1" =
    let newInput = renameTemp input m
        (gs', newMap') = refresh_gates m gs (getWires newInput ++ s)
    in (Gate name [] newInput VStar VStar b inv: gs', newMap')

refresh_gates m (Gate name [] input VStar VStar b inv : gs) s
  | getName name == "Discard" =
    let newInput = renameTemp input m
        (gs', newMap') = refresh_gates m gs (getWires newInput ++ s)
    in (Gate name [] newInput VStar VStar b inv: gs', newMap')

refresh_gates m (Gate name [] VStar output VStar b inv: gs) []
  | getName name == "Init0" || getName name == "Init1" =
    let (gs', newMap') = refresh_gates m gs []
    in (Gate name [] VStar output VStar b inv : gs', newMap')

refresh_gates m (Gate name [] VStar output VStar b inv : gs) (h:s)
  | getName name == "Init0" || getName name == "Init1" =
    let x:[] = getWires output
        m' = m `Map.union` Map.fromList [(x, h)]
        (gs', newMap') = refresh_gates m' gs s
    in (Gate name [] VStar (VLabel h) VStar b inv : gs', newMap')

-- All the other possible initialization.
refresh_gates m (Gate name vs VStar output ctrl b inv : gs) s =
  let (gs', newMap') = refresh_gates m gs s
  in (Gate name vs VStar output ctrl b inv : gs', newMap')

-- All the other possible termination.
refresh_gates m (Gate name vs input VStar ctrl b inv : gs) s =
  let input' = renameTemp input m
      (gs', newMap') = refresh_gates m gs s
  in (Gate name vs input' VStar ctrl b inv : gs', newMap')


refresh_gates m (Gate name vs input output ctrl b inv : gs) s =
  let newInput = renameTemp input m
      newCtrl = renameTemp ctrl m
      outWires = getWires output
      newOutput = newInput
      ins = getWires newInput
      newMap = m `Map.union` Map.fromList (zip outWires ins)
      (gs', newMap') = refresh_gates newMap gs s
  in (Gate name vs newInput newOutput newCtrl b inv : gs', newMap')

-- | Check whether a value is a boolean constant.
isBool :: Value -> Bool
isBool (VConst x) | getName x == "True" = True
isBool (VConst x) | getName x == "False" = True
isBool _ = False

-- | Convert a boolean value to 'Bool'. It is an error to call this
-- with a value that is not a boolean constant.
toBool :: Value -> Bool
toBool (VConst x) | getName x == "True" = True
toBool (VConst x) | getName x == "False" = False

-- | Convert a value to a natural number. It is an error to call this
-- with a value that is not a Peano number. This is used for printing
-- the parameters of a gate.
toNum (VConst x) | getName x == "Z" = 0
toNum (VApp (VConst s) n) | getName s == "S" =
  toNum n + 1


-- | Rename the labels of a morphism according to a binding.
rename :: Morphism -> Map Label Label -> Morphism            
rename morph m =
  let ins = input morph
      outs = output morph
      gs = gates morph
      ins' = renameTemp ins m
      outs' = renameTemp outs m
      gs' = renameGs gs m
  in Morphism ins' gs' outs'

-- | Rename a template value according to a binding.
renameTemp :: Value -> Map Label Label -> Value
renameTemp (VLabel x) m =
  case Map.lookup x m of
    Nothing -> (VLabel x)
    Just y -> VLabel y
renameTemp a@(VConst _) m = a
renameTemp VStar m = VStar
renameTemp (VApp e1 e2) m = VApp (renameTemp e1 m) (renameTemp e2 m)
renameTemp (VPair e1 e2) m = VPair (renameTemp e1 m) (renameTemp e2 m)
renameTemp a m =
  error "applying renameTemp function to an ill-formed template"     

-- | Rename a list of gates according to a binding.
renameGs :: [Gate] -> Map Label Label -> [Gate]
renameGs gs m = map helper gs
  where helper (Gate id params ins outs ctrls b inv) =
          Gate id params (renameTemp ins m) (renameTemp outs m)
          (renameTemp ctrls m) b inv

-- | Generate a fresh modality.
freshMode :: [String] -> Modality
freshMode s =
  freshNames (take 3 s) $
  \ [x, y, z] -> M (BVar x) (BVar y) (BVar z)

freshMode2 :: [String] -> Modality
freshMode2 s =
  freshNames (take 2 s) $
  \ [y, z] -> M (BConst True) (BVar y) (BVar z)

-- | Bind all the free mod variables.
abstractMode :: Exp -> Exp
abstractMode e =
  let s = S.distinctElems $ getVars ModVars e
  in if null s then e else Mod (abst s e)

isBuildIn Reverse = True
isBuildIn Controlled = True
isBuildIn WithComputed = True
isBuildIn Dynlift = True
isBuildIn Box = True
isBuildIn UnBox = True
isBuildIn ExBox = True
isBuildIn (Pos _ e) = isBuildIn e
isBuildIn _ = False


-- | Compare equality for types, ignore modality. 
noModEq :: Exp -> Exp -> Bool
noModEq (Var x) (Var y) = x == y
noModEq (Const x) (Const y) = x == y
noModEq (LBase x) (LBase y) = x == y
noModEq (Base x) (Base y) = x == y
noModEq (Arrow x1 x2 _) (Arrow y1 y2 _) =
  (noModEq x1 y1) && (noModEq x2 y2)
noModEq (ArrowP x1 x2) (ArrowP y1 y2) =
  (noModEq x1 y1) && (noModEq x2 y2)
noModEq (App x1 x2) (App y1 y2) =
  (noModEq x1 y1) && (noModEq x2 y2)
noModEq (AppType x1 x2) (AppType y1 y2) =
  (noModEq x1 y1) && (noModEq x2 y2)
noModEq (AppTm x1 x2) (AppTm y1 y2) =
  (noModEq x1 y1) && (noModEq x2 y2)
  
noModEq (AppP x1 x2) (AppP y1 y2) =
  (noModEq x1 y1) && (noModEq x2 y2)
noModEq (AppDict x1 x2) (AppDict y1 y2) =
  (noModEq x1 y1) && (noModEq x2 y2)
noModEq (AppDep x1 x2) (AppDep y1 y2) =
  (noModEq x1 y1) && (noModEq x2 y2)
noModEq (AppDepInt x1 x2) (AppDepInt y1 y2) =
  (noModEq x1 y1) && (noModEq x2 y2)
noModEq (AppDepTy x1 x2) (AppDepTy y1 y2) =
  (noModEq x1 y1) && (noModEq x2 y2)
  
noModEq (Tensor x1 x2) (Tensor y1 y2) =
  (noModEq x1 y1) && (noModEq x2 y2)

noModEq (Exists (Abst a x1) x2) (Exists (Abst b y1) y2) =
  (noModEq (apply [(a, Var b)] x1) y1) && (noModEq x2 y2)  
noModEq (Pair x1 x2) (Pair y1 y2) =
  (noModEq x1 y1) && (noModEq x2 y2)

noModEq (Imply x1 x2 _) (Imply y1 y2 _) =
  (and $ zipWith noModEq x1 y1) && (noModEq x2 y2)

noModEq (Bang x1 x2) (Bang y1 y2) =
  noModEq x1 y1

noModEq (ForceP x1) (ForceP y1) =
  noModEq x1 y1

noModEq (Force x1) (Force y1) =
  noModEq x1 y1

noModEq (Lift x1) (Lift y1) =
  noModEq x1 y1

noModEq (Circ x1 x2 _) (Circ y1 y2 _) =
  (noModEq x1 y1) && (noModEq x2 y2)

noModEq (Exists (Abst a x1) x2) (Exists (Abst b y1) y2) =
  (noModEq (apply [(a, Var b)] x1) y1) && (noModEq x2 y2)  

noModEq (Pi (Abst as x1) x2 _) (Pi (Abst bs y1) y2 _) =
  let sub = zip as (map Var bs) 
  in (noModEq (apply sub x1) y1) && (noModEq x2 y2)  

noModEq (PiInt (Abst as x1) x2) (PiInt (Abst bs y1) y2) =
  let sub = zip as (map Var bs) 
  in (noModEq (apply sub x1) y1) && (noModEq x2 y2)  

noModEq (PiImp (Abst as x1) x2 _) (PiImp (Abst bs y1) y2 _) =
  let sub = zip as (map Var bs) 
  in (noModEq (apply sub x1) y1) && (noModEq x2 y2)  

noModEq (Forall (Abst as x1) x2) (Forall (Abst bs y1) y2) =
  let sub = zip as (map Var bs) 
  in (noModEq (apply sub x1) y1) && (noModEq x2 y2)  

noModEq Set Set = True
noModEq Unit Unit = True
noModEq Star Star = True
noModEq (Lam (Abst xs e1)) (Lam (Abst ys e2)) =
  let sub = zip xs (map Var ys) 
  in noModEq (apply sub e1) e2
noModEq (LamP (Abst xs e1)) (LamP (Abst ys e2)) =
  let sub = zip xs (map Var ys) 
  in noModEq (apply sub e1) e2

noModEq (LamDict (Abst xs e1)) (LamDict (Abst ys e2)) =
  let sub = zip xs (map Var ys) 
  in noModEq (apply sub e1) e2

noModEq (LamDep (Abst xs e1)) (LamDep (Abst ys e2)) =
  let sub = zip xs (map Var ys) 
  in noModEq (apply sub e1) e2

noModEq (LamDepInt (Abst xs e1)) (LamDepInt (Abst ys e2)) =
  let sub = zip xs (map Var ys) 
  in noModEq (apply sub e1) e2

noModEq (LamDepTy (Abst xs e1)) (LamDepTy (Abst ys e2)) =
  let sub = zip xs (map Var ys) 
  in noModEq (apply sub e1) e2

noModEq (LamType (Abst xs e1)) (LamType (Abst ys e2)) =
  let sub = zip xs (map Var ys) 
  in noModEq (apply sub e1) e2

noModEq (LamTm (Abst xs e1)) (LamTm (Abst ys e2)) =
  let sub = zip xs (map Var ys) 
  in noModEq (apply sub e1) e2


noModEq (Case e (B br)) (Case e' (B br')) =
  let r1 = noModEq e e'
      r2 = and $ zipWith helper br br'
  in r1 && r2
  where helper (Abst (PApp id1 ps1) e1) (Abst (PApp id2 ps2) e2) =
          (id1 == id2) && helper2 ps1 e1 ps2 e2
        helper2 ((Left (NoBind a1)):ps1) e1 ((Left (NoBind a2)):ps2) e2 =
          if noModEq a1 a2 then
            helper2 ps1 e1 ps2 e2
            else False
        helper2 ((Right a1):ps1) e1 ((Right a2):ps2) e2 =
          helper2 ps1 (apply [(a1, Var a2)] e1) ps2 e2
        helper2 [] e1 [] e2 = noModEq e1 e2

noModEq (Let e1 (Abst a1 b1)) (Let e2 (Abst a2 b2)) =
  noModEq e1 e2 && noModEq (apply [(a1, Var a2)] b1) b2

noModEq (LetPair e1 (Abst a1 b1)) (LetPair e2 (Abst a2 b2)) =
  let sub = zip a1 (map Var a2)
  in noModEq e1 e2 && noModEq (apply sub b1) b2

noModEq (LetPat e1 (Abst (PApp id1 p1) b1)) (LetPat e2 (Abst (PApp id2 p2) b2)) =
  noModEq e1 e2 && id1 == id2 && helper2 p1 b1 p2 b2 
  where helper2 ((Left (NoBind a1)):ps1) e1 ((Left (NoBind a2)):ps2) e2 =
          if noModEq a1 a2 then
            helper2 ps1 e1 ps2 e2
            else False
        helper2 ((Right a1):ps1) e1 ((Right a2):ps2) e2 =
          helper2 ps1 (apply [(a1, Var a2)] e1) ps2 e2
        helper2 [] e1 [] e2 = noModEq e1 e2

noModEq a b = False
  -- error $ show $ text "from noModEq:" <> disp a <> text ":" <> disp b



deMeta :: [Variable] -> Exp -> Exp
deMeta vars (Pos p e) = Pos p (deMeta vars e)
deMeta vars (Unit) = Unit
deMeta vars (Set) = Set
deMeta vars Star = Star
deMeta vars Sort = Sort
deMeta vars a@(Var x) = a
deMeta vars a@(MetaVar x) =
  if x `elem` vars then Var x
  else error $ "unbound metavar:" ++ (show $ disp x)
deMeta vars a@(Base x) = a
deMeta vars a@(LBase x) = a
deMeta vars a@(Const x) = a

deMeta vars (App e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in App e1' e2'

deMeta vars (AppP e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppP e1' e2'

deMeta vars (WithType e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in WithType e1' e2'

deMeta vars (AppType e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppType e1' e2'  

deMeta vars (AppTm e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppTm e1' e2'  

deMeta vars (AppDep e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppDep e1' e2'  

deMeta vars (AppDepInt e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppDepInt e1' e2'  

deMeta vars (AppDepTy e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppDepTy e1' e2'  

deMeta vars (AppDict e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in AppDict e1' e2'  

deMeta vars (Tensor e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in Tensor e1' e2'
  
deMeta vars (Pair e1 e2) = 
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in  Pair e1' e2'

deMeta vars (Arrow e1 e2 m) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in Arrow e1' e2' m

deMeta vars (ArrowP e1 e2) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in ArrowP e1' e2'

deMeta vars (Imply e1 e2 m) =
  let e1' = map (deMeta vars) e1
      e2' = deMeta vars e2
  in Imply e1' e2' m

deMeta vars (Bang e m) = Bang (deMeta vars e) m
deMeta vars (UnBox) = UnBox
deMeta vars (Reverse) = Reverse
deMeta vars (Controlled) = Controlled
deMeta vars (WithComputed) = WithComputed
deMeta vars (Dynlift) = Dynlift
deMeta vars (Box) = Box 
deMeta vars (ExBox) = ExBox 
deMeta vars (Lift e) = Lift (deMeta vars e) 
deMeta vars (Force e) = Force (deMeta vars e)
deMeta vars (ForceP e) = ForceP (deMeta vars e)

deMeta vars (Circ e1 e2 m) =
  let e1' = (deMeta vars e1)
      e2' = (deMeta vars e2)
  in Circ e1' e2' m

deMeta vars (LetPair m bd) = open bd $ \ xs b ->
  let m' = (deMeta vars m)
      b' = (deMeta (xs ++ vars) b)
  in LetPair m' (abst xs b') 

deMeta vars (LetPat m bd) = open bd $ \ (PApp id vs) b ->
  let m' = deMeta vars m
      (bvs, vs') = pvar vs
      b' = deMeta (bvs ++ vars) b
  in LetPat m' (abst (PApp id vs') b')
 where  pvar ([]) = ([], [])

        pvar (Right x : xs) =
          let (bv, fv) = pvar xs in
          (x:bv, Right x : fv)

        pvar (Left (NoBind (MetaVar x)):xs) =
          let (bv, fv) = pvar xs in
          if x `elem` vars then
            (bv, Left (NoBind (Var x)):fv)
          else (x:bv, Right x : fv)

        -- pvar (Left (NoBind (Var x)):xs) =
        --   let (bv, fv) = pvar xs in
        --   if x `elem` vars then
        --     (bv, Left (NoBind (Var x)):fv)
        --   else (x:bv, Right x : fv)
          
        pvar ((Left (NoBind x)):xs) =
          let (bv, fv) = pvar xs
              x' = deMeta vars x
          in (bv, Left (NoBind x'):fv)
   
deMeta vars (Let m bd) = open bd $ \ p b ->
  let m' = (deMeta vars m)
      b' = (deMeta (p:vars) b)
  in Let m' (abst p b') 

deMeta vars (LamTm bd) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
   in LamTm $ abst xs m'

deMeta vars (LamDep bd) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
   in LamDep (abst xs m') 

deMeta vars (LamDepTy bd) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
   in LamDepTy (abst xs m') 

deMeta vars (LamDepInt bd) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
   in LamDepInt (abst xs m') 

deMeta vars (Lam bd) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
   in Lam (abst xs m') 

deMeta vars (LamAnn ty bd) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
       ty' = deMeta vars ty
   in LamAnn ty' (abst xs m') 

deMeta vars (LamAnnP ty bd) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
       ty' = deMeta vars ty
   in LamAnnP ty' (abst xs m') 

deMeta vars (LamP bd) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
   in LamP (abst xs m') 

deMeta vars (LamType bd) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
   in LamType $ abst xs m'

deMeta vars (LamDict bd) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
   in LamDict $ abst xs m'

deMeta vars (Pi bd ty mod) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
       ty' = deMeta vars ty
   in Pi (abst xs m') ty' mod

deMeta vars (PiImp bd ty mod) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
       ty' = deMeta vars ty
   in PiImp (abst xs m') ty' mod

deMeta vars (PiInt bd ty) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
       ty' = deMeta vars ty
   in PiInt (abst xs m') ty'

deMeta vars (Exists bd ty) =
  open bd $ \ xs m ->
   let m' = deMeta (xs:vars) m
       ty' = deMeta vars ty
   in Exists (abst xs m') ty'

deMeta vars (Forall bd ty) =
  open bd $ \ xs m ->
   let m' = deMeta (xs ++ vars) m
       ty' = deMeta vars ty
   in Forall (abst xs m') ty'

      
deMeta vars a@(Case e (B br)) =
  let e' = deMeta vars e
      br' = map helper br
  in Case e' (B br')
  where helper b = open b $ \ (PApp id vs) b ->
          let (bvs, vs') = pvar vs in
          abst (PApp id vs') (deMeta (bvs ++vars) b)

        pvar ([]) = ([], [])

        pvar ((Right x):xs) =
          let (bv, fv) = pvar xs in
          (x:bv, (Right x):fv)

        pvar ((Left (NoBind (MetaVar x))):xs) =
          let (bv, fv) = pvar xs in
          if x `elem` vars then
            (bv, (Left (NoBind (Var x))):fv)
          else (x:bv, (Right x):fv)

        -- pvar ((Left (NoBind (EigenVar x))):xs) =
        --   let (bv, fv) = pvar xs in
        --   if x `elem` vars then
        --     (bv, (Left (NoBind (Var x))):fv)
        --   else (x:bv, (Right x):fv)

        pvar ((Left (NoBind x)):xs) =
          let (bv, fv) = pvar xs
              x' = deMeta vars x
          in (bv, (Left (NoBind x')):fv)
deMeta vars (Mod (Abst vs b)) = Mod (abst vs (deMeta vars b))
deMeta vars a = error $ "from deMeta" ++ (show $ disp a)

