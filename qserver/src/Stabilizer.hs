{-# LANGUAGE FlexibleInstances, BangPatterns, GeneralizedNewtypeDeriving #-}
module Stabilizer where
-- | In the current stabilizer formalism,
-- one must measure all the qubits to obtain the actual state.
-- It does not support partial measurement.

import Text.PrettyPrint
import Control.Monad
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap hiding (intersection)
import Data.Set (Set)
import Data.List
import Debug.Trace
import qualified Data.Set as S hiding (intersection)
import Prelude hiding ((<>))
import System.Random


-- | Pauli matrices
data PMatrice = I | X | Y | Z deriving (Eq, Show, Read)

-- | Factors for Pauli group.
data Factor = Plus | Minus | PlusI | MinusI deriving (Eq, Show, Read)

-- | Pauli group.
type Pauli = (Factor, PMatrice)


-- | Clifford group.
data Clifford = H | CNot | S | P Pauli  deriving (Eq, Show, Read)


prod :: Pauli -> Pauli -> Pauli
prod (f1, p1) (f2, p2) | p1 == p2 && f1 == f2 = (Plus, I)
prod (f1, p1) (f2, p2) | p1 == p2 = (Minus, I)
prod p (Plus, I) = p
prod (Plus, I) p = p



actUnary :: Clifford -> Pauli -> Pauli
actUnary H (Plus, X) = (Plus, Z) 
actUnary H (Plus, Z) = (Plus, X)

actUnary (P (Plus, X)) (Plus, X) = (Plus, X) 
actUnary (P (Plus, X)) (Plus, Z) = (Minus, Z)

actUnary (P (Plus, Y)) (Plus, X) = (Minus, X) 
actUnary (P (Plus, Y)) (Plus, Z) = (Minus, Z)

actUnary (P (Plus, Z)) (Plus, X) = (Minus, X) 
actUnary (P (Plus, Z)) (Plus, Z) = (Plus, Z)

actUnary S (Plus, X) = (Plus, Y) 
actUnary S (Plus, Z) = (Plus, Z)

actUnary H (Minus, Z) = (Minus, X)

actUnary a b = error $ "from actUnary:" ++ show a ++ show b

-- | Act cnot, first argument is the control bit. 
actCNot :: Pauli -> Pauli -> (Pauli, Pauli)
actCNot (Plus, X) (Plus, I) = ((Plus, X), (Plus, X))
actCNot (Plus, I) (Plus, X) = ((Plus, I), (Plus, X))
actCNot (Plus, X) (Plus, X) = ((Plus, X), (Plus, I))
actCNot (Plus, Z) (Plus, I) = ((Plus, Z), (Plus, I))
actCNot (Plus, I) (Plus, Z) = ((Plus, Z), (Plus, Z)) 
actCNot (Plus, Z) (Plus, Z) = ((Plus, I), (Plus, Z))
actCNot (Minus, Z) (Plus, I) = ((Minus, Z), (Plus, I))
actCNot (Plus, I) (Minus, Z) = ((Plus, Z), (Minus, Z))
actCNot (Minus, Z) (Plus, Z) = ((Plus, I), (Minus, Z))
actCNot (Minus, X) (Plus, I) = ((Minus, X), (Plus, X))
actCNot a b = error $ "from cnot" ++ show a ++ ":" ++ show b

-- | A stabilizer state is a list of generators of stabilizers  
type StabilizerState = IntMap (IntMap Pauli)

initStabilizerState = IntMap.empty

class Disp a where
  disp :: a -> Doc 

instance Disp PMatrice where
  disp x =
    case x of
      X -> text "X"
      Y -> text "Y"
      Z -> text "Z"
      I -> text "I"

instance Disp Pauli where
  disp (Plus, x) = disp x
  disp (Minus, x) = text "-" <> disp x
  disp (PlusI, x) = text "i" <> disp x
  disp (MinusI, x) = text "-i" <> disp x

instance Disp (IntMap Pauli) where
  disp m =
    braces $ vcat
    $ map (\ (i, a) -> parens $ int i <> comma <+> disp a) $ IntMap.toAscList m

instance Disp (IntMap (IntMap Pauli)) where
  disp m =
    braces $ vcat
    $ map (\ (i, m) -> disp m) $ IntMap.toAscList m

-- | Initialize register i with 0, i.e., stablizer Z. 
initialize i m = IntMap.insert i (IntMap.insert i (Plus, Z) IntMap.empty) m

-- | Initialize register i with 1, i.e., stablizer -Z.
initialize' i m = IntMap.insert i (IntMap.insert i (Minus, Z) IntMap.empty) m


mapLookupSafe m i =
  case IntMap.lookup i m of
    Just x -> x
    Nothing -> (Plus, I)


-- | Apply a unitary clifford operator on a stabilizer state
applyUnary :: Int -> Clifford -> StabilizerState -> StabilizerState
applyUnary i c m =
  IntMap.map (\ subMap ->
               case subMap `mapLookupSafe` i of
                 (Plus, I) -> subMap
                 p -> IntMap.insert i (actUnary c p) subMap
             ) m


-- | Apply cnot, where i is the primary control.
applyBinary :: Int -> Int -> StabilizerState -> StabilizerState
applyBinary i j m =
  IntMap.map (\ subMap ->
               case (subMap `mapLookupSafe` i, subMap `mapLookupSafe` j) of
                 ((Plus, I), (Plus, I)) -> subMap
                 (p, q) -> let (p', q') = actCNot p q
                               subMap1= IntMap.insert i p' subMap
                               subMap2= IntMap.insert j q' subMap1
                           in subMap2
             ) m


-- | We only implement measure on Z, i.e., measurement on computational
-- basis. 
measurement :: RandomGen g => g -> Int -> StabilizerState -> StabilizerState
measurement g i s = snd $ 
  IntMap.mapAccumWithKey
        (\ m k subMap ->
          let p = subMap `mapLookupSafe` i
          in if commute p then (m, subMap)
             else case m of
               Nothing -> 
                 let (_, z) = choose g
                 in (Just subMap, (IntMap.insert i z IntMap.empty))
               Just m' ->
                 let r = multiply (IntMap.toAscList m') subMap []
                 in (m, IntMap.fromList r)
        ) Nothing s
  where commute p = (snd p == Z) || (snd p == I)
        choose g =
          let (x, g') = randomR (0.0, 1.0 :: Double) g
              z = x > 0.5
          in if z then (g', (Plus, Z)) else (g', (Minus, Z))

        multiply [] !m2 r = (IntMap.toAscList m2)++r
        multiply ((i, p):xs) !m2 r =
          case IntMap.lookup i m2 of
            Nothing -> multiply xs m2 ((i, p):r)
            Just p' -> multiply xs (IntMap.delete i m2) ((i, prod p p'):r)
        
          
-- | Obtain the measured state. Assuming all the qubits are measured.
getBits :: StabilizerState -> ([Int], [Bool])
getBits s = 
  let m = IntMap.toAscList s
      l = length m
      h:tl = map (\ (i, subMap) -> stable subMap) m
      (pos, ds) = foldl' combine h tl
  in (pos, head ds)
       where combine (ps1, ss1) (ps2, ss2) = 
               let r = [s1++s2 | s1 <- ss1, s2 <- ss2, allEq ps1 ps2 s1 s2]
               in (ps1++ps2, r)
             allEq ps1 ps2 x y =
               and $ map (\ p ->
                         let Just indx = elemIndex p ps1
                             Just indy = elemIndex p ps2
                         in ((x !! indx) == (y !! indy))) (intersect ps1 ps2)
               

-- | Assume an IntMap of Zs, i.e., we have the result of the measurement.
-- Generate a set of stabilized states for a stabilizer. 

stable :: IntMap Pauli -> ([Int], [[Bool]])
stable m =
  let s = IntMap.toAscList m
      m' = [a | a@(i, (_, b)) <- s, b == Z ]
      n = length m'
      pos = map fst m'
      (q, r) = divMod n 2 
      p = polarity s
      zs = nub $ allPossibleZs 0 p q n
  in (pos, zs)
   where -- | Calculate the polarity of a stabilizer. 'True' means positive.
         polarity [] = error "empty list from polarity"
         polarity xs =
           let xs' = map (\ (i, (f, p)) ->
                           case f of
                             Plus -> True
                             Minus -> False
                         ) xs
           in foldl' nxor (head xs') (tail xs')
         nxor a b = (a == b)


         
-- | generate all possible stabilizer state for Zs. 
allPossibleZs i p q n | i > q = []

allPossibleZs i p q n | i <= q =
  let ones = maxOnes i p
      l = length ones
      zeros = take (n - l) $ repeat False
      pre = if (n-l == 0) then [ones] 
            else if (n-l < 0) then []
                 else permutations (ones ++ zeros)
      res = allPossibleZs (i+1) p q n 
  in pre++res
  

maxOnes q p =
  let r = repeat True
  in if p then take (q * 2) r else take (q*2 + 1) r



