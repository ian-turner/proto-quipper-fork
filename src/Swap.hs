module Swap (permutation_to_swaps) where
import Data.List (elemIndex, sortBy, permutations)


-- | A movement contains an index and a movement distant.
-- The index ranges from 0 - n indexing the list. Movement
-- (Up j b) means the element in the index i is moved up to a new index of j - b.
-- (Down i a) means the element in the index j is moved down to a new index of i + a  

data Movement = Down Int Int | Up Int Int 
  deriving (Show, Eq)

-- | Determine if two movement intersect with each other.
-- We assume the index of the first movement is less than the index of
-- the second movement. 
intersection :: Movement -> Movement -> Bool
intersection (Down i a) (Up j b) | i < j = i + a > j - b
intersection _ _ = False


-- | Generate a list movements from two input lists.
-- We assume the the second input list is a permutation of the
-- first input list. 

gen_movements :: (Ord a) => [a] -> [a] -> [Movement]
gen_movements ls1 ls2 =
  let ls1' = zip [0 .. ] ls1
  in helper ls1'
  where helper ((i, a):res) =
          case elemIndex a ls2 of
            Nothing -> error "from gen_movements"
            Just dest | dest > i -> Down i (dest - i) : helper res
            Just dest | dest == i -> helper res
            Just dest | dest < i -> Up i (i - dest) : helper res
        helper [] = []


-- | Generate a list of intersected movements from a list
-- of movements, the intersected movement is sorted according
-- to the metric of |i-j|, where (Down i a, Up j b) is from the output.  
gen_intersections :: [Movement] -> [(Movement, Movement)]
gen_intersections l =
  let a = l
  in sortBy myCompare (helper a l)
  where helper ((Up _ _):res) l = helper res l
        helper (m@(Down i a):res) l =
          map (\ y -> (m, y)) (filter (\ x -> intersection m x) l) ++ helper res l
        helper [] l = []
        myCompare (Down i1 _, Up j1 _) (Down i2 _, Up j2 _) | abs (i1-j1) < abs (i2 - j2) = LT
        myCompare (Down i1 _, Up j1 _) (Down i2 _, Up j2 _) | abs (i1-j1) > abs (i2 - j2) = GT
        myCompare (Down i1 _, Up j1 _) (Down i2 _, Up j2 _) | abs (i1-j1) == abs (i2 - j2) = EQ


-- | replace a movement with a new movement in the list. 
replace :: Movement -> Movement -> [(Movement, Movement)] -> [(Movement, Movement)]
replace a b [] = []
replace a b ((c, d):res) | a == c = (b, d) : replace a b res
replace a b ((c, d):res) | a == d = (c, b) : replace a b res
replace a b ((c, d):res) | otherwise = (c, d) : replace a b res

-- | remove a movement from a list of intersections. 
remove :: Movement -> [(Movement, Movement)] -> [(Movement, Movement)]
remove a [] = []
remove a ((c, d):res) | a == c || a == d = remove a res
remove a ((c, d):res) | otherwise = (c, d) : remove a res


-- | generate a sequence of swap gates from a list of intersections. 
gen_swaps :: [(Movement, Movement)] -> [(Int, Int)]
gen_swaps ((x@(Down i a), y@(Up j b)):res)
  | (i + a == j) && (j - b == i) =
    let res' = remove y (remove x res)
    in (i,j) : gen_swaps res'
  | i + a == j =
    let res' = replace y (Up i ((i-j)+b)) $ remove x res
    in (i, j) : gen_swaps res' 
  | j - b == i =
    let res' = replace x (Down j ((i-j)+a)) $ remove y res
    in (i, j) : gen_swaps res' 
  | otherwise =
    let res' = replace x (Down j ((i-j)+a)) (replace y (Up i ((i-j)+b)) res)
    in (i, j) : gen_swaps res' 
gen_swaps [] = []


-- | Generate a list of swap gates from an original list of items (x) and
-- the permuted list (y). 
permutation_to_swaps :: (Ord a) => [a] -> [a] -> [(Int, Int)]
permutation_to_swaps x y = gen_swaps (gen_intersections (gen_movements x y))

-- Optional test code
-- import System.Random
-- shuffle :: [a] -> IO [a]
-- shuffle [] = return []
-- shuffle lst = do
--   n <- getIx
--   let (e, rest) = pickElem n
--   r <- shuffle rest
--   return (e:r)
--   where
--     getIx = getStdRandom $ randomR (1, length lst)
--     pickElem n = case splitAt n lst of
--         ([], s) -> error $ "failed at index " ++ show n -- should never match
--         (r, s)  -> (last r, init r ++ s)
  
-- test :: IO ()
-- test = do
--   let l = [0 .. 9]
--   l1 <- shuffle l
--   putStrLn $ "original list: " ++ show l
--   putStrLn $ "permuted list: " ++ show l1
--   putStrLn $  "swaps: " ++ show (permutation_to_swaps l l1)


  




