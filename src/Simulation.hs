{-# LANGUAGE ScopedTypeVariables #-}

module Simulation where

import SyntacticOperations hiding (toBool)
import Syntax
import Utils

import qualified Control.Exception as E
import Network.Socket
import System.IO

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Control.Monad
import Text.PrettyPrint

import Debug.Trace

data ReadWrite a = RW_Return a
                 | RW_Write Gate (ReadWrite a)
                 | RW_Read Label (Bool -> ReadWrite a)

instance Monad ReadWrite where
  return a = RW_Return a
  f >>= g =
    case f of
      RW_Return a -> g a
      RW_Write gate f' -> RW_Write gate (f' >>= g)
      RW_Read bit cont -> RW_Read bit (\bool -> cont bool >>= g)
 
instance Applicative ReadWrite where
  pure = return
  (<*>) = ap

instance Functor ReadWrite where
  fmap = liftM

gateRW :: Gate -> ReadWrite ()
gateRW g = RW_Write g (return ())

dynliftRW :: Label -> ReadWrite Bool
dynliftRW q = RW_Read q (\ans -> return ans)

boxGates :: ReadWrite b -> ([Gate], b)
boxGates (RW_Return b) = ([], b)
boxGates (RW_Write x c) = (x:xs, r)
  where c'= boxGates c
        r = snd c'
        xs = fst c'
        
boxGates (RW_Read q c) = error "modality violation, please send bug report"

data Response = Null
              | OK
              | Reply String
              | Terminate
              | Error String
              | InternalError String
              deriving (Eq, Show, Read)

simulate :: ReadWrite a -> IO (a, [Gate])
simulate m =
  (runTCPClient "127.0.0.1" "1901" $ \s -> do
      h <- socketToHandle s ReadWriteMode
      hGetLine h
      (v, gs) <- interaction m h Map.empty []
      hPutStrLn h "quit"
      return (v, gs))
  `E.catch` \ (e :: E.IOException) -> return (withoutSimulator m)

withoutSimulator :: ReadWrite a -> (a, [Gate])
withoutSimulator (RW_Return a) = (a, [])
withoutSimulator (RW_Write g r) = 
  let (a, gs) = withoutSimulator r
  in (a, g:gs)
withoutSimulator (RW_Read _ _) = E.throw $ userError "qserver is not up, can't dynamic lift"
                                                      
interaction :: ReadWrite a -> Handle -> Map Label Label -> [Label] -> IO (a, Gates)
interaction (RW_Return a) h map ls = return (a, [])

interaction (RW_Read l k) h map ls =
          do let (VLabel l') = renameTemp (VLabel l) map
             hPutStrLn h ("R "++ show l')
             r <- hGetLine h
             case read r of
               Reply str | str == "0" ->
                 let g = Gate (Id "Dynlift") [] (VLabel l) (VConst (Id "False")) VStar False
                     res = interaction (k False) h map (l':ls)
                 in fmap (\ (x, y) -> (x, g:y)) res
               Reply str | str == "1" ->
                 let g = Gate (Id "Dynlift") [] (VLabel l) (VConst (Id "False")) VStar True
                     res = interaction (k True) h map (l':ls)
                 in fmap (\ (x, y) -> (x, g:y)) res
                 

interaction (RW_Write g@(Gate name []  (VLabel w) VStar VStar _) c) h map ls
          | getName name == "Discard" =
            do let (VLabel w') = renameTemp (VLabel w) map
               hPutStrLn h ("D " ++ show w')
               let res = interaction c h map (w':ls)
               fmap (\ (x, y) -> (x, g:y)) res
               
interaction (RW_Write g@(Gate name []  (VLabel w) VStar VStar _) c) h map ls
          | getName name == "Term0" =
            do let (VLabel w') = renameTemp (VLabel w) map
               hPutStrLn h ("M " ++ show w')
               hPutStrLn h ("R " ++ show w')
               r' <- hGetLine h
               case read r' of
                 Reply s | s == "0" -> 
                   let res =  interaction c h map (w':ls)
                   in fmap (\ (x, y) -> (x, g:y)) res
                 Reply s ->
                   error $ "Wire termination error: expecting to terminate with 0, but get: " ++ s
          | getName name == "Term1" =
            do let (VLabel w') = renameTemp (VLabel w) map
               hPutStrLn h ("M " ++ show w')
               hPutStrLn h ("R " ++ show w')
               r' <- hGetLine h
               case read r' of
                 Reply s | s == "1" ->
                   let res =  interaction c h map (w':ls)
                   in fmap (\ (x, y) -> (x, g:y)) res
                 Reply s ->
                   error $ "termination error, expecting to terminate with 1, but get: " ++ s
                
interaction (RW_Write g@(Gate name [] VStar (VLabel w) VStar _) c) h map []
          | getName name == "Init0" =
          do let cmd = ("Q " ++ show w)
             hPutStrLn h cmd
             let res = interaction c h map []
             fmap (\ (x, y) -> (x, g:y)) res 
             
          | getName name == "Init1" =
          do hPutStrLn h ("Q " ++ show w ++ " 1")
             let res = interaction c h map []
             fmap (\ (x, y) -> (x, g:y)) res
             
             
interaction (RW_Write g@(Gate name [] VStar (VLabel w) VStar _) c) h map (v:vs)
          | getName name == "Init0" =
          do let map' = map `Map.union` Map.fromList [(w, v)]
             hPutStrLn h ("Q " ++ show v)
             let res = interaction c h map' vs
             fmap (\ (x, y) -> (x, g:y)) res
             
          | getName name == "Init1" =
          do let map' = map `Map.union` Map.fromList [(w, v)]
             hPutStrLn h ("Q " ++ show v ++ " 1")
             let res = interaction c h map' vs
             fmap (\ (x, y) -> (x, g:y)) res
             

interaction (RW_Write g@(Gate name [] (VLabel v) (VLabel w) VStar _) c) h map ls =
          do let (VLabel v') = renameTemp (VLabel v) map
                 map' = map `Map.union` Map.fromList [(w, v')]
                 gn = toGateName (getName name)
             hPutStrLn h (gn ++ " "++ show v')
             let res = interaction c h map' ls
             fmap (\ (x, y) -> (x, g:y)) res
             
-- binary unitary gate
interaction (RW_Write g@(Gate name [] v@(VPair (VLabel _) (VLabel _))
                         w@(VPair _ _) VStar _) cs) h map ls =
          do let (VPair (VLabel a) (VLabel b)) = renameTemp v map
                 (VPair (VLabel c) (VLabel d)) = w
                 map' = map `Map.union` Map.fromList [(c, a), (d, b)]
                 gn = toGateName (getName name)
             hPutStrLn h (gn++ " "++ show a ++ " " ++ show b)
             let res = interaction cs h map' ls
             fmap (\ (x, y) -> (x, g:y)) res
             
-- ternary unitary gate
interaction (RW_Write g@(Gate name [] v@(VPair (VPair _ _) _)
                         w@(VPair (VPair _ _) _) VStar _) cs) h map ls =
          do let (VPair (VPair (VLabel a) (VLabel b)) (VLabel e)) = renameTemp v map
                 (VPair (VPair (VLabel c) (VLabel d)) (VLabel e')) = w
                 map' = map `Map.union` Map.fromList [(c, a), (d, b), (e', e)]
                 gn = toGateName (getName name)
             hPutStrLn h (gn++ " "++ show a ++ " " ++ show b ++ " " ++ show e)
             let res = interaction cs h map' ls
             fmap (\ (x, y) -> (x, g:y)) res
             

interaction (RW_Write g res) h map ls =
  error $ "Unsupported gate: " ++ (show g)

                                                   
toGateName "CNot" = "CNOT"
toGateName "Meas" = "M"
toGateName "Toffoli" = "TOF"
toGateName "QNot" = "X"
toGateName "H" = "H"
toGateName "ZGate" = "Z"
toGateName "C_X" = "X"
toGateName "C_Z" = "Z"
toGateName "SGate" = "S"
toGateName "TGate" = "T"
toGateName "TGate_inv" = "T*"
toGateName "Discard" = "D"
toGateName a = E.throw $ userError $ "unsupported gate: " ++ a

runTCPClient :: HostName -> ServiceName -> (Socket -> IO a) -> IO a
runTCPClient host port client = withSocketsDo $ do
    addr <- resolve
    E.bracket (open addr) close client
  where
    resolve = do
        let hints = defaultHints { addrSocketType = Stream }
        head <$> getAddrInfo (Just hints) (Just host) (Just port)
    open addr = do
        sock <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
        connect sock $ addrAddress addr
        return sock

