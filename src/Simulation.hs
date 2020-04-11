{-# LANGUAGE ScopedTypeVariables #-}

module Simulation where

import SyntacticOperations hiding (toBool)
import Syntax
import Utils

import qualified Control.Exception as E
import Network.Socket
import System.IO

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State
import Control.Monad.Except
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
boxGates (RW_Write x c) =
  let r = boxGates c
  in (x:fst r, snd r)

boxGates (RW_Read q c) = error "from box Gate"

data Response = Null
              | OK
              | Reply String
              | Terminate
              | Error String
              | InternalError String
              deriving (Eq, Show, Read)



simulate :: ReadWrite a -> IO a
simulate m =
  (runTCPClient "127.0.0.1" "1901" $ \s -> do
      h <- socketToHandle s ReadWriteMode
      hGetLine h
      res <- interaction m h Map.empty []
      hPutStrLn h "quit"
      return res) `E.catch` \ (e :: E.IOException) -> withoutSimulator m

withoutSimulator :: ReadWrite a -> IO a
withoutSimulator (RW_Return a) = return a
withoutSimulator a = E.throw $ userError "qserver is not up, can't run simulator"
                                                      
interaction :: ReadWrite a -> Handle -> Map Label Label -> [Label] -> IO a
interaction (RW_Return a) h map ls = return a
interaction (RW_Read l k) h map ls =
          do let (VLabel l') = renameTemp (VLabel l) map
             hPutStrLn h ("R "++ labelToNum l')
             r <- hGetLine h
             case read r of
               Reply str | str == "0" -> interaction (k False) h map (l':ls)
               Reply str | str == "1" -> interaction (k True) h map (l':ls)
interaction (RW_Write (Gate name []  (VLabel w) VStar VStar _) c) h map ls
          | getName name == "Discard" =
            do let (VLabel w') = renameTemp (VLabel w) map
               hPutStrLn h ("D " ++ labelToNum w')
               interaction c h map (w':ls)
interaction (RW_Write (Gate name []  (VLabel w) VStar VStar _) c) h map ls
          | getName name == "Term0" =
            do let (VLabel w') = renameTemp (VLabel w) map
               hPutStrLn h ("M " ++ labelToNum w')
               hPutStrLn h ("R " ++ labelToNum w')
               r' <- hGetLine h
               case read r' of
                        Reply s | s == "0" -> interaction c h map (w':ls)
                        Reply s ->
                          error $ "termination error, expecting to terminate with 0, but get:" ++ s
          | getName name == "Term1" =
            do let (VLabel w') = renameTemp (VLabel w) map
               hPutStrLn h ("M " ++ labelToNum w')
               hPutStrLn h ("R " ++ labelToNum w')
               r' <- hGetLine h
               case read r' of
                 Reply s | s == "1" -> interaction c h map (w':ls)
                 Reply s ->
                          error $ "termination error, expecting to terminate with 1, but get:" ++ s
                
interaction (RW_Write (Gate name [] VStar (VLabel w) VStar _) c) h map []
          | getName name == "Init0" =
          do let cmd = ("Q " ++ labelToNum w)
             hPutStrLn h cmd
             interaction c h map []
             -- r <- hGetLine h
             -- case read r of
             --   OK -> interaction c h map []
             --   a -> error $ "from interaction" ++ show a ++ ":" ++ cmd
          | getName name == "Init1" =
          do hPutStrLn h ("Q " ++ labelToNum w ++ " 1")
             interaction c h map []
             -- r <- hGetLine h
             -- case read r of
             --   OK -> interaction c h map []
interaction (RW_Write (Gate name [] VStar (VLabel w) VStar _) c) h map (v:vs)
          | getName name == "Init0" =
          do let map' = map `Map.union` Map.fromList [(w, v)]
             hPutStrLn h ("Q " ++ labelToNum v)
             interaction c h map' vs
             -- r <- hGetLine h
             -- case read r of
             --   OK -> interaction c h map' vs
          | getName name == "Init1" =
          do let map' = map `Map.union` Map.fromList [(w, v)]
             hPutStrLn h ("Q " ++ labelToNum v ++ " 1")
             interaction c h map' vs
             -- r <- hGetLine h
             -- case read r of
             --   OK -> interaction c h map' vs
interaction (RW_Write (Gate name [] (VLabel v) (VLabel w) VStar _) c) h map ls =
          do let (VLabel v') = renameTemp (VLabel v) map
                 map' = map `Map.union` Map.fromList [(w, v')]
                 g = toGateName (getName name)
             hPutStrLn h (g++ " "++ labelToNum v')
             interaction c h map' ls
             -- r <- hGetLine h
             -- case read r of
             --    OK -> interaction c h map' ls
             --    a -> error $ show a
interaction (RW_Write (Gate name [] v@(VPair _ _) w@(VPair _ _) VStar _) res) h map ls =
          do let (VPair (VLabel a) (VLabel b)) = renameTemp v map
                 (VPair (VLabel c) (VLabel d)) = w
                 map' = map `Map.union` Map.fromList [(c, a), (d, b)]
                 g = toGateName (getName name)
             hPutStrLn h (g++ " "++ labelToNum a ++ " " ++ labelToNum b)
             interaction res h map' ls
             -- r <- hGetLine h
             -- case read r of
             --    OK -> interaction res h map' ls
                   
interaction (RW_Write g res) h map ls =
  error $ "from interaction:" ++ (show g)
  
labelToNum l =
  let r = tail (show l) in if null r then "0" else r
                                                   
toGateName "CNot" = "CNOT"
toGateName "Meas" = "M"
toGateName "QNot" = "X"
toGateName "H" = "H"
toGateName "ZGate" = "Z"
toGateName "C_X" = "X"
toGateName "C_Z" = "Z"
toGateName "SGate" = "S"
toGateName "TGate" = "T"
toGateName "TGate*" = "T*"
toGateName "Discard" = "D"

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

