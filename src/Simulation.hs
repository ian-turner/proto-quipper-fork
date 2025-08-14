{-# LANGUAGE ScopedTypeVariables #-}

module Simulation where

import SyntacticOperations hiding (toBool)
import Syntax
import Utils

import qualified Control.Exception as E
import Network.Socket
import qualified Network.Socket.ByteString as NBS

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Control.Monad
import Text.PrettyPrint
import Debug.Trace

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import Data.IORef
import Numeric (showFFloat)
import Data.Char (isDigit)
import Data.Number.CReal (CReal)  -- kept only for type of MR; we *don't* use showCReal

--------------------------------------------------------------------------------
-- Small, robust line-oriented socket I/O (no Handles)

newtype RecvState = RecvState { bufRef :: IORef BS.ByteString }

newRecvState :: IO RecvState
newRecvState = RecvState <$> newIORef BS.empty

sendLine :: Socket -> String -> IO ()
sendLine s msg = NBS.sendAll s (BC.snoc (BC.pack msg) '\n')

-- Read one '\n'-terminated ASCII/UTF-8 line (without trailing '\n').
recvLine :: Socket -> RecvState -> IO String
recvLine s (RecvState ref) = do
  buf <- readIORef ref
  case BC.elemIndex '\n' buf of
    Just i -> do
      let (line, rest) = BS.splitAt i buf
      writeIORef ref (BS.drop 1 rest)  -- drop the '\n'
      pure (BC.unpack line)
    Nothing -> do
      chunk <- NBS.recv s 4096
      if BS.null chunk
        then E.throwIO (userError "connection closed while reading line")
        else do
          let newBuf = BS.append buf chunk
          writeIORef ref newBuf
          recvLine s (RecvState ref)

--------------------------------------------------------------------------------

data ReadWrite a = RW_Return a
                 | RW_Write Gate (ReadWrite a)
                 | RW_Read Label (Bool -> ReadWrite a)

instance Monad ReadWrite where
  return = RW_Return
  f >>= g =
    case f of
      RW_Return a      -> g a
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
  case boxGates c of
    (xs, r) -> (x:xs, r)
boxGates (RW_Read _ _) = error "modality violation, please send bug report"

data Response = Null
              | OK
              | Reply String
              | Terminate
              | Error String
              | InternalError String
              deriving (Eq, Show, Read)

simulate :: Bool -> ReadWrite a -> IO (a, [Gate])
simulate b m =
  (runTCPClient "127.0.0.1" "1901" $ \s -> do
      st <- newRecvState
      recvLine s st
      when b        $ sendLine s "Stabilizer"
      when (not b)  $ sendLine s "Universal"
      (v, gs) <- interaction m s st Map.empty []
      sendLine s "quit"
      pure (v, gs))
  `E.catch` \(_ :: E.IOException) -> return (withoutSimulator m)

withoutSimulator :: ReadWrite a -> (a, [Gate])
withoutSimulator (RW_Return a) = (a, [])
withoutSimulator (RW_Write g r) =
  let (a, gs) = withoutSimulator r
  in (a, g:gs)
withoutSimulator (RW_Read _ _) = E.throw $ userError "qserver is not up, can't dynamic lift"

-- Safer labelToNum: extract trailing digits from Show instance (fallback "0")
labelToNum :: Show a => a -> String
labelToNum l =
  case dropWhile (not . isDigit) (show l) of
    "" -> "0"
    ds -> ds

-- Format a CReal with bounded precision by converting to Double
fmtR :: Int -> CReal -> String
fmtR p x = showFFloat (Just (max 0 (min 17 p))) (realToFrac x :: Double) ""

-- Format a Double with bounded precision
fmtD :: Int -> Double -> String
fmtD p x = showFFloat (Just (max 0 (min 17 p))) x ""

-- NOTE: Interaction now uses Socket + RecvState (no Handle).
interaction :: ReadWrite a -> Socket -> RecvState -> Map Label Label -> [Label] -> IO (a, Gates)
interaction (RW_Return a) _ _ _ _ = return (a, [])

interaction (RW_Read l k) s st mp ls = do
  let (VLabel l') = renameTemp (VLabel l) mp
  sendLine s ("R " ++ labelToNum l')
  r <- recvLine s st
  case (reads r :: [(Response, String)]) of
    (Reply str, _):_ | str == "0" ->
      let g = Gate (Id "Dynlift") [] (VLabel l) (VConst (Id "FalseX")) VStar False Nothing [] []
          res = interaction (k False) s st mp (l':ls)
      in fmap (\(x,y) -> (x, g:y)) res
    (Reply str, _):_ | str == "1" ->
      let g = Gate (Id "Dynlift") [] (VLabel l) (VConst (Id "TrueX")) VStar True Nothing [] []
          res = interaction (k True) s st mp (l':ls)
      in fmap (\(x,y) -> (x, g:y)) res
    (x, _):_ -> error $ "Unexpected response: " ++ show x
    []       -> error $ "Unparseable response: " ++ r

interaction (RW_Write g@(Gate name []  (VLabel w) VStar VStar _ _ _ _) c) s st mp ls
  | getName name == "Discard" = do
      let (VLabel w') = renameTemp (VLabel w) mp
      sendLine s ("D " ++ labelToNum w')
      let res = interaction c s st mp (w':ls)
      fmap (\(x,y) -> (x, g:y)) res

interaction (RW_Write g@(Gate name []  (VLabel w) VStar VStar _ _ _ _) c) s st mp ls
  | getName name == "Term0" = do
      let (VLabel w') = renameTemp (VLabel w) mp
      sendLine s ("M " ++ labelToNum w')
      sendLine s ("R " ++ labelToNum w')
      r' <- recvLine s st
      case (reads r' :: [(Response, String)]) of
        (Reply v, _):_ | v == "0" ->
          let res = interaction c s st mp (w':ls)
          in fmap (\(x,y) -> (x, g:y)) res
        (Reply v, _):_ ->
          error $ "Wire termination error: expecting to terminate with 0, but got: " ++ v
        _ -> error $ "Unparseable response: " ++ r'
  | getName name == "Term1" = do
      let (VLabel w') = renameTemp (VLabel w) mp
      sendLine s ("M " ++ labelToNum w')
      sendLine s ("R " ++ labelToNum w')
      r' <- recvLine s st
      case (reads r' :: [(Response, String)]) of
        (Reply v, _):_ | v == "1" ->
          let res = interaction c s st mp (w':ls)
          in fmap (\(x,y) -> (x, g:y)) res
        (Reply v, _):_ ->
          error $ "termination error, expecting to terminate with 1, but got: " ++ v
        _ -> error $ "Unparseable response: " ++ r'

interaction (RW_Write g@(Gate name [] VStar (VLabel w) VStar _ _ _ _) c) s st mp []
  | getName name == "Init0" = do
      sendLine s ("Q " ++ labelToNum w)
      let res = interaction c s st mp []
      fmap (\(x,y) -> (x, g:y)) res
  | getName name == "Init1" = do
      sendLine s ("Q " ++ labelToNum w ++ " 1")
      let res = interaction c s st mp []
      fmap (\(x,y) -> (x, g:y)) res

interaction (RW_Write g@(Gate name [] VStar (VLabel w) VStar _ _ _ _) c) s st mp (v:vs)
  | getName name == "Init0" = do
      let mp' = mp `Map.union` Map.fromList [(w, v)]
      sendLine s ("Q " ++ labelToNum v)
      let res = interaction c s st mp' vs
      fmap (\(x,y) -> (x, g:y)) res
  | getName name == "Init1" = do
      let mp' = mp `Map.union` Map.fromList [(w, v)]
      sendLine s ("Q " ++ labelToNum v ++ " 1")
      let res = interaction c s st mp' vs
      fmap (\(x,y) -> (x, g:y)) res

interaction (RW_Write g@(Gate name [VWrapR (MR len r)] (VLabel v) (VLabel w) VStar _ _ _ _) c) s st mp ls
  | getName name == "Rot" = do
      let (VLabel v') = renameTemp (VLabel v) mp
          mp' = mp `Map.union` Map.fromList [(w, v')]
          gn = toGateName (getName name)
      sendLine s (gn ++ " " ++ fmtR len r ++ " " ++ labelToNum v')
      let res = interaction c s st mp' ls
      fmap (\(x,y) -> (x, g:y)) res

interaction (RW_Write g@(Gate name [VWrapR (MR len r)] (VLabel v) (VLabel w) VStar _ _ _ _) c) s st mp ls
  | getName name == "Rot_Inv" = do
      let (VLabel v') = renameTemp (VLabel v) mp
          mp' = mp `Map.union` Map.fromList [(w, v')]
          gn = toGateName (getName name)
      sendLine s (gn ++ " " ++ fmtR len (-r) ++ " " ++ labelToNum v')
      let res = interaction c s st mp' ls
      fmap (\(x,y) -> (x, g:y)) res

interaction (RW_Write g@(Gate name [VWrapR (MR len r), VWrapR (MR len' r')] (VLabel v) (VLabel w) VStar _ _ _ _) c) s st mp ls
  | getName name == "Diag" = do
      let (VLabel v') = renameTemp (VLabel v) mp
          mp' = mp `Map.union` Map.fromList [(w, v')]
          gn = toGateName (getName name)
      sendLine s (gn ++ " " ++ fmtR len r ++ " " ++ fmtR len' r' ++ " " ++ labelToNum v')
      let res = interaction c s st mp' ls
      fmap (\(x,y) -> (x, g:y)) res

-- single gate
interaction (RW_Write g@(Gate name [] (VLabel v) (VLabel w) VStar _ _ _ _) c) s st mp ls = do
  let (VLabel v') = renameTemp (VLabel v) mp
      mp' = mp `Map.union` Map.fromList [(w, v')]
      gn = toGateName (getName name)
  sendLine s (gn ++ " " ++ labelToNum v')
  let res = interaction c s st mp' ls
  fmap (\(x,y) -> (x, g:y)) res

-- binary unitary gate
interaction (RW_Write g@(Gate name [n] v@(VPair (VLabel _) (VLabel _))
                         w@(VPair _ _) VStar _ _ _ _) cs) s st mp ls
  | getName name == "R" = do
      let (VPair (VLabel a) (VLabel b)) = renameTemp v mp
          (VPair (VLabel c) (VLabel d)) = w
          mp' = mp `Map.union` Map.fromList [(c, a), (d, b)]
          gn = toGateName (getName name)
          Just n' = toInt n
          r  = (2 :: Double) * pi / (2 ^^ n')   -- Double; ^^ for Int exponent
          p  = 17
      sendLine s (gn ++ " " ++ fmtD p r ++ " " ++ labelToNum a ++ " " ++ labelToNum b)
      let res = interaction cs s st mp' ls
      fmap (\(x,y) -> (x, g:y)) res

interaction (RW_Write g@(Gate name [n] v@(VPair (VLabel _) (VLabel _))
                         w@(VPair _ _) VStar _ _ _ _) cs) s st mp ls
  | getName name == "R_Inv" = do
      let (VPair (VLabel a) (VLabel b)) = renameTemp v mp
          (VPair (VLabel c) (VLabel d)) = w
          mp' = mp `Map.union` Map.fromList [(c, a), (d, b)]
          gn = toGateName (getName name)
          Just n' = toInt n
          r  = negate ((2 :: Double) * pi / (2 ^^ n'))
          p  = 17
      sendLine s (gn ++ " " ++ fmtD p r ++ " " ++ labelToNum a ++ " " ++ labelToNum b)
      let res = interaction cs s st mp' ls
      fmap (\(x,y) -> (x, g:y)) res

interaction (RW_Write g@(Gate name [] v@(VPair (VLabel _) (VLabel _))
                         w@(VPair _ _) VStar _ _ _ _) cs) s st mp ls = do
  let (VPair (VLabel a) (VLabel b)) = renameTemp v mp
      (VPair (VLabel c) (VLabel d)) = w
      mp' = mp `Map.union` Map.fromList [(c, a), (d, b)]
      gn = toGateName (getName name)
  sendLine s (gn ++ " " ++ labelToNum a ++ " " ++ labelToNum b)
  let res = interaction cs s st mp' ls
  fmap (\(x,y) -> (x, g:y)) res

-- ternary unitary gate
interaction (RW_Write g@(Gate name [] v@(VPair (VPair _ _) _)
                         w@(VPair (VPair _ _) _) VStar _ _ _ _) cs) s st mp ls = do
  let (VPair (VPair (VLabel a) (VLabel b)) (VLabel e)) = renameTemp v mp
      (VPair (VPair (VLabel c) (VLabel d)) (VLabel e')) = w
      mp' = mp `Map.union` Map.fromList [(c, a), (d, b), (e', e)]
      gn = toGateName (getName name)
  sendLine s (gn ++ " " ++ labelToNum a ++ " " ++ labelToNum b ++ " " ++ labelToNum e)
  let res = interaction cs s st mp' ls
  fmap (\(x,y) -> (x, g:y)) res

interaction (RW_Write g _) _ _ _ _ =
  error $ "Unsupported gate: " ++ show g

toGateName "CNot"       = "CNOT"
toGateName "CY"         = "CY"
toGateName "CZ"         = "CZ"
toGateName "Meas"       = "M"
toGateName "Toffoli"    = "TOF"
toGateName "QNot"       = "X"
toGateName "H"          = "H"
toGateName "ZGate"      = "Z"
toGateName "YGate"      = "Y"
toGateName "C_X"        = "X"
toGateName "C_Z"        = "Z"
toGateName "SGate"      = "S"
toGateName "TGate"      = "T"
toGateName "TGate_Inv"  = "T*"
toGateName "SGate_Inv"  = "S*"
toGateName "Discard"    = "D"
toGateName "Rot"        = "ROT"
toGateName "Rot_Inv"    = "ROT"
toGateName "R"          = "CROT"
toGateName "R_Inv"      = "CROT"
toGateName "Diag"       = "DIAG"
toGateName a =
   E.throw $ userError $ "unsupported gate: " ++ a

-- Socket-only client with deterministic close and no Handles.
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
      setSocketOption sock NoDelay 1
      connect sock $ addrAddress addr
      pure sock

-- | Convert applicative natural number into the haskell Int type.
toInt :: Value -> Maybe Int
toInt (VApp (VConst id) t') =
  if getName id == "S" then do
    n <- toInt t'
    return (1 + n)
  else Nothing
toInt (VConst id) =
  if getName id == "Z" then Just 0 else Nothing
toInt _ = Nothing
