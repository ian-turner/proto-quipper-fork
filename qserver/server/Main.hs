module Main where

import QuantumServer
import System.IO
import System.Console.GetOpt
import System.Exit
import System.Environment
import Network.Socket hiding (defaultPort)
import Text.Read
import Control.Monad
import Control.Concurrent
import Data.Time.Clock
import Data.Time.LocalTime
usage = usageInfo header options
  where
    header = "Usage: qserver [options]\n" ++ "Options:"

data Options = Options {
  daemon :: Bool,   -- ^ Run as daemon?
  port :: PortNumber,   -- ^ Which port to listen on?
  maxconn :: Int,   -- ^ Maximal number of simultaneous connections, it has to be >= 1.
  logall :: Bool    -- ^ Log all communications? Default: just connections.
  } deriving Show

defaultPort :: Int
defaultPort = 1901

defaultOptions :: Options
defaultOptions = Options {
  daemon = False,
  port = fromIntegral defaultPort,
  maxconn = 10,
  logall = False
  }

-- | Exit with an error message after a command line error. This also
-- outputs information on where to find command line help.
optfail :: String -> IO a
optfail msg = do
  hPutStr stderr msg
  hPutStrLn stderr "Try --help for more info."
  exitFailure

options :: [OptDescr (Options -> IO Options)]
options =
  [ Option ['h'] ["help"] (NoArg o_help) "print usage info and exit",
    Option ['d'] ["daemon"] (NoArg o_daemon) "run as a network service",
    Option ['p'] ["port"] (ReqArg o_port "<port>") ("port to listen on (default: " ++ show defaultPort ++ ")"),
    Option ['n'] ["maxconn"] (ReqArg o_maxconn "<n>") ("limit on simultaneous connections (default: " ++ show (maxconn defaultOptions) ++ ")"),
    Option ['l'] ["logall"] (NoArg o_logall) ("log all communications? (default: just connections)")
  ]
  where
    o_help :: Options -> IO Options
    o_help o = do
      putStrLn usage
      exitSuccess

    o_daemon :: Options -> IO Options
    o_daemon o = return o { daemon = True }
    
    o_port :: String -> Options -> IO Options
    o_port s o =
      case readEither s of
      Right n | n >= 0 -> return o { port = n }
      _ -> optfail ("Invalid port -- " ++ s ++ "\n")

    o_maxconn :: String -> Options -> IO Options
    o_maxconn s o =
      case readEither s of
      Right n -> return o { maxconn = n }
      _ -> optfail ("Invalid number -- " ++ s ++ "\n")
    
    o_logall :: Options -> IO Options
    o_logall o = return o { logall = True }

-- | Process /argv/-style command line options into an 'Options' structure.
dopts :: [String] -> IO Options
dopts argv =
  case getOpt Permute options argv of
   (o, [], []) -> (foldM (flip id) defaultOptions o)
   (_, _, []) -> optfail "Too many non-option arguments\n"
   (_, _, errs) -> optfail (concat errs)


main :: IO ()
main = do
  args <- getArgs
  options <- dopts args
  case daemon options of
    False -> do
      server stdin stdout (\s -> return ())
    True -> do
      let logger = if logall options then logmsg else (\s -> return ())
      addr <- resolve options
      s <- open addr
      listen s 1024 
      accept_n (maxconn options) s logger (port options)

resolve options = 
  do let hints = defaultHints {
           addrFlags = [AI_PASSIVE]
           , addrSocketType = Stream
           }
     head <$> getAddrInfo (Just hints) Nothing (Just $ show $ port options)
  
open addr = do
        sock <- socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr)
        setSocketOption sock ReuseAddr 1
        withFdSocket sock $ setCloseOnExecIfNeeded
        bind sock $ addrAddress addr
        listen sock 1024
        return sock

-- | Accept one connection at a time, on the given socket.
accept_one_by_one :: Socket -> (String -> IO ()) -> PortNumber -> IO ()
accept_one_by_one s logger port = do
  (s', addr) <- accept s
  logmsg_time ("connection from address:" ++ show addr)
  h <- socketToHandle s' ReadWriteMode
  server h h (\s -> logger (show port ++ ": " ++ s))
  hClose h
  logmsg_time ("connection from " ++ show addr ++ " closed")
  accept_one_by_one s logger port

-- | Accept parallel connections on the socket. Each connection forks
-- its own thread.
accept_multiple :: Socket -> (String -> IO ()) -> PortNumber -> IO ()
accept_multiple s logger port = do
  (s', addr) <- accept s
  h <- socketToHandle s' ReadWriteMode
  logmsg_time ("connection from " ++ show addr)
  forkIO $ do
    server h h (\s -> logger (show port ++ ": " ++ s))
    hClose h
    logmsg_time ("connection from " ++ show addr ++ " closed")
  accept_multiple s logger port

-- | Accept at most /n/ parallel connections, or infinitely many if
-- /n/ == -1.
accept_n :: Int -> Socket -> (String -> IO ()) -> PortNumber -> IO ()
accept_n n s logger p
  | n < 0 = accept_multiple s logger p
  | n == 0 = return ()
  | n == 1 = accept_one_by_one s logger p
  | otherwise = do
      forkIO (accept_one_by_one s logger p)
      accept_n (n-1) s logger p

logmsg_time :: String -> IO ()
logmsg_time msg = do
  time <- getCurrentTime
  tz <- getTimeZone time
  let ltime = utcToLocalTime tz time 
  logmsg (show ltime ++ ": " ++ msg)

logmsg :: String -> IO ()
logmsg msg = do
  putStrLn msg
  hFlush stdout
