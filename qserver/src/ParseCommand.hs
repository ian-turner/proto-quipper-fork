module ParseCommand where

import Data.Typeable
import Control.Exception
import Text.Read (readEither)
import Data.Char (isPrint)

-- | A register is a natural number.
type Register = Int

-- | A control is either positive or negative.
data Ctrl = Pos Register | Neg Register
          deriving (Show)

-- | A bit is a boolean.
type Bit = Bool

-- | Abstract datatype of commands. See protocol.txt.
data Command =
  Q Bit Register
  | B Bit Register
  | N Register
  | X Register [Ctrl]
  | Y Register [Ctrl]
  | Z Register [Ctrl]
  | H Register [Ctrl]
  | S Register [Ctrl]
  | T Register [Ctrl]
  | Rot Double Register [Ctrl]
  | Diag Double Double Register [Ctrl]
  | TInv Register [Ctrl]
  | SInv Register [Ctrl]
  | CNOT Register Register [Ctrl]
  | TOF Register Register Register [Ctrl]
  | CZ Register Register [Ctrl]
  | CY Register Register [Ctrl]
  | M Register
  | D Register
  | R Register
  | Help          -- ^ Print human-readable usage information.
  | Empty         -- ^ No operation. Used for comments and empty lines.
  | Reset         -- ^ Free resources and reset the machine.
  | Fresh         -- ^ Return address of an unused register.
  | Protocol Int  -- ^ Used for negotiation of protocol versions.
  | Quit          -- ^ Free resources and quit.
  | Dump          -- ^ Dump the current quantum state.  Undocumented.
                  -- Only works for simulators.
    deriving (Show)

data Response = Null
              | OK
              | Reply String
              | Terminate
              | Error String
              | InternalError String
              deriving (Eq, Show, Read)

-- | Exception for parsing errors.
data ParseError = ParseError String String
                  deriving (Typeable)

instance Exception ParseError

instance Show ParseError where
  show (ParseError cmd msg) = "Syntax error: " ++ msg

-- | Parse a line into a command. If not well-formed, raise a parse
-- exception.
parse_command :: String -> Command
parse_command s = aux (words s) where
  aux [] = Empty
  aux (('#' : _) : _) = Empty
  aux ["Q"] = throw (ParseError s "Command Q requires an argument")
  aux ["Q", x] = Q False (parse_reg x)
  aux ["Q", x, b] = b' `seq` Q b' (parse_reg x)
    where b' = parse_bit b
  aux ("Q" : _) = throw (ParseError s "Command Q requires at most two arguments")
  aux ["B"] = throw (ParseError s "Command B requires an argument")
  aux ["B", x] = B False (parse_reg x)
  aux ["B", x, b] = b' `seq` B b' (parse_reg x)
    where b' = parse_bit b
  aux ("B" : _) = throw (ParseError s "Command B requires exactly two arguments")
  aux ["N", x] = N (parse_reg x)
  aux ("N" : _) = throw (ParseError s "Command N requires exactly one argument")
  aux ("X" : y : ctrls) = X (parse_reg y) (map parse_ctrl ctrls)
  aux ("X" : _) = throw (ParseError s "Command X requires at least one argument")
  aux ("Y" : y : ctrls) = Y (parse_reg y) (map parse_ctrl ctrls)
  aux ("Y" : _) = throw (ParseError s "Command Y requires at least one argument")
  aux ("Z" : y : ctrls) = Z (parse_reg y) (map parse_ctrl ctrls)
  aux ("Z" : _) = throw (ParseError s "Command Z requires at least one argument")
  aux ("H" : y : ctrls) = H (parse_reg y) (map parse_ctrl ctrls)
  aux ("H" : _) = throw (ParseError s "Command H requires at least one argument")
  aux ("S" : y : ctrls) = S (parse_reg y) (map parse_ctrl ctrls)
  aux ("S" : _) = throw (ParseError s "Command S requires at least one argument")
  aux ("T" : y : ctrls) = T (parse_reg y) (map parse_ctrl ctrls)
  aux ("T" : _) = throw (ParseError s "Command T* requires at least one argument")
  aux ("ROT" : r : y : ctrls) = Rot (read r) (parse_reg y) (map parse_ctrl ctrls)
  aux ("ROT" : _) = throw (ParseError s "Command ROT requires at least one argument")
  aux ("DIAG" : a : b : y : ctrls) = Diag (read a) (read b) (parse_reg y) (map parse_ctrl ctrls)
  aux ("DIAG" : _) = throw (ParseError s "Command DIAG requires at least one argument")

  aux ("T*" : y : ctrls) = TInv (parse_reg y) (map parse_ctrl ctrls)
  aux ("T*" : _) = throw (ParseError s "Command T* requires at least one argument")
  aux ("S*" : y : ctrls) = SInv (parse_reg y) (map parse_ctrl ctrls)
  aux ("S*" : _) = throw (ParseError s "Command S* requires at least one argument")
  
  aux ("CNOT" : x : y : ctrls) = CNOT (parse_reg x) (parse_reg y) (map parse_ctrl ctrls)
  aux ("CNOT" : _) = throw (ParseError s "Command CNOT requires at least two arguments")

  aux ("TOF" : x : y : z : ctrls) = TOF (parse_reg x) (parse_reg y) (parse_reg z)
                                    (map parse_ctrl ctrls)
  aux ("TOF" : _) = throw (ParseError s "Command TOF requires at least three arguments")
  
  aux ("CZ" : x : y : ctrls) = CZ (parse_reg x) (parse_reg y) (map parse_ctrl ctrls)
  aux ("CZ" : _) = throw (ParseError s "Command CZ requires at least two arguments")
  aux ("CY" : x : y : ctrls) = CY (parse_reg x) (parse_reg y) (map parse_ctrl ctrls)
  aux ("CY" : _) = throw (ParseError s "Command CY requires at least two arguments")
  
  aux ["D", x] = D (parse_reg x)
  aux ("D" : _) = throw (ParseError s "Command D requires exactly one argument")
  aux ["R", x] = R (parse_reg x)
  aux ("R" : _) = throw (ParseError s "Command R requires exactly one argument")
  aux ["M", x] = M (parse_reg x)
  aux ("M" : _) = throw (ParseError s "Command M requires exactly one argument")

  aux ("help" : _) = Help
  aux ("quit" : _) = Quit
  aux (('\EOT' : _) : _) = Quit
  aux ("reset" : _) = Reset
  aux ("dump" : _) = Dump
  aux ("fresh" : _) = Fresh
  aux (cmd : args) 
    | all isPrint cmd = throw (ParseError s ("Unknown command: " ++ show cmd))
    | otherwise = throw (ParseError s ("Bad character"))

  parse_bit "0" = False
  parse_bit "1" = True
  parse_bit b = throw (ParseError s (b ++ " is not a bit, must be 0 or 1"))

  parse_nat r = 
    case readEither r of
      Right n | n >= 0 -> n
      _ -> throw (ParseError s (r ++ " is not a natural number"))

  parse_ctrl ('-' : r) = Neg (parse_nat r)
  parse_ctrl ('+' : r) = Pos (parse_nat r)
  parse_ctrl r = Pos (parse_nat r)

  parse_reg = parse_nat
