-- | This module defines the concrete syntax for the Proto-Quipper-D surface language.
-- The concrete syntax will be resolved into abstract syntax where the variable
-- bindings are appropriately modelled.
{-# LANGUAGE DeriveDataTypeable #-}
module ConcreteSyntax where

import Data.Generics
import Data.List
import Prelude hiding ((<>))
import Syntax (Circuit(..))
import Text.Parsec.Pos
import Text.PrettyPrint
import Data.Number.CReal
import Utils

-- | The expression data type.
data Exp
  = Base String
  -- ^ Constructors must begin with upper case.
  | Var String
  -- ^ Variables and function identifiers must begin with lower case.
  | Type -- ^ The kind: @Type@.
  | Star -- ^ The term unit: @()@.
  | Unit -- ^ The unit type: @Unit@.
  | Arrow Exp Exp -- ^ Linear arrow type: @T -> T@.
  | Imply [Exp] Exp -- ^ Constraint type: @(P) => T@.
  | Tensor Exp Exp -- ^ Tensor product: @T * T'@.
  | Bang Exp -- ^ Bang type: @!A@.
  | Circ Exp Exp 
  -- ^ Circuit type: @Circ(S, S')@.
  | Pi [String] Exp Exp -- ^ Linear dependent type: @(x : T) -> T'@.
  | PiImp [String] Exp Exp -- ^ Implicit dependent type: @{x : T} -> T'@.
  | Exists String Exp Exp -- ^ Linear existential type: @(x : T) * T'@.
  | Forall [([String], Exp)] Exp -- ^ Irrelevant quantification: @forall (x : T) -> t@.
  | Lam [String] Exp -- ^ Lambda abstraction: @\\ x -> t@.
  | LamAnn [String] Exp Exp -- ^ Annotated lambda abstraction: @\\ (x : T) -> t@.
  | App Exp Exp -- ^ Application: @t t'@.
  | Pair Exp Exp -- ^ Pair and existential pair: @(a, b)@.
  | Let [Binding] Exp -- ^ Let expression.
  | Box -- ^ Circuit boxing: @box@.
  | ExBox -- ^ Existential circuit boxing: @existsBox@.
  | UnBox -- ^ Circuit unbox: @unbox@.
  | Reverse -- ^ Circuit reversal: @reverse@.
  | Controlled -- ^ Circuit control: @controlled@.
  | WithComputed -- ^ Circuit control: @controlled@.
  | Dynlift
  | Random -- ^ Random number generation function
  | Case Exp Branches -- ^ Case expression.
  | Wild -- ^ Wildcard.
  | WrapR Int CReal -- ^ real numbers
  | RealNum -- ^ type constructor Real
  | RealOp String -- ^ built-in real operators.
  | Pos Position Exp -- ^ Position wrapper.
  | WithAnn Exp Exp -- ^ Type annotation: @t : T@.
  deriving (Show, Eq)

--  | Circuit Exp [Gate] Exp
-- data Gate = Gate Id [Exp] Exp Exp Exp Bool  deriving (Show, Eq)
-- | Branches for case expression. We currently do not support
-- nested patterns.
type Branches = [(String, [Exp], Exp)]

-- | Bindings for let expression.
data Binding
  = BSingle (String, Exp) -- ^ Single let binding.
  | BPair ([String], Exp) -- ^ Multi-tuple binding.
  | BPattern (String, [Exp], Exp) -- ^ Let pattern binding.
  | BAnn (String, Exp, Exp) -- ^ Let annotation, will be translated away.
  deriving (Show, Eq)

-- | Top-level declarations.
data Decl
  = GateDecl Position String [([String], Exp)] [Exp] Exp (Bool, Bool, Bool) (Maybe String)
  -- ^ Gate declaration, ['Exp'] are the parameters for the gate,
  -- 'Exp' is  a type expression specifying the input and
  -- output of the gate. 'Maybe String'
  -- is the possible inverse gate.
  | CircuitDecl Position String Exp Circuit
  | Object Position String
  -- ^  Object declaration for simple types such as @Qubit@ or @Bit@.
  | Def Position String Exp [String] Exp Bool
  -- ^ Function definition, 'Exp' is the type expression,
  -- ['String'] is a list of arguments, 'Exp' is the definition.
  | Defn
      Position
      String
      [Either Exp ([String], Exp)]
      [Either Exp ([String], Exp)]
      Exp
      Bool
            -- ^ Function definition in infer mode.
            -- The first ['Either' 'Exp' (['String'], 'Exp')]
            -- is a list of irrelevant arguments,
            -- the second ['Either' 'Exp' (['String'], 'Exp')] is a list of annotated arguments.
            -- An argument can be either a type class constraint, or an annotated argument.
  | Data
      Position
      String
      [Exp]
      [([String], Exp)]
      [(Position, String, [Either ([String], Exp) Exp])]
            -- ^ Data type declaration. ['Exp'] is a list of type class constraints,
            -- [(['String'], 'Exp')] is a list of annotated arguments for the type constructor.
            -- The last list [('Position', 'String', ['Either' (['String'], 'Exp') 'Exp'])]
            -- is a list of constructors and their information:
            -- the left part (['String'], 'Exp') is
            -- for existential dependent quantification, the right part 'Exp'
            -- is the usual arguments.
  | SimpData
      Position {-Position for the type constructor-}
      String {- Type constructor name -}
      [String] {- Type constructor type arguments -}
      Exp {- residue kind -}
      [( Position {- Position of the equation -}
       , [Exp] {- arguments -}
       , Position {- Position of the constructor -}
       , String {- Constructor name-}
       , [Exp] {- Constructor arguments-}
        )]
            -- ^ Simple data type declaration. ['String'] are the
            -- type arguments for the type constructor. 'Exp' is a kind expression.
            -- The last list is the list of equations that defined the simple type.
  | ImportGlobal Position String -- ^ Importation of a file.
  | OperatorDecl Position String Int String
            -- ^ Declaration for fixity and priority of infix
            -- operator, e.g. infixr 30 $ . This means the infix operator $ is right associative
            -- and it has the lowest priority, which is 30. The lower the number is, the higher
            -- is the priority.
  | Class
      Position
      String
      [([String], Exp)]
      [(Position, String, Exp, (Bool, Bool, Bool))]
            -- ^ Class declaration. [(['String'], 'Exp')] is a list of annotated arguments.
            -- [('Position', 'String', 'Exp')] is a list of methods and their types.
  | Instance
      Position
      Exp
      [( Position
       , String -- method name
       , [String] -- arguments
       , Exp -- method definition
        )]
            -- ^ Instance declaration. 'Exp' is the instance type expression.
            -- [('Position', 'String', ['String'], 'Exp')] is a list of method definitions.
  deriving (Show)

-- | Command line instruction.
data Command
  = Eval Exp -- ^ Evaluate an expression.
  | Quit -- ^ Quit.
  | Help -- ^ Print help information.
  | Typing Exp -- ^ Print the type or kind information for an expression.
  | RawType Exp -- ^ Print the raw type or kind information for an expression.
  | Load Bool String
  -- ^ Load a file. The Bool is for showing ``loaded ''
  -- when type checking success. 
  | Reload -- ^ Reload a file.
  | Print Exp String -- ^ Print a circuit expression to a file.
  | Display Exp -- ^ Display a circuit expression in system pdf.
  | DisplayEx Exp -- ^ Displaying existential circuit.
  | Annotation Exp -- ^ Print the fully annotated program.
  | GateCount (Maybe String) Exp
  | TopGateCount (Maybe String) (Maybe Exp)
  | ShowCirc (Maybe Exp)
    -- ^ The number of a gate in a circuit expression if name is supplied,
    -- otherwise the total gate.
  deriving (Show)

-- | A Proto-Quipper-D program is a list of declarations.
type Program = [Decl]

-- removePos :: Exp -> Exp
-- removePos = everywhere (mkT rm)
--   where rm (Pos _ e) = e
--         rm e = e

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
flattenArrows (Arrow t1 t2) =
  let (res, h) = flattenArrows t2 in
  ((Nothing, t1):res, h)
flattenArrows a = ([], a)  

