{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveAnyClass #-}


{-|
This module describes the abstract syntax of Proto-Quipper-D. 
We use Peter Selinger's nominal library to handle variable bindings 
in the abstract syntax.
Please see <http://hackage.haskell.org/package/nominal here> for
the documentation of nominal library.
-}
module Syntax
  ( Exp(..)
  , EExp(..)
  , Value(..)
  , Pattern(..)
  , Branches(..)
  , EBranches(..)
  , EPattern(..)
  , Gate(..)
  , Morphism(..)
  , LEnv
  , Gates
  , Decl(..)
  , toExp
  , BExp(..)
  , Modality(..)
  , MyReal(..)
  , identityMod
  ) where

import Prelude hiding ((.), (<>))
import Utils

import Nominal
import Nominal.Atom
import Nominal.Atomic

import Control.Monad.Except
import Control.Monad.Identity
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as S
import Text.PrettyPrint
import Data.Number.CReal
import Data.List
import Debug.Trace

-- | The core abstract syntax tree for dpq expression.
-- The core syntax contains many
-- forms of annotations for proof checking.
data Exp
  = Var Variable  -- ^ Bound variables. 
  | MetaVar Variable -- ^ Meta variables (for unification). 
  | Const Id -- ^ Data constructors or functions.
  | LBase Id -- ^ Simple data type type-constructors.
  | Base Id -- ^ (Non-simple) Data type type-constructors.
  | Lam (Bind [Variable] Exp)
  -- ^ Lambda abstraction for linear arrow type.
  | LamP (Bind [Variable] Exp)
  -- ^ Parameter lambda abstraction for parameter arrow type.
  | Arrow Exp Exp Modality -- ^ Linear arrow type, with modality.
  | ArrowP Exp Exp -- ^ Parameter arrow type.
  | App Exp Exp -- ^ Function application.
  | AppP Exp Exp -- ^ Parameter application.
  | AppDict Exp Exp -- ^ Dictionary application.
  | Imply [Exp] Exp Modality -- ^ Constraint types, since they are
  -- essentially arrow types, we have to indicate the modality.
  | LamDict (Bind [Variable] Exp) -- ^ Dictionary abstraction.
  | Tensor Exp Exp -- ^ Tensor product.
  | Pair Exp Exp
  -- ^ Pair constructor, also for constructing existential pair.
  | Let Exp (Bind Variable Exp) -- ^ Let expression.
  | LetPair Exp (Bind [Variable] Exp)
  -- ^ Let pair and existential pair elimination.
  | LetPat Exp (Bind Pattern Exp) -- ^ Let pattern matching.
  | Exists (Bind Variable Exp) Exp -- ^ Existential types.
  | Case Exp Branches -- ^ Case expression.
  | Bang Exp Modality -- ^ Linear exponential types, with modalities.
  | Force Exp -- ^ !-type elimination.
  | ForceP Exp -- ^ The parameter version of Force.
  | Lift Exp  -- ^ !-type introduction.

  | Box -- ^ Circuit boxing operator.
  | ExBox -- ^ Existential circuit boxing operator.
  | UnBox -- ^ Circuit unboxing operator.
  | Reverse -- ^ Operator for taking the adjoint of a circuit.
  | Controlled -- ^ Operator for obtaining the controlled version of a circuit.
  | WithComputed -- ^ Operator for circuit conjugation. 
  | Circ Exp Exp Modality -- ^ The circuit type, with modalities.
  | Dynlift -- ^ Operator for dynamic lifting. 
  | Star -- ^ The unique inhabitant of unit type.
  | Unit -- ^ The unit type.
  | Set -- ^ The kind for all types.
  | Sort -- ^ The sort for all kinds.

  | Pi (Bind [Variable] Exp) Exp Modality -- ^ Linear dependent types, with modalities. 
  | PiInt (Bind [Variable] Exp) Exp -- ^ Intuitionistic dependent types.
  | PiImp (Bind [Variable] Exp) Exp Modality -- ^ Implicit dependent types, with modalities.
  | LamDep (Bind [Variable] Exp)
  -- ^ Dependent lambda abstraction. 
  | LamDepInt (Bind [Variable] Exp)
  -- ^ Dependent lambda abstraction for parameter term. 
  | AppDep Exp Exp -- ^ Dependent application. 
  | AppDepInt Exp Exp
  -- ^ Dependent application for parameter term. 
  | LamDepTy (Bind [Variable] Exp)
  -- ^ Dependent lambda type abstraction.
  | AppDepTy Exp Exp -- ^ Dependent type application. 
  | LamAnn Exp (Bind [Variable] Exp)
    -- ^ Annotated lambda abstraction.
  | LamAnnP Exp (Bind [Variable] Exp) -- ^ Shape of 'LamAnn'.
  | WithType Exp Exp -- ^ Annotated term.
  | Forall (Bind [Variable] Exp) Exp -- ^ Irrelevant quantification.
  | LamType (Bind [Variable] Exp) -- ^ Irrelevant type abstraction.
  | LamTm (Bind [Variable] Exp) -- ^ Irrelevant term abstraction.
  | AppType Exp Exp -- ^ Irrelevant type application.
  | AppTm Exp Exp -- ^ Irrelevant term application.
  | PlaceHolder -- ^ Underscore.
  | Pos Position Exp -- ^ Position wrapper.
  | Mod (Bind [Variable] Exp)
  -- ^ Top level binding for modality variables.
  | WrapR MyReal -- ^ Build-in reals. 
  | RealNum -- ^ Real type.
  | RealOp String -- ^ Build-in Real operations.
  deriving (Eq, Generic, Nominal, NominalShow, NominalSupport, Show)

-- | A real number in DPQ is a constructive real
-- with an integer indicating the precision.  
data MyReal = MR Int CReal

instance Eq MyReal where
  (MR i x) == (MR j y) =
    showCReal i x == showCReal j y

instance Nominal MyReal where
  pi • p = p

instance NominalSupport MyReal where
  support p = support ()
  
instance NominalShow MyReal where
  showsPrecSup s d (MR n l) a =
    showCReal n l

instance Show MyReal where
  show (MR n l) = showCReal n l


-- | Branches for case expressions.
data Branches =
  B [Bind Pattern Exp]
  deriving (Eq, Generic, Show, NominalSupport, NominalShow, Nominal)

-- | Pattern can a bind term variable or a type variable,
-- or have an instantiation ('Left')
-- that is bound at a higher-level.
data Pattern =
  PApp Id [Either (NoBind Exp) Variable]
  deriving (Eq, Generic, NominalShow, NominalSupport, Nominal,
            Bindable, Show)

-- | Boolean expression. We only need conjunction for modeling modalities. 
data BExp
  = BConst Bool
  | BVar Variable
  | BAnd BExp BExp
  deriving (Show, NominalShow, NominalSupport, Generic, Nominal, Eq)

-- | A data type for boxing modality, controllability, reversibility
data Modality =
  M BExp BExp BExp
  deriving (Show, NominalShow, NominalSupport, Generic, Nominal, Eq)

identityMod :: Modality
identityMod = M (BConst True) (BConst True) (BConst True)

instance Disp Pattern where
  display flag (PApp id vs) =
    display flag id <+> hsep (map helper vs)
    where
      helper (Left (NoBind x)) = parens $ display flag x
      helper (Right x) = display flag x

-- | A helper function for display various of applications.
dispAt :: Bool -> String -> Doc
dispAt b s =
  if b
    then text ""
    else text (" @" ++ s)

instance Disp Exp where
  display flag (Var x) = display flag x
  display flag (MetaVar x) = braces $ display flag x
  display flag (Const id) = display flag id
  display flag (LBase id) = display flag id
  display flag (Base id) = display flag id
  display flag (Pos _ e) = display flag e
  display flag (Mod (Abst vs e)) = display flag e
  display flag (RealNum) = text "Real"
  display flag (WrapR (MR len x)) = text $ showCReal len x
  display flag (RealOp x) = text x
  display flag (Lam bds) =
    open bds $ \vs b ->
      fsep
        [ text "\\"
        , (hsep $ map (display flag) vs)
        , text "->"
        , nest 2 $ display flag b
        ]
  display flag (LamAnn ty bds) =
    open bds $ \vs b ->
      fsep
        [ text "\\("
        , hsep $ map (display flag) vs
        , text ":"
        , display flag ty
        , text ") ->"
        , nest 2 $ display flag b
        ]
  display flag (LamAnnP ty bds) =
    open bds $ \vs b ->
      fsep
        [ text "\\'("
        , hsep $ map (display flag) vs
        , text ":"
        , display flag ty
        , text ") ->"
        , nest 2 $ display flag b
        ]
  display flag (LamP bds) =
    open bds $ \vs b ->
      fsep
        [ text "\\'"
        , (hsep $ map (display flag) vs)
        , text "->"
        , nest 2 $ display flag b
        ]
  display flag (LamDict bds) =
    open bds $ \vs b ->
      fsep
        [ text "\\dict"
        , (hsep $ map (display flag) vs)
        , text "->"
        , nest 2 $ display flag b
        ]
  display flag (LamTm bds) =
    open bds $ \vs b ->
      fsep
        [ text "\\tm"
        , (hsep $ map (display flag) vs) <+> text "->"
        , nest 2 $ display flag b
        ]
  display flag (LamDep bds) =
    open bds $ \vs b ->
      fsep
        [ text "\\dep"
        , (hsep $ map (display flag) vs) <+> text "->"
        , nest 2 $ display flag b
        ]
  display flag (LamDepTy bds) =
    open bds $ \vs b ->
      fsep
        [ text "\\depTy"
        , (hsep $ map (display flag) vs) <+> text "->"
        , nest 2 $ display flag b
        ]
  display flag (LamDepInt bds) =
    open bds $ \vs b ->
      fsep
        [ text "\\dep'"
        , (hsep $ map (display flag) vs) <+> text "->"
        , nest 2 $ display flag b
        ]
  display flag (LamType bds) =
    open bds $ \vs b ->
      fsep
        [ text "\\ty"
        , (hsep $ map (display flag) vs) <+> text "->"
        , nest 2 $ display flag b
        ]
  display flag (Forall bds t) =
    open bds $ \vs b ->
      fsep
        [ text "forall"
        , parens
            ((hsep $ map (display flag) vs) <+> text ":" <+>
                      display flag t) <+> text "->"
        , nest 5 $ display flag b
        ]
  display flag a@(App t t') =
    case toNat a of
      Nothing ->
        fsep [dParen flag (precedence a - 1) t,
              dParen flag (precedence a) t']
      Just i -> int i
    where
      toNat (App (Const id) t') =
        if getName id == "S"
          then do
            n <- toNat t'
            return $ 1 + n
          else Nothing
      toNat (Const id) =
        if getName id == "Z"
          then return 0
          else Nothing
      toNat (Pos _ e) = toNat e
      toNat _ = Nothing
  display flag a@(AppType t t') =
    fsep
      [ dParen flag (precedence a - 1) t <> dispAt flag "AppType"
      , dParen flag (precedence a) t'
      ]
  display flag a@(AppP t t') =
    case toNat a of
      Nothing ->
        fsep [dParen flag (precedence a - 1) t,
              dParen flag (precedence a) t']
      Just i -> int i
    where
      toNat (AppP (Const id) t') =
        if getName id == "S"
          then do
            n <- toNat t'
            return $ 1 + n
          else Nothing
      toNat (Const id) =
        if getName id == "Z"
          then return 0
          else Nothing
      toNat (Pos _ e) = toNat e
      toNat _ = Nothing
  display flag a@(AppDep t t') =
    fsep
      [ dParen flag (precedence a - 1) t <> dispAt flag "AppDep"
      , dParen flag (precedence a) t'
      ]
  display flag a@(AppDepTy t t') =
    fsep
      [ dParen flag (precedence a - 1) t <> dispAt flag "AppDepTy"
      , dParen flag (precedence a) t'
      ]
  display flag a@(AppDepInt t t') =
    fsep
      [ dParen flag (precedence a - 1) t <> dispAt flag "AppDepInt"
      , dParen flag (precedence a) t'
      ]
  display flag a@(AppDict t t') =
    fsep
      [ dParen flag (precedence a - 1) t <> dispAt flag "AppDict"
      , dParen flag (precedence a) t'
      ]
  display flag a@(AppTm t t') =
    fsep
      [ dParen flag (precedence a - 1) t <> dispAt flag "AppTm"
      , dParen flag (precedence a) t'
      ]
  display flag a@(Bang t m) =
    text "!" <> display flag m <> dParen flag (precedence a - 1) t

  display flag a@(Arrow t1 t2 m) =
    fsep
      [ dParen flag (precedence a) t1
      , text "->", display flag m
      , dParen flag (precedence a - 1) t2
      ]
  display flag a@(ArrowP t1 t2) =
    fsep
      [ dParen flag (precedence a) t1
      , text "->'"
      , dParen flag (precedence a - 1) t2
      ]
  -- display flag (Imply [] t2) = display flag t2
  display flag a@(Imply t1 t2 mod) =
    fsep
      [ parens (fsep $ punctuate comma $ map (display flag) t1)
      , text "=>"
      , display flag mod, nest 2 $ display flag t2
      ]
  display flag Set = text "Type"
  display flag Sort = text "Sort"
  display flag Unit = text "Unit"
  display flag Star = text "()"
  display flag a@(Tensor t t') =
    fsep
      [ dParen flag (precedence a - 1) t
      , text "*"
      , dParen flag (precedence a) t'
      ]
  display flag (Pair a b) =
    parens $ fsep [display flag a, text ",", display flag b]
  display flag (Force m) = text "&" <> display flag m
  display flag (ForceP m) = text "&'" <> display flag m
  display flag (Lift m) = text "lift" <+> display flag m
  display flag (Circ u t m) =
    text "Circ" <>
    display flag m <> (parens $ fsep [display flag u <> comma,
                                      display flag t])
  display flag (Pi bd t m) =
    open bd $ \vs b ->
      fsep
        [ parens
            ((hsep $ map (display flag) vs) <+> text ":"
                     <+> display flag t) <+> text "->"
        , display flag m, nest 2 $ display flag b
        ]
  display flag (PiImp bd t m) =
    open bd $ \vs b ->
      fsep
        [ braces
            ((hsep $ map (display flag) vs) <+> text ":" <+>
                     display flag t) <+>
          text "->"
        , display flag m, nest 2 $ display flag b
        ]
  display flag (PiInt bd t) =
    open bd $ \vs b ->
      fsep
        [ parens
            ((hsep $ map (display flag) vs) <+> text ":" <+>
                     display flag t) <+> text "->'"
        , nest 2 $ display flag b
        ]
  display flag (Exists bd t) =
    open bd $ \v b ->
      fsep
        [ parens (display flag v <+> text ":" <+> display flag t)
        , text "*"
        , nest 2 $ display flag b
        ]
  display flag (Box) = text "box"
  display flag (ExBox) = text "existsBox"
  display flag (UnBox) = text "unbox"
  display flag (Reverse) = text "reverse"
  display flag (Controlled) = text "controlled"
  display flag (WithComputed) = text "withComputed"
  display flag (Dynlift) = text "dynlift"
  display flag (Let m bd) =
    open bd $ \x b ->
      fsep
        [ text "let" <+> display flag x <+> text "="
        , display flag m
        , text "in" <+> display flag b
        ]
  display flag (LetPair m bd) =
    open bd $ \xs b ->
      fsep
        [ text "let" <+> parens (hsep $ punctuate comma $
                                   map (display flag) xs)
        , text "="
        , display flag m
        , text "in" <+> display flag b
        ]
  display flag (LetPat m bd) =
    open bd $ \ps b ->
      fsep
        [ text "let" <+> (display flag ps) <+> text "="
        , display flag m
        , text "in" <+> display flag b
        ]
  display flag (Case e (B brs)) =
    text "case" <+>
    display flag e <+> text "of" $$ nest 2 (vcat $ map helper brs)
    where
      helper bd =
        open bd $ \p b ->
          fsep [display flag p, text "->", nest 2 (display flag b)]

  display flag (WithType e ty) =
     display flag e <+> text ":" <+> display flag ty
  display flag e = error $ "from display: " ++ show e

  precedence (Var _) = 12
  precedence (MetaVar _) = 12
  precedence (Base _) = 12
  precedence (LBase _) = 12
  precedence (Const _) = 12
  precedence (RealNum) = 12
  precedence (WrapR _) = 12
  precedence (RealOp _) = 12
  precedence (Circ _ _ _) = 12
  precedence (Unit) = 12
  precedence (Star) = 12
  precedence (Box) = 12
  precedence (UnBox) = 12
  precedence (Reverse) = 12
  precedence (ExBox) = 12
  precedence (Set) = 12
  precedence (App _ _) = 10
  precedence (AppP _ _) = 10
  precedence (AppType _ _) = 10
  precedence (AppDep _ _) = 10
  precedence (AppDepInt _ _) = 10
  precedence (AppDict _ _) = 10
  precedence (AppTm _ _) = 10
  precedence (Pair _ _) = 11
  precedence (Arrow _ _ _) = 7
  precedence (ArrowP _ _) = 7
  precedence (Tensor _ _) = 8
  precedence (Bang _ _) = 9
  precedence (Pos p e) = precedence e
  precedence _ = 0

instance NominalShow (NoBind Exp) where
  showsPrecSup sup d (NoBind x) = showsPrecSup sup d x

instance Disp (Either (NoBind Exp) Variable) where
  display flag (Left (NoBind e)) = parens $ display flag e
  display flag (Right x) = display flag x

-- | Local variable environment for evaluation. 
type LEnv = Map Variable Value

-- | The value domain, for evaluation purpose.
data Value
  = VLabel Label -- ^ Labels.
  | VVar Variable -- ^ Variables, for the parameters substitution and generic control in a gate.
  | VConst Id -- ^ Constructors.
  | VTensor Value Value -- ^ Runtime tensor product types, for generating fresh labels.
  | VUnit -- ^ Runtime unit type for generating unit value.
  | VLBase Id -- ^ Runtime simple types.
  | VBase Id -- ^ Runtime non-simple type.
  | VLam (Bind LEnv (Bind [Variable] EExp))
    -- ^ Lambda forms a closure. ['Variable'] is the list of variables that are referred by this closure.
    
  | VPair Value Value -- ^ Pair of values.
  | VStar -- ^ Unit value.
  | VLift (Bind LEnv EExp) -- ^ Lift forms a closure. ['Variable']
    -- is the list of variables that is refered by this closure.
  | VLiftCirc (Bind [Variable] (Bind LEnv EExp))
    -- ^ Circuit binding, [Variable] is like a lambda that handles the parameter arguments
    -- and the control argument, LEnv binds a variable to a circuit value.
  | Wired (Bind [Label] Morphism)
    -- ^ Complete circuit.
  | VApp Value Value
    -- ^ Applicative value, for runtime efficiency, we also
    -- store free variables.
  | VForce Value -- ^ Value version of 'ForceP.
  | VComputed Value
  | VBox -- ^ Value version of 'Box'.
  | VExBox -- ^ Value version of 'ExBox'.
  | VUnBox -- ^ Value version of 'UnBox'.
  | VReverse -- ^ Value version of 'Reverse'.
  | VControlled -- ^ Value version of 'Controlled'.
  | VWithComputed
  | VDynlift
  | VWrapR MyReal
  | VRealOp String
  deriving (Show, NominalShow, NominalSupport, Generic, Nominal)


instance Bindable (Map Variable Value) where
  binding loc = do
    loc' <- map_binding (Map.toList loc)
    pure $ Map.fromList loc'
    where
      map_binding [] = pure []
      map_binding ((k, v):t) = do
        k' <- binding k
        v' <- nobinding v
        t' <- map_binding t
        pure ((k', v') : t')

-- | Gate, ['Value'] is a list of parameters, the last three values
-- are input, output, control and controllable flag.
data Gate =
  Gate
    { gateName :: Id
    , params :: [Value]
    , inputVal :: Value
    , outputVal :: Value
    , ctrl :: Value
    , ctrlFlag :: Bool
    , inv :: Maybe Id
    }
  deriving (Show, NominalShow, NominalSupport, Generic, Nominal)

-- | A list of gates.
type Gates = [Gate]

-- | Morphism denotes an incomplete circuit, a completion would be
-- using the Wired constructor to bind all the free labels in it.
data Morphism =
  Morphism
    { input :: Value
    , gates :: Gates
    , output :: Value
    }
  deriving (Show, NominalShow, NominalSupport, Generic, Nominal)

instance Disp Value where
  display flag (VLabel l) = display flag l
  display flag (VVar l) = text $ show l
  display flag (VLBase id) = display flag id
  display flag (VBase id) = display flag id
  display flag (VConst id)
    | getName id == "Z" = text "0"
  display flag (VConst id)
    | getName id == "VNil" = text "[]"
  display flag (VConst id) = display flag id
  display flag (VTensor x y) =
    display flag x <+> text "*" <+> display flag y
  display flag (VPair x y) =
    parens $ fsep [display flag x, text ",", display flag y]
  display flag (VUnit) = text "Unit"
  display flag (VStar) = text "()"
  display flag (VBox) = text "box"
  display flag (VExBox) = text "existsBox"
  display flag (VUnBox) = text "unbox"
  display flag (VReverse) = text "reverse"
  display flag (VControlled) = text "controlled"
  display flag (VWithComputed) = text "withComputed"
  display flag (VDynlift) = text "dynlift"
  display flag (Wired (Abst ws m)) = brackets (hsep $ punctuate comma $ map (display flag) ws) $$ display flag m
  display flag (VLam (Abst _ bd)) = open bd $ \vs b ->
    fsep
        [ text "\\"
        , (hsep $ map (display flag) vs)
        , text "->"
        , nest 2 $ display flag b
        ]
  display flag (VWrapR (MR len x)) = text $ showCReal len x
  display flag (VRealOp x) = text x
  -- text "<fun-value>"
  display flag (VLift (Abst _ m)) =
    text "vlift" <+> display flag m
  -- text "<lift-value>"
  display flag (VLiftCirc (Abst vs (Abst env e))) = 
    -- text "<fun-value>"
    brackets (hsep $ punctuate comma $ map (display flag) vs) $$
    braces (display flag env)
    $$ display flag e

  display flag a@(VApp t t') =
    case toNat a of
      Nothing ->
        case toVec a of
          Nothing ->
            fsep
              [dParen flag (precedence a - 1) t,
                dParen flag (precedence a) t']
          Just vs ->
            brackets $ fsep $ punctuate comma $
              map (\x -> display flag x) vs
      Just i -> int i
    where
      toNat (VApp (VConst id) t') =
        if getName id == "S"
          then do
            n <- toNat t'
            return $ 1 + n
          else Nothing
      toNat (VConst id) =
        if getName id == "Z"
          then return 0
          else Nothing
      toNat _ = Nothing
      toVec (VConst id) =
        if getName id == "VNil"
          then return []
          else Nothing
      toVec (VApp (VApp (VConst id) e) res) =
        if getName id == "VCons"
          then do
            vs <- toVec res
            return $ e : vs
          else Nothing
      toVec _ = Nothing
  display flag (VForce v) = text "&" <> display flag v
  precedence (VVar _) = 12
  precedence (VConst _) = 12
  precedence (VBase _) = 12
  precedence (VLBase _) = 12
  precedence (VTensor _ _) = 8
  precedence (VPair _ _) = 11
  precedence (VApp _ _) = 10
  precedence _ = 0

instance Disp (Map Variable Value) where
  display flag l =
    vcat $
    map (\(x, y) -> dispRaw x <+> text ":=" <+> display flag y)
      (Map.toList l)

instance Disp (Map Variable (Value, Int, Int)) where
  display flag l =
    vcat $
    map
      (\(x, (y, n, ref)) ->
         dispRaw x <> text ":" <> int n <> text ":" <> int ref <+>
         text ":=" <+> display flag y)
      (Map.toList l)

instance Disp Morphism where
  display flag (Morphism ins gs outs) = nest 2 (vcat $ map (display flag) gs)

instance Disp Gate where
  display flag (Gate g params ins outs ctrls b _) =
    display flag g <> comma <+>
    brackets (hsep $ punctuate comma (map (display flag) params)) <> comma <+>
    (display flag ins) <> comma <+>
    (display flag outs) <> comma <+>
    (display flag ctrls) <> comma <+> text (show b)

-- | Convert a /basic value/ from the value domain to an expression,
-- so that the type checker can take advantage of cbv.
toExp :: Value -> Exp
toExp (VConst id) = Const id
toExp VStar = Star
toExp (VApp a b) = App (toExp a) (toExp b)
toExp (VPair a b) = Pair (toExp a) (toExp b)

-- | Declarations in abstract syntax, resolved from the declarations
-- in the concrete syntax.
data Decl
  = Object Position Id -- ^ Declaration for qubit or bit.
  | Data Position Id Exp [(Position, Id, Exp)]
            -- ^ Data type declaration.
            -- 'Id': the type constructor, 'Exp': a kind expression, [('Position', 'Id', 'Exp')]:
            -- the list of data constructors with corresponding types.
  | SimpData Position Id Int Exp [(Position, Maybe Int, Id, Exp)]
            -- ^ Simple data type declaration.
            -- 'Id': the type constructor, 'Int': the number of type arguments,
            -- 'Exp': partial kind annotation. In [('Position', 'Maybe' 'Int', 'Id', 'Exp')],
            -- 'Maybe' 'Int': the position where dependent pattern matching is performed.
            -- 'Id': data constructor, 'Exp': pretypes for the data constructors, to
            -- be further processed.
  | Class Position Id Exp Id Exp [(Position, Id, Exp)]
            -- ^ Class declaration.
            -- 'Id': class name, 'Exp': instance function type,
            -- [('Position', 'Id', 'Exp')]: list of methods and their definitions.
  | Instance Position Id Exp [(Position, Id, Exp)]
            -- ^ Instance declaration.
            -- 'Id': instance function name, 'Exp': instance function type,
            -- [('Position', 'Id', 'Exp')]: list of methods and their definitions.
  | Def Position Id Exp Exp Bool
            -- ^ Function declaration. 'Id': name, 'Exp': type, 'Exp': definition.
             
  | GateDecl Position Id (Maybe Exp) Exp (Maybe (Id, Exp)) Bool

  | CircuitDecl Position Id Exp Morphism
            -- ^ Gate declaration. 'Id': name, ['Exp']: parameters, 'Exp': input/output.
  | ImportDecl Position String
            -- ^ Importation.
  | OperatorDecl Position String Int String
            -- ^ Operator declaration. String: operator name, Int: precedence, String: fixity.
  | Defn Position Id (Maybe Exp) Exp Bool-- ^ Function declaration in infer mode. 'Id': name,
            -- 'May' 'Exp': maybe a partial type,
            -- 'Exp': definition

-- | A data structure for the erased expression, all bind variables are annotated
-- with its approximate occurrences. 'ELift' and 'ELamP maintain a list of free variables.
data EExp
  = EVar Variable
  | EConst Id
  | EBase Id
  | ELBase Id
  | EApp EExp EExp
  | EPair EExp EExp
  | ETensor EExp EExp
  | EArrow EExp EExp
  | ELam (Bind [Variable] EExp)
  | ELift EExp
  | EForce EExp
  | EUnBox
  | EReverse
  | EControlled
  | EWithComputed
  | EBox
  | EExBox
  | EDynlift
  | ELet EExp (Bind Variable EExp)
  | ELetPair EExp (Bind [Variable] EExp)
  | ELetPat EExp (Bind EPattern EExp)
  | ECase EExp EBranches
  | EStar
  | EUnit
  | EWrapR MyReal
  | ERealOp String
  deriving (Eq, Generic, Nominal, NominalShow, NominalSupport, Show)

-- | Branches for erased case.
data EBranches =
  EB [Bind EPattern EExp]
  deriving (Eq, Generic, Show, NominalSupport, NominalShow, Nominal)

-- | Erased pattern.
data EPattern =
  EPApp Id [Variable]
  deriving (Eq, Generic, NominalShow, NominalSupport, Nominal, Bindable, Show)

instance Disp EExp where
  display flag (EVar l) = text $ show l
  display flag (ELBase id) = display flag id
  display flag (EBase id) = display flag id
  display flag (EConst id) = display flag id
  display flag (ETensor x y) = display flag x <+> text "*" <+> display flag y
  display flag (EArrow x y) = display flag x <+> text "->" <+> display flag y
  display flag (EPair x y) =
    parens $ display flag x <+> text "," <+> display flag y
  display flag (EUnit) = text "Unit"
  display flag (EStar) = text "()"
  display flag (EBox) = text "box"
  display flag (EWrapR (MR len x)) = text $ showCReal len x
  display flag (ERealOp x) = text x

  display flag (EExBox) = text "existsBox"
  display flag (EUnBox) = text "unbox"
  display flag (EReverse) = text "reverse"
  display flag (EControlled) = text "controlled"
  display flag (EWithComputed) = text "withComputed"
  display flag (EDynlift) = text "dynlift"
  display flag (ELam (Abst vs e)) =
    sep
      [ text "\\"
      , hsep (map (\x -> dispRaw x) vs)
      , text "->"
      , nest 2 (display flag e)
      ]
  display flag (ELift e) = text "elift" <+> display flag e
  display flag a@(EApp v1 v2) =
    fsep [dParen flag (precedence a - 1) v1, dParen flag (precedence a) v2]
  display flag (EForce v) = text "&" <> display flag v
  display flag (ECase e (EB brs)) =
    text "case" <+>
    display flag e <+> text "of" $$ nest 2 (vcat $ map helper brs)
    where
      helper bd =
        open bd $ \p b -> fsep [dispRaw p, text "->", nest 2 (display flag b)]
  display flag (ELet m bd) =
    open bd $ \x b ->
      fsep
        [ text "elet" <+> dispRaw x <+> text "="
        , display flag m
        , text "in" <+> display flag b
        ]
  display flag (ELetPair m bd) =
    open bd $ \xs b ->
      fsep
        [ text "elet" <+> parens (hsep $ punctuate comma $ map dispRaw xs)
        , text "="
        , display flag m
        , text "in" <+> display flag b
        ]
  display flag (ELetPat m bd) =
    open bd $ \ps b ->
      fsep
        [ text "elet" <+> (dispRaw ps) <+> text "="
        , display flag m
        , text "in" <+> display flag b
        ]
  precedence (EVar _) = 12
  precedence (EConst _) = 12
  precedence (EBase _) = 12
  precedence (ELBase _) = 12
  precedence (ETensor _ _) = 8
  precedence (EPair _ _) = 11
  precedence (EApp _ _) = 10
  precedence _ = 0

instance Disp EPattern where
  display flag (EPApp id vs) =
    display flag id <+> hsep (map (\x -> parens (display False x)) vs)

instance Disp BExp where
  display flag (BVar x) = dispRaw x
  display flag (BConst True) = text "1"
  display flag (BConst False) = text "0"
  display flag (BAnd e1 e2) = display flag e1 <> text "&" <> display flag e2

instance Disp Modality where
  display flag (M x y z) = 
    braces $
    display flag x <> comma <+> display flag y <> comma <+> display flag z


dispBoxable (BConst True) = text "Boxable"
dispBoxable (BConst False) = text "NonBoxable"
dispBoxable (BAnd e1 e2) = dispBoxable e1 <> text "&" <> dispBoxable e2
dispBoxable (BVar x) = dispRaw x

dispControllable (BConst True) = text "Controllable"
dispControllable (BConst False) = text "NonControllable"
dispControllable (BAnd e1 e2) =
  dispControllable e1 <> text "&" <> dispControllable e2
dispControllable (BVar x) = dispRaw x

dispReversible (BConst True) = text "Reversible"
dispReversible (BConst False) = text "NonReversible"
dispReversible (BAnd e1 e2) =
  dispReversible e1 <> text "&" <> dispReversible e2
dispReversible (BVar x) = dispRaw x
