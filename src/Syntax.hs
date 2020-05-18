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
This module describes the abstract syntax of Proto-Quipper-D. We use Peter Selinger's
nominal library to handle the affair of variable bindings in the abstract syntax.
Please see <http://hackage.haskell.org/package/nominal here> for
the documentation of nominal library.
-}
module Syntax
       (
         Exp(..),
         EExp(..),
         Value(..),
         Pattern(..),
         Branches(..),
         EBranches(..),
         EPattern(..),
         Gate(..),
         Morphism(..),
         LEnv,
         Gates,
         Decl(..),
         toExp,
         BExp(..),
         Modality(..),
         identityMod
       )
       where

import Utils
import Prelude hiding ((.), (<>))


import Nominal
import Nominal.Atom
import Nominal.Atomic

import Control.Monad.Identity
import Control.Monad.Except
import Text.PrettyPrint
import qualified Data.Map as Map
import qualified Data.Set as S
import Data.Map (Map)

import Data.List
import Debug.Trace



-- | The core abstract syntax tree for dpq expression. The core syntax contains
-- the surface syntax and other forms of annotations for proof checking.
data Exp =
  Var Variable -- ^ Variable. 
  | EigenVar Variable  -- ^ Eigenvariable, it acts as constant during unification. 
  | GoalVar Variable -- ^ Goal variable, it is to be substituted by a dictionary. 

  -- User defined constant
  | Const Id  -- ^ Data constructors or functions. 
  | LBase Id -- ^ Simple type constructors.
  | Base Id  -- ^ (Non-simple) Data type constructors.

  -- Arrows
  | Lam (Bind [Variable] Exp) -- ^ Lambda abstraction for linear arrow type.
  | Lam' (Bind [Variable] Exp) -- ^ Parameter lambda abstraction for parameter arrow type.

  | Arrow Exp Exp -- ^ Linear arrow type. 
  | Arrow' Exp Exp -- ^ Parameter arrow type.
    
  | App Exp Exp -- ^ Application. 
  | App' Exp Exp -- ^ Parameter application.

    -- Dictionary abstraction and application.  
  | AppDict Exp Exp -- ^ Dictionary application. 
  | Imply [Exp] Exp -- ^ Constraint types. 
  | LamDict (Bind [Variable] Exp) -- ^ Dictionary abstraction.

    -- Pair and existential  
  | Tensor Exp Exp -- ^ Tensor product. 
  | Pair Exp Exp  -- ^ Pair constructor, also works for existential pair. 
  | Let Exp (Bind Variable Exp)  -- ^ Single let expression. 
  | LetPair Exp (Bind [Variable] Exp) -- ^ Let pair matching and existential pair matching.
  | LetPat Exp (Bind Pattern Exp) -- ^ Let pattern matching. 
  | Exists (Bind Variable Exp) Exp -- ^ Existential pair.
  | Case Exp Branches -- ^ Case expression.

    -- Lift and force  
  | Bang Exp Modality -- ^ Linear exponential type.
  | Force Exp -- ^ Force. 
  | Force' Exp -- ^ Force', the parameter version of Force.
  | Lift Exp -- ^ Lift. 

    -- Circuit operations  
  | Box -- ^ Circuit boxing. 
  | ExBox -- ^ Existential circuit boxing. 
  | UnBox -- ^ Circuit unboxing.
  | Reverse  -- ^ Obtain the adjoint of a circuit.
  | Controlled  -- ^ Obtain the controlled version of a circuit.
  | WithComputed  
  | Circ Exp Exp Modality -- ^ The circuit type. 
  | Dynlift
    -- constants  
  | Star  -- ^ Unique inhabitant of unit type.
  | Unit -- ^ The unit type.
  | Set  -- ^ The kind for all types. 
  | Sort  -- ^ The sort for all kinds. 

    -- Dependent types
  | Pi (Bind [Variable] Exp) Exp -- ^ Linear dependent types. 
  | Pi' (Bind [Variable] Exp) Exp -- ^ Intuitionistic dependent types.
    
  | PiImp (Bind [Variable] Exp) Exp -- ^ Implicit dependent types. 

  | LamDep (Bind [Variable] Exp) -- ^ Linear dependent lambda abstraction (abstracting term). 
  | LamDep' (Bind [Variable] Exp) -- ^ Intuitionistic dependent lambda abstraction (abstracting term). 

  | AppDep Exp Exp -- ^ Linear dependent application (term application). 
  | AppDep' Exp Exp -- ^ Intuitionistic dependent application (term application). 

  -- explicit type abstraction and application
  | LamDepTy (Bind [Variable] Exp) -- ^ Dependent lambda abstraction (abstracting type). 
  | AppDepTy Exp Exp -- ^ Dependent application (type application). 

  | LamAnn Exp (Bind [Variable] Exp)
    -- ^ Annotated lambda abstraction. This uses infer mode to infer the body. 
  | LamAnn' Exp (Bind [Variable] Exp) -- ^ Shape of 'LamAnn'. 
  
  | WithType Exp Exp -- ^ Annotated term.

  -- Irrelavent quantification.  
  | Forall (Bind [Variable] Exp) Exp  -- ^ Irrelevant quantification.     
  | LamType (Bind [Variable] Exp) -- ^ Irrelevant type abstraction.
  | LamTm (Bind [Variable] Exp) -- ^ Irrelevant term abstraction.
  | AppType Exp Exp -- ^ Irrelevant type application. 
  | AppTm Exp Exp  -- ^ Irrelevant term application.
  -- others.  
  | PlaceHolder -- ^ Wildcard. 
  | Pos Position Exp -- ^ Position wrapper.
  | Mod (Bind [Variable] Exp) -- ^ Top level binding for modality variables. 
  deriving (Eq, Generic, Nominal, NominalShow, NominalSupport, Show)

-- | Branches for case expressions.
data Branches = B [Bind Pattern Exp]
              deriving (Eq, Generic, Show, NominalSupport, NominalShow, Nominal)

-- | Pattern can a bind term variable or a type variable, or have an instantiation ('Left')
-- that is bound at a higher-level. 
data Pattern = PApp Id [Either (NoBind Exp) Variable] 
             deriving (Eq, Generic, NominalShow, NominalSupport, Nominal, Bindable, Show)

-- | Boolean expression.
data BExp = BConst Bool
          | BVar Variable
          | BAnd BExp BExp
  deriving (Show, NominalShow, NominalSupport, Generic, Nominal, Eq)

-- | A data type for modality: bx, ctrl, adj
data Modality = M BExp BExp BExp 
  deriving (Show, NominalShow, NominalSupport, Generic, Nominal, Eq)


identityMod :: Modality
identityMod = M (BConst True) (BConst True) (BConst True)


instance Disp Pattern where
  display flag (PApp id vs) =
    display flag id <+>
    hsep (map helper vs) 
    where helper (Left (NoBind x)) =
            braces $ display flag x
          helper (Right x) = display flag x 

-- | A helper function for display various of applications.
dispAt :: Bool -> String -> Doc          
dispAt b s =
  if b then text "" else text (" @"++s)

instance Disp Exp where
  display flag (Var x) = display flag x
  display flag (GoalVar x) = display flag x
  display flag (EigenVar x) = brackets (display flag x)
  display flag (Const id) = display flag id
  display flag (LBase id) = display flag id
  display flag (Base id) = display flag id
  display flag (Pos _ e) = display flag e
  display flag (Mod (Abst vs e)) = display flag e
  display flag (Lam bds) =
    open bds $ \ vs b ->
    fsep [text "\\" , (hsep $ map (display flag) vs), text "->", nest 2 $ display flag b]
  display flag (LamAnn ty bds) =
    open bds $ \ vs b ->
    fsep [text "\\(" , hsep $ map (display flag) vs, text ":", display flag ty,  text ") ->", nest 2 $ display flag b]

  display flag (LamAnn' ty bds) =
    open bds $ \ vs b ->
    fsep [text "\\'(" , hsep $ map (display flag) vs, text ":", display flag ty,  text ") ->", nest 2 $ display flag b]

  display flag (Lam' bds) =
    open bds $ \ vs b ->
    fsep [text "\\'" , (hsep $ map (display flag) vs), text "->", nest 2 $ display flag b]
  display flag (LamDict bds) =
    open bds $ \ vs b ->
    fsep [text "\\dict" , (hsep $ map (display flag) vs), text "->", nest 2 $ display flag b]    
  display flag (LamTm bds) =
    open bds $ \ vs b ->
    fsep [text "\\tm" , (hsep $ map (display flag) vs) <+> text "->", nest 2 $ display flag b]
    
  display flag (LamDep bds) =
    open bds $ \ vs b ->
    fsep [text "\\dep" , (hsep $ map (display flag) vs) <+> text "->", nest 2 $ display flag b]

  display flag (LamDepTy bds) =
    open bds $ \ vs b ->
    fsep [text "\\depTy" , (hsep $ map (display flag) vs) <+> text "->", nest 2 $ display flag b]

  display flag (LamDep' bds) =
    open bds $ \ vs b ->
    fsep [text "\\dep'" , (hsep $ map (display flag) vs) <+> text "->", nest 2 $ display flag b]
    
  display flag (LamType bds) =
    open bds $ \ vs b ->
    fsep [text "\\ty" , (hsep $ map (display flag) vs) <+> text "->", nest 2 $ display flag b]

  display flag (Forall bds t) =
    open bds $ \ vs b ->
    fsep [text "forall",
          parens ((hsep $ map (display flag) vs) <+> text ":" <+> display flag t)
          <+> text "->", nest 5 $ display flag b]

  display flag a@(App t t') =
    case toNat a of
      Nothing ->
            fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
      Just i -> int i
    where toNat (App (Const id) t') =
            if getName id == "S" then
              do n <- toNat t'
                 return $ 1+n
              else Nothing
          toNat (Const id) = 
            if getName id == "Z" then
                 return 0
            else Nothing
          toNat (Pos _ e) = toNat e
          toNat _ = Nothing
    
    
  display flag a@(AppType t t') =
    fsep [dParen flag (precedence a - 1) t <> dispAt flag "AppType",
          dParen flag (precedence a) t']
    
  display flag a@(App' t t') =
    case toNat a of
      Nothing ->
            fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']
      Just i -> int i
    where toNat (App' (Const id) t') =
            if getName id == "S" then
              do n <- toNat t'
                 return $ 1+n
              else Nothing
          toNat (Const id) = 
            if getName id == "Z" then
                 return 0
            else Nothing
          toNat (Pos _ e) = toNat e
          toNat _ = Nothing


  display flag a@(AppDep t t') =
       fsep [dParen flag (precedence a - 1) t <> dispAt flag "AppDep",
             dParen flag (precedence a) t']

  display flag a@(AppDepTy t t') =
       fsep [dParen flag (precedence a - 1) t <> dispAt flag "AppDepTy",
             dParen flag (precedence a) t']

  display flag a@(AppDep' t t') =
    fsep [dParen flag (precedence a - 1) t <> dispAt flag "AppDep'",
          dParen flag (precedence a) t']
    
  display flag a@(AppDict t t') =
    fsep [dParen flag (precedence a - 1) t <> dispAt flag "AppDict",
          dParen flag (precedence a) t']
    
  display flag a@(AppTm t t') =
     fsep [dParen flag (precedence a - 1) t <> dispAt flag "AppTm",
           dParen flag (precedence a) t']
    
  display flag a@(Bang t m) =
    text "!" <> display flag m <> dParen flag (precedence a - 1) t

  display flag a@(Arrow t1 t2) =
    fsep [dParen flag (precedence a) t1, text "->" , dParen flag (precedence a - 1) t2]

  display flag a@(Arrow' t1 t2) =
    fsep [dParen flag (precedence a) t1, text "->'" , dParen flag (precedence a - 1) t2]    

  display flag (Imply [] t2) = display flag t2

  display flag a@(Imply t1 t2) =
    fsep [parens (fsep $ punctuate comma $ map (display flag) t1), text "=>" , nest 2 $ display flag t2]
    
  display flag Set = text "Type"
  display flag Sort = text "Sort"
  display flag Unit = text "Unit"
  display flag Star = text "()"
  display flag a@(Tensor t t') =
    fsep [dParen flag (precedence a - 1) t,  text "*", dParen flag (precedence a) t']
  display flag (Pair a b) =
    parens $ fsep [display flag a, text "," , display flag b]
    
  display flag (Force m) = text "&" <> display flag m
  display flag (Force' m) = text "&'" <> display flag m
  display flag (Lift m) = text "lift" <+> display flag m

  display flag (Circ u t m) =
    text "Circ" <> display flag m <> (parens $ fsep [display flag u <> comma, display flag t])
  display flag (Pi bd t) =
    open bd $ \ vs b ->
    fsep [parens ((hsep $ map (display flag) vs) <+> text ":" <+> display flag t)
    <+> text "->" , nest 2 $ display flag b]

  display flag (PiImp bd t) =
    open bd $ \ vs b ->
    fsep [braces ((hsep $ map (display flag) vs) <+> text ":" <+> display flag t)
    <+> text "->" , nest 2 $ display flag b]

  display flag (Pi' bd t) =
    open bd $ \ vs b ->
    fsep [parens ((hsep $ map (display flag) vs) <+> text ":" <+> display flag t)
    <+> text "->'" , nest 2 $ display flag b]
    
  display flag (Exists bd t) =
    open bd $ \ v b ->
    fsep [parens (display flag v <+> text ":" <+> display flag t),
           text "*" , nest 2 $ display flag b]    
  display flag (Box) = text "box"
  display flag (ExBox) = text "existsBox"
  display flag (UnBox) = text "unbox" 
  display flag (Reverse) = text "reverse"
  display flag (Controlled) = text "controlled"
  display flag (WithComputed) = text "withComputed"
  display flag (Dynlift) = text "dynlift"
  display flag (Let m bd) =
    open bd $ \ x b ->
    fsep [text "let" <+> display flag x <+> text "=", display flag m,
          text "in" <+> display flag b]
    
  display flag (LetPair m bd) =
    open bd $ \ xs b ->
    fsep [text "let" <+> parens (hsep $ punctuate comma $ map (display flag) xs),
          text "=", display flag m,
          text "in" <+> display flag b]

  display flag (LetPat m bd) =
    open bd $ \ ps b ->
    fsep [text "let" <+> (display flag ps) <+> text "=" , display flag m,
          text "in" <+> display flag b]

  display flag (Case e (B brs)) =
    text "case" <+> display flag e <+> text "of" $$
    nest 2 (vcat $ map helper brs)
    where helper bd =
            open bd $ \ p b -> fsep [display flag p, text "->" , nest 2 (display flag b)]
  display flag (WithType e ty) =
    display flag e <+> text ":" <+> display flag ty
  display flag e = error $ "from display: " ++ show e

  precedence (Var _ ) = 12
  precedence (GoalVar _ ) = 12
  precedence (EigenVar _ ) = 12
  precedence (Base _ ) = 12
  precedence (LBase _ ) = 12
  precedence (Const _ ) = 12
  precedence (Circ _ _ _) = 12
  precedence (Unit) = 12
  precedence (Star) = 12
  precedence (Box) = 12
  precedence (UnBox) = 12
  precedence (Reverse) = 12
  precedence (ExBox) = 12
  precedence (Set) = 12
  precedence (App _ _) = 10
  precedence (App' _ _) = 10  
  precedence (AppType _ _) = 10
  precedence (AppDep _ _) = 10
  precedence (AppDep' _ _) = 10

  precedence (AppDict _ _) = 10
  precedence (AppTm _ _) = 10
  precedence (Pair _ _) = 11
  precedence (Arrow _ _) = 7
  precedence (Arrow' _ _) = 7
  precedence (Tensor _ _) = 8
  precedence (Bang _ _) = 9
  precedence (Pos p e) = precedence e
  precedence _ = 0

instance NominalShow (NoBind Exp) where
  showsPrecSup sup d (NoBind x) = showsPrecSup sup d x

instance Disp (Either (NoBind Exp) Variable) where
  display flag (Left (NoBind e)) = braces $ display flag e
  display flag (Right x) = display flag x


-- | The value domain, for evaluation purpose.  
data Value =
  VLabel Label -- ^ Labels.
  | VVar Variable -- ^ For the parameters and generic control in a gate. 
  | VConst Id -- ^ Constructors.
  | VTensor Value Value -- ^ Runtime tensor product for generating fresh labels. 
  | VUnit -- ^ Runtime unit type for generating unit value.
  | VLBase Id -- ^ Runtime simple types.
  | VBase Id -- ^ Runtime non-simple type. 
  | VLam (Bind LEnv (Bind [Variable] EExp))
    -- ^ Lambda forms a closure. ['Variable']
    -- is the list of variables that are referred by this closure.
  | VPair Value Value -- ^ Pair of values.
  | VStar -- ^ Unit value. 
  | VLift (Bind LEnv EExp) -- ^ Lift forms a closure. ['Variable']
    -- is the list of variables that is refered by this closure.
  | VLiftCirc (Bind [Variable] (Bind LEnv EExp))
    -- ^ Circuit binding, [Variable] is like a lambda that handles the parameter arguments
    -- and the control argument, LEnv binds a variable to a circuit value.
  | VCircuit Morphism
    -- ^ Unbound circuit (incomplete).
    -- ^ Complete circuit.
  | VApp Value Value
    -- ^ Applicative value, for runtime efficiency, we also
    -- store free variables.
  | VForce Value -- ^ Value version of 'Force'.
  | VComputed Value
  | VBox -- ^ Value version of 'Box'.
  | VExBox -- ^ Value version of 'ExBox'.
  | VUnBox -- ^ Value version of 'UnBox'.
  | VReverse -- ^ Value version of 'Reverse'.
  | VControlled -- ^ Value version of 'Controlled'.
  | VWithComputed
  | VDynlift
  deriving (Show, NominalShow, NominalSupport, Generic, Nominal)

-- | Local variable environment for evaluation. It contains the
-- approximate number of uses of for each variable. 
type LEnv = Map Variable Value

instance Bindable (Map Variable Value) where
  binding loc = do
    loc' <- map_binding (Map.toList loc)
    pure $ Map.fromList loc'
      where
        map_binding [] = pure []
        map_binding ((k,v):t) = do
          k' <- binding k
          v' <- nobinding v
          t' <- map_binding t
          pure ((k',v'):t')  

-- | Gate, ['Value'] is a list of parameters, the last three values
-- are input, output, control and controllable flag.          
data Gate = Gate{
  gateName :: Id,
  params :: [Value],
  inputVal :: Value,
  outputVal :: Value,
  ctrl :: Value,
  ctrlFlag :: Bool
  }
  deriving (Show, NominalShow, NominalSupport, Generic, Nominal)
-- | A list of gates.
type Gates = [Gate]

-- | Morphism denotes an incomplete circuit, a completion would be
-- using the Wired constructor to bind all the free labels in it.
data Morphism = Morphism {input :: Value,
                          gates :: Gates,
                          output :: Value}
  deriving (Show, NominalShow, NominalSupport, Generic, Nominal)
           
  
instance Disp Value where
  display flag (VLabel l) = display flag l
  display flag (VVar l) = text $ show l
  display flag (VLBase id) = display flag id
  display flag (VBase id) = display flag id
  display flag (VConst id) | getName id == "Z" = text "0"
  display flag (VConst id) | getName id == "VNil" = text "[]"
  display flag (VConst id) = display flag id
  display flag (VTensor x y) = display flag x <+> text "*" <+> display flag y
  display flag (VPair x y) = parens $ fsep [ display flag x, text "," , display flag y]
  display flag (VUnit) = text "Unit"
  display flag (VStar) = text "()"
  display flag (VBox) = text "box"
  display flag (VExBox) = text "existsBox"
  display flag (VUnBox) = text "unbox"
  display flag (VReverse) = text "reverse"
  display flag (VControlled) = text "controlled"
  display flag (VWithComputed) = text "withComputed"
  display flag (VDynlift) = text "dynlift"
  display flag (VCircuit m) = display flag m
  display flag (VLam _) = text "lam"
  display flag (VLift _) = text "vlift"
  display flag (VLiftCirc (Abst vs (Abst env e))) = text "vliftCirc"

  display flag a@(VApp t t') = 
    case toNat a of
      Nothing ->
        case toVec a of
          Nothing ->
            fsep [dParen flag (precedence a - 1) t, dParen flag (precedence a) t']

          Just vs -> brackets $ fsep $ punctuate comma $ map (\ x -> display flag x ) vs
      Just i -> int i
    where toNat (VApp (VConst id) t') =
            if getName id == "S" then
              do n <- toNat t'
                 return $ 1+n
              else Nothing
          toNat (VConst id) = 
            if getName id == "Z" then
                 return 0
            else Nothing
          toNat _ = Nothing
          toVec (VConst id) =
            if getName id == "VNil" then return []
            else Nothing
          toVec (VApp (VApp (VConst id) e) res) =
            if getName id == "VCons" then
              do vs <- toVec res
                 return $ e:vs
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
     map (\ (x, y) ->
           dispRaw x <+> text ":=" <+> display flag y) (Map.toList l)
                      

instance Disp (Map Variable (Value, Int, Int)) where
   display flag l =
     vcat $
     map (\ (x, (y, n, ref)) -> dispRaw x <> text ":" <> int n
                                <> text ":" <> int ref <+> text ":=" <+> display flag y)
     (Map.toList l)

instance Disp Morphism where
 display flag (Morphism ins gs outs) =
   nest 2 (vcat $ map (display flag) gs) 


instance Disp Gate where
  display flag (Gate g params ins outs ctrls b) =
    display flag g <> comma <+> brackets (hsep $ punctuate comma (map (display flag) params))
    <> comma <+> (display flag ins) <> comma <+> (display flag outs) <> comma
    <+> (display flag ctrls) <> comma <+> text (show b)

-- | Convert a /basic value/ from the value domain to an expression,
-- so that the type checker can take advantage of cbv.   
toExp :: Value -> Exp
toExp (VConst id) = Const id
toExp VStar = Star
toExp (VApp a b) = App (toExp a) (toExp b)
toExp (VPair a b) = Pair (toExp a) (toExp b)

-- | Declarations in abstract syntax, resolved from the declarations
-- in the concrete syntax. 
data Decl = Object Position Id -- ^ Declaration for qubit or bit.
            
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
            -- ^ Function declaration. 'Id': name, 'Exp': type, 'Exp': definition
          | GateDecl Position Id [Exp] Exp Modality
          | CircuitDecl Position Id Exp Morphism
            -- ^ Gate declaration. 'Id': name, ['Exp']: parameters, 'Exp': input/output.
          | ImportDecl Position String
            -- ^ Importation.
          | OperatorDecl Position String Int String
            -- ^ Operator declaration. String: operator name, Int: precedence, String: fixity.
          | Defn Position Id (Maybe Exp) Exp Bool
            -- ^ Function declaration in infer mode. 'Id': name,
            -- 'May' 'Exp': maybe a partial type,
            -- 'Exp': definition


-- | A data structure for the erased expression, all bind variables are annotated
-- with its approximate occurrences. 'ELift' and 'ELam' maintain a list of free variables.

data EExp =
  EVar Variable
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
  deriving (Eq, Generic, Nominal, NominalShow, NominalSupport, Show)

-- | Branches for erased case.
data EBranches = EB [Bind EPattern EExp]
               deriving (Eq, Generic, Show, NominalSupport, NominalShow, Nominal)

-- | Erased pattern.
data EPattern = EPApp Id [Variable]
              deriving (Eq, Generic, NominalShow, NominalSupport, Nominal, Bindable, Show)


instance Disp EExp where
  display flag (EVar l) = text $ show l
  display flag (ELBase id) = display flag id
  display flag (EBase id) = display flag id
  display flag (EConst id) = display flag id
  display flag (ETensor x y) = display flag x <+> text "*" <+> display flag y
  display flag (EArrow x y) = display flag x <+> text "->" <+> display flag y
  display flag (EPair x y) = parens $ display flag x <+> text "," <+> display flag y
  display flag (EUnit) = text "Unit"
  display flag (EStar) = text "()"
  display flag (EBox) = text "box"
  display flag (EExBox) = text "existsBox"
  display flag (EUnBox) = text "unbox"
  display flag (EReverse) = text "reverse"
  display flag (EControlled) = text "controlled"
  display flag (EWithComputed) = text "withComputed"
  display flag (EDynlift) = text "dynlift"
  display flag (ELam (Abst vs e)) = 
    sep [text "\\elam",
         hsep (map (\ x -> dispRaw x) vs),
         text "->", nest 2 (display flag e)]
  display flag (ELift e) = 
   text "elift" <+> display flag e
 
  display flag a@(EApp v1 v2) =
    fsep [dParen flag (precedence a - 1) v1, dParen flag (precedence a) v2]
  display flag (EForce v) = text "&" <> display flag v
  display flag (ECase e (EB brs)) =
    text "case" <+> display flag e <+> text "of" $$
    nest 2 (vcat $ map helper brs)
    where helper bd =
            open bd $ \ p b -> fsep [dispRaw p, text "->" , nest 2 (display flag b)]

  display flag (ELet m bd) =
    open bd $ \ x b ->
    fsep [text "elet" <+> dispRaw x <+> text "=", display flag m,
          text "in" <+> display flag b]
    
  display flag (ELetPair m bd) =
    open bd $ \ xs b ->
    fsep [text "elet" <+> parens (hsep $ punctuate comma $ map dispRaw xs),
          text "=", display flag m,
          text "in" <+> display flag b]

  display flag (ELetPat m bd) =
    open bd $ \ ps b ->
    fsep [text "elet" <+> (dispRaw ps) <+> text "=" , display flag m,
          text "in" <+> display flag b]

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
    display flag id <+>
    hsep (map (\ x -> parens (display False x)) vs) 

instance Disp BExp where
  display flag (BVar x) = dispRaw x
  display flag (BConst True) = text "1"
  display flag (BConst False) = text "0"
  display flag (BAnd e1 e2) = display flag e1 <> text "&" <> display flag e2
  
instance Disp Modality where
  display flag (M x y z) =
    braces $ display flag x <> comma
    <> display flag y <> comma <> display flag z 

  
