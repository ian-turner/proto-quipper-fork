{-# LANGUAGE FlexibleContexts #-}

-- | An indentation sensitive parser for Proto-Quipper-D.
-- We use <https://hackage.haskell.org/package/parsec parsec library>
-- and <https://hackage.haskell.org/package/indents indents library> for parsing.
module Parser
  ( ParserState
  , parseModule
  , initialParserState
  , parseImports
  , parseCommand
  , parseExp
  ) where

import ConcreteSyntax
import SyntacticOperations
import qualified Syntax as A
import Utils

import Control.Monad.Identity
import Data.Char hiding (isControl)
import qualified Data.IntMap as IM
import Data.List
import Data.Maybe
import Prelude hiding (const)
import Text.Parsec hiding (Empty, ParseError, State)
import qualified Text.Parsec as P
import Text.Parsec.Expr (Assoc(..), Operator(..), buildExpressionParser)
import Text.Parsec.Indent
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token
import Data.Number.CReal

-- *  Parsing a module
-- | A parser for Proto-Quiper-D is an ident-parser with a ParserState.
type Parser a = IndentParser String ParserState a

-- | A parser state contains an expression parser together with
-- an operator table. The initial expression parser is built by combining
-- the initial operator table with the atomic expression parser. The operator table
-- will be updated when encountering an operator fixity declaration,
-- in which case the expression parser will be rebuilt as well.
data ParserState =
  ParserState
    { expParser :: IndentParser String ParserState Exp
    , expOpTable :: IM.IntMap [Operator String ParserState (IndentT Identity) Exp]
    }

-- | The initial parser state.
initialParserState :: ParserState
initialParserState =
  ParserState
    { expParser = buildExpressionParser initialOpTable atomExp
    , expOpTable = IM.fromAscList (zip [0 ..] initialOpTable)
    }

-- | Initial operator table. The precedence is in descending order.
-- (See Text.Parsec.Expr in the parsec package for
-- further information). Currently, we have the following build-in operators:
-- ! and quoted operators (precedence 5), * (precedence 7), -> (precedence 10), : (precedence 16).
-- The quoted operators are things like `xor`, `and`.  
initialOpTable :: [[Operator String ParserState (IndentT Identity) Exp]]
initialOpTable =
  [ []
  , []
  , []
  , []
  , []
  , [unaryBang "!" Bang, quotedOp]
  , []
  , [binOp AssocLeft "*" Tensor]
  , []
  , []
  , [binOp AssocRight "->" Arrow]
  , []
  , []
  , []
  , []
  , []
  , [binOp AssocLeft ":" WithAnn]
  ]
  where
    binOp assoc op f = Infix (reservedOp op >> return f) assoc
    quotedOp =
      Infix
        (operator' >>= \x -> return (\y z -> (App (App (Var x) y) z)))
        AssocNone
    operator' = do
      reservedOp "`"
      op <- var
      reservedOp "`"
      return op
    unaryBang op f =
      Prefix $ do
        reservedOp op
        return (\x -> f x)

-- | Parse a Proto-Quipper-D module from a file name /srcName/ and file
-- handler /cnts/.
parseModule ::
  String
  -> String
  -> ParserState
  -> Either P.ParseError ([Decl], ParserState)
parseModule srcName cnts st = runIndent $ runParserT decls st srcName cnts

-- | Parse an expression.
parseExp :: String -> ParserState -> Either P.ParseError Exp
parseExp exp st = runIndent $ runParserT term st "" exp

-- | Parse only the import declarations from a file. The imports must be declared
-- at the beginning of the file.
parseImports :: String -> String -> Either P.ParseError [Decl]
parseImports srcName cnts =
  runIndent $ runParserT imports initialParserState srcName cnts
  where
    imports = do
      reserved "module"
      const
      reserved "where"
      many importDecl

-- | Parse a command line input using a given parser state.
parseCommand :: String -> ParserState -> Either P.ParseError Command
parseCommand s st = runIndent $ runParserT command st "" s

-- * Command line parser
-- | A parser for the command line.
command :: Parser Command
command = do
  whiteSpace
  quit <|> help <|> typing <|> rawType <|> reload <|> load <|> printing <|> displaying <|>
    displayEx <|>
    annotation <|>
    showCirc <|>
    gateC <|>
    topGateC <|>
    compileOpenQASM <|>
    eval

-- | Parse quit command.
quit :: Parser Command
quit = do
  try (reserved ":quit") <|> reserved ":q"
  eof
  return Quit

-- | Parse help command.
help :: Parser Command
help = do
  try (reserved ":help") <|> reserved ":h"
  eof
  return Help

-- | Parse reload command.
reload :: Parser Command
reload = do
  try (reserved ":reload") <|> reserved ":r"
  eof
  return Reload

-- | Parse the type command
typing :: Parser Command
typing = do
  try (reserved ":type") <|> reserved ":t"
  t <- term
  eof
  return $ Typing t

-- | Parse the rawtype command
rawType :: Parser Command
rawType = do
  try (reserved ":rawtype") <|> reserved ":rt"
  t <- term
  eof
  return $ RawType t

-- | Parse the print-pdf-to-file command.
printing :: Parser Command
printing = do
  try (reserved ":print") <|> reserved ":p"
  t <- term
  path <- stringLiteral
  eof
  return $ Print t path

-- | Parse the display command.
displaying :: Parser Command
displaying = do
  try (reserved ":display") <|> reserved ":d"
  t <- term
  eof
  return $ Display t

-- | Parse the displaying existential circuit command.
displayEx :: Parser Command
displayEx = do
  try (reserved ":existsDisplay") <|> reserved ":e"
  t <- term
  eof
  return $ DisplayEx t

-- | Parse the OpenQASM command
compileOpenQASM :: Parser Command
compileOpenQASM = do
  try (reserved ":saveCircQASM") <|> reserved ":qasm"
  t <- term
  path <- stringLiteral
  eof
  return $ ToQASM t path

-- | Parse the show annotation command.
annotation :: Parser Command
annotation = do
  try (reserved ":annotation") <|> reserved ":a"
  t <- try varExp <|> parens opExp
  eof
  return $ Annotation t

-- | Parse the load command.
load :: Parser Command
load = do
  try (reserved ":load") <|> reserved ":l"
  path <- stringLiteral
  eof
  return $ Load True path

-- | Parse an expression.
eval :: Parser Command
eval = do
  t <- term
  eof
  return $ Eval t

-- | Parse the gate count command.
gateC = do
  try (reserved ":gateCount") <|> reserved ":g"
  name <- option Nothing $ (stringLiteral >>= \x -> return $ Just x)
  t <- term
  eof
  return $ GateCount name t

-- | Parse the gate-count-on-expression command.
topGateC = do
  try (reserved ":topGateCount") <|> reserved ":tg"
  name <- option Nothing $ (stringLiteral >>= \x -> return $ Just x)
  t <- option Nothing $ (term >>= \x -> return $ Just x)
  eof
  return $ TopGateCount name t

-- | Parse a show state command.
showCirc = do
  try (reserved ":show") <|> reserved ":s"
  r <- option Nothing $ (term >>= \x -> return $ Just x)
  eof
  return $ ShowCirc r

-- * Parsers for various of declarations
-- | Parse a top-level declaration. All declarations have to have the
-- same level of indentation.
decls :: Parser ([Decl], ParserState)
decls = do
  reserved "module"
  name <- const
  reserved "where"
  bs <-
    block
      (simpleDecl <|> importDecl <|> classDecl <|> instanceDecl <|> gateDecl <|>
       objectDecl <|>
       dataDecl <|>
       operatorDecl <|>
       funDecl <|>
       funDef <?> "top level declaration")
  st <- getState
  eof
  return (bs, st)

-- | Parse the operator fixity declaration.
operatorDecl :: Parser Decl
operatorDecl = do
  r <- choice [reserved i >> return i | i <- ["infix", "infixr", "infixl"]]
  level <- fromInteger <$> integer
  op <- operator
  p <- getPosition
  st <- getState
  let table = IM.insertWith (++) level [toOp op r App Base] $ expOpTable st
      prog = buildExpressionParser (map snd (IM.toAscList table)) atomExp
  putState $ ParserState prog table
  return (OperatorDecl (P p) op level r)
  where
    toOp op "infix" app var =
      Infix (reservedOp op >> return (\x y -> app (app (var op) x) y)) AssocNone
    toOp op "infixr" app var =
      Infix
        (reservedOp op >> return (\x y -> app (app (var op) x) y))
        AssocRight
    toOp op "infixl" app var =
      Infix (reservedOp op >> return (\x y -> app (app (var op) x) y)) AssocLeft


-- | Parse a head /h/ and many /p/, they can be across many lines,
-- but they must be properly indented.
manyLines :: Parser ([a] -> b) -> Parser a -> Parser b
manyLines h p = withPos $ h <*/> p

-- | Parse an importation declaration.
importDecl :: Parser Decl
importDecl = do
  reserved "import"
  p <- getPosition
  mod <- stringLiteral
  return $ ImportGlobal (P p) mod

-- | Parse a type class declaration. We allow phatom class, i.e. class without
-- any method, in that case, one should not use the keyword "where".
-- Method definitions have to have same level of indentation.
classDecl :: Parser Decl
classDecl = do
  reserved "class"
  (p, c, vs) <-
    manyLines
      (do p <- getPosition
          c <- const
          return $ \ps -> (p, c, ps))
      (try ann <|> impAnn)
  mds <-
    option [] $ do
      reserved "where"
      block method
  return $ Class (P p) c vs mds
  where
    method = do
      fs <-
        sepBy (try noControl <|> try noReverse <|> try noModal <|> noBox) comma
      let fs' = nub fs
      pos <- getPosition
      n <- parens operator <|> var
      reservedOp ":"
      t <- typeExp
      let m =
            if NoModal `elem` fs'
              then (False, False, False)
              else ( not (NoBox `elem` fs')
                   , not (NoControl `elem` fs')
                   , not (NoReverse `elem` fs'))
      return (P pos, n, t, m)

-- | Parse an instance declaration. For the instance of the phantom class,
-- one should not use the keyword "where".
-- Method definitions have to have same level of indentation.
instanceDecl :: Parser Decl
instanceDecl = do
  reserved "instance"
  p <- getPosition
  t <- instanceType
  mds <-
    option [] $ do
      reserved "where"
      block method
  return $ Instance (P p) t mds
  where
    method = do
      pos <- getPosition
      n <- parens operator <|> var
      args <- many var
      reservedOp "="
      def <- term
      return (P pos, n, args, def)

-- | Parse an object declaration.
objectDecl :: Parser Decl
objectDecl = do
  reserved "object"
  p <- getPosition
  o <- const
  return $ Object (P p) o

tensorType = do
  tys <- sepBy1 (unitTy <|> constExp) (reservedOp "*")
  let res = foldl Tensor (head tys) (tail tys)
  return res

simpleType = do
  tys <- sepBy1 tensorType (reservedOp "->")
  let (bds, h) = (init tys, last tys)
  let res = foldr Arrow h bds
  return res


-- | Flags for indicating non-modalities
data NonMod
  = NoBox
  | NoControl
  | NoReverse
  | NoModal
  deriving (Eq)

-- | Parse the #NoControl flag
noControl = do
  reserved "#NoControl"
  return NoControl

-- | Parse the #NoModal flag
noModal = do
  reserved "#NoModal"
  return NoModal

-- | Parse the #NoBox flag
noBox = do
  reserved "#NoBox"
  return NoBox

-- | Parse the #NoReverse flag
noReverse = do
  reserved "#NoReverse"
  return NoReverse

-- | Parse a gate declaration.
gateDecl :: Parser Decl
gateDecl = do
  isCtrl <- option True (do{
    reserved "#NoControl";
    return False})     
  reserved "gate"
  p <- getPosition
  g <- const
  qs <- option [] $ try $ 
             do ans <- (many1 ann)
                reservedOp "->"
                return ans
  args <- many ((const >>= \ a -> return $ Pos (P p) (Base a) ) <|> parens appExp)
  reservedOp ":"
  ty <- simpleType
  inv <-
    option Nothing $ do
      reservedOp ":"
      g' <- const
      return $ Just g'
  let m = (True, isCtrl, isJust inv)
  return $ GateDecl (P p) g qs args ty m inv

-- | Parse a data type declaration. We allow data type without any constructor,
-- in that case, one should not use '='. The syntax is similar to Haskell 98
-- data type declaration, except we allow existential dependent data type and constraint
-- data type.
dataDecl :: Parser Decl
dataDecl = do
  reserved "data"
  tc <-
    option [] $ do
      tyClass <- parens (sepBy1 typeExp comma)
      reserved "=>"
      return tyClass
  (p, head, vs) <-
    manyLines
      (do p <- getPosition
          c <- const
          return $ \ps -> (p, c, ps))
      annotation
  constrs <- option [] $ reservedOp "=" >> (sepBy1 br (reservedOp "|"))
  return $ Data (P p) head tc vs constrs
  where
    br =
      manyLines
        (do p <- getPosition
            c <- const
            return $ \ps -> (P p, c, ps))
        arg
    arg =
      try (ann >>= \x -> return $ Left x) <|>
      (singleExp >>= \x -> return $ Right x)
    annotation = ann <|> impAnn

-- | Parse a simple data type declaration. All clauses have to have
-- the same level of indentation.
simpleDecl :: Parser Decl
simpleDecl = do
  reserved "simple"
  p <- getPosition
  head <- const
  vs <- many var
  reservedOp ":"
  kd <- kindExp
  reserved "where"
  constrs <- block (br head)
  when (null constrs) $
    unexpected ("expected at least one constructor for simple type.")
  return $ SimpData (P p) head vs kd constrs
  where
    br h = do
      pPat <- getPosition
      c <- const
      when (h /= c) $ unexpected (c ++ ", expected name: " ++ h)
      args <- many singlePat
      reservedOp "="
      manyLines
        (do p <- getPosition
            cons <- const
            return $ \tys -> (P pPat, args, P p, cons, tys))
        singlePat

clifford = do
  reserved "#Clifford"
  return True

-- | Parse a function declaration with top-level type annotation.
funDecl :: Parser Decl
funDecl = do
  (f, isClifford) <-
    try $ do
      isClifford <- option False clifford
      f <- parens operator <|> var
      reservedOp ":"
      return (f, isClifford)
  ty <- typeExp
  p <- getPosition
  f' <- try var <|> parens operator
  when (f /= f') $ unexpected (f' ++ ", expected name: " ++ f)
  args <- many var
  reservedOp "="
  def <- term
  return $ Def (P p) f ty args def isClifford

-- | Parse a function definition in the infer mode, where one only annotates
-- types for arguments of the function.
funDef :: Parser Decl
funDef = do
  isClifford <- option False clifford
  p <- getPosition
  f <- parens operator <|> var
  qs <-
    option [] $
    try $ do
      ans <- many1 (try annotation <|> classExp)
      reservedOp "."
      return ans
  args <-
    if null qs
      then many (try explicitAnnotation <|> classExp)
      else many1 (try explicitAnnotation <|> classExp)
  reservedOp "="
  def <- term
  return $ Defn (P p) f qs args def isClifford
  where
    explicitAnnotation = do
      x <- ann
      return $ Right x
    annotation = do
      x <- ann <|> impAnn
      return $ Right x
    classExp = parens typeExp >>= \x -> return $ Left x

-- * Expression parsers
-- | Parse a term. It is built from the operator table.
term :: Parser Exp
term = wrapPos $ getState >>= \st -> expParser st

-- | Parse a kind expression, but it is really a synonym for 'term'.
kindExp :: Parser Exp
kindExp = term

-- | Parse a type expression, but it is really a synonym for 'term'.
typeExp :: Parser Exp
typeExp = term

-- * Parsers for various atomic expressions
-- | Parse an atomic expression. Of course it is defined mutually recursively
-- with the full expression parser.
atomExp :: Parser Exp
atomExp =
  wrapPos
    (circType <|> forallType <|> ifExp <|> caseExp <|> letExp <|> doExp <|>
     lamAnn <|>
     lam <|>
     idiomExp <|>
     num <|>
     vector <|>
     implicitType <|>
     piType <|>
     impType <|>
     existsType <|>
     appExp <?> "expression")


-- | An expression parser for pattern application.
patApp :: Parser Exp
patApp =
  wrapPos $
  manyLines
    (do head <- constExp
        return $ foldl' (\z x -> App z x) head)
    singlePat

-- | An expression parser for a single pattern.
singlePat :: Parser Exp
singlePat =
  wrapPos (try varExp <|> try constExp <|> parens patApp <?> "single pattern")

-- | An expression parser for a single expression.
singleExp :: Parser Exp
singleExp =
  wrapPos (try varExp <|> try constExp <|> parens term <?> "single expression")

-- | Parse an annotation. E.g. @(x1 x2 : Nat)@.
ann :: Parser ([String], Exp)
ann =
  parens $ do
    xs <- many1 var
    reservedOp ":"
    ty <- typeExp
    return (xs, ty)

-- | Parse an implicit annotation. E.g. in @List a@, the variable @a@
-- is parsed to @(a : Type)@.
impAnn :: Parser ([String], Exp)
impAnn = var >>= \x -> return ([x], Type)

-- | Parse an operator in to expression.
opExp :: Parser Exp
opExp = do
  op <- operator
  return $ Base op

-- | Parse /m/, then parse/p/, but return the
-- result of /m/.
followedBy :: Parser b -> Parser a -> Parser b
followedBy m p = do
  r <- m
  p
  return r

realType =
  do reserved "Real"
     return RealNum

-- | A sign for positive and negative reals. 
data Sign = Positive | Negative


applySign :: Num a => Sign -> a -> a
applySign Positive =  id
applySign Negative =  negate
               
sign  :: Parser Sign
sign  =  do { char '-'
            ; return Negative
            }
     <|> return Positive

-- | Parse an unsign number and automatically determine if it is a natural number or a real.
-- If the number is real, included the length of its decimals.
naturalOrFloat :: Parser (Either Integer (Int, CReal))
naturalOrFloat =
  do n <- naturals
     r <- option Nothing $ do{ reservedOp ".";
                               d <- lexeme (many1 digit);
                               return $ Just d
                               }
     case r of
       Nothing -> return $ Left n
       Just i ->
         let len = genericLength i
             i' :: Integer
             i' = read i
         in
         return $ Right
         (len, (fromInteger n :: CReal) +
               ((fromInteger i' / (fromInteger $ 10 ^ len) :: CReal)))

-- | Parse a sign number as a natural number or real. 
number :: Parser (Either Integer (Int, CReal))
number =  do { s <- sign
             ; num <- naturalOrFloat
             ; return (case (num, s) of
                          (Right (l, x), _) -> Right (l, (applySign s x))
                          (Left x, Negative) -> Right (0, negate $ fromInteger x)
                          (Left x, Positive) -> Left x
                      )
             }     

-- | A parser from number to internal presentation of numbers.
num =
  do i <- try number
     case i of
       Left j -> toNat j
       Right (l, i) -> return $ WrapR l i
  where toNat i | i == 0 = return $ Base "Z"
        toNat i | i > 0 =
          do n <- toNat (i-1)
             return $ App (Base "S") n



-- | Parse the vector bracket notation. Currently, we will convert a vector notation into
-- the algebraic data type @Vec@ in the standard library.
vector :: Parser Exp
vector = do
  elems <- brackets (term `sepBy` comma)
  return $ foldr (\x y -> App (App (Base "VCons") x) y) (Base "VNil") elems

-- | Parse an if-then-else expression. Currently, if-then-else is translated
-- to pattern matching on the type @Bool@ in the standard library.
ifExp :: Parser Exp
ifExp = do
  reserved "if"
  c <- term
  reserved "then"
  t1 <- term
  reserved "else"
  t2 <- term
  return $ Case (WithAnn c (Base "Bool")) [("True", [], t1), ("False", [], t2)]

-- | Parse a dependent pi-type.
piType :: Parser Exp
piType = do
  (vs, ty) <-
    try $
    followedBy
      (parens $ do
         vs <- many1 var
         reservedOp ":"
         ty <- typeExp
         return (vs, ty))
      (reservedOp "->")
  t <- typeExp
  return $ Pi vs ty t

-- | Parse an implicit pi-type.
implicitType :: Parser Exp
implicitType = do
  (vs, ty) <-
    try $
    followedBy
      (braces $ do
         vs <- many1 var
         reservedOp ":"
         ty <- typeExp
         return (vs, ty))
      (reservedOp "->")
  t <- typeExp
  return $ PiImp vs ty t

-- | Parse an existential type.
existsType :: Parser Exp
existsType = do
  (v, ty) <-
    try $
    parens $ do
      v <- var
      reservedOp ":"
      ty <- typeExp
      return (v, ty)
  reservedOp "*"
  t <- typeExp
  return $ Exists v ty t

-- | Parse an instance type.
instanceType :: Parser Exp
instanceType = do
  r <-
    option
      [] forallPrefix
  t <- try impType <|> appExp
  return $ makeType r t
  where
    forallPrefix =
      do reserved "forall"
         vs <- many1 ((ann >>= \x -> return x) <|> (impAnn >>= \x -> return x))
         reservedOp "->"
         return vs
    impPiPrefix =
      followedBy (braces $ do
                     vs <- many1 var
                     reservedOp ":"
                     ty <- typeExp
                     return [Left (vs, ty)])
      (reservedOp "->")
    makeType [] t = t
    makeType ((xs, ty):res) t =
      let t' = makeType res t
       in Forall [(xs, ty)] t'
    -- makeType (Left (xs, ty):res) t =
    --   let t' = makeType res t
    --    in PiImp xs ty t'

-- | Parse an type class constraint type.
impType :: Parser Exp
impType = do
  constraints <-
    try $ do
      constraints <- parens $ typeExp `sepBy` comma
      reservedOp "=>"
      return constraints
  ty <- typeExp
  return $ Imply constraints ty

-- | Parse a forall type.
forallType :: Parser Exp
forallType = do
  vs <-
    try $ do
      reserved "forall"
      vs <- many1 (try ann <|> impAnn)
      reservedOp "->"
      return vs
  t <- typeExp
  return $ Forall vs t

-- | Parse a circuit type.
circType :: Parser Exp
circType = do
  reserved "Circ"
  (t, u) <-
    parens $ do
      t <- typeExp
      comma
      u <- typeExp
      return (t, u)
  return $ Circ t u 

-- | Parse @Type@.
ty :: Parser Exp
ty = reserved "Type" >> return Type

-- | Parse a unit.
unit :: Parser Exp
unit = reservedOp "()" >> return Star

-- | Parse the unit type.
unitTy :: Parser Exp
unitTy = reserved "Unit" >> return Unit

-- | Parse a lambda abstraction with annotation.
lamAnn :: Parser Exp
lamAnn = do
  (v, ty) <-
    try $ do
      reservedOp "\\" <|> reservedOp "λ"
      ann
  reservedOp "->"
  t <- term
  return $ LamAnn v ty t

-- | Parse a lambda abstraction.
lam :: Parser Exp
lam = do
  reservedOp "\\" <|> reservedOp "λ"
  vs <- many1 var
  reservedOp "->"
  t <- term
  return $ Lam vs t

-- | Parse a pair.
pairExp :: Parser Exp
pairExp =
  parens $ do
    t1 <- term
    comma
    t2 <- term
    return $ Pair t1 t2

-- | Parse a case expression.
caseExp :: Parser Exp
caseExp =
  withPos $ do
    reserved "case"
    e <- term
    reserved "of"
    indented
    brs <- block branch
    return $ Case e brs
  where
    branch =
      withPos $ do
        h <- const
        args <- many (try varExp <|> wild)
        reservedOp "->"
        indented
        b <- term
        return (h, args, b)

-- | Parse a box expression.
boxExp :: Parser Exp
boxExp = reserved "box" >> return Box

-- | Parse an existsBox expression.
exBoxExp :: Parser Exp
exBoxExp = reserved "existsBox" >> return ExBox

-- | Parse an unbox expression.
unBoxExp :: Parser Exp
unBoxExp = reserved "unbox" >> return UnBox

-- | Parse a reverse expression.
reverseExp :: Parser Exp
reverseExp = reserved "reverse" >> return Reverse

-- | Parse a control expression.
controlExp :: Parser Exp
controlExp = reserved "controlled" >> return Controlled

withComputedExp :: Parser Exp
withComputedExp = reserved "withComputed" >> return WithComputed

dynliftExp :: Parser Exp
dynliftExp = reserved "dynlift" >> return Dynlift

-- | Parse a let expression.
letExp :: Parser Exp
letExp = handleLet True

-- | Parse a let statement.
letStatement :: Parser Exp
letStatement = handleLet False

-- | Help to parse a let expression (True) and let statement (False).
handleLet :: Bool -> Parser Exp
handleLet b =
  if b
    then do
      reserved "let"
      bds <- block bind
      reserved "in"
      t <- term
      return $ Let bds t
    else do
      reserved "let"
      bds <- block bind
      notFollowedBy $ reserved "in"
      return $ Let bds Unit
  where
    bind = letPattern <|> pair <|> letAnn <|> single
    letAnn = do
      f <-
        try $ do
          f <- var
          reservedOp ":"
          return f
      ty <- typeExp
      f' <- var
      when (f /= f') $ unexpected (f' ++ ", expected name: " ++ f)
      reservedOp "="
      tm <- term
      return $ BAnn (f, ty, tm)
    pair = do
      xs <-
        parens $ do
          x <- try var <|> wildString
          comma
          xs <- sepBy1 (try var <|> wildString) comma
          return (x : xs)
      reservedOp "="
      d <- term
      return $ BPair (xs, d)
    single = do
      n <- try var <|> wildString
      reservedOp "="
      d <- term
      return $ BSingle (n, d)
    letPattern = do
      c <- try const
      ps <- many (try varExp <|> wild)
      reservedOp "="
      t <- term
      return $ BPattern (c, ps, t)

-- | Parse an application.
appExp :: Parser Exp
appExp =
  manyLines
    (do head <- headExp
        pos <- getPosition
        return $ foldl (\z x -> Pos (P pos) $ App z x) head)
    arg
  where
    headExp =
      wrapPos $
      try unit <|> try opExp <|> unitTy <|> ty <|> boxExp <|> exBoxExp <|>
      unBoxExp <|>
      reverseExp <|>
      realOp <|> realPi <|>
      controlExp <|>
      realType <|>
      withComputedExp <|>
      dynliftExp <|>
      try varExp <|>
      try constExp <|> do
        tms <- parens (term `sepBy1` comma)
        return $ foldl (\x y -> Pair x y) (head tms) (tail tms)
    arg =
      wrapPos $
      try unit <|> unitTy <|> ty <|> realPi <|> dynliftExp <|> reverseExp <|> try varExp <|> 
      try constExp <|> num <|>
      try vector <|>
      idiomExp <|> do
        tms <- parens (term `sepBy1` comma)
        return $ foldl (\x y -> Pair x y) (head tms) (tail tms)

-- | Parse a wild card string expression.
wild :: Parser Exp
wild = reservedOp "_" >> return Wild

-- | Parse a wild card string.
wildString :: Parser String
wildString = reservedOp "_" >> return "_"

-- | Parse a constructor expression.
constExp :: Parser Exp
constExp = const >>= \x -> return $ Base x

-- | Parse a variable expression.
varExp :: Parser Exp
varExp = (var >>= \x -> return $ Var x)

-- | Parse a variable. The variable must begin with lower case letter.
var :: Parser String
var = do
  n <- identifier
  if (isUpper (head n))
    then unexpected $
         "uppercase word: " ++ n ++ ", expected to begin with lowercase letter"
    else return n

-- | Parse a constructor. The constructor must begin with upper case letter.
const :: Parser String
const = do
  n <- identifier
  if (isLower (head n))
    then unexpected $
         "lowercase word: " ++ n ++ ", expected to begin with uppercase letter"
    else return n

-- | Add a position to the expression.
wrapPos :: Parser Exp -> Parser Exp
wrapPos par = do
  q <- getPosition
  e <- par
  let e' = pos (P q) e
  return e'
  where
    pos x (Pos y e)
      | x == y = Pos y e
    pos x y = Pos x y

-- | Parse an idiom braket. Currently we translate it using @join@, @pure@ and @ap@ from the
-- standard library.
idiomExp :: Parser Exp
idiomExp = do
  try $ reservedOp "[|"
  t <- term
  let t' = toApplicative t
  reservedOp "|]"
  return (App (Var "join") t')
  where
    toApplicative (App t t') = App (App (Var "ap") (toApplicative t)) t'
    toApplicative (Pos p e) = Pos p (toApplicative e)
    toApplicative head = App (Var "pure") head

-- | A data type for all the possible statements in the do-notation.
data DoBinding
  = LetStmt [Binding]
  | PatternBind (Binding, Exp)
  | Stmt Exp

-- | Parse a do expression. We currently rely on the @bind@, @seq@ and @return@ from the
-- standard library. We allow direct pattern matching when using '<-',
-- such pattern matching is translated to let pattern matching. We also allow
-- let statement.
doExp :: Parser Exp
doExp = do
  reserved "do"
  bds <- block pseudoDecl
  desugar 0 bds
  where
    pseudoDecl = bd <|> try letStmts <|> stmt
    pat = do
      c <- const
      ps <- many (try varExp <|> wild)
      return $ BPattern (c, ps, Wild)
    leftPair =
      parens $ do
        x <- try var <|> wildString
        comma
        xs <- sepBy1 (try var <|> wildString) comma
        return $ BPair (x : xs, Wild)
    leftVar = do
      v <- try var <|> wildString
      return $ BSingle (v, Wild)
    makeBind v (BSingle (x, _)) = BSingle (x, v)
    makeBind v (BPair (xs, _)) = BPair (xs, v)
    makeBind v (BPattern (x, y, _)) = BPattern (x, y, v)
    binding = try leftVar <|> leftPair <|> pat
    bd = do
      x <-
        try $ do
          x <- binding
          reservedOp "<-"
          return x
      t <- term
      return $ PatternBind (x, t)
    stmt = do
      t <- term
      return $ Stmt t
    letStmts = do
      (Let bds _) <- letStatement
      return $ LetStmt bds
    desugar n (Stmt t:[]) = return t
    desugar n (PatternBind _:[]) =
      unexpected $ "a do block should end with a non-binding expression."
    desugar n (LetStmt _:[]) =
      unexpected $ "a do block should end with a non-binding expression."
    desugar n (Stmt t:xs) = do
      t' <- desugar n xs
      return $ App (App (Var "seq") t) t'
    desugar n (LetStmt bds:xs) = do
      t' <- desugar n xs
      return $ Let bds t'
    desugar n (PatternBind (x, t):xs) = do
      t' <- desugar (n + 1) xs
      let v = "#bindVar" ++ show n
      return $ App (App (Var "bind") t) (Lam [v] (Let [makeBind (Var v) x] t'))


-- | A parser for operations on reals.
realOp :: Parser Exp
realOp = realSin <|> realCos <|> realExp <|> realLog <|> realSqrt
         <|> realAdd <|> realCast <|> realDiv <|> realMinus <|> realEq
         <|> realFloor <|> realRound <|> realCeiling <|> realMul <|> realLt
  where realSin = reserved "sin" >> (return $ RealOp "sin")
        realCos = reserved "cos" >> (return $ RealOp "cos")
        realExp = reserved "exp" >> (return $ RealOp "exp")
        realFloor = reserved "floor" >> (return $ RealOp "floor")
        realCeiling = reserved "ceiling" >> (return $ RealOp "ceiling")
        realRound = reserved "round" >> (return $ RealOp "round")
        realLog = reserved "log" >> (return $ RealOp "log")
        realSqrt = reserved "sqrt" >> (return $ RealOp "sqrt")
        realAdd = reserved "plusReal" >> (return $ RealOp "plusReal")
        realMinus = reserved "minusReal" >> (return $ RealOp "minusReal")
        realCast = reserved "cast" >> (return $ RealOp "cast")
        realDiv = reserved "divReal" >> (return $ RealOp "divReal")
        realMul = reserved "mulReal" >> (return $ RealOp "mulReal")
        realEq = reserved "eqReal" >> (return $ RealOp "eqReal")
        realLt = reserved "ltReal" >> (return $ RealOp "ltReal")

realPi :: Parser Exp
realPi = reserved "pi" >> (return $ RealOp "pi")

toReal :: Parser Exp
toReal = reserved "toReal" >> (return $ RealOp "toReal")


-- * Lexer
-- | A Proto-Quipper-D language token definition.
dpqStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
dpqStyle =
  Token.LanguageDef
    { Token.commentStart = "{-"
    , Token.commentEnd = "-}"
    , Token.commentLine = "--"
    , Token.nestedComments = True
    , Token.identStart = letter
    , Token.identLetter = alphaNum <|> oneOf "_'"
    , Token.opStart = oneOf ":!#$%&*+./<=>;?@\\^|-`"
    , Token.opLetter = oneOf ":!#$%&*+./<=>;?@\\^|-`"
    , Token.caseSensitive = True
    , Token.reservedNames =
        [ "gate"
        , "in"
        , "let"
        , "case"
        , "of"
        , "data"
        , "import"
        , "class"
        , "instance"
        , "simple"
        , "Clifford"
        , "reverse"
        , "box"
        , "unbox"
        , "existsBox"
        , "controlled"
        , "withComputed"
        , "dynlift"
        , "circuit"
        , "object"
        , "Circ"
        , "Unit"
        , "do"
        , "where"
        , "module"
        , "infix"
        , "infixr"
        , "infixl"
        , "Type"
        , "forall"
        , "if"
        , "then"
        , "else"
        , "pi"
        , "sin"
        , "cos"
        , "exp"
        , "log"
        , "log"
        , "sqrt"
        , "plusReal"
        , "minusReal"
        , "cast"
        , "divReal"
        , "mulReal"
        , "eqReal"
        , "ltReal"
        , "round"
        ]
    , Token.reservedOpNames =
        [ "λ"
        , "."
        , "\\"
        , "<-"
        , "->"
        , "*"
        , "()"
        , "!"
        , "_"
        , ":"
        , "="
        , "=>"
        , "[|"
        , "|]"
        , "`"
        , "#"
        ]
    }

-- | Parse a Proto-Quipper-D token.
tokenizer :: (Stream s m Char, Monad m) => Token.GenTokenParser s u m
tokenizer = Token.makeTokenParser dpqStyle

-- | Parse a literal.
stringLiteral :: (Stream s m Char, Monad m) => ParsecT s u m String
stringLiteral = Token.stringLiteral tokenizer

-- | Parse an legal identifier.
identifier :: (Stream s m Char, Monad m) => ParsecT s u m String
identifier = Token.identifier tokenizer

-- | Parse many white spaces.
whiteSpace :: (Stream s m Char, Monad m) => ParsecT s u m ()
whiteSpace = Token.whiteSpace tokenizer

-- | Parse a reserved word.
reserved :: (Stream s m Char, Monad m) => String -> ParsecT s u m ()
reserved = Token.reserved tokenizer

-- | Parse a reserved operator.
reservedOp :: (Stream s m Char, Monad m) => String -> ParsecT s u m ()
reservedOp = Token.reservedOp tokenizer

-- | Parse an operator.
operator :: (Stream s m Char, Monad m) => ParsecT s u m String
operator = Token.operator tokenizer

-- | Parse a colon.
colon :: (Stream s m Char, Monad m) => ParsecT s u m String
colon = Token.colon tokenizer

-- | Parse an integer.
integer :: (Stream s m Char, Monad m) => ParsecT s u m Integer
integer = Token.integer tokenizer

-- | Parse an natural number.
naturals :: (Stream s m Char, Monad m) => ParsecT s u m Integer
naturals = Token.natural tokenizer

-- | Parse a pair of brackets.
brackets :: (Stream s m Char, Monad m) => ParsecT s u m a -> ParsecT s u m a
brackets = Token.brackets tokenizer

-- | Parse a pair of parenthesis.
parens :: (Stream s m Char, Monad m) => ParsecT s u m a -> ParsecT s u m a
parens = Token.parens tokenizer

-- | Parse a pair of angle brackets.
angles :: (Stream s m Char, Monad m) => ParsecT s u m a -> ParsecT s u m a
angles = Token.angles tokenizer

-- | Parse a pair of braces.
braces :: (Stream s m Char, Monad m) => ParsecT s u m a -> ParsecT s u m a
braces = Token.braces tokenizer

-- | Parse a dot.
dot :: (Stream s m Char, Monad m) => ParsecT s u m String
dot = Token.dot tokenizer

-- | Parse a comma.
comma :: (Stream s m Char, Monad m) => ParsecT s u m String
comma = Token.comma tokenizer

lexeme :: (Stream s m Char, Monad m) => ParsecT s u m a -> ParsecT s u m a
lexeme = Token.lexeme tokenizer

 
