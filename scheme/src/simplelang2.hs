module Scheme where

import Text.Show.Functions
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token


type Symbol = String



--FVal is the type for primitive functions. ClosureState represents results of lambda.
data AtomicValue = NVal Int | BVal Bool | SVal String | SymVal Symbol | FVal Func | Closure ClosureState | BOT  deriving (Show)

data ClosureState = ClsSt [Symbol] (SList AtomicValue) Scheme.State deriving (Show)

type Func = SList AtomicValue -> SList AtomicValue
 
type State = Symbol -> SList AtomicValue

--Classic cons cell lists.
data SList a = Cons (SList a) (SList a) | Atom a | Nil deriving (Show)

lambdaSymb = SymVal "lambda"

-- Parser definition
languageDef =
  emptyDef { Token.identStart = alphaNum <|> char '-' <|> char '+' <|> char '/' <|> char '*' ,
             Token.identLetter = alphaNum <|> char '-' <|> char '+' <|> char '/' <|> char '*' 
             }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
parens = Token.parens lexer

symbol :: Parser (SList AtomicValue)
symbol =
  do tok <- identifier
     return $ Atom $ SymVal tok

list :: Parser (SList AtomicValue)
list =
  do list <- parens $ sepBy (symbol <|> list) (many $ char ' ')
     return $ foldr (Cons) Nil list
-- End parser definition

--The classic Lisp list functions. Know them. Love them.
car :: SList a -> SList a
car Nil = error "Can't take car of Nil"
car (Atom _) = error "Can't take car of Atom"
car (Cons c _) = c

cdr :: SList a -> SList a
cdr Nil = error "Can't take cdr of Nil"
cdr (Atom _) = error "Can't take cdr of Atom"
cdr (Cons _ c) = c

--Used internally for checking argument lists
isProperList :: SList a -> Bool
isProperList Nil = True
isProperList (Atom a) = False
isProperList (Cons car cdr) = isProperList cdr

--A fold over a single-level of a cons-ed list.
consFoldl :: (SList a -> b -> b) -> b -> SList a -> b
consFoldl f acc Nil = acc
consFoldl f acc atom@(Atom _) = f atom acc
consFoldl f acc (Cons lcar lcdr) = f lcar $ consFoldl f acc lcdr

--Only used internally for checking argument lists.
slistLen :: SList a -> Int
slistLen Nil = 0
slistLen (Atom a) = error "Improper list."
slistLen (Cons car cdr) = 1 + slistLen cdr

--Default state. Contains interpreter builtins, and fails over to parsing self evaluating values.
defaultState :: Scheme.State
defaultState "+" = Atom $ FVal (mkVariadicFxn (mkBinArithmeticOp (+)) (Atom $ NVal 0))
defaultState "-" = Atom $ FVal (mkVariadicFxn (mkBinArithmeticOp (-)) (Atom $ NVal 0)) --Fix this 
defaultState "*" = Atom $ FVal (mkVariadicFxn (mkBinArithmeticOp (*)) (Atom $ NVal 1))
defaultState "/" = Atom $ FVal (mkVariadicFxn (mkBinArithmeticOp (div)) (Atom $ NVal 1))
defaultState sym = Atom $ 

--Create a variadic function from a binary function over slists
mkVariadicFxn :: (SList AtomicValue -> SList AtomicValue -> SList AtomicValue) -> SList AtomicValue -> Func
mkVariadicFxn f init args
             |invalidList = error "Syntactic forms must be proper list"
             |otherwise = consFoldl f init args
             where invalidList = not $ isProperList args

--Makes an integer function into a binary function on slists
mkBinArithmeticOp :: (Int -> Int -> Int) -> SList AtomicValue -> SList AtomicValue -> SList AtomicValue
mkBinArithmeticOp f (Atom (NVal l)) (Atom (NVal r)) = (Atom . NVal $ f l r)
mkBinArithmeticOp f (Atom (NVal _)) _ = error "Arithmetic operation expected Int and Int. Received Int [other]"
mkBinArithmeticOp f l (Atom (NVal _)) = error $ "Arithmetic operation expected Int and Int. Received [Other] Int" ++ (show l)
mkBinArithmeticOp f _ _ = error "Arithmetic operation expected Int and Int. Received [Other] [Other]"

tryInt :: String -> [(Int,String)]
tryInt str = reads str :: [(Int,String)]

tryBool :: String -> [(Bool,String)]
tryBool str = reads str :: [(Bool,String)]

--Silly. Do it this way, until I have a better grasp on monads
readConst :: String -> AtomicValue
readConst sym = case intRes of (v,_):_ -> NVal v
                               [] -> case boolRes of (v,_):_ -> BVal v
                                                     [] -> SymVal sym
                where intRes = tryInt sym
                      boolRes = tryBool sym

--For use with lambda expressions.
updateState :: Scheme.State -> Symbol -> SList AtomicValue -> Scheme.State
updateState mapping newSym newVal inputSym 
            | inputSym == newSym = newVal
            | otherwise = mapping inputSym

--Evaluate basic s-expressions with variadic operators.
s_exprEval :: Scheme.State -> SList AtomicValue -> SList AtomicValue
s_exprEval mapping Nil = error "s_exprEval cannot be applied to Nil"
s_exprEval mapping (Atom _) = error "s_exprEval cannot be applied to Atom"
s_exprEval mapping lst@(Cons _ _) = case subEvalRes of (Cons (Atom (FVal f)) cdr) -> f cdr
                                                       (Cons (Atom (Closure cs)) cdr) -> applyClosure mapping cs cdr
                                                       (Cons (Atom _) cdr) -> error applicabilityError
                                                       _ -> error unexpectedError
                                    where subEvalRes = consFoldl consOneRes Nil lst
                                          consOneRes exp acc = Cons (basicEval mapping exp) acc
                                          applicabilityError = "s-expression starts with non-applicable value: " ++ (show lst)
                                          unexpectedError = "Nonsensical result from folding basicEval"

applyClosure :: Scheme.State -> ClosureState -> SList AtomicValue -> SList AtomicValue
applyClosure mapping c@(ClsSt syms fxn st) args 
                     |not $ matchArgList syms args = error $ "Arg list for function does not match: " ++ (show args)
                     |otherwise = basicEval newState fxn
                     where matchArgList s a = (length s) == (slistLen a)
                           argLst = consFoldl (:) [] args
                           newState = foldl updateWithPair st $ zip syms argLst
                           updateWithPair old (sym, v) = Scheme.updateState old sym v

validateBindingExpr :: SList AtomicValue -> Bool
validateBindingExpr bind@(Cons (Atom (SymVal _)) expr) 
                    |not $ isProperList bind = error $ "Define binding is not proper list: " ++ (show expr)
                    |not $ 2 == slistLen bind = error $ "Define binding is not proper length: " ++ (show expr)
                    |otherwise = True
validateBindingExpr _ = error "invalid bind expression"

appendBinding :: SList AtomicValue -> Scheme.State -> Scheme.State
appendBinding exp mapping = Scheme.updateState mapping sym val
                          where sym = extractSymbol $ car exp
                                val = basicEval mapping $ car $ cdr exp

extractSymbol :: SList AtomicValue -> Symbol
extractSymbol (Atom (SymVal s)) = s
extractSymbol _ = error "Invalid symbol in let binding"

letEval :: Scheme.State -> SList AtomicValue -> SList AtomicValue
letEval mapping expr
        |not $ isProperList expr = error "Define expression is not proper list"
        |not $ 3 == slistLen expr = error $ "Define expression is not proper length" ++ (show expr)
        |otherwise = if consFoldl foldValidation True bindings
                     then basicEval newState body
                     else error "Invalid let bindings"
        where foldValidation a b = b && (validateBindingExpr a)
              bindings = car $ cdr expr
              newState = consFoldl appendBinding mapping bindings
              body = car $ cdr $ cdr expr

lambdaEval :: Scheme.State -> SList AtomicValue -> SList AtomicValue
lambdaEval mapping expr
           |not $ validLambdaSyntax expr = error $ "Invalid lambda syntax" ++ (show expr)
           |not $ validateArgs args = error $ "Invalid argument list for lambda expr" ++ (show expr)
           |otherwise = Atom $ Closure $ ClsSt argList fxn mapping
           where args = car $ cdr expr
                 argList = consFoldl extractAndAppend [] args
                 extractAndAppend exp l = (extractSymbol exp):l
                 fxn = car $ cdr $ cdr  expr

validateArgs :: SList AtomicValue -> Bool
validateArgs args = proper && symbols
             where proper = isProperList args
                   symbols = consFoldl (\a b -> b && isSymbol a) True args 
                   isSymbol (Atom (SymVal _)) = True
                   isSymbol _ = False

validLambdaSyntax :: SList AtomicValue -> Bool
validLambdaSyntax expr@(Cons (Atom (SymVal "lambda")) lcdr)
                 |not $ isProperList expr = error $ "Define binding is not proper list" ++ (show expr)
                 |not $ 3 == slistLen expr = error $ "Define binding is not proper length" ++ (show expr)
                 |otherwise = True

--Top-level evaluation function.
basicEval :: Scheme.State -> SList AtomicValue -> SList AtomicValue
basicEval mapping Nil = Nil
basicEval mapping (Atom (SymVal sym)) = mapping sym
basicEval mapping sexpr@(Cons (Atom (SymVal "let")) _) = letEval mapping sexpr
basicEval mapping sexpr@(Cons (Atom (SymVal "lambda")) _) = lambdaEval mapping sexpr
basicEval mapping sexpr@(Cons _ _) = s_exprEval mapping sexpr


schemeEval :: String -> Either ParseError (SList AtomicValue) 
schemeEval inStr =
  do list <- parse list "" inStr
     return $ basicEval defaultState $ list

--Reader code: Not final. I'll probably find an actual text library for haskell. 
--This exists for convenience of debugging.
-- evaluateText :: String -> SList AtomicValue
-- evaluateText str = basicEval defaultState $ schemeRead str



-- schemeRead :: String -> SList AtomicValue
-- schemeRead txt = case listread $ schemeSplit txt of (Cons prog Nil, []) -> prog
--                                                     _ -> error "Bad program text"

-- listread :: [String] -> (SList AtomicValue, [String])
-- listread [] = (Nil, [])
-- listread (")":tl) = (Nil, tl)
-- listread ("(":tl) = (Cons car cdr, finalRight)
--                   where (car, newRight) = listread tl
--                         (cdr, finalRight) = listread newRight
-- listread (str:tl) = (Cons (Atom $ SymVal str) cdr, newRight)
--                   where (cdr, newRight) = listread tl

-- schemeSplit :: String -> [String]
-- schemeSplit str  = split [' '] ['(',')'] str

-- split :: [Char] -> [Char] -> String -> [String]
-- split discard singles str = reverse $ map reverse $ splitr discard singles str

-- --TODO: Code does not check for balanced parenthesis. By sheer accident, 
-- --in the absence of closing parens, the interpreter acts as though they exist
-- --at the end of the string, so that's fun.

-- --Yeah. It's ugly. I'll fix it.
-- splitr :: [Char] -> [Char] -> String -> [String]
-- splitr discard singles = foldl takeOne []
--                          where takeOne acc s
--                                        |elem s discard = case acc of [] -> [[]]
--                                                                      l@([]:tl) -> l
--                                                                      l -> []:l
--                                        |elem s singles = case acc of [] -> [s]:acc
--                                                                      (hd:tl) -> if hd == []
--                                                                                 then (s:hd):tl
--                                                                                 else [s]:acc
--                                        |otherwise = case acc of [] -> [[s]]
--                                                                 (hd:tl) -> if hd == [] 
--                                                                            then (s:hd):tl
--                                                                            else if elem (head hd) singles 
--                                                                            then [s]:(hd:tl)
--                                                                            else (s:hd):tl
