module Experiment where

import Text.Show.Functions

import Control.Monad

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Data.Char (digitToInt)

type Symbol = String 
type SExpr = SList AtomicValue

data AtomicValue = NVal Int | BVal Bool | SVal String | SymVal Symbol | FVal Func | Closure ClosureState | BOTTOM deriving (Show)

data ClosureState = ClsSt [Symbol] SExpr Experiment.State deriving (Show)

data SList a = Cons (SList a) (SList a) | Atom a | Nil deriving (Show)
 
type State = Symbol -> SList AtomicValue

type EvalContext = (Experiment.State, SExpr)

type ErrorContext = Either String EvalContext

type Func = Experiment.State -> SExpr -> SExpr -> ErrorContext
-- Parser definition

languageDef =
  emptyDef { Token.identStart = letter <|> char '-' <|> char '+' <|> char '/' <|> char '*' ,
             Token.identLetter = alphaNum <|> char '-' <|> char '+' <|> char '/' <|> char '*' 
             }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
parens = Token.parens lexer

--Weirdly I couldn't find a decent int parser already included in the API docs
--for Parsec. 
sInt :: Parser (SExpr)
sInt =
  do digits <- many1 digit
     let n = foldl (\x d -> 10 * x + digitToInt d) 0 digits 
     return (Atom (NVal n))

symbol :: Parser (SExpr)
symbol =
  do tok <- identifier
     return $ Atom $ SymVal tok

list :: Parser (SExpr)
list =
  do list <- parens $ sepBy (sInt <|> symbol <|> list) (many $ char ' ')
     return $ foldr (Cons) Nil list

prog :: Parser (SExpr)
prog = list <|> symbol <|> sInt


-- End parser definition

--Used internally for checking argument lists
isProperList :: SList a -> Bool
isProperList Nil = True
isProperList (Atom a) = False
isProperList (Cons car cdr) = isProperList cdr

--
--Only used internally for checking argument lists.
slistLen :: SList a -> Int
slistLen Nil = 0
slistLen (Atom a) = 0
slistLen (Cons car cdr) = 1 + slistLen cdr

--A fold over a single-level of a cons-ed list.
consFoldl :: (SList a -> b -> b) -> b -> SList a -> b
consFoldl f acc Nil = acc
consFoldl f acc atom@(Atom _) = f atom acc
consFoldl f acc (Cons lcar lcdr) = f lcar $ consFoldl f acc lcdr

consFoldM :: Monad m => (SList a -> b -> m b) -> b -> SList a -> m b
consFoldM f acc Nil = return acc
consFoldM f acc atom@(Atom _) = f atom acc
consFoldM f acc (Cons lcar lcdr) = (f lcar) =<< (consFoldM f acc lcdr)

mkArithBuiltin :: Int -> (Int -> Int -> Int) -> Func
mkArithBuiltin identity op sigma (Atom (NVal x)) (Atom (NVal y)) =
  Right (sigma,  Atom $ NVal (op x y))
mkArithBuiltin identity op sigma (Atom (NVal x)) Nil =
  Right (sigma, Atom $ NVal (op x identity))
mkArithBuiltin identity op sigma Nil Nil = Right (sigma, Atom $ NVal identity) -- TODO: Silly
mkArithBuiltin identity op sigma _ _ = Left "Error: Integer operator received malformed arg list, or non-integer value"

defaultState :: Experiment.State
defaultState "+" = Atom $ FVal $ mkArithBuiltin 0 (+)
defaultState "-" = Atom $ FVal $ mkArithBuiltin 0 (-)
defaultState "*" = Atom $ FVal $ mkArithBuiltin 1 (*)
defaultState "/" = Atom $ FVal $ mkArithBuiltin 1 (div)
defaultState _ = Atom $ BOTTOM 

validateLambdaSyntax :: Experiment.State -> SExpr -> ErrorContext
validateLambdaSyntax sigma expr
                 |not $ isProperList expr = Left $ "Lambda is not proper list" ++ (show expr)
                 |not $ 3 == slistLen expr = Left $ "Lambda is not proper length" ++ (show expr)
                 |otherwise =
                    case expr of
                    (Cons (Atom (SymVal "lambda")) (Cons args cdr)) -> if not $ validateArgs args then
                                                                         Left $ "Invalid arg list"
                                                                       else Right (sigma, expr)
                    _ -> Left "Possible Error: Malformed lambda? List is proper length, but structure is bad."

validateArgs :: SList AtomicValue -> Bool
validateArgs args = proper && symbols
             where proper = isProperList args
                   symbols = consFoldl (\a b -> b && isSymbol a) True args 
                   isSymbol (Atom (SymVal _)) = True
                   isSymbol _ = False

--TO DO: This is partial. Fix.
extractSymbol :: SList AtomicValue -> Either String Symbol
extractSymbol (Atom (SymVal s)) = Right s
extractSymbol _ = Left "Invalid symbol in let binding"

lambdaEval :: Experiment.State -> SExpr -> ErrorContext
lambdaEval sigma expr =
  do
    if not $ isProperList expr
      then Left $ "Lambda is not proper list" ++ (show expr)
      else Right ()
    case expr of
      (Cons (Atom (SymVal "lambda")) (Cons args (Cons body Nil))) ->
        (if not $ validateArgs args then
           Left $ "Lambda has invalid arg list"
        else 
           let extractAndAppend exp l =
                 do
                   sym <- extractSymbol exp
                   return (sym:l) in
           do arglist <- consFoldM extractAndAppend [] args
              Right (sigma, Atom $ Closure $ ClsSt arglist body sigma))
      _ -> Left "Error: Malformed lambda expression"    
           
isApplicable :: Experiment.State  -> SExpr -> Bool
isApplicable sigma (Atom (FVal _)) = True
isApplicable sigma (Atom (Closure _)) = True
isApplicable sigma _ = False

applicabilityCheck :: EvalContext -> ErrorContext
applicabilityCheck ctx@(sigma, expr) =
  if isApplicable sigma expr then
    Right ctx
  else
    Left "Error: non-applicable item found in head of s-expression"
    
evalClosureI :: ClosureState -> ErrorContext
evalClosureI (ClsSt [] body sigma) = eval sigma body
evalClosureI (ClsSt l body sigma) = Left "Internal Interpreter Error: attempted to evaluate unsaturated closure?"

evalClosure :: SExpr -> ErrorContext
evalClosure (Atom (Closure c))= evalClosureI c
evalClosure _ = Left "Internal Interpreter Error: Attempt to use non-closure as closure?"

closureSaturate :: Experiment.State -> ClosureState -> SExpr -> ErrorContext
closureSaturate sigma (ClsSt (hd:tl) body closureState) arg =
  Right $ (sigma, Atom $ Closure $ ClsSt tl body (\x -> if x == hd then arg else closureState x))
closureSaturate sigma (ClsSt [] body closureState) _ =
  Left "Error: closure received more actuals than formals"

argSaturate :: Experiment.State -> SExpr -> SExpr -> ErrorContext
argSaturate sigma (Atom (Closure c)) arg = closureSaturate sigma c arg
argSaturate sigma _ arg = Left "Internal Interpreter Error: argSaturate received non-closure"

fxnSaturateI :: Experiment.State -> Func -> SExpr -> ErrorContext
fxnSaturateI sigma f (Cons car cdr) =
  do (sigma', arg) <- eval sigma car
     (sigma'', res) <- fxnSaturateI sigma' f cdr     
     f sigma'' arg res
fxnSaturateI sigma f Nil = f sigma Nil Nil --TODO: Silly. Make a smarter recursion.
fxnSaturateI sigma f (Atom _) = Left "Internal Interpreter Error: saturate applied to improper list"

fxnSaturate :: Experiment.State -> SExpr -> SExpr -> ErrorContext
fxnSaturate sigma (Atom (FVal f)) args = fxnSaturateI sigma f args
fxnSaturate _ _ _ = Left "Internal Interpreter Error: fxnSaturate received non-builtin?"
    
apply :: Experiment.State  -> SExpr -> SExpr -> ErrorContext
apply sigma f@(Atom (Closure _)) (Cons car cdr) =
  do (sigma', arg) <- eval sigma car
     (_, accF) <- argSaturate sigma' f arg
     apply sigma' accF cdr
apply sigma f@(Atom (FVal _)) args = fxnSaturate sigma f args     
apply sigma f Nil =  evalClosure f
apply sigma _ (Atom _) = Left "Cannot apply to malformed arglist"

evalApplicable :: Experiment.State -> SExpr -> ErrorContext
evalApplicable sigma (Cons car cdr) =
  do
    ctx <- eval sigma car
    (sigma', symb) <- applicabilityCheck ctx
    apply sigma' symb cdr

evalAtom :: Experiment.State -> AtomicValue -> ErrorContext
evalAtom sigma v@(NVal _) = Right (sigma, Atom v)
evalAtom sigma (SymVal s) =
  case sigma s of
  (Atom BOTTOM) -> Left $ "variable: " ++ s ++ " not bound in current context"
  v@(Atom (FVal _)) -> Right (sigma, v)
  v@(Atom (Closure _)) -> Right (sigma, v)
  v -> Right (sigma, v)
evalAtom _ _ = Left "Non integer/function datatypes undefined"

eval :: Experiment.State -> SExpr -> ErrorContext
eval sigma Nil = Right (sigma, Nil)
eval sigma (Atom v) = evalAtom sigma v
eval sigma l@(Cons (Atom (SymVal "lambda")) cdr) = lambdaEval sigma l
eval sigma l@(Cons car cdr) = evalApplicable sigma l

readAndEval :: String -> Either ParseError  ErrorContext
readAndEval inStr =
  do
    list <- parse prog "" inStr
    return $ eval defaultState $ list

tryRun :: String -> IO ()
tryRun prog =
  case readAndEval prog of
    Left e -> putStrLn (show e)
    Right ctx -> case ctx of
                   Left e -> putStrLn e
                   Right (_, exp) -> putStrLn (show exp)
    
