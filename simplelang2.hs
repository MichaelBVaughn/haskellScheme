import Text.Show.Functions

data NAryTree a = Node [NAryTree a] | Leaf a deriving (Show)

type Symbol = String 
--data SExpr = NAryTree Symbol 
--data ParseTree = NAryTree AtomicValue 

--FVal is the type for primitive functions
data AtomicValue = NVal Int | BVal Bool | SVal String | SymVal Symbol | FVal Func deriving (Show)

type Func = SList AtomicValue -> SList AtomicValue
 
type State = Symbol -> SList AtomicValue

data SList a = Cons (SList a) (SList a) | Atom a | Nil deriving (Show)

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

--Fold over sequence of cons pairs. 
consFoldl :: (SList a -> b -> b) -> b -> SList a -> b
consFoldl f acc Nil = acc
consFoldl f acc atom@(Atom _) = f atom acc
consFoldl f acc (Cons lcar lcdr) = f lcar $ consFoldl f acc lcdr

--Only used internally for checking argument lists.
slistLen :: SList a -> Int
slistLen Nil = 0
slistLen (Atom a) = error "Improper list."
slistLen (Cons car cdr) = 1 + slistLen cdr

defaultState :: State
defaultState "+" = Atom $ FVal (mkVariadicFxn (mkBinArithmeticOp (+)) (Atom $ NVal 0))
defaultState "-" = Atom $ FVal (mkVariadicFxn (mkBinArithmeticOp (-)) (Atom $ NVal 0)) 
defaultState "*" = Atom $ FVal (mkVariadicFxn (mkBinArithmeticOp (*)) (Atom $ NVal 1))
defaultState "/" = Atom $ FVal (mkVariadicFxn (mkBinArithmeticOp (div)) (Atom $ NVal 1))
defaultState sym = Atom $ readConst sym

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
mkBinArithmeticOp f _ (Atom (NVal _)) = error "Arithmetic operation expected Int and Int. Received [Other] Int"
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


--Depth first tree accumulation
treeAccumDF :: (NAryTree a -> [b] -> b) -> [b] -> NAryTree a -> b
treeAccumDF f init l@(Leaf x) = f l init
treeAccumDF f init n@(Node xs) = f n $ map (treeAccumDF f init) xs

--Convert n-ary tree to scheme-style data structure
mapToScheme :: (NAryTree Symbol) -> [SList AtomicValue] -> SList AtomicValue
mapToScheme (Leaf s) _ = Atom $ SymVal s
mapToScheme (Node _) vals = foldr Cons Nil vals

makeConsList :: NAryTree Symbol -> SList AtomicValue
makeConsList = treeAccumDF mapToScheme [Nil]

updateState :: State -> Symbol -> SList AtomicValue -> State
updateState mapping newSym newVal inputSym 
            | inputSym == newSym = newVal
            | otherwise = mapping inputSym

--Evaluate basic s-expressions with variadic operators.
s_exprEval :: State -> SList AtomicValue -> SList AtomicValue
s_exprEval mapping Nil = error "s_exprEval cannot be applied to Nil"
s_exprEval mapping (Atom _) = error "s_exprEval cannot be applied to Atom"
s_exprEval mapping lst@(Cons _ _) = case subEvalRes of (Cons (Atom (FVal f)) cdr) -> f cdr
                                                       (Cons (Atom _) cdr) -> error applicabilityError
                                                       _ -> error unexpectedError
                                    where subEvalRes = consFoldl consOneRes Nil lst
                                          consOneRes exp acc = Cons (basicEval mapping exp) acc
                                          applicabilityError = "s-expression starts with non-applicable value"
                                          unexpectedError = "Nonsensical result from folding basicEval"

basicEval :: State -> SList AtomicValue -> SList AtomicValue
basicEval mapping Nil = Nil
basicEval mapping (Atom (SymVal sym)) = mapping sym
basicEval mapping sexpr@(Cons _ _) = s_exprEval mapping sexpr


--Reader code
evaluateText :: String -> SList AtomicValue
evaluateText str = basicEval defaultState $ schemeRead str

schemeRead :: String -> SList AtomicValue
schemeRead txt = case listread $ schemeSplit txt of (Cons prog Nil, []) -> prog
                                                    _ -> error "Bad program text"

listread :: [String] -> (SList AtomicValue, [String])
listread [] = (Nil, [])
listread (")":tl) = (Nil, tl)
listread ("(":tl) = (Cons car cdr, finalRight)
                  where (car, newRight) = listread tl
                        (cdr, finalRight) = listread newRight
listread (str:tl) = (Cons (Atom $ SymVal str) cdr, newRight)
                  where (cdr, newRight) = listread tl

schemeSplit :: String -> [String]
schemeSplit str  = split [' '] ['(',')'] str

split :: [Char] -> [Char] -> String -> [String]
split discard singles str = reverse $ map reverse $ splitr discard singles str

splitr :: [Char] -> [Char] -> String -> [String]
splitr discard singles = foldl takeOne []
                         where takeOne acc s
                                       |elem s discard = case acc of [] -> [[]]
                                                                     l@([]:tl) -> l
                                                                     l -> []:l
                                       |elem s singles = case acc of [] -> [s]:acc
                                                                     (hd:tl) -> if hd == []
                                                                                then (s:hd):tl
                                                                                else [s]:acc
                                       |otherwise = case acc of [] -> [[s]]
                                                                (hd:tl) -> if hd == [] 
                                                                           then (s:hd):tl
                                                                           else if elem (head hd) singles 
                                                                           then [s]:(hd:tl)
                                                                           else (s:hd):tl

a
