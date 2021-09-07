import PA1Helper ( runProgram, Lexp(..) )
import System.Environment (getArgs)
import Data.Map (Map)
import qualified Data.Map as SymbolIDs
import qualified Data.Map as Map
import Data.Set (Set)
import Debug.Trace ( trace ) 
import qualified Data.Set as BoundIDs
import qualified Data.Set as Set
import Data.Maybe ( fromJust )
import qualified Distribution.Simple as SymbolIDs

-- Haskell representation of lambda expression
-- data Lexp = Atom String | Lambda String Lexp | Apply Lexp  Lexp 

-- Given a filename and function for reducing lambda expressions,
-- reduce all valid lambda expressions in the file and output results.
-- runProgram :: String -> (Lexp -> Lexp) -> IO ()

-- This is the identity function for the Lexp datatype, which is
-- used to illustrate pattern matching with the datatype. "_" was
-- used since I did not need to use bound variable. For your code,
-- however, you can replace "_" with an actual variable name so you
-- can use the bound variable. The "@" allows you to retain a variable
-- that represents the entire structure, while pattern matching on
-- components of the structure.

id' :: Lexp -> Lexp
id' v@(Atom _) = v
id' lexp@(Lambda _ _) = lexp
id' lexp@(Apply _ _) = lexp

debug :: String -> Lexp -> Lexp
debug s l = trace (s ++ show l) l

-- \x.(\y.(y x) (y x))
-- \z.(\y.(y z) (y x))
-- \z.((y x) z)

-- (\x.(\y.(x y) x) q)
-- (\y.(q y) q)


-- (\x.\y.(y x) (y w))
-- (\x.\z.(z x) (y w))
-- (\z.(z (y w)))

delim :: String
delim = "x"

type LabelMapT = Map String Int
type BoundSetT = Set String
data LexpLabelMapPair = LexpLabelMapPair {
    lexp :: Lexp
    , labels :: LabelMapT 
}

getLexp :: LexpLabelMapPair -> Lexp
getLexp llmp@(LexpLabelMapPair lexp _) = lexp

getLabels :: LexpLabelMapPair -> LabelMapT 
getLabels llmp@(LexpLabelMapPair _ labels) = labels



data NextCurrLabelMapPair = NextCurrLabelMapPair {
    currLabels :: LabelMapT
    , nextLabels :: LabelMapT
}

getCurrLabels :: NextCurrLabelMapPair -> LabelMapT
getCurrLabels nclmp@(NextCurrLabelMapPair currLabels _) = currLabels

getNextLabels :: NextCurrLabelMapPair -> LabelMapT
getNextLabels nclmp@(NextCurrLabelMapPair _ nextLabels) = nextLabels



initLabels :: Lexp -> BoundSetT -> LabelMapT
initLabels v@(Atom name) bounded
    | Set.member name bounded = Map.empty
    | otherwise = Map.singleton name 0
initLabels la@(Lambda name lexp) bounded = initLabels lexp (Set.insert name bounded)
initLabels ap@(Apply func args) bounded = 
    Map.union (initLabels func bounded) (initLabels args bounded)


symbolLabel :: String -> LabelMapT -> String
symbolLabel symb labelmap
    | Map.member symb labelmap = 
        let countStr = show (fromJust (Map.lookup symb labelmap))
            suff = strConcat delim countStr
        in strConcat symb suff
    | otherwise =
        let suff = delim ++ "0"
        in strConcat symb suff

incrementKey :: String -> LabelMapT -> LabelMapT
incrementKey symb labelmap 
    | Map.member symb labelmap = Map.insert symb (inc (fromJust (Map.lookup symb labelmap))) labelmap
    | otherwise = Map.insert symb 0 labelmap


setNextSymbLabelUtil :: String -> LabelMapT -> LabelMapT
setNextSymbLabelUtil symb labelmap
    | Map.member (symbolLabel symb labelmap) labelmap = 
        setNextSymbLabelUtil symb (incrementKey symb labelmap) 
    | otherwise = incrementKey (symbolLabel symb labelmap) labelmap


setNextSymbLabel :: String -> LabelMapT -> LabelMapT
setNextSymbLabel symb labelmap = setNextSymbLabelUtil symb (incrementKey symb labelmap)
    

setCurrSymbLabel :: String -> LabelMapT -> LabelMapT -> NextCurrLabelMapPair
setCurrSymbLabel symb currmap nextmap = 
    let newnextmap = setNextSymbLabel symb nextmap
        newcurrmap = Map.insert symb (fromJust (Map.lookup symb newnextmap)) currmap
    in NextCurrLabelMapPair newcurrmap newnextmap

uniqueRename :: Lexp -> LabelMapT -> LabelMapT -> BoundSetT -> LexpLabelMapPair
uniqueRename at@(Atom name) currmap nextmap bounded
    | Set.member name bounded =
        let newsymb = Atom (symbolLabel name currmap)
        in LexpLabelMapPair newsymb nextmap
    | otherwise = LexpLabelMapPair at nextmap
uniqueRename la@(Lambda name lexp) currmap nextmap bounded =
    let newbounded = Set.insert name bounded
        newCurrNextPair = setCurrSymbLabel name currmap nextmap
        newCurrMap = getCurrLabels newCurrNextPair
        newNextMap = getNextLabels newCurrNextPair
        newsymb = symbolLabel name newCurrMap
        newLexpLabelMapPair = uniqueRename lexp newCurrMap newNextMap newbounded
        cumNextMap = getLabels newLexpLabelMapPair
        cumLexp = getLexp newLexpLabelMapPair
    in LexpLabelMapPair (Lambda newsymb cumLexp) cumNextMap
uniqueRename ap@(Apply func args) currmap nextmap bounded = 
    let funcLabelMapPair = uniqueRename func currmap nextmap bounded
        funcNextMap = getLabels funcLabelMapPair
        funcNextLexp = getLexp funcLabelMapPair
        argsLabelMapPair = uniqueRename args currmap funcNextMap bounded
        argsNextMap = getLabels argsLabelMapPair
        argsNextLexp = getLexp argsLabelMapPair
    in LexpLabelMapPair (Apply funcNextLexp argsNextLexp) argsNextMap




strEquals :: String -> String -> Bool
strEquals [] [] = True
strEquals _ [] = False
strEquals [] _ = False
strEquals (ax:a) (bx:b) = ax == bx && strEquals a b


isBetaReducible :: Lexp -> Bool
isBetaReducible lexp@(Apply la@(Lambda _ _) _) = True
isBetaReducible _ = False

strConcat :: String -> String -> String
strConcat a b = a ++ b

inc :: Int -> Int
inc i = i + 1

replace :: String -> Lexp -> Lexp -> Lexp
replace before after v@(Atom name)
    | before == name = after
    | otherwise = v
replace before after lexp@(Lambda name func) =
    Lambda name (replace before after func)
replace before after lexp@(Apply func args) =
    Apply (replace before after func) (replace before after args)

betaReduce :: Lexp -> Lexp
betaReduce ap@(Apply la@(Lambda symb func) args) =
    let newlexp = replace symb args func
    in
        betaReduce newlexp
betaReduce ap@(Apply func args)
        | isBetaReducible init_reduce = betaReduce init_reduce
        | otherwise = init_reduce
    where init_reduce = Apply (betaReduce func) (betaReduce args)
betaReduce at@(Atom _) = at
betaReduce la@(Lambda name lexp) = Lambda name (betaReduce lexp)

contains :: Lexp -> String -> Bool
contains v@(Atom name) symb = name == symb
contains lexp@(Lambda name func) symb = contains func symb
contains lexp@(Apply func args) symb = contains func symb || contains args symb

isEtaReducible :: Lexp -> Bool
isEtaReducible la@(Lambda name e@(Apply func at@(Atom atomName))) =
    not (contains func name) && name == atomName
isEtaReducible _ = False

getExp :: Lexp -> Lexp
getExp la@(Lambda name e@(Apply func _)) = func

etaReduce :: Lexp -> Lexp
etaReduce la@(Lambda name e@(Apply func args))
    | isEtaReducible la =
        let d = trace ("eta reducible exp: " ++ show la)
            init_reduce = getExp la
        in
            etaReduce init_reduce
    | otherwise = Lambda name (etaReduce e)
etaReduce at@(Atom _) = at
etaReduce ap@(Apply func args) = Apply (etaReduce func) (etaReduce args)

-- You will need to write a reducer that does something more than
-- return whatever it was given, of course!
reducer :: Lexp -> Lexp
reducer lexp = r
    where 
        initLabelMap = initLabels lexp Set.empty
        uni = getLexp (uniqueRename lexp initLabelMap initLabelMap Set.empty)
        betar = betaReduce uni
        etar = etaReduce betar
        r = etar


-- Entry point of program
main = do
    args <- getArgs
    let inFile = case args of { x:_ -> x; _ -> "input.lambda" }
    let outFile = case args of { x:y:_ -> y; _ -> "output.lambda"}
    -- id' simply returns its input, so runProgram will result
    -- in printing each lambda expression twice. 
    runProgram inFile outFile reducer


-- Takes all bound variables, and gives them a unique name


-- (\x.\y.(y x) (y w)) -> alpha
-- (\x0.\y0.(y0 x) (y w))
-- \y0.(y0 (y w))
-- WRONG: \y.(y (y w))


