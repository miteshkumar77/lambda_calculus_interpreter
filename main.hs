import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace (trace)
import PA1Helper (Lexp (..), runProgram)
import System.Environment (getArgs)

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

-- Debug passthrough function for lazy evaluation
debug :: String -> Lexp -> Lexp
debug s l = trace (s ++ show l) l

-- allows file names to be unique
delim :: String
delim = "x"

-- We use this datatype for alpha-renaming
type LabelMapT = Map String Int

-- We use this datatype for detecting bounded/unbounded-ness of variables
type BoundSetT = Set String

-- For returning multiple values in the current label increment function
data LexpLabelMapPair = LexpLabelMapPair
  { lexp :: Lexp,
    labels :: LabelMapT
  }

getLexp :: LexpLabelMapPair -> Lexp
getLexp llmp@(LexpLabelMapPair lexp _) = lexp

getLabels :: LexpLabelMapPair -> LabelMapT
getLabels llmp@(LexpLabelMapPair _ labels) = labels

-- For returning multiple values in the unique renaming function
data NextCurrLabelMapPair = NextCurrLabelMapPair
  { currLabels :: LabelMapT,
    nextLabels :: LabelMapT
  }

getCurrLabels :: NextCurrLabelMapPair -> LabelMapT
getCurrLabels nclmp@(NextCurrLabelMapPair currLabels _) = currLabels

getNextLabels :: NextCurrLabelMapPair -> LabelMapT
getNextLabels nclmp@(NextCurrLabelMapPair _ nextLabels) = nextLabels

-- Initialize labels such that if we have a free variable value named
-- xx0, this would conflict with a bound variable which will start counting
-- upwards from xx0 xx1 ..., so we must make sure that xx0 is marked as occupied
-- before running our unique renaming algorithm
initLabels :: Lexp -> BoundSetT -> LabelMapT
initLabels v@(Atom name) bounded
  | Set.member name bounded = Map.empty
  | otherwise = Map.singleton name 0
initLabels la@(Lambda name lexp) bounded = initLabels lexp (Set.insert name bounded)
initLabels ap@(Apply func args) bounded =
  Map.union (initLabels func bounded) (initLabels args bounded)

-- Based on the LabelMap, get the string representation of
-- a particular symbol after renaming it
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

-- Util function for setNextSymbLabel
-- Keep incrementing a symbol's value in the map until
-- the string representation of that symbol isn't a key in the map
-- Then also add the string representation of this as a key to the map
-- with value 0
setNextSymbLabelUtil :: String -> LabelMapT -> LabelMapT
setNextSymbLabelUtil symb labelmap
  | Map.member (symbolLabel symb labelmap) labelmap =
    setNextSymbLabelUtil symb (incrementKey symb labelmap)
  | otherwise = incrementKey (symbolLabel symb labelmap) labelmap

-- Keep incrementing the value of a symbol
-- until its string representation cannot conflict with any variables
setNextSymbLabel :: String -> LabelMapT -> LabelMapT
setNextSymbLabel symb labelmap = setNextSymbLabelUtil symb (incrementKey symb labelmap)

-- We want to maintain two maps
-- the current map will contain the current mapping from symbol to number
-- within the current scope. The next map will contain the current mapping from
-- symbol to the highest number we have seen so far for this value in the entire
-- traversal
-- That means that the next map must be passed from the return value of the left
-- subtree into the parameter of the right subtree, such that we do not duplicate
-- any values in the right subtree
--
-- setCurrSymbLabel increments the nextmap key value until it connot form a duplicate
-- and then sets the current map key value to the corresponding value in next map
-- Then it returns both modified maps
setCurrSymbLabel :: String -> LabelMapT -> LabelMapT -> NextCurrLabelMapPair
setCurrSymbLabel symb currmap nextmap =
  let newnextmap = setNextSymbLabel symb nextmap
      newcurrmap = Map.insert symb (fromJust (Map.lookup symb newnextmap)) currmap
   in NextCurrLabelMapPair newcurrmap newnextmap

-- Apply alpha renaming such that all bound variables have a unique name that
-- do not conflict with any other bound/free variable.

-- Allows us to be certain that no issues arise from name-collision.
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

isBetaReducible :: Lexp -> Bool
isBetaReducible lexp@(Apply la@(Lambda _ _) _) = True
isBetaReducible _ = False

strConcat :: String -> String -> String
strConcat a b = a ++ b

inc :: Int -> Int
inc i = i + 1

-- Within a Lexp object, replace all atoms with string value v
-- with another Lexp value
-- Used for beta reduction
replace :: String -> Lexp -> Lexp -> Lexp
replace before after v@(Atom name)
  | before == name = after
  | otherwise = v
replace before after lexp@(Lambda name func) =
  Lambda name (replace before after func)
replace before after lexp@(Apply func args) =
  Apply (replace before after func) (replace before after args)

betaReduce :: Lexp -> Lexp
betaReduce ap@(Apply func args) =
  let newlexp = Apply (betaReduce func) (betaReduce args)
   in case newlexp of
        (Apply (Lambda newsymb newfunc) newargs) -> betaReduce (replace newsymb newargs newfunc)
        _ -> newlexp
betaReduce la@(Lambda name lexp) = Lambda name (betaReduce lexp)
betaReduce at@(Atom _) = at

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
etaReduce la@(Lambda name func) =
  let init_reduce = Lambda name (etaReduce func)
   in case init_reduce of
        (Lambda iname (Apply ifunc (Atom iargs)))
          | not (contains ifunc iname) && iname == iargs -> ifunc
          | otherwise -> init_reduce
        _ -> init_reduce
etaReduce at@(Atom _) = at
etaReduce ap@(Apply func args) = Apply (etaReduce func) (etaReduce args)

-- You will need to write a reducer that does something more than
-- return whatever it was given, of course!
reducer :: Lexp -> Lexp
reducer lexp = r
  where
    initLabelMap = initLabels lexp Set.empty
    uni = getLexp (uniqueRename lexp initLabelMap initLabelMap Set.empty)
    betard = betaReduce uni
    etard = etaReduce betard
    r = etard

-- Entry point of program
main :: IO ()
main = do
  args <- getArgs
  let inFile = case args of x : _ -> x; _ -> "input.lambda"
  let outFile = case args of x : y : _ -> y; _ -> "output.lambda"
  -- id' simply returns its input, so runProgram will result
  -- in printing each lambda expression twice.
  runProgram inFile outFile reducer