import PA1Helper ( runProgram, Lexp(..) )
import System.Environment (getArgs)
import Data.Map (Map)
import qualified Data.Map as SymbolIDs
import qualified Data.Map as Map
import Data.Set (Set)
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

type SymbolIDs = Map String Int
type BoundIDs = Set String
data LexpIDs = LexpIDs{ lexp :: Lexp
                      , ids :: SymbolIDs }


isBetaReducible :: Lexp -> Bool
isBetaReducible lexp@(Apply la@(Lambda _ _) _) = True
isBetaReducible _ = False

getLexp :: LexpIDs -> Lexp
getLexp lid@(LexpIDs lexp _) = lexp

getIDs:: LexpIDs -> SymbolIDs 
getIDs lid@(LexpIDs _ symbs) = symbs

id' :: Lexp -> Lexp
id' v@(Atom _) = v
id' lexp@(Lambda _ _) = lexp
id' lexp@(Apply _ _) = lexp


strConcat :: String -> String -> String
strConcat a b = a ++ b

inc :: Int -> Int
inc i = i + 1

initSymbs :: Lexp -> BoundIDs -> SymbolIDs
initSymbs v@(Atom name) bd
    | Set.member name bd = Map.empty
    | otherwise = Map.singleton name 0
initSymbs la@(Lambda name lexp) bd = initSymbs lexp (Set.insert name bd)
initSymbs ap@(Apply func args) bd = Map.union (initSymbs func bd) (initSymbs args bd)

-- Get the symbol this input symbol should use
-- If it exists in the map, then return (symb)_(count)
getSymbol :: String -> SymbolIDs -> String
getSymbol symb mp
    | Map.member symb mp = 
        let countStr = show (fromJust (Map.lookup symb mp))
            suff = strConcat delim countStr
        in
            strConcat symb suff
    | otherwise = 
        let suff = delim ++ "0"
        in
            strConcat symb suff

-- Util function for addSymbol: 
-- keeps incrementing the count of the symbol until
-- the result of getSymbol is not within the map
-- Then return the map
addSymbolUtil :: String -> SymbolIDs -> SymbolIDs
addSymbolUtil symb mp
    | Map.member (getSymbol symb mp) mp = addSymbolUtil symb (Map.insert symb (inc (fromJust (Map.lookup symb mp))) mp)
    | otherwise = mp

-- Add an occurrence of symbol to the hashtable
-- Increment its key value if it already exists
-- This should be used when we encounter a variable 
-- that is bound in a lambda, or is a free variable
-- The algorithm discussed here: https://leetcode.com/problems/making-file-names-unique/
-- is critical to this function
addSymbol :: String -> SymbolIDs -> SymbolIDs
addSymbol symb mp
    | Map.member symb mp = addSymbolUtil symb (Map.insert symb (inc (fromJust (Map.lookup symb mp))) mp)
    | otherwise = Map.insert symb 0 mp


-- Rename the entire expression such that all bound-variables have the same
-- unique name, and all free variables have unique names
-- This allows us to avoid alpha-renaming all together
uniqueRename :: Lexp -> SymbolIDs -> BoundIDs -> LexpIDs
uniqueRename at@(Atom name) mp bd
    | Set.member name bd = 
        let newsymb = Atom (getSymbol name mp)
        in
            LexpIDs newsymb mp
    | otherwise = LexpIDs (Atom name) mp
uniqueRename la@(Lambda name lexp) mp bd = 
    let newbd = Set.insert name bd
        newmp = addSymbol name mp
        newsymb = getSymbol name newmp
        newlids = uniqueRename lexp newmp newbd
        newlamb = Lambda newsymb (getLexp newlids)
    in
        LexpIDs newlamb  (getIDs newlids)
uniqueRename ap@(Apply func args) mp bd =
    let funclids = uniqueRename func mp bd
        argslids = uniqueRename args (getIDs funclids) bd
        newap = Apply (getLexp funclids) (getLexp argslids)
    in
        LexpIDs newap (getIDs argslids)

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

isEtaReducible :: Lexp -> Bool
isEtaReducible 

etaReduce :: Lexp -> Lexp


-- You will need to write a reducer that does something more than
-- return whatever it was given, of course!
reducer :: Lexp -> Lexp
reducer lexp = r
    --where r = uniqueRename lexp SymbolIDs.empty BoundIDs.empty
    where uni = getLexp (uniqueRename lexp (initSymbs lexp BoundIDs.empty) BoundIDs.empty)
          betar = betaReduce uni 
          r = betar

-- Entry point of program
main = do
    args <- getArgs
    let inFile = case args of { x:_ -> x; _ -> "input.lambda" }
    let outFile = case args of { x:y:_ -> y; _ -> "output.lambda"}
    -- id' simply returns its input, so runProgram will result
    -- in printing each lambda expression twice. 
    runProgram inFile outFile reducer
