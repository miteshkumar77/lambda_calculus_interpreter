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


uniqueRename :: Lexp -> SymbolIDs -> BoundIDs -> LexpIDs
uniqueRename at@(Atom name) mp bd
    | Set.member name bd = 
        let newsymb = Atom (getSymbol name mp)
        in
            LexpIDs newsymb mp
    | otherwise = 
        let newmp = addSymbol name mp
            newsymb = Atom (getSymbol name newmp)
        in
            LexpIDs newsymb newmp
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

aR :: Lexp -> Lexp -> Lexp -> Lexp
aR at@(Atom _) from@(Atom _) to@(Atom _) = at
aR la@(Lambda _ _) from@(Atom _) to@(Atom _) = la
aR ap@(Apply _ _) from@(Atom _) to@(Atom _) = ap

-- You will need to write a reducer that does something more than
-- return whatever it was given, of course!
reducer :: Lexp -> Lexp
reducer lexp = getLexp r
    where r = uniqueRename lexp SymbolIDs.empty BoundIDs.empty

-- Entry point of program
main = do
    args <- getArgs
    let inFile = case args of { x:_ -> x; _ -> "input.lambda" }
    let outFile = case args of { x:y:_ -> y; _ -> "output.lambda"}
    -- id' simply returns its input, so runProgram will result
    -- in printing each lambda expression twice. 
    runProgram inFile outFile reducer
