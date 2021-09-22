import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace (trace)
import PA1Helper (Lexp (..), eqHandler, runProgram)
import PA1Utils (alphaEq, reducer)
import System.Directory

import System.Environment (getArgs)
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Token

runEqCheck :: String -> String -> String -> (Lexp -> Lexp -> Bool) -> IO ()
runEqCheck calcFile ansFile outFile alphaChecker = do
  outExists <- doesFileExist outFile
  calcExists <- doesFileExist calcFile
  ansExists <- doesFileExist ansFile
  when outExists $ removeFile outFile
  calcContents <- readFile calcFile
  ansContents <- readFile ansFile
  let calcList = lines calcContents
      ansList = lines ansContents
  sequence_ (zipWith (eqHandler alphaEq reducer outFile) calcList ansList)

main :: IO ()
main = do
  args <- getArgs
  let calcFile = case args of x : _ -> x; _ -> "auto_input.lambda"
  let ansFile = case args of x : y : _ -> y; _ -> "auto_answers.lambda"
  let outFile = case args of x : y : z : _ -> z; _ -> "auto_output.lambda"
  runEqCheck calcFile ansFile outFile alphaEq
