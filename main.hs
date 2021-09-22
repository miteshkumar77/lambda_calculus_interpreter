import PA1Helper (Lexp (..), runProgram)
import PA1Utils (reducer)
import System.Environment (getArgs)

-- Entry point of program
main :: IO ()
main = do
  args <- getArgs
  let inFile = case args of x : _ -> x; _ -> "input.lambda"
  let outFile = case args of x : y : _ -> y; _ -> "output.lambda"
  -- id' simply returns its input, so runProgram will result
  -- in printing each lambda expression twice.
  runProgram inFile outFile reducer