# Lambda Calculus Interpreter

## Group Members

- Mitesh Kumar `<kumarm4>`
- Alex He `<hea2>`

## Features

- Alpha-equivalent applicative order lambda calculus expression reducer
- Alpha-equivalency checker between two lambda calculus expressions

## Known Bugs

- Loops indefinitely on repeated sub-expressions (for example `Loop Combinator: (\x.(x x) \x.(x x))`).

## Approach

1. Rename all corresponding bound variables to something unique that also does not match any free variables. Do this with two maps of counters for each symbol.
   One map will contain the current counter that we must append to a matching variable to match the parent bound lambda symbol. The second map will contain the highest count that this number has ever been set to, so that when we see a new lambda, we can set our current map to this next map value, and increment the next value, thus keeping the counts unique, without losing track of where we are in the tree.

2. Do eta/beta reduction

## Notes

- We had to modify the definition of `Lexp` by adding `!` bang symbols in order
  to make it strictly evaluated instead of lazy. We were not able to find a way to do applicative
  order reduction without removing lazy evaluation. Consider the case
  `(\y.z (\x.(x x) \x.(x x)))`. This should loop indefinitely in an applicative order evaluation. In haskell, we will get the following structure in our beta reduction:

```
    Calling betaReduce builds the following tree:
    betaReduce (\y.z (\x.(x x) \x.(x x)))
        = betaReduce ((betaReduce \y.z) (betaReduce (\x.(x x) \x.(x x))))
```

unless we force `(betaReduce (\x.(x x) \x.(x x)))` to execute immediately,
when haskell finally decides to process the chain of calls, the entry-point
will be the outermost `betaReduce`, which will then first replace all `y` in
`z` with the lazy eval reference to `(betaReduce (\x.(x x) \x.(x x)))`, but
there are no `y`s so we end up never having to actually evaluate
`(betaReduce (\x.(x x) \x.(x x)))`, since it is never needed, even though we wrote the call structure so that the outer `betaReduce` depends on the inner one.
Hence the need for the strict evaluation designation with the `!` symbol, like
the following:

`data Lexp = Atom !String | Lambda !String !Lexp | Apply !Lexp !Lexp deriving (Eq)`
