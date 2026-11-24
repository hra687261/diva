# The grammar of DIVA's language

The comment after each rule says which commands support it:

- `run`: `diva run` runs the program. It supports the whole grammar.
- `check`: `diva check` and `diva cert` analyse the program. For a rule without
  `check`, they say that the program may fail.
- `prove`: `diva prove`, `diva spec` and `diva synth` prove the contracts. A
  function with a contract can use only the rules marked `prove`. The functions that
  it calls without a contract get the empty contract: `diva prove` proves that they
  don't fail, and nothing about their result.

## Programs

```
program ::= item item ...
item    ::= let x = e                     -- run, check, prove (after the functions with a contract)
          | let f x ... = e contract?     -- run, check, prove
          | let rec f x ... = e contract? -- run, check, prove
          | ;; e                          -- run, check, prove (after the functions with a contract)
```

`let f x y = e` is `let f = fun x -> fun y -> e`.

## Expressions

```
e ::= n                              -- an integer: run, check, prove
    | true | false | ()              -- run, check, prove
    | x                              -- a name: run, check, prove
    | - e                            -- `0 - e`: run, check, prove
    | e op e                         -- op: + - * / mod = <> < <= > >=: run, check, prove
    | e && e | e || e | not e        -- run, check, prove
    | if e then e else e             -- run, check, prove
    | if e then e                    -- `else ()`: run, check, prove
    | let x = e in e                 -- run, check, prove
    | assert e                       -- run, check, prove
    | e e                            -- a call: run, check, prove
    | e; e                           -- `let _ = e in e`: run, check, prove
    | fun x ... -> e                 -- run, check
    | let f x ... = e in e           -- run, check
    | let rec f x ... = e in e       -- run, check
    | [] | e :: e | [e; ...]         -- lists: run, check
    | match e with [] -> e | x :: xs -> e
                                     -- run, check
    | E | E e                        -- an exception: run, check
    | raise e                        -- run
    | try e with E x -> e | F -> e | k -> e
                                     -- run
    | Array.make e e                 -- a new array, with its length and its value: run
    | e.(e) | e.(e) <- e             -- read and write an array: run
    | Array.length e                 -- run
    | ref e | !e | e := e            -- refs: run
    | incr e | decr e                -- `e := !e + 1`, `e := !e - 1`: run
    | for x = e to e do e done       -- a recursive function: run, check
    | while e do e done              -- a recursive function: run, check
```

Integers have no bounds.

## Contracts

A contract is a comment after a function `f`, here with the parameters `x` and `y`:

```
contract ::= (*@ r = f x y
                 requires t
                 ensures t *)
t ::= n | x | y | r                  -- an integer, a parameter, the result
    | t op t                         -- op: + - * = <> < <= > >=
    | t && t
```

- `requires` can use only the parameters. `ensures` can use the parameters and the
  result `r`.
- There can be several `requires` and several `ensures`, or none.
- `requires` is checked at run time, once the function has all its arguments: a call
  that breaks it fails, as an `assert` does. `ensures` isn't checked at run time.
- Without the header `r = f x y`, the parameters have the names of the code, and the
  result is `result`.
- In `diva prove`, the parameters and the result are integers.
- A function with a contract can be called only with all its arguments: `f a b`.
