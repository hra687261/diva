import Diva.Parser

/-- Parse `s` and render its tree, or `none` on a parse error. -/
private def parseStr (s : String) : Option String :=
  (Diva.parse s).toOption.map toString

#guard parseStr "1 + 2 * 3 - 4"       = some "((1 + (2 * 3)) - 4)"
#guard parseStr "(1 + 2) * 3"         = some "((1 + 2) * 3)"
#guard parseStr "a - b - c"           = some "((a - b) - c)"
#guard parseStr "a = b"               = some "(a = b)"
#guard parseStr "f x y"               = some "((f x) y)"
#guard parseStr "let x = 40 in x + 2" = some "(let x = 40 in (x + 2))"
#guard parseStr "fun x -> x + 1"      = some "(fun x -> (x + 1))"
#guard parseStr "if a then b else c"  = some "(if a then b else c)"
#guard parseStr "if a then b"         = some "(if a then b else ())"
#guard parseStr "if a then b; c"      = some "(let _ = (if a then b else ()) in c)"
#guard parseStr "a = b = c"           = none

-- comparisons
#guard parseStr "a <= b"              = some "(a <= b)"
#guard parseStr "a <> b"              = some "(a <> b)"
#guard parseStr "a + 1 >= b * 2"      = some "((a + 1) >= (b * 2))"

-- unary minus binds tighter than `*`, looser than application
#guard parseStr "-3"                  = some "(0 - 3)"
#guard parseStr "-x * y"              = some "((0 - x) * y)"
#guard parseStr "-f x"                = some "(0 - (f x))"
#guard parseStr "a - -b"              = some "(a - (0 - b))"

-- `/` and `mod` sit with `*`
#guard parseStr "a + b / c mod d"     = some "(a + ((b / c) mod d))"

-- unit and assert
#guard parseStr "()"                  = some "()"
#guard parseStr "assert x"            = some "(assert x)"

-- `let rec`, with the parameter before `=` or as a `fun`
#guard parseStr "let rec f x = f x in f" = some "(let rec f x = (f x) in f)"
#guard parseStr "let rec f = fun x -> x in f" = some "(let rec f x = x in f)"
#guard parseStr "let rec f = 1 in f"  = none

-- sugar
#guard parseStr "fun x y -> x"        = some "(fun x -> (fun y -> x))"
#guard parseStr "let f x y = x in f"  = some "(let f = (fun x -> (fun y -> x)) in f)"
#guard parseStr "a && b"              = some "(if a then b else false)"
#guard parseStr "a || b"              = some "(if a then true else b)"
#guard parseStr "a || b && c"         = some "(if a then true else (if b then c else false))"
#guard parseStr "not a"               = some "(if a then false else true)"
#guard parseStr "a; b"                = some "(let _ = a in b)"
#guard parseStr "let _ = a in b"      = some "(let _ = a in b)"
#guard parseStr "fun _ -> 1"          = some "(fun _ -> 1)"
#guard parseStr "1; _"                = none  -- `_` binds but can't be used

-- lists: `::` is right-associative and looser than `+`
#guard parseStr "[]"                  = some "[]"
#guard parseStr "a :: b :: []"        = some "(a :: (b :: []))"
#guard parseStr "[a; b]"              = some "(a :: (b :: []))"
#guard parseStr "[a; b;]"             = some "(a :: (b :: []))"
#guard parseStr "[f x; a + 1]"        = some "((f x) :: ((a + 1) :: []))"
#guard parseStr "a + 1 :: l"          = some "((a + 1) :: l)"
#guard parseStr "match l with [] -> 0 | x :: xs -> x" =
  some "(match l with [] -> 0 | x :: xs -> x)"

-- top-level declarations: nested `let`s ending in the last item
#guard parseStr "let x = 1 let y = 2 ;; x + y" =
  some "(let x = 1 in (let y = 2 in (x + y)))"
#guard parseStr "let x = 1"           = some "(let x = 1 in x)"
#guard parseStr "a ;; b"              = some "(let _ = a in b)"
#guard parseStr ""                    = some "()"
-- `;;` is required before an expression that follows a declaration
#guard parseStr "let x = 1 if x = 1 then 2 else 3" = none
#guard parseStr "let x = 1 ;; if x = 1 then 2 else 3" =
  some "(let x = 1 in (if (x = 1) then 2 else 3))"
