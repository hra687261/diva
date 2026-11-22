import Diva
import Cli

/-! The `diva` executable's command-line interface. -/

open Diva Cli

/-- The contents of `path`, or of the standard input if `path` is `-`. -/
def readSource (path : String) : IO String :=
  if path == "-" then do (← IO.getStdin).readToEnd
  else IO.FS.readFile path

/-- Runs `cmd`, which may do IO, on the file given as argument, and prints its
    result. -/
def runWith' (cmd : String → IO Commands.Result) (p : Parsed) : IO UInt32 := do
  let path := p.positionalArg! "file" |>.as! String
  let r ← cmd (← readSource path)
  for l in r.out do IO.println l
  for l in r.err do IO.eprintln l
  return r.code

/-- Runs `cmd` on the file given as argument, and prints its result. -/
def runWith (cmd : String → Commands.Result) : Parsed → IO UInt32 :=
  runWith' fun src => pure (cmd src)

def runRun := runWith Commands.run

/-- The result of `reader`, or `none` if `seconds` seconds pass first (no limit if
    `seconds` is `none`). A second task, `timer`, sleeps for `seconds` seconds.
    `IO.waitAny` waits for the first of the two tasks to finish, without polling. -/
def waitFor (reader : Task α) : Option Nat → BaseIO (Option α)
  | none => return some (← IO.wait reader)
  | some seconds => do
    let timer ← IO.asTask (IO.sleep (seconds * 1000).toUInt32) .dedicated
    IO.waitAny [reader.map some, timer.map fun _ => none]

/-- Run the shell command `cmd` (any LLM) with `question` on its standard input, and
    return what it prints. After `timeout` seconds, `cmd` is stopped, with an error. -/
def askCommand (cmd : String) (timeout : Option Nat) (question : String) : IO String := do
  let child ← IO.Process.spawn
    { cmd := "sh", args := #["-c", cmd], stdin := .piped, stdout := .piped, setsid := true }
  let (stdin, child) ← child.takeStdin
  stdin.putStr question
  stdin.flush  -- `stdin` is closed after its last use, so `cmd` sees the end of the question
  -- the answer is read in another task, so that `waitFor` can stop waiting for it
  let reader ← IO.asTask child.stdout.readToEnd .dedicated
  let some answer ← waitFor reader timeout | do
    -- `child.kill` stops only `sh`, so the whole group is stopped with `kill`
    discard <| IO.Process.output { cmd := "kill", args := #["-KILL", "--", s!"-{child.pid}"] }
    throw (IO.userError s!"the oracle `{cmd}` didn't answer within {timeout.getD 0} seconds")
  let answer ← IO.ofExcept answer
  let code ← child.wait
  if code != 0 then throw (IO.userError s!"the oracle `{cmd}` exited with code {code}")
  return answer

/-- `diva check`. With `--oracle CMD`, the shell command `CMD` (an LLM, for example)
    is asked for hints when the check fails. `diva` checks them. -/
def runCheck (p : Parsed) : IO UInt32 :=
  match p.flag? "oracle" with
  | none => runWith Commands.check p
  | some cmd =>
    let rounds := (p.flag? "rounds").map (·.as! Nat) |>.getD 3
    let timeout := (p.flag? "timeout").map (·.as! Nat)
    runWith' (Commands.checkOracle (askCommand (cmd.as! String) timeout) rounds) p

def runOpt := runWith Commands.opt
def runHints := runWith Commands.hints

/-- The folder of Diva's compiled modules (`.olean` files): `../lib/lean`, starting from
    the folder of the `diva` executable. `lake build` puts them there, in `.lake/build`.
    An install must keep the same layout. -/
def libDir : IO System.FilePath := do
  let app ← IO.appPath
  let pre := app.parent.bind (·.parent) |>.getD "."
  return pre / "lib" / "lean"

/-- The name of the Lean file that `diva cert` and `diva prove` write:
    - the name given with `-o`, if there is one
    - otherwise `<name>.lean` for the program `<name>.ml`
    - for a program read from the standard input (`path` is `-`), the argument `stdin`:
      `cert.lean` for `diva cert`, `prove.lean` for `diva prove`. -/
def outFile (p : Parsed) (path stdin : String) : String :=
  match p.flag? "output" with
  | some f => f.as! String
  | none => if path == "-" then stdin else (System.FilePath.withExtension path "lean").toString

/-- Write the Lean file that `cmd` gives for the program to `outFile`. With `--check`,
    also run Lean on that file, so Lean's errors give positions in it, and print the
    message `ok` if Lean accepts it. The file imports Diva's modules, which only load in the Lean
    version that built `diva`. If `lean` is elan's, `ELAN_TOOLCHAIN` makes it run that
    version. -/
def writeAndCheck (cmd : String → Commands.Result) (stdin ok : String) (p : Parsed) :
    IO UInt32 := do
  let path := p.positionalArg! "file" |>.as! String
  let output := outFile p path stdin
  let r := cmd (← readSource path)
  for l in r.err do IO.eprintln l
  if r.code != 0 then return r.code
  IO.FS.writeFile output ("\n".intercalate r.out)
  IO.println s!"wrote {output}"
  if !p.hasFlag "check" then return 0
  let toolchain := s!"leanprover/lean4:v{Lean.versionString}"
  let out ← IO.Process.output
    { cmd := "lean", args := #[output],
      env := #[("LEAN_PATH", some (← libDir).toString), ("ELAN_TOOLCHAIN", some toolchain)] }
  if out.exitCode == 0 then
    IO.println ok
    return 0
  IO.print out.stdout
  IO.eprint out.stderr
  return 1

/-- `diva cert`: write the certificate, a Lean file stating that the program never
    fails. -/
def runCert := writeAndCheck Commands.cert "cert.lean"
  "certificate checked by Lean: the program never fails"

/-- `diva prove`: write a Lean file stating that the functions meet their contracts. -/
def runProve := writeAndCheck Commands.prove "prove.lean"
  "checked by Lean: the functions meet their contracts"

/-- `diva` without a command: print the help. -/
def runDiva (p : Parsed) : IO UInt32 := do
  p.printHelp
  return 2

def runCmd : Cmd := `[Cli|
  run VIA runRun;
  "Evaluate the program and print its return value."
  ARGS:
    file : String; "The program (`-` reads the standard input)."
]

def checkCmd : Cmd := `[Cli|
  check VIA runCheck;
  "Say where the program may fail. Exits with 1 if it may fail."
  FLAGS:
    oracle : String; "A shell command, such as an LLM, that reads a question on its standard input and proposes hints on its standard output. The hints are checked."
    rounds : Nat; "How many times to ask the oracle (3 by default)."
    timeout : Nat; "How many seconds to wait for each answer of the oracle (no limit by default). If the time is up, the oracle is stopped, and `diva` stops with an error."
  ARGS:
    file : String; "The program (`-` reads the standard input)."
]

def optCmd : Cmd := `[Cli|
  opt VIA runOpt;
  "Optimize the program and print it."
  ARGS:
    file : String; "The program (`-` reads the standard input)."
]

def hintsCmd : Cmd := `[Cli|
  hints VIA runHints;
  "Print the hints inferred for the program."
  ARGS:
    file : String; "The program (`-` reads the standard input)."
]

def certCmd : Cmd := `[Cli|
  cert VIA runCert;
  "Write a certificate: a Lean file stating that the program never fails. \
   Exits with 1 if the program may fail."
  FLAGS:
    check; "Also run Lean on the certificate. Exits with 1 if Lean rejects it."
    o, output : String; "The certificate file to write. By default `<name>.lean` for `<name>.ml`, `cert.lean` for `-`."
  ARGS:
    file : String; "The program (`-` reads the standard input)."
]

def proveCmd : Cmd := `[Cli|
  prove VIA runProve;
  "Write a Lean file stating that the functions meet their contracts, written in \
   `(*@ requires ... ensures ... *)` comments. Exits with 1 if there is no contract."
  FLAGS:
    check; "Also run Lean on the file. Exits with 1 if Lean rejects it."
    o, output : String; "The file to write. By default `<name>.lean` for `<name>.ml`, `prove.lean` for `-`."
  ARGS:
    file : String; "The program (`-` reads the standard input)."
]

def divaCmd : Cmd := `[Cli|
  diva VIA runDiva; ["dev"]
  "A simple program verifier."
  SUBCOMMANDS:
    runCmd;
    checkCmd;
    optCmd;
    hintsCmd;
    certCmd;
    proveCmd
]

/-- An error, such as an oracle that takes too long, is printed as `error: ...`, with
    the exit code 1. `IO.Process.exit` ends `diva` without waiting for the tasks that
    are still running, such as the `timer` of `waitFor`. -/
def main (args : List String) : IO UInt32 := do
  let code ← try divaCmd.validate args
    catch e =>
      IO.eprintln s!"error: {e}"
      pure 1
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit code.toUInt8
