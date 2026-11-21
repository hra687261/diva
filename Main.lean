import Diva
import Cli

/-! The `diva` executable's command-line interface. -/

open Diva Cli

/-- The contents of `path`, or of the standard input if `path` is `-`. -/
def readSource (path : String) : IO String :=
  if path == "-" then do (← IO.getStdin).readToEnd
  else IO.FS.readFile path

/-- Runs `cmd` on the file given as argument, and prints its result. -/
def runWith (cmd : String → Commands.Result) (p : Parsed) : IO UInt32 := do
  let path := p.positionalArg! "file" |>.as! String
  let r := cmd (← readSource path)
  for l in r.out do IO.println l
  for l in r.err do IO.eprintln l
  return r.code

def runRun := runWith Commands.run
def runCheck := runWith Commands.check
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

def main (args : List String) : IO UInt32 :=
  divaCmd.validate args
