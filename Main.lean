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

/-- The certificate file of `diva cert`: the `-o` flag, otherwise `<name>.lean` for the
    program `<name>.ml`, and `cert.lean` for a program read from the standard input. -/
def certFile (p : Parsed) (path : String) : String :=
  match p.flag? "output" with
  | some f => f.as! String
  | none => if path == "-" then "cert.lean" else (System.FilePath.withExtension path "lean").toString

/-- `diva cert`: write the certificate to `certFile`. With `--check`, also run Lean on
    that file, so Lean's errors give positions in it. The certificate imports Diva's
    modules, which only load in the Lean version that built `diva`. If `lean` is elan's,
    `ELAN_TOOLCHAIN` makes it run that version. -/
def runCert (p : Parsed) : IO UInt32 := do
  let path := p.positionalArg! "file" |>.as! String
  let output := certFile p path
  let r := Commands.cert (← readSource path)
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
    IO.println "certificate checked by Lean: the program never fails"
    return 0
  IO.print out.stdout
  IO.eprint out.stderr
  return 1

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

def divaCmd : Cmd := `[Cli|
  diva VIA runDiva; ["dev"]
  "A simple program verifier."
  SUBCOMMANDS:
    runCmd;
    checkCmd;
    optCmd;
    hintsCmd;
    certCmd
]

def main (args : List String) : IO UInt32 :=
  divaCmd.validate args
