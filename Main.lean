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

def divaCmd : Cmd := `[Cli|
  diva VIA runDiva; ["dev"]
  "A simple program verifier."
  SUBCOMMANDS:
    runCmd;
    checkCmd;
    optCmd;
    hintsCmd
]

def main (args : List String) : IO UInt32 :=
  divaCmd.validate args
