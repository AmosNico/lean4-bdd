module

import Bdd.Parser

public def main (args : List String) : IO Unit := do
  match args with
  | [fs] =>
    try
      let B ← parseBDD fs
      IO.println B.nvars
    catch e =>
      IO.println s!"Error reading file {fs}: {e}"
  | _ => IO.println "Usage: ./BddParser <input-file>"
