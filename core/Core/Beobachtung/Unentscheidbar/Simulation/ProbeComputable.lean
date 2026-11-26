import Core.Beobachtung.Unentscheidbar.Simulation.Nummer
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik
open Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
example : Computable (fun p : List Befehl => kodiere p) := by
  infer_instance
