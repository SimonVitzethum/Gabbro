module

public import Core.Beobachtung.Unentscheidbar.Simulation.KodierBefehlBeweis

noncomputable section

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

open Gabbro.Core.Ast.Semantik

/-- The Gödel numbering of the simulation substrate: a command program is a
    first-order tree of constructor tags and field encodings, collapsed to a
    single natural number by the `Encodable` instance. -/
def kodiere : List Befehl → ℕ :=
  Encodable.encode

def dekodiere : ℕ → Option (List Befehl) :=
  Encodable.decode

example (xs : List Nat) :
    (do let fs ← some xs; match fs with | [a] => some a | _ => none) =
      (match xs with | [a] => some a | _ => none) := by
  simp only [Option.bind_some]

theorem dekodiere_links (p : List Befehl) : dekodiere (kodiere p) = some p :=
  Encodable.encodek p

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
