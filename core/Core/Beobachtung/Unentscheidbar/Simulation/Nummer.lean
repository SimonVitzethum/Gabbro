module

public import Core.Beobachtung.Unentscheidbar.Simulation.KodierBefehlBeweisBeweis

noncomputable section

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation

/-- The Gödel numbering of the simulation substrate: a command program is a
    first-order tree of constructor tags and field encodings, collapsed to a
    single natural number by the `Encodable` instance. -/
def kodiere : List Befehl → ℕ :=
  Encodable.encode

def dekodiere : ℕ → Option (List Befehl) :=
  Encodable.decode

theorem dekodiere_links (p : List Befehl) : dekodiere (kodiere p) = some p :=
  Encodable.encodek p

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation
