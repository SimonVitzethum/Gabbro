module

public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

def AggregatSimAussage : Prop := SimFamilie.aggregat.Pflicht

theorem aggregatSim : AggregatSimAussage := by
  intro p platform b hb
  exact ⟨
    I.RegelSimSchritt.aus_gleicher_regel rfl (fun _ _ _ _ _ rule => rule),
    I.RegelStotterSchranke.null rfl⟩

end Gabbro.Core.Ast.Semantik
