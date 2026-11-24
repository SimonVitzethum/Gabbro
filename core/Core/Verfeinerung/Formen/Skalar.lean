module

public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

def SkalarSimAussage : Prop := SimFamilie.skalar.Pflicht

theorem skalarSim : SkalarSimAussage := by
  intro p platform b hb
  refine ⟨I.RegelSimSchritt.aus_gleicher_regel rfl ?_, ?_⟩
  · intro c s w plans u rule
    exact rule
  · exact I.RegelStotterSchranke.null rfl

end Gabbro.Core.Ast.Semantik
