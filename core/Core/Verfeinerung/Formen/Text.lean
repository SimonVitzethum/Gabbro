module

public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

def TextSimAussage : Prop := SimFamilie.text.Pflicht

theorem textSim : TextSimAussage := by
  unfold TextSimAussage SimFamilie.Pflicht
  intro p platform b _
  exact ⟨I.RegelSimSchritt.aus_gleicher_regel rfl (fun _ _ _ _ _ h => h),
    I.RegelStotterSchranke.null rfl⟩

end Gabbro.Core.Ast.Semantik
