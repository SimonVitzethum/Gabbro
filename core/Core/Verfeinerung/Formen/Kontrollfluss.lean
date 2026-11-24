module

public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

def KontrollflussSimAussage : Prop := SimFamilie.kontrollfluss.Pflicht

theorem kontrollflussSim : KontrollflussSimAussage := by
  intro p platform b _
  refine ⟨?_, ?_⟩
  · exact Maschine.I.RegelSimSchritt.aus_gleicher_regel rfl (fun _ _ _ _ _ step => step)
  · exact Maschine.I.RegelStotterSchranke.null rfl

end Gabbro.Core.Ast.Semantik
