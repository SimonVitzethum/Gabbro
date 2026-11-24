module

public import Core.Verfeinerung.Formen.Familie

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

def AufrufSchleifeSimAussage : Prop := SimFamilie.aufrufSchleife.Pflicht

theorem aufrufSchleifeSim : AufrufSchleifeSimAussage := by
  intro p platform b familie
  refine ⟨I.RegelSimSchritt.aus_gleicher_regel rfl (fun _ _ _ _ _ rule => rule),
    I.RegelStotterSchranke.null rfl⟩

end Gabbro.Core.Ast.Semantik
