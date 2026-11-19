/- Joint premises of the structural compiler theorem, and the obstruction
   to reusing the old witness list as a fully accepted table. -/
module

public import Grammatik.Gen.Zeugen.Schluss.Teil3
public import Grammatik.Gen.Zeugen.Schluss.Checked

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen

open Gabbro.Grammatik.Gen.Zeugen.Gap

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Adaequanz

/-- A cell-sensitive correctness predicate: every structural cell is good.
    Reset.Bad below witnesses that this predicate is not constantly true. -/
def structuralCompiler (e : Einsatz) : Prop := akzeptiert Einsatz.Hat gutTafel e

end Gabbro.Grammatik.Gen.Zeugen
