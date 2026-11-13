module
public import Stage0.Senke.Funktion
public import Stage0.Senke.Anweisung.Fast.Equivalence
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- Allocate live-context metadata once at function entry, then carry it through
    the executable lexical traversal. The specification remains `lowFun`. -/
def lowFunFast (passes : Nat) (P : Programm D) (A : D.Fn → Nat) (L : Lay D) (f : D.Fn) : Option (List II × Nat) :=
  let layout := functionFrame P f
  let cells := oldCells (P.ensures f)
  do
    let req ← lowE L (P.requires f) layout.canonicalResult
    let ens ← lowPost L layout P f layout.internalStatus
    let body ← (lowEndFast passes A L layout ens [] (0, 0) (P.rumpf f) layout.bodyReserved []
      (FrameCache.ofCtx _)).map CodeCache.value
    let snap ← EntrySnapshots.capture L cells layout.snapshotBase
    let original := relocateC FB layout.ensReserved layout.parameterWords
    let lexical := relocateC layout.ensParams (layout.bodyReserved - layout.ensReserved) layout.parameterWords
    pure (guardC 2 105 layout.canonicalResult ++ req.1 ++
      guardC layout.canonicalResult 101 layout.canonicalResult ++ original ++ snap ++ lexical ++ body.1,
      max (retTop layout) (max req.2 (max (layout.bodyParams + layout.parameterWords) body.2)))

/-- Only the executable function entry is replaced. Kernel compile witnesses and
    all existing lowering correctness statements still evaluate the specification. -/
@[csimp] theorem lowFun_eq_fast : @lowFun = @lowFunFast := by
  funext D passes P A L f
  simp only [lowFunFast, lowFun, lowEndFast_eq, CodeCache.map_value]

end Gabbro.Stage0.Senke
