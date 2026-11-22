/- Function frames are computed from the checked source signature, postcondition
   snapshots and loop nesting. The external parameter/result ABI stays canonical.

   After the depth and requires guards, preserve the incoming parameters above the
   complete snapshot prefix, capture the entry values, then relocate lexical
   parameters above the internal result/status and counters. Ensures sees the
   original parameters. Normal returns check ensures before publishing the complete
   result and status; reasons publish their canonical span without running ensures.
   The shared epilogue checks owed table/global predicates after ensures. -/
module
public import Stage0.Senke.Anweisung
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Allocation
public import Stage0.Senke.Stopp
public import Stage0.Senke.Ausdruck.Old.Sound
public import Stage0.Senke.Rueckkehr.EpilogueCode
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {V : Vertrag D}

/-- Every placement input is computed from this same checked source function. -/
def functionFrame (P : Programm D) (f : D.Fn) : FrameLayout := {
  params := D.params f
  result := D.erg f
  reasons := D.gruende f
  snapshotWords := EntrySnapshots.words (oldCells (P.ensures f))
  counterDepth := counterDepthE (P.rumpf f) }

/-- The protected prefix contains every original parameter and any entry snapshots. -/
theorem functionFrame_prefix (P : Programm D) (f : D.Fn) :
    FB + contextWords (D.params f) ≤ (functionFrame P f).internalResult := by
  simp only [functionFrame, FrameLayout.internalResult, FrameLayout.ensParams,
    FrameLayout.ensReserved, FrameLayout.parameterWords]
  omega

/-- The code of `f`, and the first slot it does not write. -/
def lowFun (passes : Nat) (P : Programm D) (A : D.Fn → Nat) (L : Lay D) (f : D.Fn) : Option (List II × Nat) :=
  let layout := functionFrame P f
  let cells := oldCells (P.ensures f)
  do
    let req ← lowE L (P.requires f) layout.canonicalResult
    let ens ← lowPost L layout P f layout.internalStatus
    let body ← lowEnd (reserved := layout.bodyReserved) passes A L layout ens [] (0, 0) (P.rumpf f)
    let snap ← EntrySnapshots.capture L cells layout.snapshotBase
    let original := relocateC FB layout.ensReserved layout.parameterWords
    let lexical := relocateC layout.ensParams (layout.bodyReserved - layout.ensReserved) layout.parameterWords
    pure (guardC 2 105 layout.canonicalResult ++ req.1 ++
      guardC layout.canonicalResult 101 layout.canonicalResult ++ original ++ snap ++ lexical ++ body.1,
      max (retTop layout) (max req.2 (max (layout.bodyParams + layout.parameterWords) body.2)))

/-- Function placement depends only on the measured requirement and
    body. The originals, snapshots and ABI scaffolding have fixed sizes. -/
theorem lowFun_measure {passes : Nat} {P : Programm D} {A B : D.Fn → Nat} {L R : Lay D} {f : D.Fn}
    {original relocated : List II × Nat}
    (requiresMeasure : (lowE L (P.requires f) (functionFrame P f).canonicalResult).map codeMeasure =
      (lowE R (P.requires f) (functionFrame P f).canonicalResult).map codeMeasure)
    (bodyMeasure : let frame := functionFrame P f
      ∀ leftPost rightPost leftBody rightBody,
        lowPost L frame P f frame.internalStatus = some leftPost →
        lowPost R frame P f frame.internalStatus = some rightPost →
        lowEnd (reserved := frame.bodyReserved) passes A L frame leftPost [] (0, 0) (P.rumpf f) = some leftBody →
        lowEnd (reserved := frame.bodyReserved) passes B R frame rightPost [] (0, 0) (P.rumpf f) = some rightBody →
        codeMeasure leftBody = codeMeasure rightBody)
    (first : lowFun passes P A L f = some original)
    (second : lowFun passes P B R f = some relocated) :
    codeMeasure original = codeMeasure relocated := by
  simp only [lowFun, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at first second
  obtain ⟨leftRequires, requiresLeft, leftPost, postLeft, leftBody, bodyLeft, leftSnap, snapLeft, rfl⟩ := first
  obtain ⟨rightRequires, requiresRight, rightPost, postRight, rightBody, bodyRight, rightSnap, snapRight, rfl⟩ := second
  rw [requiresLeft, requiresRight, Option.map_some, Option.map_some, Option.some.injEq] at requiresMeasure
  obtain ⟨reqSize, reqTop⟩ := Prod.mk.inj requiresMeasure
  obtain ⟨bodySize, bodyTop⟩ := Prod.mk.inj (bodyMeasure _ _ _ _ postLeft postRight bodyLeft bodyRight)
  have snapSize : leftSnap.length = rightSnap.length :=
    (EntrySnapshots.capture_length _ _ snapLeft).trans (EntrySnapshots.capture_length _ _ snapRight).symm
  simp only [codeMeasure, List.length_append, reqSize, reqTop, snapSize, bodySize, bodyTop]

end Gabbro.Stage0.Senke
