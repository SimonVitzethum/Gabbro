/- Joint witness for publishing a complete result across the snapshot prefix. -/
module
public import Stage0.Senke.Rueckkehr.Publish
public import Stage0.Senke.Ausdruck.Old.Distinct
@[expose] public section


namespace Gabbro.Stage0.Senke.ReturnProtocolProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
open DistinctSnapshotProbe (D layout value)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def placement : FrameLayout :=
  ⟨[.arr (.int 0 255) 2], some (.arr (.int 0 255) 3), 2, 4, 1⟩

def code : List II := publishC placement

def memory : Runner.Mem where
  b a := if a.toNat < 96 then
      ((code.flatMap (fun i => Runner.Prog.insB i.o i.a i.b i.c))[a.toNat]?).getD 0
    else if a.toNat = 4097 then 1
    else if a.toNat = 4105 then 32
    else if a.toNat = 4176 then 1
    else if a.toNat = 4184 then 2
    else if a.toNat = 4192 then 3 else 0
  rd _ := true
  wr _ := true

theorem frame : FrameOK memory 4096 64 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem code_at : CodeAt memory 0 code := by
  intro k hk
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
    change k < 6 at hk
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> decide +kernel +revert

theorem result_at : ResultAt layout memory 4096 placement.internalResult placement.result value := by
  constructor
  · intro i; trivial
  · change WordsAt memory 4096 10 [1, 2, 3]
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < 3 at hi; omega
    rcases cases with rfl | rfl | rfl <;> decide +kernel +revert

/-- Three unequal result limbs cross a four-word snapshot prefix. Both return
    addresses, the status after the full payload and the legacy mirror agree. -/
theorem publishResult_run_zeuge [Kern] :
    placement.canonicalResult = 6 ∧ placement.internalResult = 10 ∧
    ∃ m', Star ⟨0, 4096⟩ memory ⟨256, 8192⟩ m' ∧ Agree 4096 2 64 memory m' ∧
      ResultAt layout m' 4096 6 placement.result value ∧
      ReturnMirror m' 4096 6 ∧ ReturnFlag m' 4096 2 true 3 := by
  refine ⟨rfl, rfl, ?_⟩
  exact publishResult_run placement frame (by decide) (by decide) code_at
    (by unfold CodeFar; decide +kernel) result_at
    (by decide +kernel) (by decide +kernel)

end Gabbro.Stage0.Senke.ReturnProtocolProbe
