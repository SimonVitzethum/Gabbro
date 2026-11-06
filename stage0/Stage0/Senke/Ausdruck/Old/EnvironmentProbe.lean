/- Joint witness: complete old array/counter snapshots and a preserved two-word parameter. -/
module
public import Stage0.Senke.Ausdruck.Old.Environment
public import Stage0.Senke.Ausdruck.Old.Distinct
@[expose] public section


namespace Gabbro.Stage0.Senke.CompleteSnapshotEnvProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
open DistinctSnapshotProbe
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def parameter : Wert D (.arr (.int 0 100) 2) :=
  fun i => if i.val = 0 then ⟨33, by decide, by decide⟩ else ⟨34, by decide, by decide⟩

def params : Env D [.arr (.int 0 100) 2] := .cons parameter .nil

theorem parameter_at : EnvAt layout memory 4096 params 4 := by
  apply envAt_cons (ρ := (Env.nil : Env D [])) (fun _ x => nomatch x)
  constructor
  · intro i; trivial
  · have width : integerWords 0 100 = 1 := integerWords_word (by decide) (by decide)
    have encoded : encodeWords layout (.arr (.int 0 100) 2) parameter = [33, 34] := by
      simp [encodeWords, elementEncoding, parameter]
      erw [encodeWords_int, encodeWords_int]
      simp [width, integerEncoding]
    rw [encoded]
    change WordsAt memory 4096 8 [33, 34]
    intro i hi
    have cases : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases cases with rfl | rfl <;> decide +kernel +revert

/-- Every capture/environment premise holds jointly, with three distinct array
    limbs, a different global counter, and a surviving two-word parameter. -/
theorem complete_at_zeuge [Kern] :
    EntrySnapshots.words cells = 4 ∧
    ∃ m', Star ⟨0, 4096⟩ memory ⟨128, 4096⟩ m' ∧
      EnvAt layout m' 4096 (EntrySnapshots.appendEnv params (EntrySnapshots.values world cells)) ∧
      EnvAt layout m' 4096 params 4 ∧ EntrySnapshots.At layout world m' 4096 cells 4 := by
  have emitted : EntrySnapshots.capture layout cells 4 = some code := by decide +kernel
  obtain ⟨m', run, changed, saved⟩ := EntrySnapshots.capture_ok cells 4 emitted memory 0
    frame (by decide) (by decide)
    (by intro cell hc; simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> decide +kernel)
    code_at (by unfold CodeFar; decide +kernel) inputs
  have preserved := EntrySnapshots.envAt_above parameter_at changed frame (by decide) (by decide)
  refine ⟨rfl, m', ?_, (EntrySnapshots.complete_at params world cells).mpr ⟨preserved, saved⟩,
    preserved, saved⟩
  change Star ⟨0, 4096⟩ memory ⟨128, 4096⟩ m' at run
  exact run

end Gabbro.Stage0.Senke.CompleteSnapshotEnvProbe
