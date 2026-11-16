/- Exact accepted-fixture coverage; missing cells remain explicit findings. -/
module

public import Grammatik.Gen.Zeugen.Gap.Audit
public import Grammatik.Gen.Zeugen.M.ScalarRead
public import Grammatik.Gen.Zeugen.Reset
public import Grammatik.Gen.Zeugen.M.F00_call
public import Grammatik.Gen.Zeugen.M.F01_chain
public import Grammatik.Gen.Zeugen.M.F02_foot
public import Grammatik.Gen.Zeugen.M.F03_reg
public import Grammatik.Gen.Zeugen.M.F04_nolock
public import Grammatik.Gen.Zeugen.M.F06_pool
public import Grammatik.Gen.Zeugen.M.F07_race
public import Grammatik.Gen.Zeugen.M.F08_answer
public import Grammatik.Gen.Zeugen.M.F09_mask
public import Grammatik.Gen.Zeugen.M.M16_13
public import Grammatik.Gen.Zeugen.M.M169_350
public import Grammatik.Gen.Zeugen.M.M103_803
public import Grammatik.Gen.Zeugen.M.M103_131

@[expose] public section

set_option maxRecDepth 4096

namespace Gabbro.Grammatik.Gen.Zeugen.Recovery

open Gabbro.Grammatik Gabbro.Grammatik.Gen

def records : List (Einsatz × List Zelle) := [
  (F00_call.e, F00_call.zellen),
  (F01_chain.e, F01_chain.zellen),
  (F02_foot.e, F02_foot.zellen),
  (F03_reg.e, F03_reg.zellen),
  (Gap.F03_reg.e, Gap.F03_reg.zellen),
  (F04_nolock.e, F04_nolock.zellen),
  (F06_pool.e, F06_pool.zellen),
  (F07_race.e, F07_race.zellen),
  (F08_answer.e, F08_answer.zellen),
  (F09_mask.e, F09_mask.zellen),
  (M16_13.e, M16_13.zellen),
  (M169_350.e, M169_350.zellen),
  (M103_803.e, M103_803.zellen),
  (M103_131.e, M103_131.zellen),
  (M49_50.e, M49_50.zellen),
  (Gap.M99_824.e, Gap.M99_824.e.zellen.eraseDups),
  (Gap.M99_825.e, Gap.M99_825.e.zellen.eraseDups)]

def fixtures : List Einsatz := records.map Prod.fst

def cells : List Zelle := (records.flatMap Prod.snd).eraseDups

private theorem record_checked : ∀ p ∈ records, p.1.gueltig = true ∧
    ∀ x, p.1.Hat x ↔ x ∈ p.2 := by
  intro p member
  simp only [records, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨F00_call.e_gueltig, fun x => ?_⟩
    change x ∈ F00_call.e.zellen ↔ x ∈ F00_call.zellen
    rw [← F00_call.zellen_exact, List.mem_eraseDups]
  · refine ⟨F01_chain.e_gueltig, fun x => ?_⟩
    change x ∈ F01_chain.e.zellen ↔ x ∈ F01_chain.zellen
    rw [← F01_chain.zellen_exact, List.mem_eraseDups]
  · refine ⟨F02_foot.e_gueltig, fun x => ?_⟩
    change x ∈ F02_foot.e.zellen ↔ x ∈ F02_foot.zellen
    rw [← F02_foot.zellen_exact, List.mem_eraseDups]
  · refine ⟨F03_reg.e_gueltig, fun x => ?_⟩
    change x ∈ F03_reg.e.zellen ↔ x ∈ F03_reg.zellen
    rw [← F03_reg.zellen_exact, List.mem_eraseDups]
  · refine ⟨Gap.F03_reg.e_gueltig, fun x => ?_⟩
    change x ∈ Gap.F03_reg.e.zellen ↔ x ∈ Gap.F03_reg.zellen
    rw [← Gap.F03_reg.zellen_exact, List.mem_eraseDups]
  · refine ⟨F04_nolock.e_gueltig, fun x => ?_⟩
    change x ∈ F04_nolock.e.zellen ↔ x ∈ F04_nolock.zellen
    rw [← F04_nolock.zellen_exact, List.mem_eraseDups]
  · refine ⟨F06_pool.e_gueltig, fun x => ?_⟩
    change x ∈ F06_pool.e.zellen ↔ x ∈ F06_pool.zellen
    rw [← F06_pool.zellen_exact, List.mem_eraseDups]
  · refine ⟨F07_race.e_gueltig, fun x => ?_⟩
    change x ∈ F07_race.e.zellen ↔ x ∈ F07_race.zellen
    rw [← F07_race.zellen_exact, List.mem_eraseDups]
  · refine ⟨F08_answer.e_gueltig, fun x => ?_⟩
    change x ∈ F08_answer.e.zellen ↔ x ∈ F08_answer.zellen
    rw [← F08_answer.zellen_exact, List.mem_eraseDups]
  · refine ⟨F09_mask.e_gueltig, fun x => ?_⟩
    change x ∈ F09_mask.e.zellen ↔ x ∈ F09_mask.zellen
    rw [← F09_mask.zellen_exact, List.mem_eraseDups]
  · refine ⟨M16_13.e_gueltig, fun x => ?_⟩
    change x ∈ M16_13.e.zellen ↔ x ∈ M16_13.zellen
    rw [← M16_13.zellen_exact, List.mem_eraseDups]
  · refine ⟨M169_350.e_gueltig, fun x => ?_⟩
    change x ∈ M169_350.e.zellen ↔ x ∈ M169_350.zellen
    rw [← M169_350.zellen_exact, List.mem_eraseDups]
  · refine ⟨M103_803.e_gueltig, fun x => ?_⟩
    change x ∈ M103_803.e.zellen ↔ x ∈ M103_803.zellen
    rw [← M103_803.zellen_exact, List.mem_eraseDups]
  · refine ⟨M103_131.e_gueltig, fun x => ?_⟩
    change x ∈ M103_131.e.zellen ↔ x ∈ M103_131.zellen
    rw [← M103_131.zellen_exact, List.mem_eraseDups]
  · refine ⟨GateAudit.m49_50_checked, fun x => ?_⟩
    change x ∈ M49_50.e.zellen ↔ x ∈ M49_50.zellen
    rw [← M49_50.zellen_exact, List.mem_eraseDups]

  · refine ⟨GateAudit.m99_824_checked, fun x => ?_⟩
    change x ∈ Gap.M99_824.e.zellen ↔ x ∈ Gap.M99_824.e.zellen.eraseDups
    simp only [List.mem_eraseDups]
  · refine ⟨GateAudit.m99_825_checked, fun x => ?_⟩
    change x ∈ Gap.M99_825.e.zellen ↔ x ∈ Gap.M99_825.e.zellen.eraseDups
    simp only [List.mem_eraseDups]

theorem checked : ∀ e ∈ fixtures, e.gueltig = true := by
  intro e member
  change e ∈ records.map Prod.fst at member
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 member
  exact (record_checked p hp).1

/-- Both directions use the exact cell records checked in each fixture. -/
theorem cells_iff (x : Zelle) : (∃ e ∈ fixtures, e.Hat x) ↔ x ∈ cells := by
  constructor
  · rintro ⟨e, member, present⟩
    change e ∈ records.map Prod.fst at member
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 member
    change x ∈ (records.flatMap Prod.snd).eraseDups
    exact List.mem_eraseDups.2 (List.mem_flatMap.2
      ⟨p, hp, ((record_checked p hp).2 x).mp present⟩)
  · intro present
    change x ∈ (records.flatMap Prod.snd).eraseDups at present
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 (List.mem_eraseDups.1 present)
    exact ⟨p.1, List.mem_map.2 ⟨p, hp, rfl⟩, ((record_checked p hp).2 x).mpr hx⟩

/-- The original Boolean-read and reset baselines are retained. -/
def baseline : List Einsatz := [ScalarRead.e, Reset.Good.e]

def baselineCells : List Zelle := [
  ⟨0, 0, true, [true, false, false]⟩,
  ⟨1, 0, true, [true, false, true]⟩,
  ⟨2, 0, true, [false, true, false, false]⟩,
  ⟨2, 2, false, [true, true, false]⟩,
  ⟨2, 3, false, [false, true, true]⟩,
  ⟨5, 0, true, [false, false]⟩,
  ⟨6, 0, true, [false, false, false]⟩,
  ⟨6, 1, true, [false, true, false, false]⟩,
  ⟨7, 0, true, [false, true]⟩,
  ⟨7, 1, false, [true, false, true]⟩,
  ⟨10, 0, true, [true]⟩,
  ⟨7, 1, false, [true, false, false]⟩]

theorem baseline_exact : (baseline.flatMap Einsatz.zellen).eraseDups = baselineCells := by decide

private theorem baseline_cells_iff (x : Zelle) :
    (∃ e ∈ baseline, e.Hat x) ↔ x ∈ baselineCells := by
  constructor
  · rintro ⟨e, member, present⟩
    rw [← baseline_exact]
    exact List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨e, member, present⟩)
  · intro present
    rw [← baseline_exact] at present
    exact List.mem_flatMap.1 (List.mem_eraseDups.1 present)

/-- Baseline membership, acceptance and a real reset cell hold jointly. -/
theorem baseline_zeuge : Reset.Good.e ∈ baseline ∧ Reset.Good.e.gueltig = true ∧
    Reset.Good.e.Hat ⟨10, 0, true, [true]⟩ ∧ ⟨10, 0, true, [true]⟩ ∈ baselineCells := by
  have member : Reset.Good.e ∈ baseline := by simp [baseline]
  exact ⟨member, Reset.Good.e_gueltig, Reset.Good.e_hat,
    (baseline_cells_iff _).mp ⟨_, member, Reset.Good.e_hat⟩⟩

/-- The full accepted M retains both baseline programs. -/
def allFixtures : List Einsatz := fixtures ++ baseline

def allCells : List Zelle := (cells ++ baselineCells).eraseDups

theorem all_checked : ∀ e ∈ allFixtures, e.gueltig = true := by
  intro e member
  simp only [allFixtures, baseline, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with recovered | rfl | rfl
  · exact checked e recovered
  · exact ScalarRead.e_gueltig
  · exact Reset.Good.e_gueltig

theorem all_cells_iff (x : Zelle) : (∃ e ∈ allFixtures, e.Hat x) ↔ x ∈ allCells := by
  change (∃ e ∈ fixtures ++ baseline, e.Hat x) ↔ x ∈ (cells ++ baselineCells).eraseDups
  constructor
  · rintro ⟨e, member, present⟩
    apply List.mem_eraseDups.2
    apply List.mem_append.2
    rcases List.mem_append.1 member with recovered | old
    · exact Or.inl ((cells_iff x).mp ⟨e, recovered, present⟩)
    · exact Or.inr ((baseline_cells_iff x).mp ⟨e, old, present⟩)
  · intro present
    rcases List.mem_append.1 (List.mem_eraseDups.1 present) with recovered | old
    · obtain ⟨e, member, present⟩ := (cells_iff x).mpr recovered
      exact ⟨e, List.mem_append_left _ member, present⟩
    · obtain ⟨e, member, present⟩ := (baseline_cells_iff x).mpr old
      exact ⟨e, List.mem_append_right _ member, present⟩

def requested : List Zelle := (F00_call.requested ++ F01_chain.requested ++ F02_foot.requested ++ F03_reg.requested ++ F04_nolock.requested ++ F06_pool.requested ++ F07_race.requested ++ F08_answer.requested ++ F09_mask.requested).eraseDups

def provisional : List Zelle := [⟨7, 0, true, [true, false]⟩, ⟨7, 1, false, [false, true, true]⟩]

def firm : List Zelle := requested.filter (fun x => !provisional.contains x)

def newlyRecovered : List Zelle := allCells.filter (fun x => !baselineCells.contains x)

def missing : List Zelle := firm.filter (fun x => decide (x ∉ allCells))

theorem counts : baselineCells.length = 12 ∧ cells.length = 85 ∧
    allCells.length = 85 ∧ newlyRecovered.length = 73 ∧
    firm.length = 69 ∧ (firm.filter allCells.contains).length = 67 ∧
    (provisional.filter allCells.contains).length = 2 ∧ missing.length = 2 := by decide +kernel

/-- Wave E's accepted atomic reader closes design cells 24 and 51. -/
theorem atomic_reader_recovered_zeuge :
    M49_50.e ∈ allFixtures ∧ M49_50.e.gueltig = true ∧
    M49_50.e.Hat ⟨2, 0, true, [false, false, false, true]⟩ ∧
    M49_50.e.Hat ⟨2, 3, false, [true, true, true]⟩ :=
  ⟨List.mem_append_left _ (List.mem_map.2
    ⟨(M49_50.e, M49_50.zellen), by simp [records], rfl⟩),
    GateAudit.m49_50_checked, M49_50.e_hat _ (by decide), M49_50.e_hat _ (by decide)⟩

/-- Atomic/register totality restores three more cells; two firm cells remain. -/
theorem missing_exact : missing = [
    ⟨2, 3, false, [false, true, false]⟩,
    ⟨2, 3, false, [true, true, false]⟩] := by decide

/-- No accepted M fixture contains a listed missing cell. -/
theorem missing_not_covered : ∀ x ∈ missing, ¬ (∃ e ∈ allFixtures, e.Hat x) := by
  intro x member covered
  have absent : x ∉ allCells := of_decide_eq_true (List.mem_filter.1 member).2
  exact absent ((all_cells_iff x).mp covered)

theorem coverage_zeuge : F00_call.e ∈ fixtures ∧ F00_call.e ∈ allFixtures ∧
    F00_call.e.gueltig = true ∧ ⟨0, 0, true, [true, false, false]⟩ ∈ cells ∧
    ⟨0, 0, true, [true, false, false]⟩ ∈ allCells ∧
    F00_call.e.Hat ⟨0, 0, true, [true, false, false]⟩ := by
  have recordMember : F00_call.e ∈ fixtures :=
    List.mem_map.2 ⟨(F00_call.e, F00_call.zellen), List.mem_cons_self, rfl⟩
  have member : F00_call.e ∈ allFixtures := List.mem_append_left _ recordMember
  have present := F00_call.e_hat ⟨0, 0, true, [true, false, false]⟩ (by decide)
  exact ⟨recordMember, member, F00_call.e_gueltig,
    (cells_iff _).mp ⟨_, recordMember, present⟩,
    (all_cells_iff _).mp ⟨_, member, present⟩, present⟩

theorem missing_zeuge : ⟨2, 3, false, [false, true, false]⟩ ∈ missing ∧ ¬ (∃ e ∈ allFixtures, e.Hat ⟨2, 3, false, [false, true, false]⟩) :=
  ⟨by decide +kernel, missing_not_covered _ (by decide +kernel)⟩

#print axioms all_checked
#print axioms all_cells_iff

end Gabbro.Grammatik.Gen.Zeugen.Recovery
