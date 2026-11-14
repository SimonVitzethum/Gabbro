/- Fragment-gap refusals are not counterexamples and never belong to N. -/
module

public import Grammatik.Gen.Zeugen.Gap.Audit

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.Gap

open Gabbro.Grammatik Gabbro.Grammatik.Gen
open Invarianten.Frag

/-- Inputs identifying the checker fragment that refuses a structural fixture. -/
inductive GapGrund where
  | atomar (f : Nat)
  | rufInd
  | sperrQuelle
  deriving DecidableEq, Repr

/-- The exact body-read test used before contract VC generation. -/
def AtomicGapInput (g : Einsatz) (index : Nat) : Prop :=
  letI := g.aufz
  ∃ f ∈ g.fs, (g.fs.idxOf f = index) ∧ Invarianten.Pruefer.atomicFreeB g.P f = false

/-- Detect an indirect call in any body, using the canonical syntax fold. -/
def CallIndGapInput (g : Einsatz) : Prop :=
  letI := g.aufz
  g.fs.any (fun f =>
    !(mE ⟨fun _ => true, fun _ => false, fun _ => true⟩ (g.P.rumpf f))) = true

/-- An actual lock-taking body, with the same absent sources as contractCause. -/
def LockGapInput (g : Einsatz) : Prop :=
  letI := g.aufz
  g.fs.any (fun f => g.ls.any (fun lock => nimmtB g.P f lock &&
    ((fun _ => none : Invarianten.Pruefer.LockSources g.S) lock).isNone)) = true

def GapBelegt (g : Einsatz) : GapGrund → Prop
  | .atomar f => AtomicGapInput g f
  | .rufInd => CallIndGapInput g
  | .sperrQuelle => LockGapInput g

/-- Stable old-M order. Neither accepted-M nor wrong-program-N membership. -/
def fragmentGaps : List Einsatz :=
  [M99_824.e, M99_825.e, M49_50.e, M47_549.e,
   M16_13.e, M169_350.e, M103_803.e, M103_131.e]

theorem m99_824_input : AtomicGapInput M99_824.e 0 := by decide

/-- The input fact and the exact diagnostic agree on this closed fixture. -/
theorem m99_824_cause_link : AtomicGapInput M99_824.e 0 →
    GateAudit.contractCause M99_824.e = some (.unsupported "contract body reads atomic memory outside the checked VC fragment") :=
  fun _ => GateAudit.m99_824_cause

theorem m99_824_cause_link_zeuge : AtomicGapInput M99_824.e 0 ∧
    GateAudit.contractCause M99_824.e = some (.unsupported "contract body reads atomic memory outside the checked VC fragment") :=
  ⟨m99_824_input, m99_824_cause_link m99_824_input⟩

theorem m99_825_input : AtomicGapInput M99_825.e 0 := by decide

/-- The input fact and the exact diagnostic agree on this closed fixture. -/
theorem m99_825_cause_link : AtomicGapInput M99_825.e 0 →
    GateAudit.contractCause M99_825.e = some (.unsupported "contract body reads atomic memory outside the checked VC fragment") :=
  fun _ => GateAudit.m99_825_cause

theorem m99_825_cause_link_zeuge : AtomicGapInput M99_825.e 0 ∧
    GateAudit.contractCause M99_825.e = some (.unsupported "contract body reads atomic memory outside the checked VC fragment") :=
  ⟨m99_825_input, m99_825_cause_link m99_825_input⟩

theorem m49_50_input : AtomicGapInput M49_50.e 0 := by decide

/-- The input fact and the exact diagnostic agree on this closed fixture. -/
theorem m49_50_cause_link : AtomicGapInput M49_50.e 0 →
    GateAudit.contractCause M49_50.e = some (.unsupported "contract body reads atomic memory outside the checked VC fragment") :=
  fun _ => GateAudit.m49_50_cause

theorem m49_50_cause_link_zeuge : AtomicGapInput M49_50.e 0 ∧
    GateAudit.contractCause M49_50.e = some (.unsupported "contract body reads atomic memory outside the checked VC fragment") :=
  ⟨m49_50_input, m49_50_cause_link m49_50_input⟩

theorem m47_549_input : CallIndGapInput M47_549.e := by decide

/-- The input fact and the exact diagnostic agree on this closed fixture. -/
theorem m47_549_cause_link : CallIndGapInput M47_549.e →
    GateAudit.contractCause M47_549.e = some (.unsupported "contract statement is outside the checked scalar/control fragment") :=
  fun _ => GateAudit.m47_549_cause

theorem m47_549_cause_link_zeuge : CallIndGapInput M47_549.e ∧
    GateAudit.contractCause M47_549.e = some (.unsupported "contract statement is outside the checked scalar/control fragment") :=
  ⟨m47_549_input, m47_549_cause_link m47_549_input⟩

theorem m16_13_input : LockGapInput M16_13.e := by decide

/-- The input fact and the exact diagnostic agree on this closed fixture. -/
theorem m16_13_cause_link : LockGapInput M16_13.e →
    GateAudit.contractCause M16_13.e = some (.unsupported "semantic lock invariant has no reified source formula; user duty") :=
  fun _ => GateAudit.m16_13_cause

theorem m16_13_cause_link_zeuge : LockGapInput M16_13.e ∧
    GateAudit.contractCause M16_13.e = some (.unsupported "semantic lock invariant has no reified source formula; user duty") :=
  ⟨m16_13_input, m16_13_cause_link m16_13_input⟩

theorem m169_350_input : LockGapInput M169_350.e := by decide

/-- The input fact and the exact diagnostic agree on this closed fixture. -/
theorem m169_350_cause_link : LockGapInput M169_350.e →
    GateAudit.contractCause M169_350.e = some (.unsupported "semantic lock invariant has no reified source formula; user duty") :=
  fun _ => GateAudit.m169_350_cause

theorem m169_350_cause_link_zeuge : LockGapInput M169_350.e ∧
    GateAudit.contractCause M169_350.e = some (.unsupported "semantic lock invariant has no reified source formula; user duty") :=
  ⟨m169_350_input, m169_350_cause_link m169_350_input⟩

theorem m103_803_input : LockGapInput M103_803.e := by decide

/-- The input fact and the exact diagnostic agree on this closed fixture. -/
theorem m103_803_cause_link : LockGapInput M103_803.e →
    GateAudit.contractCause M103_803.e = some (.unsupported "semantic lock invariant has no reified source formula; user duty") :=
  fun _ => GateAudit.m103_803_cause

theorem m103_803_cause_link_zeuge : LockGapInput M103_803.e ∧
    GateAudit.contractCause M103_803.e = some (.unsupported "semantic lock invariant has no reified source formula; user duty") :=
  ⟨m103_803_input, m103_803_cause_link m103_803_input⟩

theorem m103_131_input : LockGapInput M103_131.e := by decide

/-- The input fact and the exact diagnostic agree on this closed fixture. -/
theorem m103_131_cause_link : LockGapInput M103_131.e →
    GateAudit.contractCause M103_131.e = some (.unsupported "semantic lock invariant has no reified source formula; user duty") :=
  fun _ => GateAudit.m103_131_cause

theorem m103_131_cause_link_zeuge : LockGapInput M103_131.e ∧
    GateAudit.contractCause M103_131.e = some (.unsupported "semantic lock invariant has no reified source formula; user duty") :=
  ⟨m103_131_input, m103_131_cause_link m103_131_input⟩

theorem checked_gap : ∀ g ∈ fragmentGaps, g.gueltig = false := by
  intro g member
  simp only [fragmentGaps, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact GateAudit.m99_824_refused
  · exact GateAudit.m99_825_refused
  · exact GateAudit.m49_50_refused
  · exact GateAudit.m47_549_refused
  · exact GateAudit.m16_13_refused
  · exact GateAudit.m169_350_refused
  · exact GateAudit.m103_803_refused
  · exact GateAudit.m103_131_refused

theorem gap_grund : ∀ g ∈ fragmentGaps, ∃ grund : GapGrund, GapBelegt g grund := by
  intro g member
  simp only [fragmentGaps, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.atomar 0, m99_824_input⟩
  · exact ⟨.atomar 0, m99_825_input⟩
  · exact ⟨.atomar 0, m49_50_input⟩
  · exact ⟨.rufInd, m47_549_input⟩
  · exact ⟨.sperrQuelle, m16_13_input⟩
  · exact ⟨.sperrQuelle, m169_350_input⟩
  · exact ⟨.sperrQuelle, m103_803_input⟩
  · exact ⟨.sperrQuelle, m103_131_input⟩

theorem gap_grund_zeuge : M99_824.e ∈ fragmentGaps ∧
    GapBelegt M99_824.e (.atomar 0) ∧ M99_824.e.gueltig = false :=
  ⟨List.mem_cons_self, m99_824_input, GateAudit.m99_824_refused⟩

/-- The refusal annex is separate from the unchanged witness table. -/
theorem gap_annex : GapAnnex fragmentGaps := ⟨checked_gap⟩

#print axioms checked_gap
#print axioms gap_grund

end Gabbro.Grammatik.Gen.Zeugen.Gap
