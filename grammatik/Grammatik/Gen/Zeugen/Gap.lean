/- Fragment refusals are outside accepted M and wrong-program N. -/
module

public import Grammatik.Gen.Zeugen.Gap.Audit
public import Grammatik.Gen.Zeugen.Gap.F03_reg
public import Grammatik.Gen.Abdeckung.Mitglieder
public import Grammatik.Gen.Fein.Zellen
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs
import all Init.Data.String.Decode
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.OrderInstances

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.Gap

open Gabbro.Grammatik Gabbro.Grammatik.Gen
open Invarianten.Frag

inductive GapGrund where
  | atomar (f : Nat)
  | rufInd
  | registerRead
  deriving DecidableEq, Repr

def AtomicGapInput (g : Einsatz) (index : Nat) : Prop :=
  letI := g.aufz
  ∃ f ∈ g.fs, g.fs.idxOf f = index ∧ Invarianten.Pruefer.atomicFreeB g.P f = false

def CallIndGapInput (g : Einsatz) : Prop :=
  letI := g.aufz
  g.fs.any (fun f =>
    !(mE ⟨fun _ => true, fun _ => false, fun _ => true⟩ (g.P.rumpf f))) = true

/-- The canonical fine cell identifies an end-block register-read constructor. -/
def RegisterGapInput (g : Einsatz) : Prop := g.HatF ⟨0, 6, 10, false, []⟩

def GapBelegt (g : Einsatz) : GapGrund → Prop
  | .atomar f => AtomicGapInput g f
  | .rufInd => CallIndGapInput g
  | .registerRead => RegisterGapInput g

/-- The atomic/indirect inputs remain refused; four lock fixtures have returned to M. -/
def fragmentGaps : List Einsatz :=
  [M99_824.e, M99_825.e, M49_50.e, M47_549.e, F03_reg.e]

theorem m99_824_input : AtomicGapInput M99_824.e 0 := by decide

theorem m99_824_cause_link : AtomicGapInput M99_824.e 0 →
    GateAudit.contractCause M99_824.e = some (.unsupported
      "contract body reads atomic memory outside the checked VC fragment") := fun _ => GateAudit.m99_824_cause

theorem m99_824_cause_link_zeuge : AtomicGapInput M99_824.e 0 ∧
    GateAudit.contractCause M99_824.e = some (.unsupported
      "contract body reads atomic memory outside the checked VC fragment") :=
  ⟨m99_824_input, m99_824_cause_link m99_824_input⟩

theorem m99_825_input : AtomicGapInput M99_825.e 0 := by decide

theorem m99_825_cause_link : AtomicGapInput M99_825.e 0 →
    GateAudit.contractCause M99_825.e = some (.unsupported
      "contract body reads atomic memory outside the checked VC fragment") := fun _ => GateAudit.m99_825_cause

theorem m99_825_cause_link_zeuge : AtomicGapInput M99_825.e 0 ∧
    GateAudit.contractCause M99_825.e = some (.unsupported
      "contract body reads atomic memory outside the checked VC fragment") :=
  ⟨m99_825_input, m99_825_cause_link m99_825_input⟩

theorem m49_50_input : AtomicGapInput M49_50.e 0 := by decide

theorem m49_50_cause_link : AtomicGapInput M49_50.e 0 →
    GateAudit.contractCause M49_50.e = some (.unsupported
      "contract body reads atomic memory outside the checked VC fragment") := fun _ => GateAudit.m49_50_cause

theorem m49_50_cause_link_zeuge : AtomicGapInput M49_50.e 0 ∧
    GateAudit.contractCause M49_50.e = some (.unsupported
      "contract body reads atomic memory outside the checked VC fragment") :=
  ⟨m49_50_input, m49_50_cause_link m49_50_input⟩

theorem m47_549_input : CallIndGapInput M47_549.e := by decide

theorem m47_549_cause_link : CallIndGapInput M47_549.e →
    GateAudit.contractCause M47_549.e = some (.unsupported
      "contract statement is outside the checked scalar/control fragment") := fun _ => GateAudit.m47_549_cause

theorem m47_549_cause_link_zeuge : CallIndGapInput M47_549.e ∧
    GateAudit.contractCause M47_549.e = some (.unsupported
      "contract statement is outside the checked scalar/control fragment") :=
  ⟨m47_549_input, m47_549_cause_link m47_549_input⟩

theorem f03_reg_input : RegisterGapInput F03_reg.e := by decide

theorem f03_reg_cause_link : RegisterGapInput F03_reg.e →
    GateAudit.contractCause F03_reg.e = some (.unsupported
      "contract end block is outside the checked control fragment") := fun _ => F03_reg.e_cause

theorem f03_reg_cause_link_zeuge : RegisterGapInput F03_reg.e ∧
    GateAudit.contractCause F03_reg.e = some (.unsupported
      "contract end block is outside the checked control fragment") :=
  ⟨f03_reg_input, f03_reg_cause_link f03_reg_input⟩

theorem checked_gap : ∀ g ∈ fragmentGaps, g.gueltig = false := by
  intro g member
  simp only [fragmentGaps, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact GateAudit.m99_824_refused
  · exact GateAudit.m99_825_refused
  · exact GateAudit.m49_50_refused
  · exact GateAudit.m47_549_refused
  · exact F03_reg.e_refused

/-- The input cells are structurally admitted, unlike the wrong programs of N. -/
theorem gap_structural : ∀ g ∈ fragmentGaps,
    Adaequanz.akzeptiert Einsatz.Hat gutTafel g := by
  intro g member
  simp only [fragmentGaps, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact M99_824.e_strukturell
  · exact M99_825.e_strukturell
  · exact M49_50.e_strukturell
  · exact M47_549.e_strukturell
  · exact F03_reg.e_strukturell

theorem gap_grund : ∀ g ∈ fragmentGaps, ∃ grund : GapGrund, GapBelegt g grund := by
  intro g member
  simp only [fragmentGaps, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact ⟨.atomar 0, m99_824_input⟩
  · exact ⟨.atomar 0, m99_825_input⟩
  · exact ⟨.atomar 0, m49_50_input⟩
  · exact ⟨.rufInd, m47_549_input⟩
  · exact ⟨.registerRead, f03_reg_input⟩

theorem gap_grund_zeuge : M99_824.e ∈ fragmentGaps ∧
    GapBelegt M99_824.e (.atomar 0) ∧
    Adaequanz.akzeptiert Einsatz.Hat gutTafel M99_824.e ∧ M99_824.e.gueltig = false :=
  ⟨List.mem_cons_self, m99_824_input, M99_824.e_strukturell, GateAudit.m99_824_refused⟩

theorem gap_annex : GapAnnex fragmentGaps := ⟨checked_gap⟩

#print axioms checked_gap
#print axioms gap_structural
#print axioms gap_grund

end Gabbro.Grammatik.Gen.Zeugen.Gap
