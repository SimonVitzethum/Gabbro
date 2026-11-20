/- The remaining indirect-call refusal is outside accepted M and wrong-program N. -/
module

public import Grammatik.Gen.Zeugen.Gap.Audit
public import Grammatik.Gen.Abdeckung.Mitglieder
public import Grammatik.Gen.Fein.Zellen

@[expose] public section

namespace Gabbro.Grammatik.Gen.Zeugen.Gap

open Gabbro.Grammatik Gabbro.Grammatik.Gen
open Invarianten.Frag

inductive GapGrund where
  | rufInd
  deriving DecidableEq, Repr

def CallIndGapInput (g : Einsatz) : Prop :=
  letI := g.aufz
  g.fs.any (fun f =>
    !(mE ⟨fun _ => true, fun _ => false, fun _ => true⟩ (g.P.rumpf f))) = true

def GapBelegt (g : Einsatz) : GapGrund → Prop
  | .rufInd => CallIndGapInput g

/-- Typed atomic/register readers have checked totality; indirect calls remain outside. -/
def fragmentGaps : List Einsatz := [M47_549.e]

theorem m47_549_input : CallIndGapInput M47_549.e := by unfold CallIndGapInput; decide

theorem m47_549_cause_link : CallIndGapInput M47_549.e →
    GateAudit.contractCause M47_549.e = some (.unsupported
      "contract indirect call needs checked interface refinement") := fun _ => GateAudit.m47_549_cause

theorem checked_gap : ∀ g ∈ fragmentGaps, g.gueltig = false := by
  intro g member
  have same : g = M47_549.e := List.mem_singleton.mp member
  subst g
  exact GateAudit.m47_549_refused

theorem gap_structural : ∀ g ∈ fragmentGaps,
    Adaequanz.akzeptiert Einsatz.Hat gutTafel g := by
  intro g member
  have same : g = M47_549.e := List.mem_singleton.mp member
  subst g
  exact M47_549.e_strukturell

theorem gap_grund : ∀ g ∈ fragmentGaps, ∃ grund : GapGrund, GapBelegt g grund := by
  intro g member
  have same : g = M47_549.e := List.mem_singleton.mp member
  subst g
  exact ⟨.rufInd, m47_549_input⟩

theorem gap_annex : GapAnnex fragmentGaps := ⟨checked_gap⟩

#print axioms checked_gap
#print axioms gap_structural
#print axioms gap_grund

end Gabbro.Grammatik.Gen.Zeugen.Gap
