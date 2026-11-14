module
public import Bruecke.Kette.Verknuepfung
public import Bruecke.Anweisung.Match.ReasonKopf
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {C : Fin u.fns.length → Prop}
variable {c : Fin u.fns.length} {O : Orakel (declOf u)} {passes : Nat}
  {R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f}

/-- Every case is related, including cases that the current input does not select. -/
inductive ReasonRelated {loopMode : Bool} (u : UProg) (C : Fin u.fns.length → Prop) (c : Fin u.fns.length)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    {Γ : Ctx} (fn : UFn) (ids : List String) (Λ : List (Res (declOf u))) :
    (n : Nat) → Nat → GrundArms (declOf u) (verOf u c) loopMode Γ Λ Λ n →
      List (String × List Gabbro.Body.Stmt) → Prop where
  | nil (offset : Nat) : ReasonRelated u C c O passes R fn ids Λ 0 offset .nil []
  | cons {n offset : Nat} {b : Block (declOf u) (verOf u c) loopMode Γ Λ Λ}
      {rest : GrundArms (declOf u) (verOf u c) loopMode Γ Λ Λ n} {bb : List Gabbro.Body.Stmt}
      {bs : List (String × List Gabbro.Body.Stmt)} :
      (∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ids 0 ρ s.local' →
        BlockZiel_G u C c O passes R fn ids b σ ρ s bb) →
      ReasonRelated u C c O passes R fn ids Λ n (offset + 1) rest bs →
      ReasonRelated u C c O passes R fn ids Λ (n + 1) offset (.cons b rest) ((caseLabel offset, bb) :: bs)

/-- Selection uses the ordinal position, never an accidentally equal source case name. -/
theorem ReasonRelated.select {loopMode : Bool} {Γ : Ctx} {fn : UFn} {ids : List String} {Λ : List (Res (declOf u))}
    {count offset : Nat} {ga : GrundArms (declOf u) (verOf u c) loopMode Γ Λ Λ count}
    {bs : List (String × List Gabbro.Body.Stmt)}
    (h : ReasonRelated u C c O passes R fn ids Λ count offset ga bs) (i : Fin count) :
    ∃ (b : Block (declOf u) (verOf u c) loopMode Γ Λ Λ) (bb : List Gabbro.Body.Stmt),
      (∀ σ ρ, execGrund O passes R ga i σ ρ = execBlock O passes R b σ ρ) ∧
      (∀ ρB s, Gabbro.Body.pickArm ρB bs (caseLabel (offset + i.val)) s = Gabbro.Body.exec ρB bb s) ∧
      (∀ σ ρ s, WGRel u σ s.world → PositionalLRel fn ids 0 ρ s.local' →
        BlockZiel_G u C c O passes R fn ids b σ ρ s bb) := by
  induction h with
  | nil => exact (Nat.not_lt_zero _ i.isLt).elim
  | @cons n offset b rest bb bs hBody hRest ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero =>
      refine ⟨b, bb, fun σ ρ => rfl, fun ρB s => ?_, hBody⟩
      simp only [Nat.add_zero, Gabbro.Body.pickArm, ↓reduceIte]
    | succ i =>
      obtain ⟨b', bb', hG, hB, hRelated⟩ := ih ⟨i, Nat.lt_of_succ_lt_succ hi⟩
      refine ⟨b', bb', fun σ ρ => hG σ ρ, fun ρB s => ?_, hRelated⟩
      have hne : caseLabel offset ≠ caseLabel (offset + (i + 1)) := by
        intro he
        have := caseLabel_injective he
        omega
      simp only [Gabbro.Body.pickArm, hne, ↓reduceIte]
      have heq : offset + (i + 1) = (offset + 1) + i := by omega
      rw [heq]
      exact hB ρB s

end Gabbro.Bruecke
