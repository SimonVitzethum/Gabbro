module
public import Bruecke.Ausdruck.Records
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg}

/-- The Boolean reader has no ordering operators. -/
theorem boolOpOf_some {op : String} {o : Gabbro.Body.BinOp} (h : boolOpOf op = some o) :
    (op = "==" ∧ o = .eq) ∨ (op = "!=" ∧ o = .ne) := by
  unfold boolOpOf at h
  split at h <;> simp_all

theorem boolCmpExpr_some {fn : UFn} {op : String} {l r : USide} {e : Gabbro.Body.Expr}
    (h : boolCmpExpr u fn op l r = some e) :
    ∃ o le re, boolOpOf op = some o ∧ recordRead u fn l = some (some .bool, le) ∧
      recordRead u fn r = some (some .bool, re) ∧ e = .bin o le re := by
  unfold boolCmpExpr at h
  split at h
  · rename_i o le re ho hl hr
    cases h
    exact ⟨o, le, re, ho, hl, hr, rfl⟩
  · cases h

/-- Exact Boolean type information cannot arise from the bounded-count arithmetic path. -/
theorem recordRead_bool_ohneCount {fn : UFn} {sd : USide} {e : Gabbro.Body.Expr}
    (h : recordRead u fn sd = some (some .bool, e)) : usideHatZaehle sd = false := by
  cases sd
  case zaehle | zaehleBaum | zaehleFeld => cases h
  case add a b | sub a b | mul a b =>
    simp only [recordRead] at h
    cases hs : numericSideExprG u fn _ with
    | none => simp only [hs, Option.map_none, reduceCtorEq] at h
    | some e => simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq,
        reduceCtorEq, false_and] at h
  all_goals rfl

/-- Typed Boolean comparisons, including record projections, agree with the actual G
    equality lowering. No numeric encoding of truth values is introduced. -/
theorem lowEns_boolCmp_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {er : Option Ty} {op : String} {l r : USide} {g : Expr (declOf u) Γ Λ .bool}
    {e : Gabbro.Body.Expr}
    (h : lowEns u Γ Λ fn er (.cmp op l r) = .ok g)
    (hb : boolCmpExpr u fn op l r = some e) (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (w : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WGRel u σ w)
    (hL : LRel fn (if er.isSome then 1 else 0) ρ β) :
    Gabbro.Body.eval ⟨w, β⟩ e = some (.bool (wahr? (eval σ₀ g σ ρ))) := by
  obtain ⟨o, le, re, hop, hl, hr, rfl⟩ := boolCmpExpr_some hb
  simp only [lowEns, recordRead_bool_ohneCount hl, recordRead_bool_ohneCount hr,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, lowCmp] at h
  cases hleft : lowWertE u Γ Λ fn er l with
  | error err => simp [hleft, lowVglWert, zahlVon] at h
  | ok left =>
    obtain ⟨hvL, htL⟩ := lowWertE_recordRead_sim hleft hl hA hT σ₀ σ ρ w β hW hL
    have sameL := htL .bool rfl
    rcases left with ⟨tyL, termL⟩
    dsimp only at sameL
    subst tyL
    cases hright : lowWertE u Γ Λ fn er r with
    | error err => simp [hleft, hright, lowVglWert, zahlVon] at h
    | ok right =>
      obtain ⟨hvR, htR⟩ := lowWertE_recordRead_sim hright hr hA hT σ₀ σ ρ w β hW hL
      have sameR := htR .bool rfl
      rcases right with ⟨tyR, termR⟩
      dsimp only at sameR
      subst tyR
      simp only [hleft, hright, lowVglWert] at h
      cases hg : u.exportGate with
      | error err => simp [hg, bind, Except.bind] at h
      | ok gate =>
        rcases boolOpOf_some hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        all_goals
          simp only [hg, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          cases h
          simp only [Gabbro.Body.eval, hvL, hvR, valOf, Gabbro.Body.binop, Grammatik.eval, wahr?]
          generalize eval σ₀ termL σ ρ = a
          generalize eval σ₀ termR σ ρ = b
          cases a <;> cases b <;> rfl

end Gabbro.Bruecke
