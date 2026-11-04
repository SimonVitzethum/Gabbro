module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.Core.ZielOrtStart
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfaden

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Canonical answer delivery either completes the root or restores exactly
    the caller's resource context. No equality of runtime holdings is assumed. -/
theorem rufAntwortG_rangRahmen {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (ha : rufAntwortG z vor σ a = some z') :
    (z'.stapel = z.stapel ∧ z'.kopf.f = z.kopf.f ∧
      z'.kopf.rest.2.2.1 = (vertragVon D z.kopf.f).ende) ∨
    ∃ caller rst, z.stapel = caller :: rst ∧ z'.stapel = rst ∧
      z'.kopf.f = caller.f ∧ z'.kopf.rest.2.2.1 = caller.rest.2.2.1 := by
  cases hs : z.stapel with
  | nil =>
    simp only [rufAntwortG, hs, Option.some.injEq] at ha
    subst z'
    exact Or.inl ⟨by simp only [hs], rfl, rfl⟩
  | cons caller rst =>
    cases hr : antwortRestG z.kopf.f a caller.rest with
    | none => simp [rufAntwortG, hs, hr] at ha
    | some rest =>
      simp [rufAntwortG, hs, hr] at ha
      subst z'
      exact Or.inr ⟨caller, rst, by simp only [hs], rfl, rfl,
        antwortRestG_ressourcen _ _ _ _ hr⟩

/-! ## 1. Every rule, classified by what it does to holdings and held locks -/

set_option hygiene false in
/-- A head-local step that keeps the held locks and the held holdings. -/
macro "rangA1" : tactic => `(tactic| (
  refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
  · first
      | (simp only [rufUpdateG_self]; done)
      | (simp only [rufUpdateG_self]; subst_vars; simp only [lese_offen]; rfl)
  · intro K hK
    dsimp only; rw [rufUpdateG_self]
    rw [‹(M.faeden f).kopf.rest = _›] at hK
    exact hK))

set_option hygiene false in
/-- A head-local step that keeps the held locks; the held holdings pass a
    block or statement. -/
macro "rangA1h" t:term : tactic => `(tactic| (
  refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
  · first
      | (simp only [rufUpdateG_self]; done)
      | (simp only [rufUpdateG_self]; subst_vars; simp only [lese_offen]; rfl)
  · intro K hK
    dsimp only; rw [rufUpdateG_self]
    rw [‹(M.faeden f).kopf.rest = _›] at hK
    exact $t K hK))

set_option hygiene false in
/-- A foreign call keeps the held locks while its signature updates holdings. -/
macro "rangAxiomOpt" ho:term "," hs:term "," hh:term : tactic => `(tactic| (
  refine Or.inl ⟨by simp only [rufUpdateG_self], by simp only [rufUpdateG_self], Or.inl ⟨?_, ?_⟩⟩
  · simp only [rufUpdateG_self]
    have hoE := $ho
    have hsE := $hs
    rw [hoE, hsE]
    exact lese_offen _ _ _
  · intro K hK
    dsimp only; rw [rufUpdateG_self]
    have hhE := $hh
    rw [hhE] at hK
    exact (held_nachSig_iff _ _ K).mpr hK))

set_option hygiene false in
/-- A push. -/
macro "rangB" g:term "," c:term : tactic => `(tactic| (
  refine Or.inr (Or.inl ⟨$g, $c, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩)
  · dsimp only; rw [rufUpdateG_self]
  · dsimp only; rw [rufUpdateG_self]
  · dsimp only; rw [rufUpdateG_self]
  · intro K hK
    rw [‹(M.faeden f).kopf.rest = _›] at hK
    exact (held_nachSig_iff _ _ K).mpr hK
  · simp only [rufUpdateG_self]
    rw [hs0]
    exact lese_offen _ _ _
  · rw [‹(M.faeden f).kopf.rest = _›]
    first
      | exact ‹RufPasst _ _ _ _›
      | (subst_vars; exact ‹RufPasst _ _ _ _›)))

end Gabbro.Grammatik
