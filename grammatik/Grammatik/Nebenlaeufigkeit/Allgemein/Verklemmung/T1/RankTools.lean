module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.Core.ZielOrtStart
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtEinfaden

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

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
