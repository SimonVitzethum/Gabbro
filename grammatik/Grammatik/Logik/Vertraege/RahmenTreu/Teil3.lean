module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

/-! ## 7. THE CALL, at every disciplined world -/

/-- **THE FRAME OF A CALL, AT EVERY DISCIPLINED WORLD.** `rufAt_gut` (Satz.lean)
    proves the same and more at worlds meeting `HeldB`; this proves the frame
    and the held locks wherever the callee-entry discipline holds, by the same
    induction on the depth. The two premises are the hardware's (H1) and the
    static scope discipline (`ScopesOkProg`: every scoped return spares the
    residual and respects the floor). A normal return collapses its release
    (`TreuRet.toTreu_entry`); a propagated reason carries it. -/
theorem rufAt_treu (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O)
    (hS : ScopesOkProg P) :
    ∀ fuel, TreuR (rufAt P O passes fuel) := by
  intro fuel
  induction fuel with
  | zero => intro f σ ρ _ σ' h; simp only [RufAusgang.welt, rufAt, reduceCtorEq] at h
  | succ n ih =>
      intro f σ ρ hh σ' h
      simp only [rufAt] at h ⊢
      have g0 : Treu (D.schreibt f) (D.gschreibt f) σ
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) := treu_lese _ _ _
      have hb := end_treu O passes (rufAt P O passes n) ih hO (D.signatur f).boden
        (bodenUnter_refl _) (P.rumpf f)
        (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ (by exact hS f)
        (g0.heldB hh)
      revert h; split <;> intro h
      · simp only [RufAusgang.welt, reduceCtorEq] at h
      · revert h; split <;> intro h
        · rename_i σ2 v hs
          have hbb := hb σ2 (by rw [hs]; rfl); rw [hs] at hbb
          specialize hbb (residHeld_anfang (D.signatur f))
          have g2 : Treu (D.schreibt f) (D.gschreibt f) _ σ2 :=
            hbb.toTreu_entry (g0.heldB hh)
          have g3 : Treu (D.schreibt f) (D.gschreibt f) σ2
              (σ2.lese (vertragVon D f).ende (P.ensures f).orte) :=
            treu_lese σ2 (vertragVon D f).ende (P.ensures f).orte
          revert h; split <;> intro h
          · simp only [RufAusgang.welt, reduceCtorEq] at h
          · have g4 : Treu (D.schreibt f) (D.gschreibt f) _
                ((D.invs.filter (schuldet f)).foldl
                  (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                  (σ2.lese (vertragVon D f).ende (P.ensures f).orte)) :=
              treu_foldl_lese P (D.invs.filter (schuldet f)) _
            revert h; split <;> intro h
            · simp only [RufAusgang.welt, reduceCtorEq] at h
            · simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
              exact ((g0.trans g2).trans g3).trans g4
        · rename_i σ2 r hs
          simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
          have hbb := hb _ (by rw [hs]; rfl); rw [hs] at hbb
          specialize hbb (residHeld_anfang (D.signatur f))
          exact g0.transRet hbb
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · simp only [RufAusgang.welt, reduceCtorEq] at h
        · simp only [RufAusgang.welt, reduceCtorEq] at h

#print axioms Gabbro.Grammatik.rufAt_treu

end Gabbro.Grammatik
