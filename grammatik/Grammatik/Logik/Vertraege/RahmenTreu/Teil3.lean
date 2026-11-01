module

public import Grammatik.Kern.Syntax.Satz
public import Grammatik.Logik.Vertraege.RahmenTreu.Teil2

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

/-! ## 7. THE CALL, at every world -/

/-- **THE FRAME OF A CALL, AT EVERY WORLD.** `rufAt_gut` (Satz.lean) proves
    the same and more at worlds meeting `HeldB`; this proves the frame and
    the held locks at ALL of them, by the same induction on the depth. The
    only premise is the hardware's (H1). -/
theorem rufAt_treu (P : Programm D) (O : Orakel D) (passes : Nat) (hO : TreuO O) :
    ∀ fuel, TreuR (rufAt P O passes fuel) := by
  intro fuel
  induction fuel with
  | zero => intro f σ ρ σ' h; simp only [RufAusgang.welt, rufAt, reduceCtorEq] at h
  | succ n ih =>
      intro f σ ρ σ' h
      simp only [rufAt] at h
      have g0 : Treu (D.schreibt f) (D.gschreibt f) σ
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) := treu_lese _ _ _
      split at h
      · simp only [RufAusgang.welt, reduceCtorEq] at h
      · have hb := end_treu O passes (rufAt P O passes n) ih hO (P.rumpf f)
          (σ.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte) ρ
        split at h
        · rename_i σ2 v hs
          have g2 : Treu (D.schreibt f) (D.gschreibt f) _ σ2 := hb σ2 (by rw [hs]; rfl)
          have g3 : Treu (D.schreibt f) (D.gschreibt f) σ2
              (σ2.lese (vertragVon D f).ende (P.ensures f).orte) :=
            treu_lese σ2 (vertragVon D f).ende (P.ensures f).orte
          split at h
          · simp only [RufAusgang.welt, reduceCtorEq] at h
          · have g4 : Treu (D.schreibt f) (D.gschreibt f) _
                ((D.invs.filter (schuldet f)).foldl
                  (fun σ' i => σ'.lese (invSicht D i) (P.invariante i).orte)
                  (σ2.lese (vertragVon D f).ende (P.ensures f).orte)) :=
              treu_foldl_lese P (D.invs.filter (schuldet f)) _
            split at h
            · simp only [RufAusgang.welt, reduceCtorEq] at h
            · simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
              exact ((g0.trans g2).trans g3).trans g4
        · rename_i σ2 r hs
          simp only [RufAusgang.welt, Option.some.injEq] at h; subst h
          exact g0.trans (hb _ (by rw [hs]; rfl))
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · rename_i hl _ _ _; exact absurd hl (by decide)
        · simp only [RufAusgang.welt, reduceCtorEq] at h
        · simp only [RufAusgang.welt, reduceCtorEq] at h

#print axioms Gabbro.Grammatik.rufAt_treu

end Gabbro.Grammatik
