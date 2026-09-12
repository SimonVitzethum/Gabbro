/-
  Audit 26, finding F11 -- Zeugnis.lean: `zeugnis_sound` (line 313)
  concludes `∃ _ : Expr D Γ Λ (.int lo hi), True`. Pattern (c): the
  existential pairs the real witness with `True`, so the conclusion is
  existence-only -- equivalent to `Nonempty` of the judgment. Consumers
  can appeal TO its existence but cannot compute WITH the judgment. The
  file is explicit ("An ∃, not the term itself"), so severity is low;
  the demo pins the shape: the `True` half proves itself and the whole
  is exactly `Nonempty`.
-/
import Grammatik.Zeugnis

open Gabbro.Grammatik

/-- F11: the conclusion is exactly `Nonempty` of the judgment. -/
theorem audit26_sound_is_nonempty {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} (c : CertExpr D) (lo hi : Int)
    (h : GueltigAbleitung D Γ Λ c lo hi) :
    Nonempty (Expr D Γ Λ (.int lo hi)) := by
  obtain ⟨ee, _⟩ := zeugnis_sound c lo hi h
  exact ⟨ee⟩

/-- F11: the `True` half is vacuous -- it proves itself. -/
theorem audit26_sound_true_vacuous {D : Deklaration} {Γ : Ctx}
    {Λ : List (Res D)} (c : CertExpr D) (lo hi : Int)
    (h : GueltigAbleitung D Γ Λ c lo hi) : True := by
  obtain ⟨_, _⟩ := zeugnis_sound c lo hi h
  exact trivial

#print axioms audit26_sound_is_nonempty
#print axioms audit26_sound_true_vacuous

/-
CUTS:
  (C1) Whether soundness SHOULD deliver the term for computation (e.g. an
       evaluator over the witness) is out of scope; the file names the
       witness-pair shape explicitly.
-/
