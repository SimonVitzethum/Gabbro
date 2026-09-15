/-
  File:      Grammatik/RufLogikZeuge.lean
  Subject:   **WITNESSES** for the handler congruence and its two consumers,
             on the two chains of the corpus -- non-degenerate, on programs
             that do work.

  1. `tiefe_zeuge_104` -- on the 104 chain (`einzahlen(k, 0, 7)` from the zero
     state, which moves the slot `0 -> 100`): at depth `0` the call IS the
     `abstieg` residue, at depth `2` it returns and moves the slot, and from
     depth `2` upward it is the SAME outcome at every depth. So both
     disjuncts of `rufAt_tiefer` are inhabited on one program, and
     `rufAt_stabil_ab` is applied to an outcome that is not `ok` by accident.

  2. `nurAbstieg_zeuge_108` -- on the 108 chain, which has NO locks
     (`Kette108.kein_lock`): there the residual frame hypothesis
     `RufRahmenTreu` is free (`rufRahmenTreu_ohneSperren`), so clause 4e(ii)
     of the closing theorem lands UNCONDITIONALLY: no call of 108's program
     ends in a `logik` outcome other than an `abstieg`, at any depth, from any
     entry meeting the callee's `requires`. Non-degenerate: 108's own call
     RETURNS (`kette_108_zeuge`), so the statement is not empty.
-/
import Grammatik.Kette104Satz
import Grammatik.Kette108

namespace Gabbro.Grammatik.Kette104

/-- **WITNESS for `rufAt_tiefer` / `rufAt_stabil_ab` on the 104 chain.** -/
theorem tiefe_zeuge_104 :
    rufAt P4 O4 0 0 ein4 (sp4.welt []) rho7 = .logik (.abstieg ein4) ∧
    (∃ σ' : World D4, rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok σ' () ∧
      ((sp4.welt []).slots t4 0 f4).n = 0 ∧ (σ'.slots t4 0 f4).n = 100) ∧
    (∀ k : Nat, rufAt P4 O4 0 (2 + k) ein4 (sp4.welt []) rho7 =
      rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7) := by
  have hR : rufAt P4 O4 0 2 ein4 (sp4.welt []) rho7 = .ok _ () := rfl
  refine ⟨rfl, ⟨_, hR, rfl, rfl⟩, ?_⟩
  exact rufAt_stabil_ab P4 O4 0 2 ein4 (sp4.welt []) rho7 (fun g h => by rw [hR] at h; cases h)

#print axioms Gabbro.Grammatik.Kette104.tiefe_zeuge_104

end Gabbro.Grammatik.Kette104

namespace Gabbro.Grammatik.Kette108

/-- 108's declaration has no lock, so no world holds one. -/
theorem stufen8 : StufenOk P8 :=
  stufenOk_ohne P8 (fun f => by rcases fn_zwei f with e | e <;> subst e <;> rfl)

/-- **The residual frame hypothesis holds on 108** -- the declaration has no
    locks, so `HeldB` is vacuous and `rufAt_gut` gives the frame everywhere. -/
theorem rahmenTreu_108 (passes : Nat) : ∀ n : Nat, RufRahmenTreu P8 (rufAt P8 O8 passes n) :=
  rufRahmenTreu_ohneSperren P8 O8 passes hw8.1 stufen8 (fun L => kein_lock L)

/-- **WITNESS for `rufAt_nurAbstieg` / clause 4e(ii), UNCONDITIONAL on 108**:
    no call of 108's program ends in a `logik` outcome other than an
    `abstieg`, at any depth, at any entry meeting the callee's `requires`.
    Non-degenerate: 108's own call returns (`kette_108_zeuge`). -/
theorem nurAbstieg_zeuge_108 :
    (∀ (passes n : Nat) (f : D8.Fn) (σ : World D8) (ρG : Env D8 (D8.params f)) (e : Logik D8),
      ReqAmEintritt P8 f σ ρG → rufAt P8 O8 passes n f σ ρG = .logik e →
        ∃ h : D8.Fn, e = .abstieg h) ∧
    (∃ (σ' : World D8) (v : ErgVal D8 (D8.erg a8)),
      rufAt P8 O8 0 1 a8 (sp8.welt []) .nil = .ok σ' v) := by
  refine ⟨?_, ?_⟩
  · exact (schlusssatz kette_108 O8 hw8 tvOrc tvXR tvXR_funktional
      (fun f => CallAt EL8.lay tvOrc tvXR (kProg zert108) 1 (fnNr f)) (fun _ => 1)
      (fun _ _ _ _ _ h => h) (speicherR E8.sp0) init8 start8).2.2.2.2.2.2.2.1.2
      (fun passes n => rahmenTreu_108 passes n)
  · exact ⟨_, _, rfl⟩

#print axioms Gabbro.Grammatik.Kette108.rahmenTreu_108
#print axioms Gabbro.Grammatik.Kette108.nurAbstieg_zeuge_108

end Gabbro.Grammatik.Kette108
