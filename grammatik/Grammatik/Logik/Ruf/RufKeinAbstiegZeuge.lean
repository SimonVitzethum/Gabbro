/-
  File:      Grammatik/RufKeinAbstiegZeuge.lean
  Subject:   **WITNESS** for `rufAt_keinAbstieg` on the cost-bound fixture
              `zP` (`KostenGZeuge.lean`): `zWrap` calls `lies` and `einzahlen`,
              so its call tree is non-degenerate -- depth `1` does NOT admit
              it (`zP_tief_wrap_eins`) and depth `2` does (`zP_tief_wrap`).
              At depth `2` no call of `zWrap` ends in an `abstieg`, on every
              budget, world, environment and oracle.
-/
module
public import Grammatik.Logik.Ruf.RufKeinAbstiegTief
public import Grammatik.Logik.Fortschritt.KostenGZeuge
@[expose] public section


namespace Gabbro.Grammatik

/-- **WITNESS for `rufAt_keinAbstieg`.** `zWrap` has a real call tree
    (`lies` and `einzahlen` below it): depth `1` is not enough and depth `2`
    is, and at depth `2` the `abstieg` is unreachable on every budget,
    world, environment and oracle. -/
theorem rufAt_keinAbstieg_zeuge :
    rufTief zP 2 zWrap = true ∧
    rufTief zP 1 zWrap = false ∧
    ∀ (passes : Nat) (σ : World zD) (ρ : Env zD (zD.params zWrap)) (hh : zD.Fn),
      rufAt zP zO passes 2 zWrap σ ρ ≠ .logik (.abstieg hh) := by
  refine ⟨zP_tief_wrap, zP_tief_wrap_eins, fun passes σ ρ hh => ?_⟩
  exact rufAt_keinAbstieg zP zO passes 2 zWrap σ ρ hh zP_tief_wrap

#print axioms Gabbro.Grammatik.rufAt_keinAbstieg_zeuge

end Gabbro.Grammatik
