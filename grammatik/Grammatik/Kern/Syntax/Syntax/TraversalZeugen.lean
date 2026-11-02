module

public import Grammatik.Kern.Syntax.Syntax.Teil3

public section

namespace Gabbro.Grammatik

/-- A failed first test still selects a live member of a nonempty domain. -/
theorem waehleMinimal_istMitglied_zeuge :
    (fun k : Nat => k == 2) 2 = true ∧ 2 ∈ ([1, 2, 3] : List Nat) := by
  exact waehleMinimal_istMitglied (ks := [1, 2, 3])
    (p := fun k => k == 2) (v := 2) (by decide)

/-- Exhaustion checks every entry of a nonempty domain. -/
theorem waehleMinimal_keinMitglied_zeuge :
    ∀ v ∈ ([1, 2, 3] : List Nat), (fun k : Nat => k == 4) v = false := by
  exact waehleMinimal_keinMitglied (ks := [1, 2, 3])
    (p := fun k => k == 4) (by decide)

/-- Concrete all-false membership tests establish exhaustion. -/
theorem waehleMinimal_alleFalsch_zeuge :
    waehleMinimal [1, 2, 3] (fun k => k == 4) = none := by
  exact waehleMinimal_alleFalsch (ks := [1, 2, 3])
    (p := fun k : Nat => k == 4) (h := waehleMinimal_keinMitglied_zeuge)

/-- Both directions of completeness hold on a populated domain. -/
theorem waehleMinimal_vollstaendig_zeuge :
    waehleMinimal [1, 2, 3] (fun k => k == 4) = none ↔
      ∀ v ∈ ([1, 2, 3] : List Nat), (fun k : Nat => k == 4) v = false :=
  waehleMinimal_vollstaendig

end Gabbro.Grammatik
