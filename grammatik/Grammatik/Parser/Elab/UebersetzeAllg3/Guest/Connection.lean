module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
public import Grammatik.Parser.Elab.UebersetzeAllg3.Guest.Export
@[expose] public section
namespace Gabbro.Grammatik.Parser.UebersetzeAllg2
open Uebersetze UebersetzeAllg

/-- Every actual successful program assembly retains every source foreign
    pre/postcondition. The projection carries successful contract lowering
    from the same unit gate; a substitute contract cannot be selected. -/
theorem lowerAllg_axVertrag (u : UProg) (P : Programm (declOf u))
    (fs : List (declOf u).Fn) (h : lowerAllg u = .ok (P, fs))
    (a : (declOf u).Ax) : lowerAxContract u a = .ok (P.axVertrag a) := by
  unfold lowerAllg at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i gate
        have hg : (ptrPaarGate u && ptrLowerOk u && axContractsB u) = true := gate
        obtain ⟨rfl, _⟩ := Measures.checkedProgram_eq h
        exact axVertragOf_exact u a (Bool.and_eq_true.mp hg).2
      · cases h

/-- A source software origin is disjoint from a named hardware witness.
    The service must separately establish ForeignPflicht and isolation. -/
theorem source_software_origin (u : UProg) (a : Fin u.axs.length)
    (software : (u.axs.get a).software = true)
    (witness : (u.axs.get a).beleg = none) :
    (declOf u).axHerkunft a = some AxOrigin.software ∧
      (declOf u).axBeleg a = none := by
  change herkunftAt u a = some AxOrigin.software ∧ belegAt u a = none
  simp [herkunftAt, belegAt, software, witness]

end Gabbro.Grammatik.Parser.UebersetzeAllg2
