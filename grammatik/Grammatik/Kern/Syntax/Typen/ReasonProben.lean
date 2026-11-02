module

public import Grammatik.Kern.Syntax.Typen.Reason

@[expose] public section

namespace Gabbro.Grammatik

private def closedReason : ReasonSpec :=
  ⟨7, [⟨3, by decide⟩, ⟨2 ^ 100, by decide⟩], true, by decide⟩

private def openReason : ReasonSpec := { closedReason with name := 8, closed := false }

private def emptyOpenReason : ReasonSpec := ⟨9, [], false, by decide⟩

/-- Known cases retain their declared order, including a code larger than a runner word. -/
theorem reason_closedEquiv_zeuge :
    (ReasonVal.closedEquiv closedReason rfl) ⟨1, by decide⟩ =
      ReasonVal.known closedReason ⟨1, by decide⟩ := rfl

theorem reason_known_index_zeuge :
    ReasonVal.known closedReason
      (ReasonVal.index rfl (ReasonVal.known closedReason ⟨1, by decide⟩)) =
        ReasonVal.known closedReason ⟨1, by decide⟩ :=
  ReasonVal.known_index rfl _

theorem reason_index_known_zeuge :
    ReasonVal.index rfl (ReasonVal.known closedReason ⟨1, by decide⟩) = ⟨1, by decide⟩ :=
  ReasonVal.index_known rfl _

theorem reason_decode_complete_zeuge :
    ReasonVal.decode openReason (2 ^ 100) =
      some (ReasonVal.known openReason ⟨1, by decide⟩) :=
  ReasonVal.decode_complete _

/-- Unknown codes survive an open boundary even when the declaration has no known cases. -/
theorem reason_empty_open_zeuge :
    (ReasonVal.decode emptyOpenReason (2 ^ 100)).isSome = true := by decide

theorem reason_equal_iff_zeuge :
    ReasonVal.equal (ReasonVal.known closedReason ⟨0, by decide⟩)
      (ReasonVal.known closedReason ⟨1, by decide⟩) = false := by decide

theorem reason_decode_bounded_zeuge :
    0 ≤ (2 ^ 100 : Int) ∧ (2 ^ 100 : Int) < (2 ^ 128 : Nat) :=
  ReasonVal.decode_bounded (ReasonVal.decode_complete
    (ReasonVal.known closedReason ⟨1, by decide⟩))

/-- Equal known cases do not erase declaration identity or openness. -/
theorem reason_nominal_zeuge : closedReason ≠ openReason ∧
    closedReason.codes = openReason.codes := by decide

theorem reason_foreign_declaration_zeuge :
    closedReason ≠ { closedReason with name := 8 } := by decide

theorem reason_openness_zeuge :
    closedReason ≠ { closedReason with closed := false } := by decide

theorem reason_unknown_closed_refused : ReasonVal.decode closedReason 4 = none := by decide

theorem reason_negative_refused : ReasonVal.decode openReason (-1) = none := by decide

theorem reason_overflow_refused : ReasonVal.decode openReason (2 ^ 128) = none := by decide

theorem reason_inhabitedB_iff_zeuge :
    ReasonVal.inhabitedB emptyOpenReason = true ∧ Nonempty (ReasonVal emptyOpenReason) :=
  ⟨rfl, (ReasonVal.inhabitedB_iff _).mp rfl⟩

theorem reason_empty_closed_refused :
    ReasonVal.inhabitedB { emptyOpenReason with closed := true } = false := rfl

end Gabbro.Grammatik
