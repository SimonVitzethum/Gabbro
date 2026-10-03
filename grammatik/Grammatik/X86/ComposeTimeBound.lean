/-
  File:      Grammatik/X86/ComposeTimeBound.lean
  Subject:   TIME-BOUND CLOSING (lane 836).

  Closes the fuel-bounded validation acceptance to the proved work/time
  transfer over the SAME decoded list: the producer leg is the accepted
  fail-closed traversal (`ValidationBudget.decodeFuel` over canonical
  bytes, full consumption, derived count bound); the consumer leg is the
  accepted budget/time composition (`BudgetExecution.budgetAusfuehrung_transfer`
  over `Deckung` work coverage plus the named per-form hardware bound
  `HardwareAssumptions.laufKosten_schranke`). Tuning tables never enter:
  `expand` maxima stay backend-declared data checked by admission Bools.
-/
import Grammatik.X86.ValidationBudget
import Grammatik.X86.BudgetExecution
import Grammatik.X86.TimeTransfer
import Grammatik.X86.CostSummary
import Grammatik.X86.HardwareAssumptions
import Grammatik.X86.Ausfuehrung
import Grammatik.ZielOrtEinfadenZeuge

namespace Gabbro.Grammatik.X86

/-! ## Closing interface: validation acceptance to time bound.

    PRODUCER (`ValidationBudget`): a fuel-bounded traversal of canonical
    bytes yields the decoded prefix `xs` with no rest (`hDec`).
    CONSUMER (`BudgetExecution`/`TimeTransfer`): admitted summary/profile
    (`hAdm`), successful named-cost aggregation (`hCost`), per-step bound
    (`hb`), and summary work coverage over the source budget (`hDeck`).
    The closing theorem ties both legs over the same `xs`: validation
    acceptance, admission halves, the derived count bound and the target
    time bound. No internals re-proved, no new interpreter, no new cost
    model. -/

/-- CLOSING: a fuel-accepted decoded prefix covered in machine work by an
    admitted summary over the source budget is covered in named target
    time. All five premises are used: `hDec` feeds validation acceptance
    and the count bound, `hAdm` the admission halves, `hCost`/`hb` the
    hardware aggregation, `hDeck` the work side. -/
theorem ComposeTimeBound_verbindung
    (s : CostSummary) (p : HardwareProfil) (fuel : Nat) (bs : List Byte)
    (xs : List Decodiert) (src B t : Nat)
    (hDec : decodeFuel fuel bs = some (xs, []))
    (hAdm : zeitTransferZulaessig s p = true)
    (hCost : laufKosten p xs = some t)
    (hb : ∀ d ∈ xs, ∃ c, schrittKosten p d = some c ∧ c ≤ B)
    (hDeck : Deckung s src xs) :
    validAllFuel fuel bs = true ∧
    kostenSummeOk s = true ∧ profilGueltig p = true ∧
    xs.length ≤ fuel ∧
    ∀ k, expandBound s src = some k → t ≤ B * k := by
  have hValid := validAllFuel_some_empty fuel bs xs hDec
  have hAdm2 := zeitTransferZulaessig_braucht_ok s p hAdm
  have hLen := decodeFuel_ins_le_fuel fuel bs xs [] hDec
  have hT := budgetAusfuehrung_transfer s p xs src B t hCost hb hDeck
  exact ⟨hValid, hAdm2.1, hAdm2.2, hLen, hT⟩

end Gabbro.Grammatik.X86
