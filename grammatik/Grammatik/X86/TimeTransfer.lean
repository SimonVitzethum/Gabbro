/-
  File:      Grammatik/X86/TimeTransfer.lean
  Subject:   TARGET-WORK TO SOURCE-TIME TRANSFER SKELETON (lane 547, N17).

  Reuses the accepted cost aggregation (`HardwareAssumptions`: per-form
  named bounds, `laufKosten` and its lemmas) and the accepted summary
  schema (`CostSummary`: `kostenSummeOk`, `expandBound`, `targetWork`,
  `blattSummary`), plus the actual source bound (`KostenG.kostenTiefF`,
  the `ZeitAb` right-hand side `kostenTief` at the use site) and the
  non-degenerate source fixture (`ZielOrtEinfadenZeuge`, via CostSummary).

  Claim: a finite executed target prefix whose every step carries a
  named per-form bound, covered in machine work by an admitted summary
  over a source budget, is covered in target time. Hardware timing
  supplies per-form bounds only; source correspondence and the
  conclusion are proved, never assumed. Full scheduling / IR
  correspondence stays CUT; no constant-time or CAS-progress promise.
-/
import Grammatik.X86.CostSummary
import Grammatik.X86.HardwareAssumptions
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- Transfer admission: an admitted summary AND an admitted profile.
    Data and admission are separate so a refused transfer stays statable. -/
def zeitTransferZulaessig (s : CostSummary) (p : HardwareProfil) : Bool :=
  kostenSummeOk s && profilGueltig p

/-- Admission splits into its two halves; both premises are used. -/
theorem zeitTransferZulaessig_braucht_ok (s : CostSummary) (p : HardwareProfil)
    (h : zeitTransferZulaessig s p = true) :
    kostenSummeOk s = true ∧ profilGueltig p = true := by
  unfold zeitTransferZulaessig at h
  simp at h
  exact h

/-! ## Transfer core.

    A finite target prefix `xs` (the same decoded list that `lauf`
    executes) whose every step carries a named per-form cost of at most
    `B`, and whose machine work is covered by the summary over the
    source budget `src` (the `ZeitAb` right-hand side `kostenTief` at
    the use site; `kostenTiefF` for foreign costs), is covered in target
    time `t ≤ B * k` for every summary bound `k` of `src`. The two
    bounds composed are independent facts -- the hardware per-step
    bound over the executed prefix, the summary work coverage over the
    source budget -- not one sum renamed. Units stay separate: `src`
    counts source steps (the `Budget` ops side), `targetWork` counts
    retired instructions, `t` counts named target time. -/

/-- Transfer core: per-step hardware bound plus summary work coverage
    give target-time coverage. All three premises are used: `hCost`
    and `hb` feed `laufKosten_schranke`, `hWork` feeds the work side. -/
theorem zeitTransfer (s : CostSummary) (p : HardwareProfil)
    (xs : List Decodiert) (src B t : Nat)
    (hCost : laufKosten p xs = some t)
    (hb : ∀ d ∈ xs, ∃ c, schrittKosten p d = some c ∧ c ≤ B)
    (hWork : ∀ k, expandBound s src = some k →
      targetWork (xs.map (fun d => d.befehl)) ≤ k) :
    ∀ k, expandBound s src = some k → t ≤ B * k := by
  intro k hk
  have hsch := laufKosten_schranke p xs B t hb hCost
  have hle := hWork k hk
  have htw : targetWork (List.map (fun d : Decodiert => d.befehl) xs)
      = xs.length := by
    simp [targetWork]
  have hle' : xs.length ≤ k := by omega
  have hmono : B * xs.length ≤ B * k := Nat.mul_le_mul_left B hle'
  omega

/- CUTS:
    - Skeleton only: transfer core, refusals and the joint witness follow.
    - No source/target scheduling or IR correspondence (`XCorr`); no
      constant-time and no CAS-progress promise.
-/

#print axioms zeitTransferZulaessig_braucht_ok
#print axioms zeitTransfer

end Gabbro.Grammatik.X86
