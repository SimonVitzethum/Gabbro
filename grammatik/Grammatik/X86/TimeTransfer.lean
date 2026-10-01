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

/-! ## No hidden stutter.

    A successful aggregation certifies every step of the prefix with a
    named per-form cost: no executed step hides behind a zero-cost
    premise, and a refused form admits no successful aggregation at all
    (the obstruction below). Both facts reuse the accepted aggregation
    equations, never a new cost model. -/

/-- A successful cost aggregation names a cost for every prefix step:
    aggregation success leaves no step unpriced. -/
theorem zeitTransfer_kosten_benannt (p : HardwareProfil)
    (xs : List Decodiert) (t : Nat)
    (hCost : laufKosten p xs = some t) :
    ∀ d ∈ xs, ∃ c, schrittKosten p d = some c := by
  induction xs generalizing t with
  | nil =>
    intro d hd
    rw [laufKosten_nil] at hCost
    simp at hd
  | cons hd tl ih =>
    intro d hm
    cases hkd : schrittKosten p hd with
    | none =>
      have hnone : laufKosten p (hd :: tl) = none :=
        laufKosten_kopf_verweigert p hd tl hkd
      rw [hnone] at hCost
      cases hCost
    | some c =>
      cases htl : laufKosten p tl with
      | none =>
        have hnone : laufKosten p (hd :: tl) = none :=
          laufKosten_rest_verweigert p hd tl c hkd htl
        rw [hnone] at hCost
        cases hCost
      | some t' =>
        rw [List.mem_cons] at hm
        rcases hm with rfl | hmem
        · exact ⟨c, hkd⟩
        · exact ih t' htl d hmem

/-! ## Refusals.

    The transfer admits no unbounded CAS retry behind a constant bound,
    no waiting exclusion without exact source correspondence, no
    CAS-spin exclusion at all, and no prefix whose head form the
    profile refuses: each is a proved `false` / non-existence from the
    accepted `kostenSummeOk` refusals and the aggregation equations.
    Every premise below is used by its proof. -/

/-- An unbounded retry site behind a claimed retry bound refuses
    transfer admission (a CAS retry loop is unbounded). -/
theorem zeitTransfer_verweigert_retry (s : CostSummary) (p : HardwareProfil)
    (k : Nat)
    (hRetry : s.retryBound = none)
    (hExpand : s.expand .retryTry = some k) :
    zeitTransferZulaessig s p = false := by
  unfold zeitTransferZulaessig
  have h := kostenSummeOk_verweigert_unbegrenzt s k hRetry hExpand
  rw [h]
  simp

/-- A waiting exclusion without exact source correspondence refuses
    transfer admission: machine waiting counts as excluded only where
    it corresponds exactly to source-level non-firing. -/
theorem zeitTransfer_verweigert_ohneQuelle (s : CostSummary)
    (p : HardwareProfil) (e : Exclusion)
    (hm : e ∈ s.exclusions)
    (hq : e.sourceCorresponds = false) :
    zeitTransferZulaessig s p = false := by
  unfold zeitTransferZulaessig
  have h := kostenSummeOk_verweigert_ohneQuelle s e hm hq
  rw [h]
  simp

/-- A CAS-spin exclusion refuses transfer admission unconditionally:
    a lowering-introduced spin has no source counterpart. -/
theorem zeitTransfer_verweigert_spin (s : CostSummary) (p : HardwareProfil)
    (e : Exclusion)
    (hm : e ∈ s.exclusions)
    (hSpin : e.kind = .casSpin) :
    zeitTransferZulaessig s p = false := by
  unfold zeitTransferZulaessig
  have h := kostenSummeOk_verweigert_spin s e hm hSpin
  rw [h]
  simp

/-- OBSTRUCTION: a prefix whose head form carries no named bound admits
    no successful aggregation -- hence no transfer instance runs on it.
    A retry/spin step the profile refuses cannot hide behind a
    zero-cost premise; it stops the whole prefix. -/
theorem zeitTransfer_verweigert_ohneKosten (p : HardwareProfil)
    (d : Decodiert) (rest : List Decodiert)
    (h : schrittKosten p d = none) :
    ¬ ∃ t, laufKosten p (d :: rest) = some t := by
  intro ⟨t, ht⟩
  have hnone := laufKosten_kopf_verweigert p d rest h
  rw [hnone] at ht
  cases ht

/- CUTS:
    - Skeleton only: transfer core, refusals and the joint witness follow.
    - No source/target scheduling or IR correspondence (`XCorr`); no
      constant-time and no CAS-progress promise.
-/

#print axioms zeitTransferZulaessig_braucht_ok
#print axioms zeitTransfer
#print axioms zeitTransfer_kosten_benannt
#print axioms zeitTransfer_verweigert_retry
#print axioms zeitTransfer_verweigert_ohneQuelle
#print axioms zeitTransfer_verweigert_spin
#print axioms zeitTransfer_verweigert_ohneKosten

end Gabbro.Grammatik.X86
