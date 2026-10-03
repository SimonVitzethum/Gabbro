/-
  File:      Grammatik/X86/ComposeBudgetResum.lean
  Subject:   Composition closing: budget-resumption closing (lane 834).

  Producer/consumer interface closed here: source budget exhaustion
  (`Budget.runOps` over-budget head, `BudgetExecution.stoppReihenfolge`)
  to target work spent (`CostSummary.expandBound`/`targetWork` via
  `BudgetExecution.Deckung` and `budgetAusfuehrung_transfer`), with an
  explicit ghost source-budget correspondence (`GhostBudget`: the ghost
  tracks the source budget exactly). Resumption (larger source budget
  preserves coverage) is proved from the accepted expansion formula.
  Exhaustion TIMING (when the target stops relative to source
  exhaustion) stays an explicit OPEN cut, owned by the scheduling/IR
  lanes. No new interpreter, no second cost model, no checker change.
-/
import Grammatik.X86.BudgetExecution
import Grammatik.X86.CostSummary
import Grammatik.X86.HardwareAssumptions
import Grammatik.Budget

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Ghost source-budget correspondence: the ghost value tracks exactly
    the source budget the summary coverage runs over. Checked data
    (`Deckung`), never a second counter. -/
def GhostBudget (s : CostSummary) (ghost src : Nat)
    (xs : List Decodiert) : Prop :=
  ghost = src ∧ Deckung s src xs

/-- Accepted-expansion monotonicity: a larger source budget never
    shrinks the expansion bound. From the accepted formula
    (`expandBound_keinVerlust`), never a re-sum. Every premise is
    used: `hMax` fixes the uniform maximum for both sides, `hk` and
    `hk'` pin the two bounds, `hle` orders them. -/
theorem expandBound_mono (s : CostSummary) (m src src' k k' : Nat)
    (hMax : alleMax s = some m)
    (hk : expandBound s src = some k)
    (hk' : expandBound s src' = some k')
    (hle : src ≤ src') :
    k ≤ k' := by
  have e1 := expandBound_keinVerlust s src m hMax
  have e2 := expandBound_keinVerlust s src' m hMax
  rw [e1] at hk
  rw [e2] at hk'
  cases hk
  cases hk'
  have hmul : src * m ≤ src' * m := Nat.mul_le_mul_right m hle
  omega

/-- Resumption preserves coverage: the summary coverage over `src`
    covers the same segment over any larger `src'`. The ghost keeps
    tracking the OLD budget; the proof replays the accepted expansion
    on both sides. Every premise is used. -/
theorem deckung_resum (s : CostSummary) (m src src' : Nat)
    (xs : List Decodiert)
    (hMax : alleMax s = some m)
    (hDeck : Deckung s src xs)
    (hle : src ≤ src') :
    Deckung s src' xs := by
  intro k' hk'
  have e1 := expandBound_keinVerlust s src m hMax
  have e2 := expandBound_keinVerlust s src' m hMax
  have hwork := hDeck _ e1
  rw [e2] at hk'
  cases hk'
  have hmul : src * m ≤ src' * m := Nat.mul_le_mul_right m hle
  omega

/-- CLOSING: source budget exhaustion meets target work spent, with
    ghost correspondence and resumption. The four conjuncts compose
    accepted modules only: ghost tracking (rewrite of `hGhost`),
    transfer at `src` (`budgetAusfuehrung_transfer`), transfer at the
    resumed `src'` (`deckung_resum` + `budgetAusfuehrung_transfer`),
    and joint stopping order (`stoppReihenfolge`: the over-budget head
    op names the source budget breach AND the refused head form
    refuses the target aggregation). Every premise is used. -/
theorem ComposeBudgetResum_verbindung
    (s : CostSummary) (p : HardwareProfil)
    (xs : List Decodiert) (src src' B t ghost : Nat)
    (bound left : Nat) (op : Op) (rest : List Op)
    (d : Decodiert) (tl : List Decodiert)
    (m : Nat)
    (hGhost : ghost = src)
    (hMax : alleMax s = some m)
    (hDeck : Deckung s src xs)
    (hCost : laufKosten p xs = some t)
    (hb : ∀ d ∈ xs, ∃ c, schrittKosten p d = some c ∧ c ≤ B)
    (hSrcOver : ¬ op.cost ≤ left)
    (hTgtRef : schrittKosten p d = none)
    (hResum : src ≤ src') :
    Deckung s ghost xs ∧
    (∀ k, expandBound s src = some k → t ≤ B * k) ∧
    (∀ k', expandBound s src' = some k' → t ≤ B * k') ∧
    ((∃ needed, runOps bound left (op :: rest)
      = .budget "per_pass.ops" needed bound) ∧
    laufKosten p (d :: tl) = none) := by
  have hGhostDeck : Deckung s ghost xs := by
    rw [hGhost]
    exact hDeck
  have hTransfer := budgetAusfuehrung_transfer s p xs src B t hCost hb hDeck
  have hDeck' := deckung_resum s m src src' xs hMax hDeck hResum
  have hTransfer' :=
    budgetAusfuehrung_transfer s p xs src' B t hCost hb hDeck'
  have hStop := stoppReihenfolge bound left op rest p d tl hSrcOver hTgtRef
  exact ⟨hGhostDeck, hTransfer, hTransfer', hStop⟩

/-- JOINT WITNESS: the closing instantiated on concrete admitted
    values, jointly with a non-degenerate program (table `konto`
    written by `eSetze`, reached run carrying slot `5` against start
    `0`), a memory-changing reached target run (register and memory
    byte observably `0 -> 42`), the transfer bounds at `src = 1` and
    resumed `src' = 2`, and two planted refusals (over-budget head op
    names the source budget breach; refused `ret` head refuses the
    target aggregation). Every premise of `ComposeBudgetResum_verbindung`
    is instantiated jointly below (`blattSummary`, `profilZeuge`,
    `zeugeProg`, ghost `1`, bound `3`, `fremdOp 3`, `ret`). -/
theorem ComposeBudgetResum_verbindung_zeuge :
    ∃ (M : RufMaschineG eD) (rho : Env eD (eD.params ePruefe))
      (w0 : World eD),
    RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
    (eSp.slots () 0 ()).n = 0 ∧
    (eD.signatur eSetze).schreibt () = true ∧
    RufEreignisF.eintritt ePruefe rho w0 ∈ (M.faeden 0).log ∧
    ReqAmEintritt eP ePruefe w0 rho ∧
    (w0.slots () 0 ()).n = 5 ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => s.register Register.rbx) = some 42) ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => s.speicher.bytes (BitVec.ofNat 64 8192))
      = some (BitVec.ofNat 8 42)) ∧
    (zeugeZustand.speicher.bytes (BitVec.ofNat 64 8192)
      = BitVec.ofNat 8 0) ∧
    (∀ k, expandBound blattSummary 1 = some k → 7 ≤ 3 * k) ∧
    (∀ k', expandBound blattSummary 2 = some k' → 7 ≤ 3 * k') ∧
    (∃ needed, runOps 3 3 [fremdOp 3]
      = .budget "per_pass.ops" needed 3) ∧
    laufKosten profilZeuge [{ befehl := Befehl.ret, laenge := 1 }]
      = none := by
  obtain ⟨M, hr, h0, rho, w0, hm, hreq, h5⟩ := ziel_ort_einfaden_zeuge
  obtain ⟨hmem1, hmem2, hmem3⟩ := zeuge_speicher_aendert_sich
  have hMax : alleMax blattSummary = some 5 := by decide
  have hDeck : Deckung blattSummary 1 zeugeProg := by
    intro k hk
    rw [blattSummary_schranke] at hk
    cases hk
    decide
  have hCost : laufKosten profilZeuge zeugeProg = some 7 := by decide
  have hSrcOver : ¬ (fremdOp 3).cost ≤ 3 := by decide
  have hTgtRef :
      schrittKosten profilZeuge { befehl := Befehl.ret, laenge := 1 } =
        none := rfl
  have hMain := ComposeBudgetResum_verbindung blattSummary profilZeuge
    zeugeProg 1 2 3 7 1 3 3 (fremdOp 3) []
    { befehl := Befehl.ret, laenge := 1 } [] 5 rfl hMax hDeck hCost
    laufKosten_schranke_zeuge_hbound hSrcOver hTgtRef (by decide)
  obtain ⟨_, hT1, hT2, hStop⟩ := hMain
  exact ⟨M, rho, w0, hr, h0, rfl, hm, hreq, h5, hmem1, hmem2, hmem3,
    hT1, hT2, hStop.1, hStop.2⟩

/- CUTS:
     Proved here, by composing already-accepted modules (never
     re-proved, never duplicated): ghost source-budget correspondence
     (`GhostBudget`: ghost tracks `src` exactly); accepted-expansion
     monotonicity (`expandBound_mono`, from `expandBound_keinVerlust`);
     resumption coverage (`deckung_resum`); the closing
     (`ComposeBudgetResum_verbindung`: ghost tracking +
     `budgetAusfuehrung_transfer` at `src` + resumed transfer at `src'`
     + `stoppReihenfolge` joint stopping order); and the joint
     non-degenerate witness (`ComposeBudgetResum_verbindung_zeuge`:
     table-writing program, reached run with slot `0 -> 5`,
     memory-changing target run `0 -> 42`, both transfer bounds, both
     planted refusals).
     NOT proved here, and not claimed:
     - Exhaustion TIMING stays OPEN: when the target stops relative to
       source exhaustion (scheduling, interleavings, waiting delays)
       is owned by the scheduling/IR lanes, never derived here. The
       transfer bounds admitted finite prefixes only.
     - No lowering correspondence proved: `Deckung` is carried data.
       Which source step lowers to which target segment is established
       by the lowering/IR producer (`DerivedWorkBound.deckung_fragment`
       derives it for the covered fragment; the generic IR is absent).
     - No hardware cycle claim: `t` counts named per-form bounds from
       the selected profile, never measured silicon latencies; `ret`
       stays refused (`none`).
     - No constant-time and no CAS-progress/fairness promise:
       unbounded retries are refused, never bounded.
     - No new interpreter, executor, decoder or cost model: the one
       `Ausfuehrung.schritt`/`lauf`, the one `laufKosten` aggregation,
       the one `targetWork` and the actual `runOps`/`foreverLauf`/`rufAt`
       equations are reused untouched.
     - No checker, Spec, goal, emitter or friend-reserved file touched.
-/

#print axioms GhostBudget
#print axioms expandBound_mono
#print axioms deckung_resum
#print axioms ComposeBudgetResum_verbindung
#print axioms ComposeBudgetResum_verbindung_zeuge

end Gabbro.Grammatik.X86
