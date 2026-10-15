/-
  File:      Grammatik/X86/BudgetExecution.lean
  Subject:   SOURCE BUDGET-STOP TO TARGET WORK CONNECTION (lane 572).

  Connects actual source budget exhaustion (`Budget.runOps`/`runPasses`,
  `Semantik.foreverLauf` at zero passes, `rufAt` at zero depth) with the
  accepted finite target runs (`Ausfuehrung.lauf`, `laufKosten`,
  `targetWork`/`expandBound`, `zeitTransfer`) through an explicit
  representation interface (`Deckung`). The per-step lowering
  correspondence is carried data, never assumed; the single IR is absent
  (no `IR.lean` in the tree), so that leg stays OPEN and is named in CUTS.
-/
import Grammatik.Budget
import Grammatik.Semantik
import Grammatik.KostenG
import Grammatik.ZielOrtEinfadenZeuge
import Grammatik.X86.CostSummary
import Grammatik.X86.HardwareAssumptions
import Grammatik.X86.TimeTransfer
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.ObservationProjection
import Grammatik.X86.LockedOps

namespace Gabbro.Grammatik.X86

/-- Explicit representation interface: the target segment `xs` spends its
    machine work inside the summary bound over the source budget `src`
    (a `kostenTiefF` value at the use site). Checked coverage data: which
    source step lowers to which target instruction is established by the
    lowering/IR producer, OPEN here (no `IR.lean` in the tree). -/
def Deckung (s : CostSummary) (src : Nat) (xs : List Decodiert) : Prop :=
  ∀ k, expandBound s src = some k →
    targetWork (xs.map (fun d => d.befehl)) ≤ k

/-- The empty segment is covered wherever the summary binds zero work:
    no hidden minimum, no silent floor. -/
theorem deckung_leer (s : CostSummary) (src : Nat)
    (h : expandBound s src = some 0) : Deckung s src [] := by
  intro k hk
  rw [h] at hk
  cases hk
  simp [targetWork]

/-! ## 1. Actual source budget exhaustion: named stops, never silent.

    Three independent budget-stop channels of the model, each with its
    own name: `forever` budget spent (`Hardware.fortschritt`, from
    `foreverLauf` at zero passes -- the `FortschrittG` budget disjunct),
    recursion depth spent (`Logik.abstieg`, from `rufAt` at zero depth),
    and ops budget spent (`BudgetOut.budget`, from `runOps` past the
    bound). All three are loud by construction. -/

/-- Source `forever` budget exhaustion through the actual `execStmt`
    semantics: at zero passes the loop stops LOUDLY at its named
    assumption -- the `hardware` stop class, never a silent overrun. -/
theorem forever_erschoepft_benannt {D : Deklaration} {V : Vertrag D}
    {l : Bool} {Γ : Ctx} (a : D.Annahme)
    (schritt : World D → Env D Γ → Ausgang V true Γ)
    (inv : World D → Env D Γ → World D × Bool)
    (σ : World D) (ρ : Env D Γ) :
    foreverLauf (l := l) a schritt inv 0 σ ρ
      = .hardware (.fortschritt a) := rfl

/-- Source depth exhaustion through the actual call semantics: at zero
    depth a call answers the named `abstieg` logic stop -- the measure
    did not fall, never a silent descent. -/
theorem rufAt_tiefe_erschoepft {D : Deklaration} (P : Programm D)
    (O : Orakel D) (passes : Nat) (f : D.Fn)
    (σ : World D) (ρ : Env D (D.params f)) :
    rufAt P O passes 0 f σ ρ = .logik (.abstieg f) := rfl

/-- Source ops split over concatenation: removing an eliminated check's
    ops changes the sum -- so an optimisation that drops a check MUST
    recompute `kostenTiefF` over the lowered body, never inherit it.
    (The E3/A3 obstruction of the budget audit; recomputation is OPEN.) -/
theorem totalCost_anhang (l1 l2 : List Op) :
    totalCost (l1 ++ l2) = totalCost l1 + totalCost l2 := by
  induction l1 with
  | nil => simp [totalCost]
  | cons hd tl ih =>
    simp only [List.cons_append, totalCost_cons, ih, Nat.add_assoc]

/-! ## 2. Where target work is spent: source budget bounds target time.

    The composition is over two INDEPENDENT facts, never one sum
    renamed: the named per-form hardware bound over the executed finite
    prefix (`laufKosten_schranke`), and the summary work coverage over
    the source budget (`Deckung`, carried data with its producer named
    in CUTS). Units stay separate: `src` counts source steps (the
    `Budget` ops side), `targetWork` counts retired instructions, `t`
    counts named target time. -/

/-- Transfer core: per-step hardware bound plus summary work coverage
    over the source budget give target-time coverage. All four premises
    are used: `hCost` and `hb` feed `laufKosten_schranke`, `hDeck` and
    `hk` feed the work side. -/
theorem budgetAusfuehrung_transfer (s : CostSummary)
    (p : HardwareProfil) (xs : List Decodiert) (src B t : Nat)
    (hCost : laufKosten p xs = some t)
    (hb : ∀ d ∈ xs, ∃ c, schrittKosten p d = some c ∧ c ≤ B)
    (hDeck : Deckung s src xs) :
    ∀ k, expandBound s src = some k → t ≤ B * k := by
  intro k hk
  have hsch := laufKosten_schranke p xs B t hb hCost
  have hle := hDeck k hk
  have htw : targetWork (List.map (fun d : Decodiert => d.befehl) xs)
      = xs.length := by
    simp [targetWork]
  have hle' : xs.length ≤ k := by omega
  have hmono : B * xs.length ≤ B * k := Nat.mul_le_mul_left B hle'
  omega

/-! ## 3. Stopping order preserved: head-first and fail-closed, both sides.

    Source `runOps` checks BEFORE each step (`runOps_cons`): the first
    op that does not fit stops the whole run under the budget name, no
    matter what the tail holds. Target `laufKosten` refuses head-first
    (`laufKosten_kopf_verweigert`): one unbounded form refuses the whole
    aggregation, no matter what the tail holds. The joint order: an
    over-budget head op and a refused head form stop BOTH sides, each
    under its own name -- exhaustion is never reordered behind success. -/

/-- Joint stopping order: an over-budget head op names the source
    budget breach AND a refused head form refuses the target
    aggregation. Every premise is used by its own side. -/
theorem stoppReihenfolge (bound left : Nat) (op : Op) (rest : List Op)
    (p : HardwareProfil) (d : Decodiert) (tl : List Decodiert)
    (hSrc : ¬ op.cost ≤ left)
    (hTgt : schrittKosten p d = none) :
    (∃ needed, runOps bound left (op :: rest)
      = .budget "per_pass.ops" needed bound) ∧
    laufKosten p (d :: tl) = none := by
  constructor
  · rw [runOps_cons, if_neg hSrc]
    exact ⟨_, rfl⟩
  · exact laufKosten_kopf_verweigert p d tl hTgt

/-! ## 4. Obstructions: no free retry, no hidden stutter, no silent stop.

    A retry/spin step the profile refuses cannot hide behind a zero-cost
    premise; an unbounded retry site behind a constant bound refuses
    admission AND transfer; a successful aggregation names a cost for
    every executed step, so no executed step hides; a refusal projects
    observably apart from success, so no stop is silent. -/

/-- OBSTRUCTION (retry): an unbounded retry site behind a claimed bound
    refuses summary admission AND transfer admission together. A CAS
    retry loop is unbounded (`cas_schleife_unbeschraenkt`, used in the
    companion below); it never gets a free constant. -/
theorem kein_freier_versuch (s : CostSummary) (p : HardwareProfil)
    (k : Nat)
    (hRetry : s.retryBound = none)
    (hExpand : s.expand .retryTry = some k) :
    kostenSummeOk s = false ∧ zeitTransferZulaessig s p = false := by
  have h := kostenSummeOk_verweigert_unbegrenzt s k hRetry hExpand
  refine ⟨h, ?_⟩
  unfold zeitTransferZulaessig
  rw [h]
  simp

/-- OBSTRUCTION (no constant retry bound): for every claimed constant
    some retry count exceeds it. Waits and CAS retries never get a free
    cost or a constant bound -- any work bound that sums shape costs
    over a retired trace without a per-site proved attempt bound
    undercounts every spin loop, without bound. -/
theorem stutter_ohne_schranke (K : Nat) : ∃ n, K < casKosten n := by
  exact ⟨K + 1, by unfold casKosten; omega⟩

/-- OBSTRUCTION (hidden stutter): a successful aggregation names a cost
    for every prefix step -- an optimisation that introduces an
    unpriced (hidden) target step breaks aggregation success instead of
    hiding behind zero cost. -/
theorem optimierung_darf_nichts_verstecken (p : HardwareProfil)
    (xs : List Decodiert) (t : Nat)
    (hCost : laufKosten p xs = some t)
    (d : Decodiert) (hm : d ∈ xs) :
    ∃ c, schrittKosten p d = some c :=
  zeitTransfer_kosten_benannt p xs t hCost d hm

/-- OBSERVATION ORDER: a byte-step refusal projects to `fehler`, never
    to `ok` -- stops are observably distinct from success on both the
    source side (named `budget`/`hardware`/`abstieg` outcomes above) and
    the target side. No stop is silent. -/
theorem beobachtung_stopp_sichtbar (V : Sichtbar) (s : Zustand)
    (h : beobAusgang V (byteschritt s) = .fehler) :
    byteschritt s = .verweigert := by
  cases hbs : byteschritt s with
  | verweigert => rfl
  | weiter t =>
    have hne := beobAusgang_weiter_ungleich V t
    rw [hbs] at h
    exact absurd h hne

/-! ## 5. Joint witness on a non-degenerate source program.

    The fixture program `eP` writes table `konto` (proved by `rfl`);
    its reached run carries the entry world with slot `5` against a
    start of `0` -- a real memory-changing source run, not an empty one.
    Jointly with it: source budget within (exact leftover) AND source
    budget exhaustion (named outcome), the finite target run aggregating
    to time 7 AND executing to the proved store-changing state
    (register and memory byte observably moved from zero to 42), the
    transfer bound over unit source budget, the real source bound
    `kostenTiefF` plugging into the schema, and two planted refusals
    (unpriced `ret`, unbounded retry behind a constant). -/

/-- JOINT WITNESS: real store plus exhaustion on both sides, with the
    transfer bound and planted refusals, on a table-writing program. -/
theorem budgetAusfuehrung_zeuge :
    ∃ (M : RufMaschineG eD) (rho : Env eD (eD.params ePruefe))
      (w0 : World eD),
    RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
    (eSp.slots () 0 ()).n = 0 ∧
    (eD.signatur eSetze).schreibt () = true ∧
    RufEreignisF.eintritt ePruefe rho w0 ∈ (M.faeden 0).log ∧
    ReqAmEintritt eP ePruefe w0 rho ∧
    (w0.slots () 0 ()).n = 5 ∧
    runPass ⟨5⟩ [fremdOp 3] = .ok 1 ∧
    (∃ needed, runOps 3 3 [fremdOp 3]
      = .budget "per_pass.ops" needed 3) ∧
    laufKosten profilZeuge zeugeProg = some 7 ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => s.register Register.rbx) = some 42) ∧
    ((lauf zeugeProg zeugeZustand).map
      (fun s => s.speicher.bytes (BitVec.ofNat 64 8192))
      = some (BitVec.ofNat 8 42)) ∧
    (zeugeZustand.speicher.bytes (BitVec.ofNat 64 8192)
      = BitVec.ofNat 8 0) ∧
    (∀ k, expandBound blattSummary 1 = some k → 7 ≤ 3 * k) ∧
    laufKosten profilZeuge [{ befehl := Befehl.ret, laenge := 1 }]
      = none ∧
    kostenSummeOk { blattSummary with retryBound := none } = false ∧
    ∃ k, expandBound blattSummary
      (kostenTiefF eP (fun a : eD.Ax => nomatch a) 0 1 eSetze)
      = some k := by
  obtain ⟨M, hr, h0, rho, w0, hm, hreq, h5⟩ := ziel_ort_einfaden_zeuge
  have hCost : laufKosten profilZeuge zeugeProg = some 7 := by
    decide
  have hDeck : Deckung blattSummary 1 zeugeProg := by
    intro k hk
    rw [blattSummary_schranke] at hk
    cases hk
    decide
  have hT := budgetAusfuehrung_transfer blattSummary profilZeuge
    zeugeProg 1 3 7 hCost laufKosten_schranke_zeuge_hbound hDeck
  exact ⟨M, rho, w0, hr, h0, rfl, hm, hreq, h5, rfl,
    runOps_fremd_exceeds 3 3 3 (by omega), hCost,
    (zeuge_speicher_aendert_sich).1,
    (zeuge_speicher_aendert_sich).2.1,
    (zeuge_speicher_aendert_sich).2.2, hT, by decide, by decide,
    expandBound_gilt _ _ blattSummary_beschraenkt⟩

/- CUTS:
    - No lowering correspondence proved: `Deckung` is carried data.
      Which source step lowers to which target segment, with which
      multiplicity, is established by the lowering/IR producer. The
      single IR is absent (no `IR.lean` in the tree); deriving
      `Deckung` from validator acceptance via a generic `valX86_sound`
      is phase-B work. The transfer composes the two bounds; it never
      re-sums the expansion into a runtime claim.
    - No per-site exclusion proofs: `sourceCorresponds` stays carried
      data checked by `kostenSummeOk`; the positive correspondence per
      waiting site is phase-B work.
    - No cycle bounds: `t` counts named per-form bounds from the
      selected profile, never measured silicon latencies; `ret` stays
      refused (`none`).
    - No constant-time and no CAS-progress promise: the transfer bounds
      admitted finite prefixes only; unbounded retries are refused
      (`kein_freier_versuch`, `stutter_ohne_schranke`), never bounded.
    - Check elimination / inlining cost recomputation (`totalCost_anhang`
      pins the arithmetic the recomputation owes) is OPEN: removing a
      check changes budget timing.
    - No new target semantics: the one `Ausfuehrung.schritt` over the
      14 pilot forms, the one `laufKosten` aggregation and the one
      `beobAusgang` projection are reused untouched; no duplicated
      evaluator, no second cost model.
    - No checker/source change: nothing is tightened to ease proof;
      source stops are the actual `foreverLauf`/`rufAt`/`runOps`
      equations, target runs the actual `lauf`/`laufKosten` values.
-/

#print axioms forever_erschoepft_benannt
#print axioms rufAt_tiefe_erschoepft
#print axioms totalCost_anhang
#print axioms deckung_leer
#print axioms budgetAusfuehrung_transfer
#print axioms stoppReihenfolge
#print axioms kein_freier_versuch
#print axioms stutter_ohne_schranke
#print axioms optimierung_darf_nichts_verstecken
#print axioms beobachtung_stopp_sichtbar
#print axioms budgetAusfuehrung_zeuge

end Gabbro.Grammatik.X86
