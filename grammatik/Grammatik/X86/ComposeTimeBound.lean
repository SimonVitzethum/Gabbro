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

/-! ## Planted refusals: timeout, unpriced form, unbounded retry.

    Each refusal below is a proved non-instance of the closing theorem:
    exhausted fuel admits no decoded prefix, the unpriced `ret` form
    admits no aggregation, and an unbounded retry site behind a constant
    bound kills the admission premise. Nothing is weakened to make the
    closing go through. -/

/-- PLANTED REFUSAL (timeout): fuel 1 admits no decoded prefix of the
    one-byte program that needs fuel 2 -- timeout never accepts, so the
    closing theorem has no instance there. Both premises pin the refused
    shape: `hFuel` the budget, `hBs` the program. -/
theorem ComposeTimeBound_verweigert_timeout (fuel : Nat) (bs : List Byte)
    (hFuel : fuel = 1) (hBs : bs = [natByte 195]) :
    ¬ ∃ xs, decodeFuel fuel bs = some (xs, []) := by
  subst hFuel
  subst hBs
  obtain ⟨hne, _⟩ := wit_timeout_refuses
  intro ⟨xs, hx⟩
  rw [hx] at hne
  cases hne

/-- PLANTED REFUSAL (unpriced form): the lone `ret` admits no successful
    aggregation -- `ret` carries no named constant bound, so the closing
    theorem's cost premise has no instance there. -/
theorem ComposeTimeBound_verweigert_ret :
    ¬ ∃ t, laufKosten profilZeuge
      [{ befehl := Befehl.ret, laenge := 1 }] = some t := by
  intro ⟨t, ht⟩
  have h := laufKosten_zeuge_verweigert
  rw [ht] at h
  cases h

/-- PLANTED REFUSAL (unbounded retry): an unbounded retry site behind a
    claimed constant bound kills the admission premise -- a CAS retry
    loop never gets a free constant, so the closing theorem has no
    instance there. All three premises are used: `hRetry`/`hExpand` feed
    the accepted transfer refusal, `hAdm` the contradiction. -/
theorem ComposeTimeBound_verweigert_retry (s : CostSummary)
    (p : HardwareProfil) (k : Nat)
    (hRetry : s.retryBound = none)
    (hExpand : s.expand .retryTry = some k)
    (hAdm : zeitTransferZulaessig s p = true) :
    False := by
  have h := zeitTransfer_verweigert_retry s p k hRetry hExpand
  rw [hAdm] at h
  cases h

/-! ## Memory-changing run through the composed step.

    The composed step below is one canonical `push` of 42 (canonical
    byte `80` in): the reached run observably changes the stack byte,
    so the closing is execution evidence, never a conjunction of checks
    alone. The source side reuses the accepted table-writing fixture in
    the joint witness below. -/

/-- Witness start: the canonical state with `rax` holding 42. -/
def zeugePushStart : Zustand :=
  { zeugeZustand with register := regSet zeugeReg Register.rax 42 }

/-- The composed single-`push` step reaches a state whose stack byte
    observably differs from the start: a real memory-changing run of
    exactly the step the closing witness decodes, aggregates and bounds. -/
theorem zeugePush_aendert :
    ∃ s', lauf [{ befehl := Befehl.push64 Register.rax, laenge := 1 }]
      zeugePushStart = some s' ∧
      s'.speicher.bytes (BitVec.ofNat 64 8184) ≠
        zeugePushStart.speicher.bytes (BitVec.ofNat 64 8184) := by
  refine ⟨_, rfl, by decide⟩

/-! ## Joint witness: every premise together, non-degenerate.

    All five premises of `ComposeTimeBound_verbindung` on jointly
    admitted concrete data (admitted leaf summary, admitted witness
    profile, canonical `push`-of-42 byte under fuel 2, unit source
    budget, per-step bound 2, aggregated time 2), with the derived
    validation acceptance, admission halves, count bound and time bound;
    jointly with the table-writing source fixture's reached entry run
    (slot `0` at start, `5` at entry -- a real memory-changing source
    run, not an empty one) and the composed step's own memory-changing
    reached run above. -/

/-- JOINT WITNESS: admitted bounded memory-changing run with the
    composed time bound, on a table-writing program. -/
theorem ComposeTimeBound_verbindung_zeuge :
    ∃ (s : CostSummary) (p : HardwareProfil) (fuel : Nat) (bs : List Byte)
      (xs : List Decodiert) (src B t : Nat),
      decodeFuel fuel bs = some (xs, []) ∧
      zeitTransferZulaessig s p = true ∧
      laufKosten p xs = some t ∧
      (∀ d ∈ xs, ∃ c, schrittKosten p d = some c ∧ c ≤ B) ∧
      Deckung s src xs ∧
      validAllFuel fuel bs = true ∧
      kostenSummeOk s = true ∧ profilGueltig p = true ∧
      xs.length ≤ fuel ∧
      (∀ k, expandBound s src = some k → t ≤ B * k) ∧
      (∃ (M : RufMaschineG eD) (rho : Env eD (eD.params ePruefe))
        (w0 : World eD),
        RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
        (eSp.slots () 0 ()).n = 0 ∧
        (eD.signatur eSetze).schreibt () = true ∧
        RufEreignisF.eintritt ePruefe rho w0 ∈ (M.faeden 0).log ∧
        ReqAmEintritt eP ePruefe w0 rho ∧
        (w0.slots () 0 ()).n = 5) ∧
      (∃ s', lauf [{ befehl := Befehl.push64 Register.rax, laenge := 1 }]
        zeugePushStart = some s' ∧
        s'.speicher.bytes (BitVec.ofNat 64 8184) ≠
          zeugePushStart.speicher.bytes (BitVec.ofNat 64 8184)) := by
  have hDec : decodeFuel 2 [natByte 80]
      = some ([⟨Befehl.push64 Register.rax, 1⟩], []) := by
    decide
  have hAdm : zeitTransferZulaessig blattSummary profilZeuge = true := by
    decide
  have hCost : laufKosten profilZeuge
      [{ befehl := Befehl.push64 Register.rax, laenge := 1 }]
      = some 2 := by
    decide
  have hb : ∀ d ∈ [{ befehl := Befehl.push64 Register.rax, laenge := 1 }],
      ∃ c, schrittKosten profilZeuge d = some c ∧ c ≤ 2 := by
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    exact ⟨2, rfl, Nat.le_refl 2⟩
  have hDeck : Deckung blattSummary 1
      [{ befehl := Befehl.push64 Register.rax, laenge := 1 }] := by
    intro k hk
    rw [blattSummary_schranke] at hk
    cases hk
    decide
  have hC := ComposeTimeBound_verbindung blattSummary profilZeuge 2
    [natByte 80] [{ befehl := Befehl.push64 Register.rax, laenge := 1 }]
    1 2 2 hDec hAdm hCost hb hDeck
  obtain ⟨hValid, hOk, hProf, hLen, hT⟩ := hC
  obtain ⟨M, hr, h0, rho, w0, hm, hreq, h5⟩ := ziel_ort_einfaden_zeuge
  have hSrc : (∃ (M : RufMaschineG eD) (rho : Env eD (eD.params ePruefe))
      (w0 : World eD),
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      (eSp.slots () 0 ()).n = 0 ∧
      (eD.signatur eSetze).schreibt () = true ∧
      RufEreignisF.eintritt ePruefe rho w0 ∈ (M.faeden 0).log ∧
      ReqAmEintritt eP ePruefe w0 rho ∧
      (w0.slots () 0 ()).n = 5) :=
    ⟨M, rho, w0, hr, h0, rfl, hm, hreq, h5⟩
  exact ⟨_, _, _, _, _, _, _, _, hDec, hAdm, hCost, hb, hDeck,
    hValid, hOk, hProf, hLen, hT, hSrc, zeugePush_aendert⟩

/- CUTS:
    - Proved here, by composition over accepted modules only: the
      fuel-bounded validation acceptance (`decodeFuel` yields `xs` with
      no rest, `validAllFuel`, `xs.length ≤ fuel`) tied to the proved
      work/time transfer (`Deckung` coverage plus the named per-form
      hardware bound give `t ≤ B * k`) over the SAME decoded list;
      admission halves (`kostenSummeOk`, `profilGueltig`); three planted
      refusals (fuel timeout, unpriced `ret`, unbounded retry behind a
      constant); one memory-changing reached run of the composed step
      (canonical `push` of 42) and the joint witness on the
      table-writing source fixture with its reached entry run.
    - NOT proved here, and not claimed:
      - No lowering correspondence: `Deckung` stays carried data. Which
        source step lowers to which target segment, with which
        multiplicity, is established by the lowering/IR producer
        (DerivedWorkBound derives it for the covered fragment; the
        generic validator-soundness leg is phase-B work with the
        decoder/bridge lanes).
      - No per-site exclusion proofs: `sourceCorresponds` stays carried
        data checked by `kostenSummeOk`; the positive correspondence per
        waiting site is phase-B work.
      - No cycle bounds: `t` counts named per-form bounds from the
        selected profile, never measured silicon latencies; `ret` stays
        refused (`none`); tuning tables never enter the proof.
      - No constant-time and no CAS-progress promise: the closing bounds
        admitted finite prefixes only; unbounded retries are refused,
        never bounded.
      - No full hardware model: bytes are model `Byte` lists, memory the
        model `Speicher`; caches, TLBs, store buffers, interrupts,
        faults and concurrency interleavings stay with their owners
        (TSO/bridge lanes own the per-access target-to-W/GX simulation).
      - No new interpreter, no second cost model, no new semantics: the
        one `decodeFuel` traversal, the one `laufKosten` aggregation,
        the one `targetWork` count and the actual `lauf` runs are reused
        untouched. No checker, Spec, goal, emitter or friend-reserved
        file is touched; no new diagnostic/gift/example/CLI numbers.
-/

#print axioms ComposeTimeBound_verbindung
#print axioms ComposeTimeBound_verweigert_timeout
#print axioms ComposeTimeBound_verweigert_ret
#print axioms ComposeTimeBound_verweigert_retry
#print axioms zeugePush_aendert
#print axioms ComposeTimeBound_verbindung_zeuge

end Gabbro.Grammatik.X86
