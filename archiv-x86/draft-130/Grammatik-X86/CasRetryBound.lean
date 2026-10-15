/-
  File:      Grammatik/X86/CasRetryBound.lean
  Subject:   Static CAS retry attempt bound derived from contention
    structure, with per-program DIVERGENCE where contention is unknown.

  Lane 784 (hardware completion): one bounded-or-divergent retry discipline
  over the accepted single-attempt steps (`LockedOps.casSchritt`, the
  `LockedInstructionExecution` LOCK CMPXCHG rows). A terminating retry trace
  `fs ++ [true]` whose failures charge against at most `n` distinct foreign
  installers runs at most `n + 1` attempts; the cost summary carrying the
  derived bound names exactly `some (n + 1)`. Unknown contention derives
  `none` (recorded DIVERGENCE, never a free constant) and refuses every
  claimed constant through the accepted refusals. No new interpreter, no new
  decoder, no cycle claim, no source/checker/goal change.

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`,
  Intel SDM 325462-093US September 2026):
  - CMPXCHG compare-and-exchange, Vol. 2A 3-194 (txt line 46967): REX.W +
    0F B1/r compares RAX with r/m64; equal sets ZF and loads the source
    into the destination, else clears ZF and loads the destination into
    RAX. With LOCK the instruction executes atomically; the destination
    receives a write cycle regardless of the comparison result.
  - LOCK prefix, Vol. 2A 3-565 (txt line 63495): LOCK may prepend to
    CMPXCHG (among others) with a memory destination; the processor then
    has exclusive use of the shared memory for the instruction duration.
  - What the manual does NOT give: any bound on SOFTWARE retry loops.
    One attempt is atomic; how many attempts a loop needs depends on
    contention, which is a program property carried here as checked data.
-/
import Grammatik.X86.LockedOps
import Grammatik.X86.CostSummary
import Grammatik.X86.BudgetExecution
import Grammatik.X86.LockedInstructionExecution
import Grammatik.ZielOrtEinfadenZeuge

namespace Gabbro.Grammatik.X86

/-- Contention structure at one CAS retry site, as checked data: either a
    bound on distinct foreign installers overlapping the retry window, or
    unknown. Unknown records per-program DIVERGENCE; it never defaults to
    a constant. -/
inductive Contention where
  | begrenzt (fremd : Nat)
  | unbekannt
  deriving DecidableEq, Repr

/-- Static retry bound derived from contention: `n` distinct foreign
    installers admit at most `n + 1` attempts (each failure charges to a
    distinct installer, the final attempt succeeds); unknown contention is
    `none` = recorded DIVERGENCE, never a free constant. -/
def retryBoundOf : Contention → Option Nat
  | .begrenzt n => some (n + 1)
  | .unbekannt => none

/-- A bounded contention derives exactly `some (n + 1)`: the static bound
    is computed from the structure, never a free constant. -/
theorem retryBoundOf_begrenzt (n : Nat) :
    retryBoundOf (.begrenzt n) = some (n + 1) := rfl

/-- Unknown contention derives `none`: recorded DIVERGENCE, never zero
    and never a guessed constant. -/
theorem retryBoundOf_unbekannt : retryBoundOf .unbekannt = none := rfl

/-- Failure count of one retry trace: `false` is a failed attempt (the
    accepted stutter), `true` the terminating success. A pure count over
    outcome lists, not a cost model and not an interpreter. -/
def fehlZaehler : List Bool → Nat
  | [] => 0
  | false :: rest => fehlZaehler rest + 1
  | true :: rest => fehlZaehler rest

/-- Charging lemma: when every entry before the final success is a
    failure, the failure count of the whole trace is the prefix length.
    Both premises shape the count: `hFail` discharges every match arm of
    `fehlZaehler`, so the charge is exact, never estimated. -/
theorem fehlZaehler_angehaengt (fs : List Bool)
    (hFail : ∀ b ∈ fs, b = false) :
    fehlZaehler (fs ++ [true]) = fs.length := by
  induction fs with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : hd = false := hFail hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ b ∈ tl, b = false :=
      fun b hm => hFail b (List.mem_cons.mpr (Or.inr hm))
    have hi := ih htl
    subst hhd
    show fehlZaehler (tl ++ [true]) + 1 = tl.length + 1
    exact congrArg (· + 1) hi

/-- CONNECTION (derived static retry bound): a terminating retry trace
    `bs = fs ++ [true]` (failures then one success) whose failures charge
    against at most `n` distinct foreign installers (`hCharge`) runs at
    most `n + 1` attempts, and the cost summary carrying the derived bound
    names exactly `some (n + 1)` -- never a free constant. Every premise is
    used: `hForm` fixes the trace shape, `hFail` the failure identity
    feeding the exact charge count, `hCharge` the contention bound,
    `hBound` the summary linkage. -/
theorem CasRetryBound_verbindung (bs fs : List Bool) (n : Nat)
    (s : CostSummary)
    (hForm : bs = fs ++ [true])
    (hFail : ∀ b ∈ fs, b = false)
    (hCharge : fehlZaehler bs ≤ n)
    (hBound : s.retryBound = retryBoundOf (.begrenzt n)) :
    bs.length ≤ n + 1 ∧ s.retryBound = some (n + 1) ∧
      casKosten bs.length ≤ n + 2 := by
  have hzaehl := fehlZaehler_angehaengt fs hFail
  rw [hForm] at hCharge ⊢
  rw [hzaehl] at hCharge
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [hBound]; rfl
  · unfold casKosten
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- DIVERGENCE (no free constant): unknown contention derives `none`,
    and for every claimed constant some retry count exceeds it -- the
    accepted unboundedness (`stutter_ohne_schranke`), reused, never
    re-proved. A program without contention structure gets a recorded
    divergence, never a guessed bound. -/
theorem casDivergenz_ohne_schranke (K : Nat) :
    retryBoundOf .unbekannt = none ∧ ∃ n, K < casKosten n :=
  ⟨rfl, stutter_ohne_schranke K⟩

/-- DIVERGENCE refuses admission: a summary that claims a finite
    `retryTry` expansion while carrying unknown (divergent) contention is
    refused by the validator Bool -- the accepted refusal
    (`kostenSummeOk_verweigert_unbegrenzt`), reused. Both premises are
    used: `hDiv` turns the recorded divergence into the `none` the refusal
    needs, `hExpand` exhibits the disallowed constant claim. -/
theorem casDivergenz_verweigert_summe (s : CostSummary) (k : Nat)
    (hDiv : s.retryBound = retryBoundOf .unbekannt)
    (hExpand : s.expand .retryTry = some k) :
    kostenSummeOk s = false := by
  have hNone : s.retryBound = none := by rw [hDiv]; rfl
  exact kostenSummeOk_verweigert_unbegrenzt s k hNone hExpand

/-- EXECUTED two-attempt retry (failure then success) over the accepted
    single-attempt steps, reusing the joint witnesses: expecting 5 against
    word 0 stutters (`cas_fehlschlag_zeuge`), then expecting 0 installs 9
    with read-back 9, and the pair observably changes canonical memory.
    This is the executed shape the outcome list `[false, true]` stands
    for -- no second evaluator, no redefined step. -/
theorem casWiederholung_ausgefuehrt :
    casSchritt lockAddr 5 9 0 lockStart = some (lockStart, false) ∧
    casSchritt lockAddr 0 9 0 lockStart = some (casNach, true) ∧
    read64 casNach.mem lockAddr = some 9 ∧
    lockStart.mem.bytes lockAddr ≠ casNach.mem.bytes lockAddr := by
  refine ⟨cas_fehlschlag_zeuge, by rfl, by decide, by decide⟩

/-- The executed pair has the terminating-trace shape with exactly one
    charged failure: the list the main connection bounds. -/
theorem casWiederholung_form :
    [false, true] = [false] ++ [true] ∧
    (∀ b ∈ [false], b = false) ∧
    fehlZaehler [false, true] = 1 := by
  refine ⟨rfl, by decide, rfl⟩

/-- FETCHED grounding: a CAS attempt runs through the fetched LOCK path,
    never through the unified pilot dispatcher -- the accepted dispatch
    (`decodeLockExt_lock`), reused: LOCK CMPXCHG bytes are refused by
    `decodeExt` and taken only where it refuses, so no pilot form is
    shadowed and no attempt hides behind a pilot row. Both premises are
    used: `h1` routes past the pilot dispatcher, `h2` takes the lock row. -/
theorem casLaeuft_ueber_lock (bs : List Byte) (a : LockAnweisung)
    (rest : List Byte)
    (h1 : decodeExt bs = none)
    (h2 : decodeLock bs = some (a, rest)) :
    decodeLockExt bs = some (a, rest) ∧ decodeExt bs = none :=
  ⟨decodeLockExt_lock bs a rest h1 h2, h1⟩

/-- Joint witness: the closed LOCK CMPXCHG bytes are refused by the pilot
    dispatcher and taken whole by the combined decode -- the accepted pins
    (`pin_lock_ext_verweigert_cmpxchg`, `pin_lock_cmpxchg_decodiert`),
    jointly instantiated. -/
theorem casLaeuft_ueber_lock_zeuge :
    ∃ (a : LockAnweisung) (rest : List Byte),
      decodeLockExt pinCmpxchg = some (a, rest) ∧
        decodeExt pinCmpxchg = none :=
  ⟨_, _, casLaeuft_ueber_lock pinCmpxchg _ _
    pin_lock_ext_verweigert_cmpxchg pin_lock_cmpxchg_decodiert⟩

/-- JOINT WITNESS for `CasRetryBound_verbindung`: all its premises hold
    together on one failure plus one success charged against one foreign
    installer, with the derived summary bound -- jointly with the
    non-degenerate package: the fixture program writes a table, its
    reached run moves the slot `0 -> 5`, and the executed CAS pair changes
    canonical memory. No empty run, no table-free program. -/
theorem CasRetryBound_verbindung_zeuge :
    ∃ (bs fs : List Bool) (n : Nat) (s : CostSummary)
      (M : RufMaschineG eD) (rho : Env eD (eD.params ePruefe))
      (w0 : World eD),
      (bs = fs ++ [true]) ∧
      (∀ b ∈ fs, b = false) ∧
      (fehlZaehler bs ≤ n) ∧
      (s.retryBound = retryBoundOf (.begrenzt n)) ∧
      (bs.length ≤ n + 1 ∧ s.retryBound = some (n + 1) ∧
        casKosten bs.length ≤ n + 2) ∧
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      (eSp.slots () 0 ()).n = 0 ∧
      (eD.signatur eSetze).schreibt () = true ∧
      RufEreignisF.eintritt ePruefe rho w0 ∈ (M.faeden 0).log ∧
      ReqAmEintritt eP ePruefe w0 rho ∧
      (w0.slots () 0 ()).n = 5 ∧
      casSchritt lockAddr 0 9 0 lockStart = some (casNach, true) ∧
      lockStart.mem.bytes lockAddr ≠ casNach.mem.bytes lockAddr := by
  obtain ⟨M, hr, h0, rho, w0, hm, hreq, h5⟩ := ziel_ort_einfaden_zeuge
  have hConn := CasRetryBound_verbindung [false, true] [false] 1
    { blattSummary with retryBound := retryBoundOf (.begrenzt 1) }
    rfl (by decide) (by decide) rfl
  obtain ⟨_, hsucc, _, hdiff⟩ := casWiederholung_ausgefuehrt
  refine ⟨[false, true], [false], 1,
    { blattSummary with retryBound := retryBoundOf (.begrenzt 1) },
    M, rho, w0, rfl, by decide, by decide, rfl, hConn,
    hr, h0, rfl, hm, hreq, h5, hsucc, hdiff⟩

/-- Joint witness for the divergence refusal: the admitted leaf summary
    with its retry bound replaced by the recorded DIVERGENCE still claims
    a finite `retryTry` expansion, so the validator Bool refuses it --
    jointly with the unboundedness fact. No constant is guessed. -/
theorem casDivergenz_verweigert_summe_zeuge :
    (kostenSummeOk { blattSummary with retryBound :=
      (retryBoundOf .unbekannt) } = false) ∧
    (∃ n, 5 < casKosten n) ∧
    retryBoundOf .unbekannt = none :=
  ⟨casDivergenz_verweigert_summe _ 5 rfl rfl,
    (casDivergenz_ohne_schranke 5).2, rfl⟩

/- CUTS:
   - Proved here: the contention datatype with the derived static bound
     (`retryBoundOf_begrenzt`: `n` installers give `some (n + 1)`;
     `retryBoundOf_unbekannt`: unknown gives `none`); the exact failure
     charge (`fehlZaehler_angehaengt`); the connection
     (`CasRetryBound_verbindung`: a terminating trace charged against `n`
     installers runs at most `n + 1` attempts with shape cost at most
     `n + 2`, and the carrying summary names `some (n + 1)`); the
     divergence side (`casDivergenz_ohne_schranke`: no free constant;
     `casDivergenz_verweigert_summe`: a divergent summary claiming a
     finite expansion is refused); the executed grounding
     (`casWiederholung_ausgefuehrt`: a real failure-stutter plus a
     memory-changing install over the accepted `casSchritt`, with the
     trace shape `casWiederholung_form`); the fetched-byte routing
     (`casLaeuft_ueber_lock`: LOCK CMPXCHG bytes run through the fetched
     LOCK path, never the pilot dispatcher); joint witnesses for the
     connection (on the table-writing fixture with its `0 -> 5` reached
     run plus the memory-changing CAS install), the refusal, and the
     dispatch pins.
   - NOT proved here, and not claimed:
     - No per-site contention proof: which program points share a retry
       site and how many distinct foreign installers overlap its window
       is established by the lowering/certificate producer as checked
       data (`Contention`), never derived here.
     - No fairness, progress or termination promise: a divergent site may
       spin forever; `FortschrittG`/liveness transfer stays with its
       owner. The bound covers terminating traces only.
     - No hardware timing: `casKosten` counts shape units (attempts plus
       outcome), never cycles; LOCK latency needs named assumptions plus
       the proved work transfer (bridge lanes own it).
     - No TSO/W/GX refinement: the per-access target-to-W/GX simulation
       stays with the bridge; this module reuses the accepted
       single-attempt steps and adapters without restating them.
     - No fault claim: architectural faults (#UD on LOCK misuse,
       permission faults) stay with `DecodeFault`/`HardwareFaults`; the
       failure path here is the accepted stutter/write-back pair, whose
       exact observable difference the failure adapter already pins.
     - No new decoder, evaluator, cost model or IR: the one `casSchritt`,
       the one `decodeLockExt`/`decodeExt` dispatch, the one
       `kostenSummeOk` Bool and the one `targetWork`/`casKosten` count are
       reused untouched.
     - No source, checker, contract, budget, goal or emitter change:
       nothing here speaks about `Vertrag`, `Stmt`, duties, `gabbro_ziel`
       or emitted bytes; no diagnostic/gift/example/CLI number is minted
       and no emission counter moves.
-/

#print axioms retryBoundOf_begrenzt
#print axioms retryBoundOf_unbekannt
#print axioms fehlZaehler_angehaengt
#print axioms CasRetryBound_verbindung
#print axioms CasRetryBound_verbindung_zeuge
#print axioms casDivergenz_ohne_schranke
#print axioms casDivergenz_verweigert_summe
#print axioms casDivergenz_verweigert_summe_zeuge
#print axioms casWiederholung_ausgefuehrt
#print axioms casWiederholung_form
#print axioms casLaeuft_ueber_lock
#print axioms casLaeuft_ueber_lock_zeuge

end Gabbro.Grammatik.X86
