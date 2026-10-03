# MUSE-REPORT-986: Exact review of author 836 (Composition closing: time-bound closing)

CANDIDATE: 836 6c73cdbbf351e3f22e2a2e313843709ba1ebcdc1
VERDICT: ACCEPT

## Clone/branch verification

Review clone `/home/simon/Dokumente/gabbro-muse/a986`, task branch `muse/986`.
Review materials were taken from the staged exact-review snapshot
`.tmp/review/` (no other clones touched, no network):
`SNAPSHOT.json` pins author 836 head
`6c73cdbbf351e3f22e2a2e313843709ba1ebcdc1` on base `e7c75908…`
(files: `MUSE-REPORT-836.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/ComposeTimeBound.lean`, clean tree).
PATCH, OWNER-TASK, MUSE-REPORT-836, BUILD-EVIDENCE and the staged
`ComposeTimeBound.lean` were each read in full. Owned file only:
`MUSE-REPORT-986.md`; no source or live-control changes.

## What the candidate does

New file `grammatik/Grammatik/X86/ComposeTimeBound.lean` (250 lines) plus
one import line in `grammatik/Grammatik.lean`. It closes the fuel-bounded
validation acceptance to the proved work/time transfer over the SAME
decoded list, reusing accepted legs only:

- PRODUCER (`ValidationBudget`, accepted): `decodeFuel fuel bs = some (xs, [])`
  implies `validAllFuel_some_empty` (full acceptance) and
  `decodeFuel_ins_le_fuel` (`xs.length <= fuel`).
- CONSUMER (`BudgetExecution`/`TimeTransfer`, accepted):
  `budgetAusfuehrung_transfer` over `Deckung` work coverage plus the named
  per-form hardware bound, with admission split by
  `zeitTransferZulaessig_braucht_ok`.
- TARGET `ComposeTimeBound_verbindung` is generic over arbitrary admitted
  `(s p fuel bs xs src B t)` with five premises, each used in the proof:
  `hDec` feeds `hValid` and `hLen`; `hAdm` feeds the admission halves;
  `hCost`/`hb`/`hDeck` feed `budgetAusfuehrung_transfer`. The conclusion
  (validation acceptance, both admission halves, count bound,
  `forall k, expandBound s src = some k -> t <= B * k`) is derived, not a
  premise restated; no existential-of-premise; no contract quantification.
- Three planted refusals are proved non-instances of three distinct
  premises, each reusing an accepted refusal lemma, nothing weakened:
  timeout (`wit_timeout_refuses`, fuel 1 vs `[natByte 195]`),
  unpriced `ret` (`laufKosten_zeuge_verweigert`, axiom-free),
  unbounded retry behind a constant (`zeitTransfer_verweigert_retry`).
- `zeugePush_aendert`: the composed single-`push64 rax` step from
  `zeugePushStart` (rax = 42) reaches a state whose stack byte at 8184
  observably differs — a real memory-changing `lauf` run of exactly the
  decoded/aggregated/bounded step (rsp starts at 8192 per `zeugeReg`;
  push stores toward 8184, consistent with the accepted push-ordering probe).
- Joint witness `ComposeTimeBound_verbindung_zeuge` instantiates all five
  premises jointly on admitted data (`blattSummary`, `profilZeuge`, fuel 2,
  `[natByte 80]`, single `push64 rax`, src 1, B 2, t 2) with `decide` legs,
  the derived conclusions via the TARGET itself, the table-writing source
  fixture's reached entry run (`ziel_ort_einfaden_zeuge`: slot 0 at start,
  5 at entry, `eSetze` writes by `rfl`), and the composed memory-changing
  run. Non-degenerate on both sides (source table write + target stack
  byte change); no empty run.

## Independent architecture checks (against this clone's accepted tree)

- Byte forms: 80 decodes to `push64` length 1 (`Codec.decode`: 80 <= n < 88
  via `codeReg (n - 80)`; `codeReg 0 = .rax`), 195 decodes to `ret`
  length 1; `wit_decode_ret` / `wit_timeout_refuses` confirm fuel-2 accept
  and fuel-1 timeout on `[195]`. The witness's `hDec`/`hCost`/`hb`
  (`push64 -> some 2`, `profilZeuge` MXCSR `0x1F80`) match
  `HardwareAssumptions.zeugekosten` (`push64 _ => some 2`, `ret => none`).
- `Deckung` is `∀ k, expandBound s src = some k -> targetWork … <= k`
  (`BudgetExecution.lean`); `blattSummary_schranke`
  (`expandBound blattSummary 1 = some 5`) with `targetWork [push] = 1`
  discharges `hDeck` honestly (1 <= 5 after casing on the rewritten
  equation). No tuning table enters: `expand` maxima stay backend-declared
  data checked by admission Bools, as claimed.
- `ret` stays refused (`none`); `zeitTransfer_verweigert_retry` kills the
  admission premise for `retryBound = none` behind `expand .retryTry`;
  `kostenSummeOk` exclusions stay carried. No per-site exclusion, cycle,
  constant-time, CAS-progress, cache/TLB/interrupt/fault or interleaving
  claim is made — CUTS names each with its owning lane, including the open
  per-access target-to-W/GX simulation bridge.
- No new interpreter/executor/cost model/semantics: the one `decodeFuel`
  traversal, one `laufKosten` aggregation, one `targetWork` count and the
  actual `lauf` runs are reused untouched. No diagnostic/gift/example/CLI
  numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/emitter or
  friend-reserved optimiser edits (PATCH confirms: only the new file, one
  import line, and the author report).
- Text scan of the staged file: no `sorry`, `admit`, `axiom`,
  `native_decide`, `unsafe`; no `Prop`-typed premise; no `intro _`-style
  premise discard. CUTS block plus `#print axioms` for all six names
  present as required.

## Evidence and reproduction status

- Author BUILD-EVIDENCE: `./lean-probe …/ComposeTimeBound.lean`
  `== 0 error(s)`; axiom prints
  (`verbindung` [propext, Quot.sound], timeout [propext], ret none,
  retry [propext], `zeugePush_aendert` [propext, Quot.sound],
  joint witness [propext, Classical.choice, Quot.sound] — all within
  standard); `./lean-bau` 509 jobs green incl. `Built …ComposeTimeBound`
  and `Built Grammatik`; `BeweisAtomar.lean` probe 0 errors with
  `gabbro_ziel` on `[propext, Classical.choice, Quot.sound]` unchanged.
  One honest intermediate 2-error probe (flat witness assembly mis-split)
  repaired via a separate `have hSrc` — verified in the evidence log.
- My own verification was read-level against the accepted producer
  interfaces in this clone (signatures of `validAllFuel_some_empty`,
  `decodeFuel_ins_le_fuel`, `budgetAusfuehrung_transfer`,
  `zeitTransferZulaessig_braucht_ok`, `zeitTransfer_verweigert_retry`,
  `blattSummary`/`blattSummary_schranke`, `profilZeuge`,
  `laufKosten_zeuge_verweigert`, `wit_timeout_refuses`,
  `ziel_ort_einfaden_zeuge`, `natByte`, `zeugeZustand`/`zeugeReg` all
  confirmed). No premise looked suspicious on inspection, so no queued
  reproduction run was triggered; per the report-only ownership I did not
  apply the PATCH (non-owned files) and therefore do not claim a fresh
  `./lean-bau` of the candidate in this clone. The staged
  `./lean-probe`/`./lean-bau` evidence plus the signature-level reuse
  check is the basis of this ACCEPT.

## Bounded acceptance / what is NOT closed

- `Deckung` stays carried data: which source step lowers to which target
  segment with which multiplicity comes from the lowering/IR producer
  (`DerivedWorkBound` for its fragment; generic validator soundness is
  phase-B work). `sourceCorresponds` per waiting site likewise stays
  carried. `t` counts named per-form bounds from the selected profile,
  never measured silicon latencies. Finite admitted prefixes only;
  unbounded retries refused, never bounded. Bytes are model `Byte` lists,
  memory model `Speicher`; TSO/bridge, faults, interrupts, concurrency
  stay with their owners. The file's CUTS state exactly this; the claim
  boundary is precise and I find no fake closure or guarantee weakening
  and no desired-correctness premise smuggled in as an assumption.

## Task assessment

Nothing in the owner task statement appears wrong. The ZEUGE target
(`ComposeTimeBound_verbindung` + jointly inhabited, non-degenerate,
memory-changing `_zeuge`) is met as stated within the bounded scope above.
Minimal-repair set: none.
