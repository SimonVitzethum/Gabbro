# MUSE-REPORT-1043: Exact review of author 893 (address-mode selection rule)

## CANDIDATE / VERDICT

- CANDIDATE: 893 efb8c9bb1fe1af21c6ea89f9c12292d3e94070e1
- VERDICT: ACCEPT (bounded — see "Acceptance boundary")

Reviewer clone verified: `/home/simon/Dokumente/gabbro-muse/a1043`, branch
`muse/1043`, HEAD `b040b155159f47629542b0083e2f0a8a607f2b4c`, which equals the
snapshot base. The candidate file is absent from this tree (expected: review
against the pinned snapshot in `.tmp/review/author-893/`). No source file was
touched by this review; the only owned file is this report.

## What was reviewed

Pinned snapshot (`.tmp/review/SNAPSHOT.json`): 3 files —
`MUSE-REPORT-893.md`, `grammatik/Grammatik.lean` (one added import line after
`OptFoldConst`, verified), `grammatik/Grammatik/X86/OptAddrModeSel.lean`
(509 lines, read in full). Also read: `OWNER-TASK.md` (task text, ZEUGE line)
and `BUILD-EVIDENCE.json` (queued-wrapper history: repeated `./lean-probe`
runs including two red intermediates that were repaired, final `./lean-bau`
`== exit 0; 0 error line(s)`, `Build completed successfully (511 jobs)`).

## Findings (all checked against the base tree, not just Lean-green)

1. HARD RULES: clean. Substring-aware scan of the candidate finds no `sorry`,
   `admit` (only English "admitted/admission" in comments), `axiom`,
   `native_decide`, `unsafe`, `intro _`, or `have _ :=`. Axiom report from the
   author's final probe matches the standard `gabbro_ziel` set: worst case
   `OptAddrModeSel_verbindung_zeuge` depends on exactly
   `[propext, Classical.choice, Quot.sound]`; the connection on
   `[propext, Quot.sound]`; several lemmas on nothing. Every premise of every
   theorem is used in its proof (traced: `hEq`/`hz` feed `addrSel_wert`;
   `hA`/`hN`/`hW` feed `addrSel_lea`; all seven premise groups feed the seven
   conjuncts of `OptAddrModeSel_verbindung`). No premise has type `Prop`
   itself. No new diagnostic/gift/example/CLI numbers, no MARKE changes, no
   source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.
2. Architecture (checked against `AddressEncoding.lean` in this base and the
   supplied Intel SDM snapshot 325462-093US): the candidate invents no
   hardware semantics — it reuses `adrEff`, `dispWortArt`, `passtIn8`,
   `kompaktArt`/`kompaktArt_klein`, `fussZugelassen`, `leaFormSchritt` plus
   its `dst`/`flags`/`speicher` projection lemmas, `ripForm`,
   `adrEff_rip_prestate`, and `adrOk`, all present with the claimed
   signatures. `adrOk` already encodes the SDM constraints (RIP-relative only
   as disp32 without registers; `rbp`/`r13` never displacement-less;
   `rsp` never an index); LEA flag/memory non-effects match the SDM (LEA
   affects no flags, performs no memory access). `passtIn8` checks the true
   signed-byte range. SIB is covered generically (arbitrary base/index/scale;
   witness uses scale-8 over `r8`/`r9`, i.e. REX registers). Width-confusion
   pin present (`0xFF` reads as `-1`, never `255`).
3. Witness: `OptAddrModeSel_verbindung_zeuge` instantiates ALL premises
   jointly at `r8`/`r9`/scale-8/displacement-0, selects `8200`
   (= 8192 + 1*8 + 0; `storeWitReg` gives `r8 = 8192`, `r9 = 1`, `rax = 42`,
   confirmed in base), steps both LEA sides from length 5, lands the wide
   write of `42` via `write64`, on table-writing `refD` (`refEin_schreibt`,
   confirmed) beside the reached memory-changing run `MB`
   (`refB_erreicht` + `refB_schreibt`, slot 0: 0 -> 100, confirmed).
   Non-degeneracy requirement satisfied. `hEq`/`hK` discharged by `decide`
   at the concrete site; the `fun _ =>` weakening to the conditional form is
   benign (unconditional decided fact plus jointly proved admission).
4. Refusals: all four DESIGN failure cases proved as theorems
   (`gross`, `umbruch`, `ripFremd`, `ohneNachpruefung`) with `decide` pins
   for ok/gross/ohneNachpruefung plus the RIP-with-registers `adrOk`
   refusal pin. Umbruch/ripFremd have theorems but no `decide` pins — minor,
   theorems are machine-checked.
5. No guarantee weakening, no desired-simulation premise: `hEq`/`hK` are
   per-site recomputation obligations conditional on admission (a merely
   trusted width never selects, stated in comments); source-level contracts
   and call logs are covered by read/write/LEA outcome agreement, and the
   report honestly states no source simulation is claimed (lowering lanes
   own it). CUTS lists exactly what is not proved (silicon, encoder round
   trip, source correspondence, TSO/GX, whole image) with `#print axioms`
   for every theorem.

## Bounded weaknesses (disclosed, not verdict-changing)

- (a) `addrSel_gleit_unberuehrt` (and the connection's IEEE conjunct) is the
  tautology `gleitPasst … = gleitPasst …` by `rfl`: true, but it formalises
  no float-state non-interference (e.g. no FP-component equality). Acceptable
  as bounded: neither LEA nor address computation touches FP/MXCSR state, no
  such state is in the touched path, and the author labels it non-interference
  "stated as such" with "no rounding scope claimed".
- (b) `DispArt.kein` (disp0) is outside the connection, which relates
  `.d8`↔`.d32` only. This matches the reused canonical `kompaktArt`, which
  never returns `.kein`; zero-displacement elision belongs to the encoder
  row, not this rule. Claim does not exceed proof.
- (c) `keinUmbruch`/`ripBildOk`/`nachgeprueft` are validator Bools without
  kernel-recomputed citations (only displacement has `hEq`/`hK`). Soundness
  is unaffected (preservation follows from address equality either way) and
  the refusal direction is proved; patch-byte re-decoding belongs to the
  fetch/patch lanes' rows.
- (d) `probe_addrSel_ersparnis` states `≤` rather than the 3-byte saving the
  canonical `kompakt_ersparnis` gives — true but weak.

## Acceptance boundary

ACCEPT covers: validator-admitted narrow↔wide value/fault/observation
agreement, the four admission-Bool refusals, byte-form choice for fitting
displacements, and the joint non-degenerate witness. It does NOT cover
silicon correspondence, encoder round trips, source simulation, TSO/GX, or
whole-image validation — all explicitly excluded in CUTS.

## Reproduction note

No reproduction build was run in this tree: the review owns only this report
and the candidate is not applied here (applying it would exceed ownership).
Green evidence is the author's queued-wrapper history at the pinned commit
(`./lean-bau` exit 0, 0 errors, 511 jobs; per-file `./lean-probe` 0 errors).
Base-vocabulary cross-checks above were done by read-only inspection of this
clone at the snapshot base. Working tree left clean apart from this report.
