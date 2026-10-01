# MUSE-REPORT-585: Independent exact-candidate connection review of 567

Lane 585, branch `muse/585`, clone `/home/simon/Dokumente/gabbro-muse/a585`.
Owns only this report. Candidate: author 567, pinned HEAD
`32cd4f6f81c8f8ba7a5bae6c79b7121e8daa6f54` (base `8596f83e`),
files `MUSE-REPORT-567.md`, `grammatik/Grammatik.lean` (one additive
import), `grammatik/Grammatik/X86/TSOHistory.lean` (new, 346 lines).

## What was reviewed

Owner task (lane 567): the ONE reusable target-to-Sicht history/view
projection over canonical `TSOZustand` (`issueByte`, `loadByte`,
`flushKern`), instantiated at `Adresse`/`Byte`, for consumers
BridgeWrite573 and BridgeRead574. Required: real finite issue/flush
sequences building fresh source messages, FIFO-consistent observations,
explicit youngest-own-store forwarding with views, a reached two-core
memory-changing joint witness, a forbidden foreign-drain/tearing example,
and a stable producer interface. Address/Byte is an intermediate layer;
typed-carrier W/GX mapping and multi-byte atomicity stay explicit cuts.

## Checks performed

- Read the full candidate module, the owner task, the owner report, the
  `PATCH.diff` and the `BUILD-EVIDENCE.json` in `.tmp/review/author-567/`.
- Resolved every reused name against live master in this clone:
  `TSOZustand`, `TSOEintrag`, `pufferSetze` (+`_gleich`/`_anders`),
  `issueByte`, `neuestens`, `loadByte`, `flushKern`, `zaunBereit`,
  `TSOSchritt`/`TSOErreichbar`, `issue_kein_speicher`,
  `flush_schreibt_kopf`, `load_ohne_eintrag`, `fifo_reihenfolge`,
  `paket_reisst`, `sbX/sbY/sbEins/sbStart/sbNach1/sbNach2/sbGespült`,
  `sb_schritt1/sb_schritt2/sb_beide_laden_null/sb_flush_schritt/
  sb_flush_aendert_speicher/sbX_ne_sbY`, `zeugenSpeicher`, and
  `Sicht`/`Sicht.null`/`Nachricht`/`Lesbar`/`Frisch` — all real, all
  with the shapes the candidate relies on. No toy model, no duplicated
  executor, no guessed ISA: every TSO transition fact is reused, none
  redefined.
- Grepped the candidate for `sorry|admit|axiom|native_decide|unsafe`:
  zero hits. `CUTS:` block present and complete. In-file `#print axioms`
  for all 15 theorems.
- Reproduced the typecheck read-only with the queued wrapper against
  this clone's master (newer than the candidate base):
  `./lean-probe .tmp/review/author-567/grammatik/Grammatik/X86/TSOHistory.lean`
  prints `== 0 error(s) in the COMPLETE output; exit 0`. Axiom report
  from that run: `sichtVon_le_eins`, `h_schritt2`, `h_flush` on no
  axioms; `spuelen_baut_frische_nachricht` on `[propext, Quot.sound]`;
  all others on `[propext]` — a subset of the standard goal axioms
  (`propext`, `Classical.choice`, `Quot.sound`). No `sorryAx`.
- Premise-use audit (by hand, all 15 theorems): no premise has type
  `Prop` itself; every premise is used (`hmiss`/`hrd` via
  `load_ohne_eintrag`, `hpend` via the load equation plus
  `neuestens_juengste`, `he` via `flush_schreibt_kopf`,
  `h1/h2/hempty/h3` via `fifo_reihenfolge`). No conclusion restates a
  premise; no contract parameters are quantified away (no contracts
  involved); nothing is called a semantics that cannot change memory
  (no new semantics is claimed at all).
- Connection substance (the user-priority test): the module derives
  genuinely new execution facts, not decorative wrappers —
  `issue_hist_bleibt` (issue globally invisible via
  `issue_kein_speicher`), `spuelen_baut_frische_nachricht` (flush builds
  timestamp-2 `Frisch` for the old history AND `Lesbar` of the flushed
  value in the new history), `fifo_hist_konsistent` (two issues plus
  flush make the older value readable at its actual value),
  `load_lesbar_ohne_weiterleitung` / `weiterleitung_ist_juengste`
  (both load paths meet the projected history at actual values, with a
  proved youngest-wins buffer split). The `paket_reisst` call in
  `hist_zerreissen` was argument-checked against the `paket_reisst`
  signature: same-core chain `sbStart -> sbNach1 -> hS2 -> hS3`,
  `hempty := rfl`, `hne := sbX_ne_sbY` — correct, and the separate
  same-core `hS2`/`hS3` pair (with `rfl` computations) is justified
  because the `sb` witnesses issue on different cores.
- Witness / refusal audit: `hist_zeuge_gelenk` is reached
  (`TSOErreichbar sbStart sbNach2` via two issue steps), two-core,
  both stale loads, flush observably changes the canonical byte, and
  the flushed value is `Lesbar` in the projected history — a real
  memory-changing run, non-degenerate. `fremd_weiterleitung_unsichtbar`
  is a proved refusal: fence-ready core 0 coexists with core 1
  forwarding `7` over canonical `0`, with no message for `7` in the
  committed history (all `decide`s elaborated in the green probe).
  `hist_zerreissen` shows tearing, correctly labelled as a non-claim
  of multi-byte atomicity.
- Overlap audit: `TSO.lean` section 10 (`tsoEineHist`,
  `tso_last_lesbar`, `tso_frisch_beispiel`) instantiates `Lesbar`/
  `Frisch` with per-load singleton histories under `Sicht.null`;
  this module's state-dependent `histVon` plus buffer-dependent
  `sichtVon` with issue-invisibility, flush-freshness, FIFO and
  youngest-split facts is a proper extension, not a duplicate.
  `FenceDrain.lean` owns drains, `ObservationProjection.lean` owns
  pilot-step observation — no name or theorem overlap. `Grammatik.lean`
  diff is one additive import line.
- CUTS honesty: the module and the owner report both state Address/Byte
  is intermediate only, with no typed-carrier W/GX mapping, no aligned
  multi-byte atomicity, no LOCK RMW, no per-access `SchrittW`
  construction, no G-step decomposition, no run induction, no
  fairness/timing/device claims, and a projection-local timestamp
  discipline. Nothing in the proofs overreaches these cuts.

## Verdict

CANDIDATE: 567 32cd4f6f81c8f8ba7a5bae6c79b7121e8daa6f54
VERDICT: ACCEPT

## Accepted bounded claim

The candidate delivers the reusable Address/Byte history/view
projection `histVon`/`sichtVon` over canonical TSO with proved:
view bound (`sichtVon_le_eins`), committed-byte presence/readability
(`histVon_mem`, `histVon_lesbar`), youngest-forwarding shape
(`neuestens_none_kein`, `neuestens_juengste`), both load-path facts at
actual values, issue invisibility, flush-built fresh messages, FIFO
consistency, computed same-core witnesses, tearing reuse, one proved
foreign-invisibility refusal, and one reached two-core memory-changing
joint witness — all within standard goal axioms. It does NOT deliver
(and does not claim) the typed-carrier W/GX mapping, multi-byte
atomicity, LOCK semantics, per-access `SchrittW` legs, or any run
induction; those stay explicitly with consumers 573/574.

## Repairs required

None. No minimal repair applies; nothing was found to be copied,
forged, vacuous, or exaggerated.

## Notes for the integrator (not conditions)

- The file uses German identifiers (`spuelen_...`, `neuestens_juengste`)
  consistent with the existing `TSO.lean` vocabulary
  (`sbGespuehlt`, `zaunBereit`); all prose is English. No action needed.
- Producer interface for 573/574, as stated in the owner report:
  `histVon`, `sichtVon`, `histVon_lesbar`,
  `spuelen_baut_frische_nachricht`, `weiterleitung_ist_juengste` +
  `neuestens_juengste`, `issue_hist_bleibt`,
  `fremd_weiterleitung_unsichtbar`, `hist_zeuge_gelenk`. Measurable
  next integration: 573 proves a `SchrittW` write leg from the
  fresh-message + FIFO facts; 574 proves the read leg from the two
  load-path facts; both reuse `hist_zeuge_gelenk` as the inhabited
  target run.

Last review probe result line:
`== 0 error(s) in the COMPLETE output; exit 0` (queued `./lean-probe`
on the exact candidate file; full `./lean-bau` was green at author
commit time per `BUILD-EVIDENCE.json`: `Build completed successfully
(428 jobs)`; this review clone's tree is unmodified and contains no
`TSOHistory.lean`, so no new `./lean-bau` line is attributable here).
