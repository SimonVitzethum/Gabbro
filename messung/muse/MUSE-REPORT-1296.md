# MUSE-REPORT-1296: Exact review of candidate 1295 (TSO projection of classified union steps)

## Verdict

CANDIDATE: 1295 5fe1dbb5d3b4f4cab471b7d2645ea09d00163cdf
VERDICT: ACCEPT

Candidate: lane 1295, pinned head `5fe1dbb5d3b4f4cab471b7d2645ea09d00163cdf`
(base `63e2ec3543deec0c4cce21e9431dfffba157ebd6`), reviewed from delivered FILES
only (SNAPSHOT.json, `author-1295/PATCH.diff`, copied tree, OWNER-TASK.md,
BUILD-EVIDENCE.json). The pinned hash itself was never queried.

## What was checked

- **Clone/branch:** this clone is `/home/simon/Dokumente/gabbro-muse/a1296`,
  `.git/HEAD` reads `ref: refs/heads/muse/1296`. Matches the lane header.
- **Changed files (exactly 3):** `grammatik/Grammatik/X86/HwKapsteinTso.lean`
  (new, 554 lines), `grammatik/Grammatik.lean` (one appended import line only),
  `MUSE-REPORT-1295.md` (new). No other existing file touched. The one-line
  Grammatik.lean diff is the only permitted existing-file change.
- **Forbidden tokens:** full read of the 554-line new file shows no `sorry`,
  `admit`, `axiom` declaration, `native_decide`, `unsafe`, or `split_ifs`.
  Only `#print axioms` lines (one per theorem, 24 total) plus the CUTS block.
- **Axioms (from BUILD-EVIDENCE final probe):** every theorem depends only on
  `[]`, `[propext]`, or `[propext, Quot.sound]` — a subset of the goal
  standard (`propext`, `Classical.choice`, `Quot.sound`). Standard.
- **Theorem inventory reviewed:** `kapTso` (def, alias of accepted `tsoAnsicht`);
  projection equations `kapTso_setKernDaten`, `kapTso_setTso`,
  `kapTso_setKernVonFp`; exact base classification `kap_basis_tso_klass`
  (silent reg/fault, forwarding `loadByte` observation, single `issueByte`,
  single `flushKern` with buffer head named — footprint named in every leg);
  reachability tools `kapTso_erreichbar_trans`, `kapTso_schritt_erreichbar`,
  `kapTso_issueListe_erreichbar`; adapter legs `kapTso_wortAusgabe_erreichbar`,
  `kap_wort_tso`, `kap_drain_tso`, `kap_fwd_tso`, `kap_stapelPush_erreichbar`,
  `kap_stapelCall_erreichbar`, `kap_stapel_tso`; union lifts
  `kap_basis_reichbar`, `kap_union_basis_tso`, `kap_union_wort_tso`,
  `kap_union_drain_tso`, `kap_union_fwd_tso`, `kap_union_stapel_tso`;
  joint summary `kap_fuenf_tso`; witness pair `kapTso_basis_beob`,
  `kapTso_zeuge`.
- **Premise use:** every premise of every theorem is used (checked leg by leg;
  `cases h`/`rcases` consume the step hypothesis; `kap_fuenf_tso` uses each
  conjunct's hypothesis in its own leg; `kapTso_basis_beob` uses `c a v`
  through the type of `hstep` and `hld`). No `Prop`-typed premises, no
  `intro _` / `have _ :=` discards, no conclusion-restates-premise, no
  contract quantification (no contracts involved — hardware-only lane).
- **Lift, not copy:** every non-new name (`tsoAnsicht`, `setKernDaten`,
  `setTso`, `setKernVonFp`, `HwSchritt` constructors, `issueByte`,
  `flushKern`, `loadByte`, `issueListe`, `wortEintraege`, `hwWortAusgabe`,
  `adapterWort1147`, `drainAdapter`, `fwdAdapter`, `stapelAdapter`,
  `stapelPush`/`stapelCall`/`stapelSlot`, `HwVollSchritt`, `KapEreignis`,
  all `kap_step_*` / `hwWit_*` / `*_witM0` witnesses) resolves to an accepted
  definition in this clone's tree (spot-verified: 83 matches for the witness
  family across `HwKapstein.lean`, `HwStackCalls.lean`, `HwDrainGeneric.lean`,
  `HwForwardingGeneric.lean`, `HardwareExecution.lean`). Nothing redefined.
- **Refusals:** none-legs propagate correctly (`rw [hh] at h; cases h` in all
  drain/fwd/stapel observation and flush legs; `none` cases for
  `issueListe`/`flushKern`/`issueByte`). No new checker code exists, so no
  `N` code or gift probe is owed (Lean-only projection lane).
- **Witness non-degeneracy:** `kapTso_zeuge` exhibits four reaching union
  steps (wort, stapel push, drain store, fwd store — all memory-changing via
  buffered multi-byte issues), the base zero-observation through the
  projection, and the two-core non-degeneracy on the same TSO model
  (`hwWit_weiterleitung`: owner forwards 42; `hwWit_fremd_alt`: foreign core
  reads stale 0; `hwWit_spülung_aendert_speicher`: drain installs 42 into
  shared memory). Non-degenerate.
- **Silicon:** the file makes no new silicon claims (no encodings, fault
  classes, or ordering rules stated); CUTS explicitly defers silicon/timing
  assumptions to the family files. Nothing to falsify against the SDM here.
- **CUTS honesty / claim size:** the file proves 5 of 21 union tags and names
  the remaining 16 as FINDINGs with per-tag reasons (lockRmw direct memory
  write via `einbettenLock` needing a drained-own-buffer leg; system plug
  direct install; isa/addr needing `concIssue` folds; uc/port device paths;
  fp/fehler/tor/vec/nested/int/bild/instanzen needing control-state lemmas).
  No W/GX bridge, no whole-word atomicity beyond guarded drains, no
  source/checker/contract/entry/budget claim, no hardware correspondence
  beyond self-consistency. The claim matches the proof.

## Last build result (live re-runs in this clone, 2026-10-05)

- `./lean-probe .tmp/review/author-1295/grammatik/Grammatik/X86/HwKapsteinTso.lean`
  (exact delivered bytes, probed in place — `cp` was refused, see note): →
  `== 0 error(s) in the COMPLETE output; exit 0`, all 24 `#print axioms`
  standard (`[]`, `[propext]`, or `[propext, Quot.sound]`). Independently
  reproduced.
- `./lean-bau` on this clone's base tree (candidate not integrated here, so
  676 jobs vs the author's 677): →
  `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (676 jobs)`. Base green; author's evidence
  covers the integrated 677-job build (`== exit 0`, same 0-error line).
- Author BUILD-EVIDENCE earlier failures (`bad_alloc`, `failed to create
  thread`, unreadable toolchain `.olean.private`) hit only the root
  `Grammatik.lean` aggregation step, varied run to run, and cleared with no
  source change — consistent with concurrent-lane resource contention,
  disclosed honestly by the author.

Note: the lane instruction says to copy the candidate file into the clone
before probing; the `cp` command was refused by the permission classifier, so
the probe ran on the delivered copy inside `.tmp/review/` (byte-identical
source of the review, imports resolved against this clone's accepted tree).
No clone file was added or modified for the check; the tree still matches base
plus this report.

## What remains open (follow-ups, not defects)

The 16 unclassified union tags listed in CUTS, in particular the locked-RMW
leg with the drained-own-buffer guard and the system-plug direct-install leg.
These are precise obstructions with named next steps, suitable as follow-up
lane tasks.

## What is wrong in the owner task (agreeing with the author's points 1–3)

The task's "exactly one accepted TSO event" phrasing is false as a
single-step claim even for classified families: a word store is eight byte
issues (`TSOErreichbar`, multi-step), not one `TSOSchritt`. The candidate
proves the honest multi-step form and keeps single-step exactness only where
it holds. The MECHANISM paragraph (one family via a new `HwAdapter`) does not
match the TASK (capstone projection over the composed union); the candidate
correctly follows the TASK. Partial coverage (5/21) with documented FINDINGs
is the task-allowed output ("steps that touch memory through any other path
are a FINDING"), and demanding all 21 in one lane would invite fake closure.

## Tool status (precise, no remaining blocker for this report)

Early in this session every `bash` call was refused by the permission
classifier (including trivial probes and `cp`). Retried per instruction with
simpler commands: read-only shell/git and the queued wrappers now run. `cp`
remains refused; worked around by probing the delivered candidate bytes in
place (see build section). Committing below via `arbeitsprotokoll/.commitmsg`
+ `./commit.sh`; if the commit call is refused, this file stays written but
uncommitted and the turn records that instead of claiming otherwise.
