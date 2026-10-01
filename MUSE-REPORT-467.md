# MUSE-REPORT-467: Independent exact-candidate review of 419 (X86 BitCount)

## Re-review of the NEWEST pinned candidate (2026-10-01, later evening)

Previous verdict (on `7feee9d0`) is stale: the author added one more commit and this is a
fresh substantive review of the NEWEST pinned snapshot. Lean code delta vs both previous
reviews: NONE — `grammatik/Grammatik/X86/BitCount.lean` blob `ed9a15a4` and the
`grammatik/Grammatik.lean` hunk (`6e68b11c..e9c9576f`, one import line) are byte-identical
again (PATCH hunk mechanically compared: 473/473 lines identical). The only change in the new
commit `5d41c247` is `MUSE-REPORT-419.md` +17 lines (Addendum 2): the integration gate failed
a second time with byte-identical evidence (`[397/398] Building Grammatik`,
`failed to create thread`, exit 134, the 7 standard `BitCount.lean` axiom lines).

Addendum 2 assessment (checked against the newest `BUILD-EVIDENCE.json`, now 32 entries):
the new evidence shows the probe crashing once with RC=134 (0 `sorryAx`) and passing on
immediate retry with RC=0/0 errors/0 `sorryAx` on identical input, plus bau again at
`[392/393] Building Grammatik` with the same thread-creation crash. Crash-then-pass within
minutes on identical input corroborates load fluctuation rather than code, and the author
again made NO code change — the correct call, same as before. No premise weakened, no
guarantee touched, still exactly the three owned files. Both earlier notes carry over: (a)
resolved well enough (module elaborates inside the integration build — its 7 axiom lines
print there — only the umbrella link crashes); (b) `gabbro_ziel` re-check remains for the
merge gate when resources allow.

Fresh independent reproduction on the NEWEST pinned files (staged only the supplied
`BitCount.lean` + the one import line, restored afterwards, tree verified clean):
`./lean-probe grammatik/Grammatik/X86/BitCount.lean` → RC=0, `0 error(s)`, `sorryAx` count 0,
`Unknown identifier|error(lean` count 0, every `depends on axioms` line within
`[propext, Quot.sound]` or fewer. All prior checks (ownership, canonical reuse, premise use,
non-vacuity, joint non-degenerate memory witness, no duplicated IR/executor, no safety
weakening) carry over unchanged since the code is byte-identical.

## Re-review of the NEW pinned candidate (2026-10-01, evening)

Previous verdict (on `2c524bb1`) is stale: the author repaired with a new commit and this is
a fresh substantive review of the NEW pinned snapshot below. Lean code delta vs the previous
review: NONE — `grammatik/Grammatik/X86/BitCount.lean` blob `ed9a15a4` and the
`grammatik/Grammatik.lean` hunk (`6e68b11c..e9c9576f`, one import line) are byte-identical to
what was reviewed before (PATCH hunk mechanically compared: 473/473 lines identical; full
definition/theorem inventory re-listed and unchanged). The only change in the new commit is
`MUSE-REPORT-419.md` +31 lines: an addendum assessing the integration-gate failure.

Addendum assessment (checked against the NEW `BUILD-EVIDENCE.json` entries): the author
claims the gate's 7 quoted `info:` lines are the module's own `#print axioms` outputs
(standard `[propext, Quot.sound]`, not errors) and the "2 error lines" are the umbrella-link
crash (`Lean exited with code 134`, `build failed` on target `Grammatik`), byte-identical to
the previously documented environmental `failed to create thread` failure. Fresh local
re-checks quoted: probe RC=0/0 errors/0 `sorryAx`/0 `error(lean…)` (new evidence entries
confirm exactly this), bau again 392/393 then umbrella-link crash. "Repair made: NONE" is the
CORRECT call: there is no defect in the owned files for the evidence to point at, and editing
proved-green code to work around a machine resource failure would be fabrication. No premise
weakened, no guarantee touched, no file outside the three owned ones read or modified. My
earlier wording nit (a) is addressed well enough by the new evidence: with a warm cache the
bau log reaches `[392/393] Building Grammatik` past the BitCount target, i.e. the module
elaborates inside the integration build and only the umbrella link crashes. Previous finding
(b) (`gabbro_ziel` re-check) stands as documented: unrunnable under the crash, merge gate
must re-run `./lean-bau` when resources allow.

Fresh independent reproduction on the NEW pinned files (staged only the supplied
`BitCount.lean` + the one import line, restored afterwards, tree verified clean):
`./lean-probe grammatik/Grammatik/X86/BitCount.lean` → RC=0, `0 error(s)`, `sorryAx` count 0,
`Unknown identifier|error(lean` count 0, every `depends on axioms` line within
`[propext, Quot.sound]` or fewer. All prior checks (ownership = exactly the 3 files, canonical
reuse, premise use, non-vacuity, joint non-degenerate memory witness, no duplicated
IR/executor, no safety weakening) carry over unchanged since the code is byte-identical.

## Clone / branch verification (unchanged)

- Clone `/home/simon/Dokumente/gabbro-muse/a467`, branch `muse/467`: MATCH (checked
  `git rev-parse --show-toplevel` and `git branch --show-current`). No other clone read.
- Candidate base `0b3132b7bb8bf108b3fd1613c70bc0955051f130` is an ancestor of this tree; pinned
  candidate HEADs (`2c524bb1`, `7feee9d0` superseded, now `5d41c247`) are not fetched here
  (no network), so the review used the exact supplied artefacts:
  so the review used the exact supplied artefacts: `.tmp/review/SNAPSHOT.json`, `author-419/OWNER-TASK.md`, `author-419/PATCH.diff`,
  `author-419/grammatik/Grammatik/X86/BitCount.lean`, `author-419/MUSE-REPORT-419.md`,
  `author-419/BUILD-EVIDENCE.json`.
- PATCH bytes vs supplied file: byte-identical (473 lines each, compared mechanically).

## What was reviewed

Lane 419 task: new reusable module `grammatik/Grammatik/X86/BitCount.lean` + one additive X86
import in `grammatik/Grammatik.lean`. Bounded claim: fixed-width population count as pure
arithmetic over the canonical `Wort`/`Breite`/`Register`/`Flags`/`Zustand`, with a defined
(ZF) / undefined (CF/OF/SF/PF, AF none) flag contract, data-only feature admission
(`PopcntMerkmal`) with a refusing register consumer (`popcntSchritt`), and joint
non-degenerate witnesses. Explicitly NOT claimed: silicon/latency, codec bytes,
`Befehl`/`schritt` wiring, source correspondence, cost transfer, TSO bridge (all in CUTS).

## Independent checks performed in this clone

1. Ownership/file list: PATCH touches exactly `MUSE-REPORT-419.md`,
   `grammatik/Grammatik.lean` (one import line), `grammatik/Grammatik/X86/BitCount.lean`.
   No `OptimizationRules.lean`/`OptimizationWitnesses.lean`, no `Befehl`/`schritt` equation, no
   checker/Spec/goal/Rust/emitter file. PASS.
2. Canonical reuse (names resolved from this tree, not invented): `trunc`/`bitAt`
   (`Wort.lean`, `bitAt (n i : Nat)` matches `popCountAux` use), `popCount8` NOT duplicated
   (absent from the new file), `laengeOk`/`ripNach`/`regSet`/`zeugeFlags` (`Ausfuehrung.lean`),
   `write64`/`read64`/`writeBytes`/`writeBytesN_hit`/`read64_nach_write64`/`addrOff_null`/
   `zeugenSpeicher`/`schreibbar8` (`Speicher.lean`), `Flags` 6-field shape
   (`cf pf af zf sf of`, `af : Option Bool`) matching `Flags.mk` uses, `Breite` 4 widths.
   `popcntSchritt` is a SEPARATE future-form step (`BitCountErgebnis`: `ok`/`verweigert`/
   `misslungen`), not a duplicate IR/executor; refusal carries no state and is not a
   `hardware` stop. PASS.
3. Forbidden tokens in the new file: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
   (the only `axiom` substring hit is the English word "admission"); no `Prop`-typed premise.
   Every theorem premise is used (`bc_ok`/`bc_verweigert`/`bc_laenge_misslungen` rewrite with
   theirs; `verweigert_heisst_verweigert` derives `hfeat` from `hzu`;
   `ohne_merkmal_kein_ok` rewrites `hstep` with `h`+`hok`, `subst z`, `intro t`, `cases hcon`).
   No conclusion restates a premise; no contract parameters quantified away; no fake semantics
   (memory facts go through real `write64`/`read64`). PASS.
4. Vacuity: `PopcntGueltig` is inhabited (`popcnt_gueltig_existenz`) AND genuinely loose
   (`popcnt_unbestimmt_unbeschraenkt` exhibits two valid snapshots differing in CF;
   `unbestimmt_bleibt_unbestimmt` keeps CF settable at zero count). The undefinedness claim is
   proved, not assumed. The `popcntFlags` keep-incoming-undefined-bits choice is stated as an
   explicit modelling choice in file §3 and CUTS, not hidden hardware truth. PASS.
5. Witnesses: value probes sparse/dense/narrow-truncated/zero (`probe_zaehlung`, incl.
   `popCount .b8 0x1FF = 8` pinning width truncation), step probes
   (`probe_sparse_schritt`/`probe_dense_schritt`/`probe_null_schritt` with ZF values),
   refusal probes (`probe_merkmal_verweigert`, `probe_laenge_verweigert`), and the joint
   witness `bitcount_speicher_zeuge`: sparse count 1 and dense count 64 through
   permission-checked `write64`/`read64` with `zeugenSpeicher.bytes 0 != m1.bytes 0` on nonzero
   words (real memory-changing execution). Negative case `ohne_merkmal_kein_ok` (no `ok`
   without the feature). PASS.
6. Reproduction via queued wrapper: staged ONLY the supplied `BitCount.lean` plus the one
   import line in my clone, ran `./lean-probe grammatik/Grammatik/X86/BitCount.lean`:
   RC=0, `0 error(s)`, `sorryAx` count 0, all 23 `depends on axioms` lines within
   `[propext, Quot.sound]` or fewer (`bits_schranke`, `popcntZugelassen_heisst` depend on no
   axioms). Restored the tree afterwards (`git status` clean, `git diff` empty). PASS.
7. Build-evidence audit: `BUILD-EVIDENCE.json` shows one intermediate probe with `sorryAx`
   (after an unknown-identifier `le_trans` breakage) then a fixed final probe RC=0 with 0
   `sorryAx` — an honest repair trail, not forged green. `./lean-bau` RED is environmental
   (`failed to create thread`, Lean exit 134) WITH a stash control failing identically without
   the change, plus ~10 retries. No green output is claimed where there is none. PASS.
8. Full `./lean-bau` was NOT re-run in this review: the module-level probe is green on the
   current tree and the umbrella-link crash is documented with a control; re-running the full
   build adds no signal for this additive module. The merge gate must re-run `./lean-bau`
   (and the `gabbro_ziel` axiom re-check, goal files untouched) when machine load allows.
9. No coordinator-snapshot operation was performed; no pool, session DB, or other lane state
   touched. `MUSE-REPORT-467.md` is the only owned deliverable.

## Defects / repair direction

None material. Two notes, neither verdict-changing: (a) the report's claim "`BitCount.olean`
builds as a dependency during ./lean-bau" overstates what the evidence shows (the bau log
shows the BitCount target FAILING on the thread crash, like everything at link time); read it
as "`lean-probe` elaborates the module green", which is verified. (b) The task's "standard
`gabbro_ziel` axiom check before committing Lean" was correctly recorded as un-runnable under
the environmental crash rather than faked.

## Scope

ACCEPT covers ONLY the precisely delivered bounded claim above: pure fixed-width popcount
arithmetic + stated flag contract + feature-gated refusal + witnesses, with the listed cuts.
No full compiler closure, no silicon/codec/source/cost/TSO claim is accepted.

CANDIDATE: 419 5d41c247ed11f82be5d73114fb088b27e9e7c94a
VERDICT: ACCEPT
