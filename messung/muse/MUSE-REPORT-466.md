# MUSE-REPORT-466: Independent exact-candidate review of 418

Lane 466, branch `muse/466`, clone `/home/simon/Dokumente/gabbro-muse/a466` (verified:
`pwd` + `git rev-parse --abbrev-ref HEAD` = `muse/466`).

## Candidate

- Author 418, pinned HEAD `b6c94f4702648c274f8bfb9c67a9795c6c58456f`
  (verified: `git fetch <a418> muse/418` gives exactly this as FETCH_HEAD).
- Base `0b3132b7bb8bf108b3fd1613c70bc0955051f130`; diff base..head is exactly
  3 files: `MUSE-REPORT-418.md` (new), `grammatik/Grammatik.lean` (+1 line),
  `grammatik/Grammatik/X86/BitScan.lean` (new, 444 lines). No other files.
- Umbrella change is exactly one additive import
  (`import Grammatik.X86.BitScan`); no friend files, no Rust, no Spec, no
  checker/emitter, no diagnostic/poison/example numbers taken.

## What I checked

1. Read OWNER-TASK.md, MUSE-REPORT-418.md, PATCH.diff, BUILD-EVIDENCE.json,
   and the full candidate `BitScan.lean`.
2. Verified every external name against the accepted tree:
   `Breite`/`Breite.bits` (`Typen.lean`), `trunc`/`maske` (`Wort.lean`),
   `write64`/`read64`/`writeBytes`/`writeBytesN_hit`/`read64_nach_write64`/
   `schreibbar8`/`lesbar8`/`addrOff_null`/`zeugenSpeicher` (`Speicher.lean`)
   all exist with the signatures the candidate uses. In particular
   `read64_nach_write64` takes `(hwr) (hrd : lesbar8 m a = true)` and the
   candidate passes `rfl` for the `zeugenSpeicher` readability side, which
   holds; `writeBytesN_hit` is called with `(n k hk hn) = (8 0 _ _)` per its
   signature. The memory witness mirrors the already-accepted
   `write_read_zeuge` pattern (same `addrOff_null (0 : Adresse)` step as
   `Speicher.lean:698`), reusing canonical memory, not a mini-machine.
3. Hygiene grep over the candidate file: zero hits for
   `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`/`intro _`/`have _ :=`.
   Imports are only the three canonical X86 modules. English only.
   `CUTS` block present and accurate (no `Befehl`/`schritt` change, no
   nonzero-totality, ZF only, no source/TSO/cost/silicon claims).
4. No collision: `bsfVon`/`bsrVon`/`bitGesetzt`/`scanZF`/etc. are absent
   from the rest of `grammatik/` in my clone.
5. Rule 13: no premises over source syntax (`Vertrag`/`Stmt`/...) and no
   `ZEUGE:` line in the owner task, so no `_zeuge` is required; the task's
   explicit witness demand (zero/nonzero boundaries + memory-changing
   context) is met by six `decide` probes and `bitscan_speicher_zeuge`
   (real `write64`/`read64` with an observable byte change).
6. Reproduced in my clone: staged only the supplied candidate
   `BitScan.lean` at its exact path, ran `./lean-probe` twice:
   both `== 0 error(s) in the COMPLETE output; exit 0`, `#print axioms`
   `[propext, Quot.sound]` throughout (`breite_bits_pos` axiom-free),
   a strict subset of the `gabbro_ziel` standard set. Removed the staged
   file afterwards; `git status` clean before writing this report.
7. Semantic spot checks (all additionally confirmed by the green `decide`
   probes, not by hand evaluation): `bsfVon` fuel `b.bits` from 0 covers
   exactly `[0, bits)`; `bsrVon` from `bits - 1` with fuel `bits` covers
   the full width; `bsrIdx_schranke`/`bsrIdx_max` discharge the
   `bits - 1` wraparound with `breite_bits_pos`; zero maps to `none` in
   both directions (never a fabricated `some 0`); narrow-width truncation
   (`0x100` at `.b8` refuses) follows from the accepted `trunc`/`maske`.
   Projection lemmas are tactic-free consequences of the two joint
   inductions; every premise is used. No vacuity: `some`-cases are
   exhibited by the probes and both validity shapes are inhabited for all
   `b w` by `bsfIdx_gueltig`/`bsrIdx_gueltig`.
8. Build-evidence audit: the author's red-umbrella story checks out. The
   evidence log shows genuine green module runs (full `#print axioms`
   output, exit 0) interleaved with `failed to create thread` crashes
   (exit 134), plus the stash control proving the pristine umbrella
   crashes identically. My two independent green probes corroborate that
   the module itself elaborates; the full-tree `./lean-bau` green and the
   `gabbro_ziel` axiom re-check remain merger-side work on a healthy
   machine, which the author states plainly instead of claiming.

## Findings

No defects. No hidden assumptions, no unused premises, no vacuity, no
forged evidence, no duplicated IR/executor, no safety weakening. The
report's claims match the code and the evidence; where the environment
blocked a check, the report says so and names the control experiment.
The bounded claim (zero-aware scan helpers + proofs + probes + memory
witness, no native/source/timing closure) is exactly what is delivered.

## Re-review of the repaired candidate (new pin)

- New pinned HEAD `eb137c770c3fae49c2157dfd15524f8524ed9da7`
  (verified: fresh `git fetch <a418> muse/418` gives exactly this as
  FETCH_HEAD; `.tmp/review/SNAPSHOT.json` pins the same hash).
- Delta old-head..new-head is exactly one commit
  (`lane 418: report repair note after integration gate failure (no code
  change)`), touching only `MUSE-REPORT-418.md` (+31 lines: the repair
  section quoted below). `git diff` over `grammatik/` between the two
  heads is empty, and the supplied `.tmp/review/author-418` copy of
  `BitScan.lean` is sha256-identical to the new head's committed file
  (`fb253d19…`). The Lean content is therefore byte-identical to what
  the first review accepted; no proof changed, so there are no changed
  proofs to re-inspect beyond confirming identity.
- New report section claims: (a) the merge build elaborated
  `BitScan.lean` successfully (all 7 probe `#print axioms` lines,
  `[propext, Quot.sound]`); (b) the gate failed only at `[397/398]
  Building Grammatik` with the same `failed to create thread` / exit 134;
  (c) local probe re-verified green, full bau still red at the umbrella
  only. These are consistent with the BUILD-EVIDENCE pattern from the
  first review (green module runs interleaved with thread-creation
  crashes) and with my own probes; the author draws no new Lean
  conclusion from them and correctly notes rule 5 forbids restructuring
  the umbrella, so no owned-file change could address the gate failure.
  The blocker statement (retry merge at lower machine load) is addressed
  to the merger/integration owner and makes no claim I need to verify
  beyond plausibility.
- Fresh reproduction in my clone on the new pin: staged only the
  supplied candidate file at its exact path, `./lean-probe` →
  `== 0 error(s) in the COMPLETE output; exit 0` with the same
  `[propext, Quot.sound]` axiom lines; staged file removed afterwards,
  `git status` clean before committing this report.
- All findings of the first review (sections above) stand unchanged:
  no defects, no hidden assumptions, no vacuity, no forged evidence,
  no duplicated IR, no safety weakening, bounded claim exactly delivered.

## Second re-review (new pin 4a6b0415)

- New pinned HEAD `4a6b0415f3322fc36ff539f1930316325db25c19`
  (verified: fresh `git fetch <a418> muse/418` gives exactly this as
  FETCH_HEAD; `.tmp/review/SNAPSHOT.json` pins the same hash).
- Delta previous-head..new-head is exactly one commit
  (`lane 418: second repair note, gate failure unchanged (no code
  change)`), touching only `MUSE-REPORT-418.md` (+12 lines: a second
  repair note restating the same gate failure with a byte-identical log).
  `git diff` over `grammatik/` is empty, and the supplied
  `.tmp/review/author-418` copy of `BitScan.lean` remains sha256-identical
  to the committed file (`fb253d19…`, unchanged since the first review).
  No proof changed; nothing new to re-inspect beyond identity.
- The new note repeats the established evidence (7 probe axiom lines
  print in the merge build, `[397/398] Building Grammatik` aborts with
  `failed to create thread` / exit 134, local probe green, full bau red
  only at the umbrella) and claims no new Lean result and no full-chain
  acceptance. Consistent with all prior evidence and my own probes.
- Fresh reproduction in my clone on the new pin: staged only the
  supplied candidate file at its exact path, `./lean-probe` →
  `== 0 error(s) in the COMPLETE output; exit 0` with the same
  `[propext, Quot.sound]` axiom lines; staged file removed afterwards,
  `git status` clean before committing this report.
- All earlier findings stand unchanged.

## Verdict

CANDIDATE: 418 4a6b0415f3322fc36ff539f1930316325db25c19
VERDICT: ACCEPT

## Re-review note 2026-10-01 (pin unchanged, fresh evidence)

- `.tmp/review/SNAPSHOT.json` still pins `4a6b0415`; fresh
  `git fetch <a418> muse/418` gives the same hash as FETCH_HEAD and
  `git diff` pin..FETCH_HEAD is empty: no author repair since the
  accepted review. The supplied review copy of `BitScan.lean` is still
  sha256 `fb253d19…`, identical to the committed file.
- Fresh evidence inspected this turn in my own clone: staged only the
  supplied candidate file at its exact path and ran `./lean-probe` →
  `== 0 error(s) in the COMPLETE output; exit 0`, with `#print axioms`
  `[propext, Quot.sound]` (strict subset of the `gabbro_ziel` standard
  set); staged file removed afterwards. This is a module-level
  elaboration check only, not a full-build claim: I do not accept from a
  build alone, and the verdict below rests on the substantive semantic
  review recorded above (canonical `trunc`/`Speicher` reuse, joint
  range/bit/extremality inductions, `decide` boundary probes, real
  `write64`/`read64` memory witness, no mini-machine, no vacuity).
- Verdict unchanged: ACCEPT of exactly the bounded candidate above.
- Precise unresolved CUTS (unchanged, merger-side): full-tree
  `./lean-bau` green at the `Grammatik` umbrella target (environmental
  `failed to create thread` / exit 134, pristine tree affected
  identically) and the `gabbro_ziel` axiom re-check, both requiring a
  healthy build host; no nonzero-operand totality (`trunc ≠ 0 → ∃ i`)
  proved; ZF only; no `Befehl` wiring, decoder/image bytes, TSO bridge,
  source lowering, cost transfer, or silicon verification.
