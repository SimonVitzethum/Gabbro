# MUSE-REPORT-619: Independent overnight closure review of 618

Clone verified: `/home/simon/Dokumente/gabbro-muse/a619`, branch `muse/619`.
Owned file only: this report. No code, Lean, wrapper, config or credential touched.
No network, no push, no other clones, no model calls.

CANDIDATE: 618 56a89078513cec9604b0ed6fe008a946a32cd017

## What was reviewed

Exact pinned snapshot `.tmp/review/SNAPSHOT.json` (author 618, base
`0044c258`, clean): two files, `MUSE-REPORT-618.md` and
`crates/gabbro-check/src/beweis.rs`. The git object for the candidate HEAD is
absent from this clone, so review ran against the exact
`.tmp/review/author-618/PATCH.diff` (210 lines), `OWNER-TASK.md`,
`BUILD-EVIDENCE.json` and `MUSE-REPORT-618.md`, cross-checked line by line
against the live tree at `435604ad` (whose `beweis.rs` is the patch pre-image:
all context lines match).

Owner task (618): bound the native Lean worker/heap demand of every measurement
spawn after the integrated suite at `758a8448` failed
`jeder_fahnen_erstname_tut_dasselbe_wie_sein_zweitname` (`fahnen.rs:723`) with
`emit --proved` GREEN (exit 0) vs `emit --mit-beweis` SETUP exit 3
(`lean::exception: failed to create thread`) on the same file -- inside lane
556's per-model gate and bounded retries, which serialise WHEN runs happen but
cannot shrink one run's thread demand.

## Findings (all verified by inspection against the live tree)

1. Owned paths respected. Snapshot lists only `beweis.rs` + the owner report;
   no Lean, checker-rule, emitter, test-file, wrapper, Spec/goal or
   friend-reserved optimiser file is touched. No `sorry`/`axiom`/`native_decide`
   surface applies (Rust-only change).
2. Scope is a strict apparatus subset. The diff only ADDS: constants
   `LEAN_BOUND_ARGS = ["-j2", "-M4096"]` and
   `LAKE_WORKER_ENV = ("LEAN_NUM_THREADS", "2")`, `.args(...)`/`.env(...)` on
   the spawns, plus two unit tests. Retry counts, gate, `ohne_ort`,
   `fehlerzeilen`, `ist_ressourcen_engpass` and every compared-output path are
   byte-identical. No verdict is compared, masked, normalised, fabricated or
   weakened; no source rule added; no test deleted or weakened.
3. Coverage of the failure channel is complete. All four Lean `Command::new`
   spawns under `crates/gabbro-check/src/` are in `beweis.rs` (verified by
   grep: `modell_bauen:156`, `lean_lauf:259`, `vorlage_quelle:662,679`; the
   remaining `Command::new` uses in the tree are C toolchains in `bau.rs`).
   The patch bounds all four: env on both `lake build`s, args+env on the direct
   `lean` run, args+env on the `lake env lean` template run.
4. Flag placement is correct. Direct run becomes
   `lean -j2 -M4096 [-o olean] file`; template run becomes
   `lake env lean -j2 -M4096 driver` -- flags reach `lean`, not `lake`. The
   bound equals the tree's own (`grammatik/lakefile.toml` `weakLeanArgs`,
   `lean-probe`'s `lake env lean -j2 -M4096`), confirmed in this clone.
   `LEAN_NUM_THREADS` has repo-instrument precedent (`zaehle-kette.py`, value 4
   there vs pinned 2 here); as the owner honestly states, the lake-side half is
   unverified but harmless if ignored, and the certain half is the direct-lean
   bound. The flags print nothing, so alias byte-equality is unaffected.
5. Tests diagnose the actual channel. `die_schranken_sind_die_des_baums` pins
   the constants to the tree's own pair; `der_kanal_meldet_den_gemessenen_aufbaufehler`
   feeds the verbatim reproduced 2026-10-01 stderr through the unchanged
   `ist_ressourcen_engpass` / `fehlerzeilen` / `ohne_ort` functions (apparatus
   path on the starvation string incl. exit-3 mapping, tree path on a
   positioned error). No synthetic channel, no weakened assertion.
6. Evidence is coherent and bounded. Pre-repair full `./cargo-pruef` reproduced
   the same family (1470/1/1, `fahnen.rs:723`); post-repair exit 0 with
   1473 passed / 0 failed / 1 ignored (+2 new unit tests), both heavy alias
   tests `ok`, plus 5/5 erstnamen and 8/8 fahnen on built binaries. I did not
   re-run the full suite in this clone: it would contend with the active lane
   pool's build leases and my report-only change cannot affect its outcome;
   acceptance below rests on diff inspection, not on re-running green.
7. No overclaim. The owner states one green suite does not prove an
   intermittent flake gone, names the next datum (WHICH `lean_lauf` call fails)
   and flags the `programmlogik/lakefile.toml` follow-up as outside owned
   paths. No closure, hardware, ISA or simulation claim is made anywhere in
   the candidate -- correctly, since this is host apparatus, not a proof leg.
   The overnight-priority clauses about source/model/byte connections,
   Tools595 and Docs594/604/605 do not apply to this candidate's scope; nothing
   in 618 touches them.

Rejected-defect screen: no self-consistency-as-proof, no timestamp reset, no
guessed ISA, no hidden simulation premise, no weakening, no disconnected
filler, no credential/env scan. None present.

`./lean-bau`: not run -- no Lean file added or touched, no `Grammatik.lean`
edit; nothing in the candidate can affect the grammar build.

## Open (not blocking)

- The flake was intermittent (~1 in 2 in the observed sample); recurrence
  remains possible under load. Next step on recurrence is owner's own note:
  log which `lean_lauf` call (Duty/Proofs/Gate) failed.
- `programmlogik/lakefile.toml` has no `weakLeanArgs`; binding `lake build`
  from the inside is a possible follow-up for the file's owner.
- A persistent starvation on BOTH spellings can still read as an alias
  difference when the two SETUP texts differ -- apparatus limit, not a 618
  defect.

## Bounded accepted scope

`crates/gabbro-check/src/beweis.rs` resource bounds only: `-j2 -M4096` on
every direct/template `lean` spawn, pinned `LEAN_NUM_THREADS=2` on every
measurement `lake build`/`lean` spawn, plus the two `ressourcen_engpass_tests`.
No semantic, verdict, message-text or comparison change.

VERDICT: ACCEPT

## Useful next independent tasks (exact ownership, not started)

- 618-followup-A (owner: whoever owns `programmlogik/lakefile.toml`): add
  `weakLeanArgs = ["-j2", "-M4096"]` there if the lake version honours it;
  verify with a loaded-machine measurement, not a single green run.
- 618-followup-B (any Rust lane): include the failing `lean_lauf` site
  (Duty/Proofs/Gate) in the SETUP text so the next recurrence is attributable.
- No filler started; no second scheduler, monitor or dispatcher touched.
