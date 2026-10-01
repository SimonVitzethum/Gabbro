# MUSE-REPORT-557: Independent exact-candidate review of 556 (CLI alias repair)

CANDIDATE: 556 ba2c40cb2ae33432e47e8e7b8a952b781da03935
VERDICT: ACCEPT

Clone verified: `/home/simon/Dokumente/gabbro-muse/a557`, branch `muse/557`.
Review scope: `.tmp/review/SNAPSHOT.json` (author 556, files
`MUSE-REPORT-556.md`, `crates/gabbro-check/src/beweis.rs`), task
(`OWNER-TASK.md`), full patch (`PATCH.diff`), evidence (`BUILD-EVIDENCE.json`),
plus independent reproduction under the queued wrapper in this clone.
Owned file: only this report. No source edit, no Lean, no push.

## What the candidate does

`crates/gabbro-check/src/beweis.rs` only (239 insertions, 22 deletions) plus
its report. Two mechanisms, both in the Lean-measurement path:

1. Bounded retry (`LEAN_VERSUCHE = 3`, `LEAN_PAUSE_MS = 5000`) of `lean_lauf`
   and `modell_bauen`, gated on `ist_ressourcen_engpass` (four lowercase
   runtime-starvation signatures) AND, for `lean_lauf`, an empty
   `fehlerzeilen`. Positioned errors never retry.
2. Cross-process gate `MessSperre` (`mass_sperre_halten`, atomic directory
   creation, std only): at most one measurement per model folder from
   `lake build` through the gate run, held by `pruefe` via RAII `Drop`,
   renewed after each Lean phase, 15-minute SIGKILL takeover. Prints nothing.
3. Three unit tests: gate fires on starvation, silent on tree/setup errors,
   lock holds one at a time (4 threads x 3 holdings, no overlap, released).

## Concrete cause: confirmed by independent reproduction, not guesswork

A `./cargo-pruef` full run on the unpatched base in this clone failed exactly
the same family: `jeder_erstname_tut_dasselbe_wie_sein_zweitname`
(`erstnamen.rs:64`) and
`jeder_fahnen_erstname_tut_dasselbe_wie_sein_zweitname` (`fahnen.rs:723`),
both on the heavy Lean-backed pairs. Captured exact values
(`.tmp/cargo-test-full.log`, git-ignored, kept out of the commit):

- erstnamen (`prove` vs `beweise`): left exit 3 with lake re-creating the
  manifest from scratch (`no previous manifest, creating one from scratch ...
  cloning mathlib`), right exit 3 with `failed to create thread`
  (`Body.lean` build, 27 s). Same exit, divergent apparatus stderr.
- fahnen (`emit --proved` vs `emit --mit-beweis`): BOTH sides exit 3 with
  `lean::exception: failed to create thread`, differing only in the build
  timing string (`Building Gabbro.Body (21s)` vs `(16s)`). Byte-equality
  reads even two identical starvation failures as an alias difference.

Isolation corroboration: light in-process pair `check` vs `pruefe` on the
same file through the built binary is byte-identical (stdout, stderr, exit
0/0). Dispatch is deterministic (`main.rs:516` single arm
`"prove" | "beweise" => befehl_beweise(rest)`; `1386,1400` single
`--proved|--mit-beweis` flag). There is no genuine alias behavior
difference. The author's quoted pair (SETUP exit 3 vs GREEN exit 0 on the
same command seconds apart) and mine (starvation vs manifest race vs
timing-only divergence) are three faces of one cause: concurrent
multi-threaded, gigabyte-heap Lean measurements on one model folder
interfering (thread starvation, lake manifest fights, timing strings).
The gate addresses all three; retry alone demonstrably did not (author's
1468/2 run), which is why the lock is the load-bearing half.

## Review criteria

- No deleted/ignored test, no masked stderr/exit: verified via `PATCH.diff`.
  Both heavy tests, both liveness floors (`erstnamen.rs:69`,
  `fahnen.rs:728`), and all refusal-naming tests are untouched. Persistent
  starvation still reports exactly as before (same `Err`/SETUP message after
  the last attempt); `ohne_ort` mapping to `Aufbau` is unchanged, so a
  resource failure never becomes GREEN.
- No weakened model: all `Stand` transitions, `fehlerzeilen`/`sorry`/axiom
  gate logic, and verdict strings are identical (grep over the candidate
  file: no new `eprint!/println!/exit`, no `Stand` change). The gate changes
  WHEN a measurement runs, never WHAT it says.
- Real pairs/options, normal/refusal coverage: `PAARE`, `FAHNEN`,
  `UNTERBEFEHLE`, dispatch, and refusal-naming tests are untouched; a truly
  diverged alias still fails `assert_eq` deterministically (divergence
  carries no starvation signature; and a starved-then-retried run compares
  true outputs afterwards). Detection power preserved.
- Deterministic output: new code prints nothing; the lock lives in
  `.lake/build/duty/.sperre.d`, outside compared stdout/stderr.
- No fictitious Lean changes: none made; unit tests are pure
  predicate/lock tests needing no proof changes.

## Evidence accepted

- `BUILD-EVIDENCE.json`: pre-repair 1467/1 and 1468/2 flakes, post-repair
  `./cargo-pruef` exit 0 with 1471 passed (1468 + 3 new), 0 failed;
  concurrent heavy binaries 5/5 and 8/8; `./lean-bau` 420 jobs green.
- My reproduction matches the claimed signature byte-for-byte in kind
  (`failed to create thread`, exit 3, lake-build path covered by the
  `modell_bauen` retry, which the report's narrative rightly includes).

## Remaining uncertainties (non-blocking)

- Author's full `.tmp` logs are git-ignored and not in the snapshot; the
  condensed tails plus my own matching reproduction close this gap but the
  original GREEN-twin side is quoted, not attached.
- Suite-time cost of serialisation is unmeasured in the evidence (green, but
  no duration quoted); correctness first, speed unclaimed.
- `.sperre.d` sits inside `.lake/build/duty`; interaction with `lake clean`
  or non-gabbro lake users is unexamined. Takeover bound (15 min) assumes no
  single phase exceeds it (measured to ~6 min); a slower future phase needs
  its own renewal.
- A new Lean starvation signature would need extending
  `ist_ressourcen_engpass`; the gate degrades such cases to serialised
  load, not divergent pairs.
- Candidate's green run taken from evidence + inspection, not re-executed
  here (report-only lane; base reproduction was the independent check).
- Minor observation, out of scope: `befehl_beweise` prints literal
  `gabbro prove:` on both spellings (both failure sides agree, so equality
  is unaffected); whether the second spelling should name itself like the
  W16 fix is a separate question, not this repair's business.

## Scope

Report-only verdict on the pinned candidate above. No credentials read, no
network, no push. `git status` clean except this report; `.tmp` logs ignored.
