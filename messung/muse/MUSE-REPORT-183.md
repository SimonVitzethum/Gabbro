# MUSE-REPORT-183 (lane 183: the Rust side of the new race rule and of start reasons)

## 0. Task and disposition of the reserved numbers

Merge `08228d7c` gave the Lean checker Bool `Akzeptiert`
(`grammatik/Grammatik/Zielsatz/Akzeptiert.lean`) a `rennB` component and
strengthened `wurzelnB`; the merge message leaves open "the Rust side of
`rennB` (`H013`)". This lane brings the Rust checker in line:
measure `H013`/`fusswache2` against the corpus and the Lean definitions,
implement the exact `rennB` condition, refuse starts with reasons or
signature-held locks, add poison probes, and measure the corpus
(0 new refusals expected).

Reserved and used: diagnostic codes `N300`–`N304`, gift numbers `964`–`967`
(all four created). Examples `128`–`129` were reserved but NOT created
(see §8). `MARKE_EMIT` untouched (still 107; §9).

## 1. The Lean definitions, read exactly

- `SchreibGetrennt` (`Zielsatz/Spec.lean:135`): for `w₁ ≠ w₂` in `ws`, if `g`
  reachable from `w₁` may write `c` (`TraegerSchreibt g c`), then every `h`
  reachable from `w₂` neither writes `c` nor carries it in a footprint
  (`fussOrteG`). One Prop covering write-write AND write-read.
- `rennB` (`Zielsatz/Akzeptiert.lean:256`): every carrier is either exempt
  (`ausgenommenB`: a guard lock exists, i.e. `waechterVon` non-empty, OR
  `atomic`, OR a publish payload of an atomic) or `SchreibGetrennt`.
- `wurzelnB` (`Akzeptiert.lean:304`): every declared start holds no lock by
  signature and has no reasons (`D.haelt w = [] ∧ D.gruende w = 0`).
- `Ruhig` (`Zielsatz/Spec.lean:208`): an idle start holds nothing, reasons
  nothing, and every function it reaches has an empty footprint and writes
  nothing. `StartZulaessig.einmal` (`Spec.lean:217`) admits a twice-started
  routine only as `Ruhig` — idle starts write nothing.
- Surface grounds: `Bewacht` = `lock … protects`; `AtomarAusgenommen` =
  `atomic` global; `PaarungAusgenommen` = payload of an atomic;
  `ws` = concurrent members plus entry/boot roots (`Akzeptiert.lean:32-36`,
  naming `startexklusiv.rs`); `TraegerSchreibt` = DECLARED write permission.

## 2. Measurement (1): H013 and fusswache2 against the Lean defs

| question | `H013` (`geteilt.rs`) | `fusswache2` (`N290`–`N294`) | Lean answer |
|---|---|---|---|
| two starts, one unguarded carrier, both write, NO reader | FIRES (per entry write) | silent (footprints list reads) | refuse (`rennB`) |
| one start writing unguarded | FIRES | silent | accept (needs a DIFFERENT start) |
| same carrier under `masks`+`ein_kern`, or `per cpu`, or `rcu protects` | exempt | n/a | NO exemption (guard/atomic/payload only) |
| start holds `Held(L)` / declares `or R` | silent | silent (`N240` only bans SHARED locks) | refuse (`wurzelnB`) |
| same routine on two threads, not idle | silent | silent | refuse (`einmal`/`Ruhig`) |
| starts pool | entries only | concurrent + entry + boot | concurrent + entry + boot |

`H013` is coarser than `rennB` in both directions (fires where Lean accepts
— single entry; exempts where Lean does not — masks, per-cpu, rcu). The
footprint legs cannot see the write-write race by construction. Neither rule
judges start reasons or per-start locks.

## 3. Placement: fusswache2.rs is the one place, H013 is untouched

`H013` has entry hulls but no starts pool, no call graphs over resolved
functions, no footprints, and no concurrent/boot roots. `fusswache2.rs`
already computes every input `rennB` needs: the starts pool (`startet`),
call-graph fixpoints (`faeden`, the `reachB` surface), declared writes
(`schreibt`, the `TraegerSchreibt` surface), footprints (`fuss`, the
`fussOrte` surface), lock guards (`sperrkarte`, the `Bewacht` surface) and
signature-held locks (`gehalten`). Extending `H013` would duplicate that
machinery (two registers over one thing); the new legs live in
`fusswache2.rs` as `race()` with helpers `atomics`/`per_core`/`payloads`.
One deliberate deviation, documented in code: `accumulates … per cpu` IS
exempt (one surface name denotes N core cells — the model has no such
carrier to judge; `H013` exempts it for the same reason). A non-per-core
accumulator would not be exempt; the corpus has none.

## 4. Implementation: N300–N304

`crates/gabbro-check/src/fusswache2.rs` (`race()`, called at the end of
`pass()`, reusing its maps; purely additive):

- `N300` — write-write across DIFFERENT starts on an unguarded, non-atomic,
  non-payload carrier. One refusal per carrier (first pair in start order
  names the witness). The flagship gap: no reader anywhere.
- `N301` — write-read across DIFFERENT starts on the same carrier class.
  Fires only where `N300` does not (a pair writing on both sides belongs to
  `N300` alone — one refusal names one defect; Lean's single Prop gives both
  conjuncts, the Rust side files the write half).
- `N302` — a start whose function declares `or R` (`FnDecl.fehler`), one
  refusal per start function.
- `N303` — a start whose function holds a lock by signature (`requires
  Held`, any strength), one refusal per start function. The strong form of
  `N240` (which only bans locks two starts SHARE).
- `N304` — two starts resolving to ONE routine that is not `Ruhig` (lock,
  reason, graph write, or graph footprint). Same-function pairs never reach
  `N300`/`N301` (`w₁ ≠ w₂`), mirroring `schreibGetrenntK_of`, which sends
  same-function threads through `einmal`.

All five are errors. Guard exemption needs a guard LOCK, held or not
(ordering comes from the guard's existence, `rennfrei_g_voll`); `rcu`
protects, `masks`/`ein_kern` do NOT exempt. Unresolvable starts are skipped
(`W003`/`N018` own them); `entrust` roots are skipped. With fewer than two
starts the race legs stay silent; `N302`/`N303` judge every start.

Sentence `wirkungen.rennboden` added to `WIRKUNGEN` in `saetze.rs`
(required by the second tooth of `pruefe-saetze.py`).

## 5. Probes (all measured, §9)

- `beispiele/gift/964-zwei-schreiber-ohne-lesen.gab` (`N300`): two starts,
  one unguarded table, no reader. Measured set: `N300` + `W001` (same-table
  writes across a declared pair — the pair half; `N300` the race half).
- `beispiele/gift/965-schreiber-leser-unbewacht.gab` (`N301`): writer plus
  bare reader. Measured set: `N301` + `N291` (the footprint half) + hint
  `E247`.
- `beispiele/gift/966-start-mit-grund.gab` (`N302`): a start with `or E`
  (each start owns its table; the second start calls the first through
  `let…else` — calling the start routine elsewhere does not unstart it).
  Measured set: `N302` + `E008` (transitive-`reads` effect on `nehmer`,
  a pre-existing rule, documented in the file header).
- `beispiele/gift/967-start-haelt-sperre.gab` (`N303`): a start holding
  `Held(L)`, the second start lock-free over an unguarded, never-written
  table. Measured set: exactly `N303` (`N240` stays silent — the strong-form
  distinction, pinned; an earlier draft with both tables guarded drew `H007`
  beside it and was reworked to this clean shape).
- 11 snippet tests in `crates/gabbro-check/tests/fusswache2.rs`: the four
  falls above over snippets, plus positives that stay silent (own tables,
  guarded writers under the `109` take-inside discipline, single start,
  atomic publish-payload twins, per-core twins, twice-started idle routine)
  and the twice-started writer (`N304`).
- Positive from the task ("two starts writing their own tables") lives as a
  snippet test, not as examples `128`–`129` (§8).

## 6. Measurement (2): the corpus

Clean examples: **0 new refusals.** The suite's
`jedes_beispiel_geht_sauber_durch` is green, and `gabbro pruefe` on the
reworked `108` is silent. The "0 new refusals" expectation holds for the
clean corpus because the one contradiction (`108`) was reworked, not
because nothing was found (§7).

Poison fallout — every `N300`–`N304` occurrence over `beispiele/gift/*.gab`,
measured with the built binary (full error-level sets; hints omitted except
where named):

| file | measured set | new codes | why real (Lean component) |
|---|---|---|---|
| `146` | H013 H222 N300 W002 | N300 | two starts' graphs write one unguarded carrier (`rennB`) |
| `704` | N300 W001 | N300 | same write-write shape, no reader |
| `708` | N300 W001 | N300 | same, across different slots |
| `743` | H013 H222 N300 W002 | N300 | transitive write still a graph write |
| `744` | H013 H222 N300 | N300 | same (common-lock hull keeps H013; race leg is separate) |
| `745` | H013 N304 | N304 | both routines start twice (member + entry) and write (`einmal`) |
| `760` | N300 W001 | N300 | `f`/`g` write unguarded `X`, no reader |
| `897` | H013 H222 N300 N304 W001 | N300 N304 | write-write on `z` + twice-started writers |
| `899` | H013 H222 N300 N304 W001 | N300 N304 | same, transitively |
| `910`–`915` | N240 (+N303 / +N303 N304 on 912) | N303 (N304 on 912) | starts hold signature locks (`wurzelnB`); 912's routine starts twice and is not idle |
| `952` | N291 N301 | N301 | write-read on unguarded carrier |
| `953` | N290 N301 | N301 | write-read through a contract footprint |
| `954` | N290 N291 N292 N301 | N301 | write-read through a callee contract |
| `964`–`967` | §5 | N300 N301 N302 N303 | the new probes |

Every gift test stays green: the gift harness is a contains-check on the
`-- erwartet:` code, and no expected code stopped firing.

## 7. Tightenings of accepted programs — per-file register

Ten existing corpus files plus `108` changed. In each case the program is
untouched and only the header books the new refusal — except `108`, whose
program predates the merged `wurzelnB` and contradicted it:

- `beispiele/108-disjoint-start-locks.gab` — **refused by `N303` ×2**
  (`wurzelnB`: `D.haelt w = []`). The old program (disjoint `Held(L)` /
  `Held(M)` over a declared pair) is a real finding: the merged Lean
  accepts no start holding any signature lock, shared or not. Measured on
  the pre-lane text from git: exactly two `N303` errors, nothing else.
  Reworked to two lock-free readers over one never-written table (silent
  under every rule — verified). The old program is kept verbatim as a
  comment in the file header; the refused root shape additionally runs as
  `beispiele/gift/967`; the pair side in gifts `910`–`915`. Downstream pins
  regenerated: `grammatik/Grammatik/Export108.lean` (namespace block
  byte-verbatim against fresh `gabbro lean-g` output, checked
  mechanically), `UebersetzeAllg2.lean` (`src108` byte-identical to the
  file, checked mechanically; tokens/items/elaboration unchanged — comments
  lex away), `ZeugnisKorpus.lean` (`c108_read_c` moved to `T`/`GTFeld`/`lit
  1` — the old pin named `GTab.U`, which no longer exists), and the
  `lean_g.rs` substring pins.
- `gift/745` — **+`N304`** (`einmal`/`Ruhig`): each routine backs a
  concurrent member AND an entry root, and writes. A twice-started writing
  routine is exactly what `StartZulaessig.einmal` refuses.
- `gift/760` — **+`N300`** (`rennB`): `f`/`g` both write the unguarded `X`
  with no reader anywhere — the flagship gap, invisible to `N290`–`N294`.
- `gift/897`, `gift/899` — **+`N300` +`N304`**: write-write on the unshared
  `z` across two starts, plus the twice-started-writer shape (§6 table).
- `gift/910`, `911`, `913`, `914`, `915` — **+`N303`** (one refusal per
  lock-holding start): each starts routines holding signature locks, which
  `wurzelnB` refuses regardless of sharing. Headers corrected from exact
  `[N240]` to `[N240, N303]`.
- `gift/912` — **+`N303` +`N304`**: the same routine on two threads holding
  `L` and writing — refused at the root and at `einmal`.

## 8. Deliberately NOT done

- Examples `128`–`129` not created: every `beispiele/*.gab` must pass AND
  emit, and the emission ratchet (`MARKE_EMIT=107`, exact equality) may not
  be touched — two passing examples would force `MARKE_EMIT` to 109.
  Positives live as snippet tests instead (§5).
- `H013` untouched (coarse per-entry rule; §3). `N240` untouched (pair
  disjointness; `N303` is its strong form beside it).
- No Lean semantics touched (checker side only): the `.lean` edits are
  downstream pins of the `108` rework plus the forced `ZeugnisKorpus`
  repair. `MARKE_EMIT` untouched.

## 9. Verification

- `./cargo-pruef` (build + `cargo test --no-fail-fast`) on this tree:
  **exit 0, 0 failures — 947 passed, 0 failed, 1 ignored**
  (the ignore is the pre-existing `seam::emit_corpus`). Total 948 —
  `README.md`/`DONE.md` now book 948 (the 902 in between was computed, not
  run: 891 + 11 without a toolchain).
- Machine: `free -g` beside the run (per the standing rule — a local run is
  a measurement, not a hope): 110 total, 80 available at run start.
  `ki-pc-fisch-101` was unreachable (DNS failure), so the server path was
  unavailable, not skipped.
- Corpus counts on disk: 107 clean examples, 668 gift files —
  `MARKE_EMIT=107` intact, `beispiele/108` still emits.
- `Export108.lean` namespace block byte-verbatim vs fresh `gabbro lean-g`
  output (checked with a script, not by eye); `src108` byte-identical to
  `beispiele/108` on disk (checked with a script).
- Lean, measured on this tree (toolchain present: elan + lake; `free -g`
  beside the runs: 110 total, 78–80 available):
  - `./lean-probe Export108.lean`: exit 0, 0 errors.
  - `./lean-probe ZeugnisKorpus.lean`, first run: 2 errors (the read_c
    cert at lines 375/379) — a STALE-OLEAN artifact, not a finding: the
    tree's `Export108.olean` (14:59) predated the lane's source edit
    (21:28), so the probe measured new pins against the old declaration
    (scratch `#eval`s confirmed it: `darf` false, `braucht = [L]` — the
    old world). Same class as the `rsync -a`/cargo staleness: a tool
    measuring a mixture of new source and old artifact. Resolved by
    rebuilding, not by editing.
  - `./lean-bau` (`lake build`, full `grammatik/`): exit 0, 0 errors,
    "Build completed successfully (206 jobs)" — this rebuilds Export108,
    UebersetzeAllg2 (whose direct probe twice exceeded the 10-minute
    timeout and is covered by the build instead: `lex108`, `parse108`,
    `elab108`, `kette108`, `lowerAllg108*` all appear in the build's
    axiom-dependency list) and ZeugnisKorpus with the fixed pin.
  - `./lean-probe ZeugnisKorpus.lean` after the build: exit 0, 0 errors.
- Full acceptance (`abnahme.py`, multi-hour) not run — beyond this lane's
  scope; the lane asked for `lean-probe`, `lean-bau`, `cargo-pruef`, and
  emission only if the emitter was touched (it was not).
