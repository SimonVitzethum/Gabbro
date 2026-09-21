# Review 2026-09-21 — integration (I0)

Branch `review-0921-integration`, local only, from master `4e6c2435`. Not merged into master,
not pushed. Built and tested **locally on the laptop** (fisch unreachable; Simon's decision of
2026-09-21). Logs: `.claude/muse-arbeit/kratz/review-0921/i0/` (untracked).

## 1. Merge order

All thirteen review branches merged with `--no-ff`, in group order. **None conflicted**: git
resolved every overlap (TODO.md rows from G02/G09/G11/G12/G13, `saetze.rs` from G04/G06/G08/G09,
`kosten.rs` from G09/G11, `emit.rs` from G04/G07) textually, and the result was checked by hand
where the task named an overlap.

| Group | Branch | Head | Merge commit |
|---|---|---|---|
| G01 | worktree-agent-a44ac063a1276ba50 | 13d9dadf | 6a6b9547 |
| G02 | worktree-agent-afaa5893cdf87417f | 724001aa | cb9f726b |
| G03 | worktree-agent-a23cb3c5dfec6212a | 102b1704 | 0c997c5c |
| G04 | worktree-agent-afe2ae83a9b89576c | 680f9268 | 4c9c9e56 |
| G05 | worktree-agent-a797b5d1a6c2ffd5e | d902aa64 | 0b8592c9 |
| G06 | worktree-agent-a9e7623d8deebc77e | 7ab3e03a | 8e2a2002 |
| G07 | worktree-agent-a32fd8b00525964be | cf2c4a1a | 96f519f2 |
| G08 | worktree-agent-a2b8e54d9fe83f2bd | b9e9d415 | 474dcaf9 |
| G09 | review-0921-g09 | 7aeff51b | 6baadf16 |
| G10 | worktree-agent-a0eccf671b4f7a8a4 | 016b9599 | f25774c4 |
| G11 | worktree-agent-a6a693b2113452f28 | c0c61dab | 527ee3ef |
| G12 | worktree-agent-a51c984adf1f7c84e | abf4fc0f | ce2f16da |
| G13 | worktree-agent-a294c9ad72799f508 | 7e0ab9b5 | 33b38940 |

Then one integration fix, `59456e46` (section 3).

### Named overlaps, checked

- **`kosten.rs`, G09 + G11.** G09 replaces the hand list in `enthaelt_traverse` by
  `crate::unterbloecke` (so `child { … }` is walked); G11 adds `StmtArt::Child` arms to
  `schleifenzusagen` and `sperrbloecke`. Different functions; both kept, both present after the
  merge.
- **G07's `endet_immer` fix vs G09 F3 (high).** G09 F3: `kosten.rs` `block`/`rest` take
  `max(durch, vorbei)` after `if c { … }` whenever `crate::endet_immer(rumpf, &[])`, and an
  integer `match` with every arm returning was read as ending. G07's `49a8996d` adds
  `StmtArt::Match(m) if int_match_may_miss(m) => false` to `lib.rs::endet_immer`, which is the
  very function `kosten.rs:849` and `:870` call; the recursion reaches nested blocks. **So G07's
  fix covers G09 F3** (the second remedy G09 itself named). It is the conservative reading, not
  the exhaustiveness refusal; the refusal stays F1's work.
- **Cosmetic, for F1:** `49a8996d` inserted `int_match_may_miss` between the doc comment of
  `endet_immer` and the function, so rustdoc now attaches the long `endet_immer` comment
  (lib.rs ≈1398–1434) to `int_match_may_miss`, and `endet_immer` carries none. Not changed here.

## 2. Build and test results

`free -g` before each heavy run (total / used / free / shared / buff-cache / available, GB):

| Run | when | free -g |
|---|---|---|
| `lake build` (integration, 1st) | 22:41:25 | 31 / 10 / 6 / 1 / 15 / 20 |
| `lake build` (integration, after fix) | 22:44:00 | 31 / 10 / 6 / 1 / 15 / 20 |
| `cargo test` (integration) | 22:44:16 | 31 / 10 / 6 / 1 / 15 / 20 |
| `cargo test` (master baseline) | 22:46:32 | 31 / 10 / 2 / 1 / 19 / 20 |
| `pruefe-emission.sh` (integration) | after `cargo build` | 31 / 10 / 6 / 1 / 15 / 20 |
| `pruefe-akzeptiert-diff.py` | — | 31 / 10 / 6 / 1 / 15 / 20 |

Peak seen during the Lean build: one `lean` process at 3.4 GB RSS (`CText104Zeuge`), 17 GB
still available. Nothing ran concurrently with `cargo test`; `programmlogik/_pruefung/lauf.sh`
was not run.

Lean caches were seeded by `cp -a` from the main tree (`grammatik/.lake` 933 MB,
`programmlogik/.lake` 7.7 GB).

| Check | Integration | Master `4e6c2435` |
|---|---|---|
| `grammatik` `lake build`, 1st | **RED**: 279/281, one error, `Grammatik.SimPruef` (`erwartet_ist_r124` false) | not built (the one error is in a theorem only the review adds) |
| `grammatik` `lake build`, after `59456e46` | **GREEN**, 281 jobs, 0 errors | — |
| `#print axioms gabbro_ziel` (`lake env lean`, `import Grammatik`) | `[propext, Classical.choice, Quot.sound]` | — |
| `sorry`/`native_decide`/`axiom` in `grammatik/Grammatik` | none (only prose mentions); the only `sorryAx` in the build log was the failing `erwartet_ist_r124` of the first run | — |
| `cargo test --no-fail-fast` | **GREEN**: 68 result lines, **1235 passed, 0 failed, 1 ignored**; build 15 s, total 59 s | GREEN: 68, 1233 passed, 0 failed, 1 ignored |
| difference | `tests/intmatch.rs` 13 vs 11 (G07: `integer_match_does_not_end_a_narrow_arm`, `label_outside_the_scrutinee_type_is_refused`); every other collection identical | |
| compiler warnings | 12, identical set to master | 12 |
| `pruefe-emission.sh` | **ALL PASS** — 37 run through, 288 of 288 compile, 2 reverse probes, exit 0, 1 min 17 s. **ASan stage 6b NOT RUN on this machine** (36 units): not a passed probe | not run |
| MARKE_EMIT counters | not moved; the guardian asked for no change | — |
| `pruefe-saetze.py` | **PASS** (exit 0): 429 codes, 179 sentences, 55 without sentence, 0 invented | — |
| `pruefe-kennungen.py` | **PASS** (exit 0) | PASS |
| `pruefe-todo.py` | RED, **16 findings** | RED, the same 16 findings (identical text) → pre-existing |
| `pruefe-englisch.py` | RED, aborts at "Quellsprache: 7965 of 41366 comment lines German" | RED, "7965 of 41275" → pre-existing; the review adds 91 comment lines and 0 German ones |
| `pruefe-akzeptiert-diff.py --selbsttest` | **ok** both directions (104 agrees; doubled start refuses at `einzeln`) | — |
| `pruefe-akzeptiert-diff.py` (full) | **exit 0**: compared 20, skip 191, partial 2 (109, 59: entry/boot roots), **findings 0**, not-measured 0; every component true on 18/18 comparable programs | — |

G03's two [UNBUILT] commits (`0ac32e54` gCs incl. globals, `12b7c007` K2 whole-entry pin) are
thereby measured: the script runs, both directions of the self-test hold, zero disagreements.

## 3. Failure caused by a review fix, and its repair

**`Grammatik.SimPruef`: `erwartet_ist_r124` (G01, `e92c458e`, unbuilt) is false.** `decide`
proved the conjunction false. Evaluated with `#eval`:

```
(List.range 9).map gOfB = [0, 0, 1, 1, 2, 2, 3, 4, 4]
erwartetGB               = [0, 0, 1, 1, 2, 2, 3, 3, 4]
```

The other three tables agree. `posB 7 = .an [] ρ0` (after `cGib`), and `Schlusssatz124.lean`
maps it to residue 4, which is what the proved `sim124` uses. The hand-typed literal was wrong
**in both languages at once**: Lean `erwartetGB` and `cert124_printed`, Rust
`corrcert.rs::SimCert124::erwartet_g_b` and its two byte-pinned test strings. That is exactly
the failure G01's theorem was written to catch, so the theorem stays and the data was fixed
(`59456e46`): Lean literal in two places, Rust literal in three. `lake build` and `cargo test`
(including `sim124_lean_literal_stimmt_mit_simpruef_ueberein` and
`sim124_json_traegt_programm_und_vier_tabellen`) green afterwards.

**Consequence for the record:** on master the stage-(b) certificate for 124 carries a wrong
`gB` entry and `pruefeSim` accepts it, because the checker compared two copies of the same wrong
literal. `MUSE-REPORT-206.md:77` quotes the wrong literal; left as history. F8 (which owns
`simpruef_liefert`'s claim) should cite this.

## 4. Reverted commits

None.

## 5. Open, for the fix lanes

- **F1:** G09 F3 is covered by G07's `endet_immer` change (section 1); the doc-comment
  misplacement in `lib.rs` goes with F1. The exhaustiveness refusal (N411–415) is still open.
- **F8:** the `gOfB` literal finding above; `simpruef_liefert` still ignores the certificate
  (G01 finding unchanged).
- **ASan (emission stage 6b)** was not run; it needs fisch or a local ASan runtime.
- **Not run here:** `abnahme.py`, `pruefe-zahlen.py`, `mutiere-pruefer.py`, `pruefe-beweise.sh`
  (no Isabelle run), `programmlogik/_pruefung/lauf.sh`.
- Every other [UNBUILT] commit of G01–G13 is now built and tested as part of this branch.
