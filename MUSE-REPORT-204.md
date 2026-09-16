# MUSE-REPORT-204 — O12: fix `124/setze`, surface failing user obligations

Lane 204, branch `muse/204`. Scope: OFFEN.md O12 halves (a) corpus fix and (b) tooling;
(c) rule proposal as report-only. No Lean files touched, no checker passes touched,
no N codes, no gift numbers, no example numbers, no MARKE_EMIT changes.

## (a) Corpus fix — `beispiele/124-two-threads-private.gab`

`setze`'s `ensures` was `konto.slots[0].stand == x`; it now reads

```
ensures  konto.slots[0].stand == konto.slots[1].stand && konto.slots[0].stand == x
```

Choice: strengthen the contract, not rewrite the locked sections. The sections
(`locks L { setze(30); }`, `locks L { setze(70); }`) are the program's point —
two threads sharing `konto` under `L` — and the body already establishes both
slots. The new clause is exactly the `kP` shape of `Korpus124.lean`
(`.und kGleich (.eq slot0 x)`), so source and model now say the same thing.
A one-paragraph O12 comment stands above the clause in the file.

Re-measurement (binary rebuilt from this branch where noted):

| check | before | after |
|---|---|---|
| `gabbro pruefe 124` | `12 items, 0 errors, 6 hints` | identical (no refusal added, none removed) |
| `gabbro lean-g 124` (`gEns_setze`) | `.eq slot0 x` | `.und (.eq slot0 slot1) (.eq slot0 x)` — the `kP` shape; this is the only export diff |
| `gabbro emit 124` | — | byte-identical (contracts do not change the C) |
| full corpus `pruefe` summaries, `beispiele/*.gab` | — | 117/117 identical |
| full poison corpus, `beispiele/gift/*.gab` (expected code vs reported codes) | — | 701/701 identical |
| `./cargo-pruef` | — | exit 0, 0 failing (final code) |
| `./emission-pruef` | — | exit 0 |

So at checker level *nothing* moves — not even 124's counts — which is the
correct outcome: strengthening a contract adds no refusal. What moves for 124
is the export (one conjunction) and the new obligation-channel rows (b).

## (b) Tooling — the release obligation in the obligation channel

`gabbro obligations [--g]` and `gabbro counterexample` now end with a
`RELEASE OBLIGATIONS` section: one row per `locks L { … }` section, as Lean
`--` comments (generated files stay green; the checker verdict is untouched —
there is no new diagnostic path anywhere in this lane).

Implementation: `freigabe_abschnitt(tree: &Programm) -> String` plus helpers,
added to **both** `crates/gabbro-check/src/obligations_g.rs` (`pub(crate)`)
and `crates/gabbro-check/src/gegenbeispiel.rs` (private) — duplicated, not
shared, so neither subcommand depends on a checker pass or on `lean_g.rs`
(both owned by other lanes; the duplication is marked in both files).
New items per file: `index_text`, `ort_mit_index`, `als_schlitz`,
`zellen_expr`, `zellen_pred`, `RufZiel`/`ruf_ziel`, `Abschnitt`,
`rufe_in_block`, `rufe_bedingt`, `rufe_in_block_bedingt`,
`sperr_abschnitte`, `sammle_funktionen`, `sammle_sperren`, `menge_text`;
`export` in each file appends the section.

The check is syntactic and one-sided (documented at `freigabe_abschnitt`):
invariant slot cells (`T.slots[i].f`, index spelled out — `Ort::text` renders
every index as `[…]` and would merge the two O12 cells) against the union of
the section's *unconditional direct* callees' `ensures` cells
(current-state reads only; `old(..)` promises nothing about the release).
Conditional/indirect/ambiguous calls and unknown expression shapes contribute
nothing — the section may oblige, it may not acquit. Verdicts:
`RELEASE HOLDS (syntactic)` (not a proof) vs `RELEASE UNPROVED:` with the
exact gap (missing cells and/or uncounted calls).

Demonstration on the pre-fix shape (weak snippet, checker-clean at
`7 items, 0 errors`):

```
-- * haupt locks `L`: invariant over {konto.slots[0].stand, konto.slots[1].stand};
   setze promises {konto.slots[0].stand}
   -- RELEASE UNPROVED: no callee promises konto.slots[1].stand.
```

Post-fix, 124 reports both sections as `RELEASE HOLDS (syntactic)`.

Tests (extended, none weakened): `tests/obligations_g.rs` (10 tests) gains
`o12_schwaches_ensures_meldet_unbewiesene_freigabe`,
`o12_starkes_ensures_haelt_die_freigabe`,
`o12_beispiel_124_haelt_an_jeder_freigabe` (helpers `O12_KOPF`,
`o12_einheit`, `o12_export`; the weak test also pins `pruefe` at 0 errors —
the failure is stated, not diagnosed).
`tests/gegenbeispiel.rs` (9 tests) gains the weak/strong pair (helpers
`O12_KOPF`, `o12_einheit`, `o12_suche`). One repair during the lane: the
negative assertions use `"RELEASE UNPROVED:"` (with colon) because the
section header itself names both verdict words.

## (c) Rule proposal — report only, NOT built

Proposed rule (O12's "what would close it"): at `release` / every
locked-section exit, demand the lock invariant from what the section's
callees PROMISE. Measured with the tool from (b) itself:

- Denominator 1 — G-exportable corpus: `gabbro lean-g` succeeds on **15 of
  117** `beispiele/*.gab`. The rule question only arises there.
- Denominator 2 — lock invariants in the corpus: exactly **3 files**
  (`118`, `119`, `124`); every other `invariant` hit is a table/group
  invariant, and those locks carry none.
- Rows: `118` has no `locks` section (signature-held) → rule silent;
  `124` post-fix HOLDS at both sections → would not fall;
  `119` (`auffuellen locks K`, no calls, direct write `k.slots[0].x = 40`)
  → `RELEASE UNPROVED: no callee promises A.slots[0].x`.

So a promises-only rule falls **1 of 2 measurable files (119)** — and that
fall is a **false positive as a refusal**: 119's body re-establishes
`A.slots[0].x <= GRENZE` by direct constant write (its header documents this
as user obligation `L`, "recorded, not decided"). As an *obligation* the same
row is a true positive. Two further boundaries:

1. The measurable population is 2 files; most of the corpus never reaches
   the question (no G form). Any refusal built on this rule would need the
   re-measurement repeated as export coverage grows.
2. The symmetric gap is untouched: signature-held functions (`118`'s
   `gib`/`nimm` write guarded slots with no `ensures`) re-establish their
   invariant at *function return*, not at a section exit — the proposed rule
   is silent there by construction.

Recommendation: do **not** build the refusal (no N code). What this lane
built — the stated per-section obligation — is the correct half of the
proposal; a future lane can extend it to signature-held exits. Lane 202 owns
the passes; nothing here touches them.

## What remains open / notes

- No Lean work was done and none was needed: no file under `grammatik/`
  changed (`git status` shows only the 5 files above), so `./lean-bau` was
  not run; `./cargo-pruef` (exit 0, 0 failing) and `./emission-pruef`
  (exit 0) are the green gates for this lane. No new theorems exist, so rule
  13 has no Lean target; the executable witnesses are the weak/strong
  snippet tests plus the 124 test.
- On the wave preamble ("independent reviewer, do not change files"): the
  lane task explicitly orders the 124 fix and the tooling, and hard rule 5
  permits changing existing files when the task says so. I followed the
  task; the reviewer framing survives in (c), which is proposal-only.
- "124 only should move": at checker-verdict level nothing moves (correct —
  no refusal was added); 124 moves in the export and in the new channel.
  No other file moves anywhere.
- Limitation (mine, documented in code): short-name matching for locks and
  callees; duplicates resolve to UNPROVED rather than guessing. Transitive
  promises, arithmetic (e.g. 119's sum/bound reasoning) and aliasing
  (119's `k.slots` vs `A.slots`) are beyond the text — HOLDS is the absence
  of a syntactic gap, never a proof.
