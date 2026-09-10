# Schreiblast, effects-first census — Lane S, 2026-09-10

Measured, not estimated. Binary `target/debug/gabbro` built 2026-09-10 03:55
(newer than all sources — no `rsync -a` mixture class). Populations name
their N everywhere (W25); `beispiele/*.gab` below never includes `gift/`.

## 1. Census: the 705/188 table today

`gabbro ceremony --per-site beispiele/*.gab` — 71 files (64 on 2026-09-01),
1125 sites (was 1054). Per-site lines only; the per-file `may fall` summary
lines were counted once by mistake and removed (they inflated every rule).

```
                          2026-09-01 (64 files)    today (71 files)
  BOOKKEEPING  T1+T2+T7+T8        462+211+25+7=705    487+235+24+11=757
  OWN LOGIC    T3+T6+T12+T5+T4      82+65+26+9+6=188   87+65+43+9+6=210
  HARDWARE     T10+T11+T9             35+35+23=93        36+37+14=87
  DERIVABLE    A1+A4 (+R*)               68 (R 0)        4+67 (R 0)
  TOTAL                                  1054                1125
```

The mark moved with the corpus, not against it: `757 → 0` with `210` staying.
Seven new files since 09-01 carry the drift (+52 bookkeeping, +22 logic).
Redundant rules (R1–R4) fire nowhere in the corpus — same as 09-01.

## 2. Derivable vs load-bearing, per entry (the 462 question)

`gabbro effects --compare beispiele/*.gab` (derivation over BODIES,
`ableitung.rs`) — the base §24 orders first, because it cannot inherit
emitter defects:

```
  `effects` entries at a function declaration        482   (was 439)
      on a function WITH a body                      389   (was 359, 189 functions)
      on `extern`/`prim` — NO body                    93   (was 80, 81 functions)
  RIGHT  covers a derived effect                     281
  RIGHT  `pure`, derived set empty                     35
  TOO WIDE  covers nothing derived                     64   (16 %)
  TOO NARROW  `pure` contradicted                       4   (known-world-name frame edge, §38)
  outside  `diverges`                                   5
  UNMEASURED  lower bound (R16)                         0   (hull base still tears 3×)
  TOO NARROW  derived, covered by no line              40   (holes, counted on the derived side)
  fixpoint: at most 2 rounds, widening fired 0x
```

Machine-writable (derivable from the body): the 281 RIGHT + 35 pure-empty —
316 of 389 (81 %) are consistent with what the bodies already say, so an
elaborator could write them. Load-bearing (a human must state): the 93
`extern`/`prim` entries (trust surface, no body — can never fall) plus the
40 holes the derivation finds and no line covers, plus the judgment over the
64 TOO WIDE (dropping them is safe for the checker but changes what a reader
sees — axis 2, a decision, not a measurement).

Side-by-side with the hull base (`gabbro abi --compare`, same files):
hull says TOO WIDE 102, derivation says 64. The 38-entry gap IS the bias
§38 named — the hull inherits callee padding, so it acquits over-declared
callers. Measured, both bases, one population.

Lock-rank over both bases (`effects --lock-rank`, 598 units incl. gift and
`messung/proben`): 6 refusals stand in both, the derivation frees exactly 1
(the built probe `460-rangprobe-an-zu-weiter-wirkung.gab`, H012), raises 0.
§39 reproduced on today's tree. Over-declaration is silent AND friction-free
in the corpus — the one freed refusal had to be built.

No new counter was needed: `zaehle-zeremonie.py` keeps its register
(A4/ceremony); the per-entry split is the tool's own `--compare` output.
`instrumente/` untouched.

## 3. Costs guardian: no ratchet exists

`pruefe-zahlen.py` carries no costs numbers; no watcher in `instrumente/`
compares `gabbro costs` output against a file. K001 holds per site — over the
whole tree (728 files, `.claude/` worktrees excluded) 953 measured sites give
843 padded (88 %), 83 exact, 27 negative, and every negative is intentional:
gift probes, `messung/proben` + `messung/fnptr-proben` demonstration probes,
and the `33-rekursion` cycle trio (70 vs 64 — a cycle promise means one pass,
«K5.4», and `pruefe` stays silent there where `gabbro costs` counts the
fixpoint: an unrecorded divergence between the two computations).

Clean `beispiele/` (71 files): 197 sites, 156 padded (79 %), 38 exact,
3 negative (the recursion trio). 113 of 197 (57 %) could DOUBLE without
K001 biting, 24 (12 %) could grow 10×. §40's 61 % stands, direction
corrected there: a measured watcher covers FEWER sites (bodies only —
210 `costs` lines vs 179–180 computed in `beispiele/`) but in BOTH
directions at single-op resolution.

Design (REPORT, not built — needs checker-adjacent work): `gabbro costs`
gains a write mode for `modul::name → computed` (~10 KB), a compare script
after the `377/377` anchor pattern turns any movement red; the `costs`
clause stays as a right to promise TIGHTER than measured. Cost class: the
full-tree run above took seconds, not minutes.

## 4. E005: contradiction only — both directions pinned

Code path (`wirkungen.rs::funktion`): `effects: None` → E001 and NO body
comparison at all; `Some` → E005 (writes) / E010 (reads) / E006/E007 (locks).
Measured with `gabbro pruefe`:

```
  omission + writing body   04-ohne-wirkungen        E001 only, no E005  (existed)
  omission + reading body   700-lesen-ohne-klausel   E001 only, no E010  (new)
  omission + pure body      701-rein-ohne-klausel    E001 only           (new)
  contradicts `pure` (write)  28-pure-schreibt       E005                (existed)
  contradicts list (write)    29-wirkung-ueberschritten E005             (existed)
  contradicts list (read)     62-lesen-ohne-reads    E010                (existed)
  contradicts `pure` (read)  /tmp probe              E010                (measured, no probe)
```

Consequence for the intermediate state: the E001/E005 split already IS the
two-register comparison — omission can never slip through the crack between
them because omission never reaches E005's question. What the state still
owes (§25/§41): the origin path is computable (`Ableitung::pfad`) but in no
refusal, and whether E005/E008/E010 carry the same verdicts on the derived
set instead of the declaration is not run.

## Open points (not mine to move)

- `instrumente/zaehle-gifttreffer.py` MARKE_SAUBER 271 → 273 expected
  (both new probes fall sauber — verified below — but the mark file is
  outside my lane); MARKE_VERDECKT unchanged.
- `cargo test` (`beispiele.rs` contains-check) and the `blindstellen`
  populations in `pruefe-zahlen.py` move with two more gift files; the
  heavy runs belong on `ki-pc-fisch-101`, unreachable today — verified the
  probes with direct `gabbro pruefe` runs only.
- `crates/gabbro-check/src/wirkungen.rs`, `saetze.rs`, `programmlogik/`
  untouched; no rule changes proposed. `beispiele/33-rekursion.gab`
  costs/pruefe divergence (70 vs 64) still recorded nowhere but here and §40.
- Re-ran everything touched: ceremony 1125, effects --compare 389+93,
  abi --compare 389+93 (gap 38), lock-rank 6/1/0, costs 953; gift
  700/701 each `1 errors, 0 hints` with exactly the expected code.

## Commands (all against the prebuilt binary, light local runs)

```
  ./target/debug/gabbro ceremony --per-site beispiele/*.gab
  ./target/debug/gabbro effects --compare beispiele/*.gab
  ./target/debug/gabbro abi --compare beispiele/*.gab
  ./target/debug/gabbro effects --lock-rank beispiele/*.gab beispiele/gift/*.gab messung/proben/*.gab
  ./target/debug/gabbro costs beispiele/*.gab            # + gift/treiber/caprock for the 953
  ./target/debug/gabbro pruefe beispiele/gift/700-lesen-ohne-klausel.gab \
                               beispiele/gift/701-rein-ohne-klausel.gab
```
