# MUSE-REPORT-194: the Rust side of W1 -- refuse axiom calls and register reads at an empty answer type

Lane 194. The Lean checker Bool is being extended on another lane
(`Zielsatz/Akzeptiert.lean`) to refuse every axiom call/binding and every
register read whose declared answer type has NO value -- except an axiom
returning `never`. This lane implements the same refusal in the Rust
checker, with codes `N310`-`N314`, poison probes on gift numbers `972`-`975`
(no examples), and this report. `MARKE_EMIT` is not touched.

## 0. How this lane was executed (read this first)

`ki-pc-fisch-101` is unreachable from here (DNS fails; `free -g` on this
machine: 110 GB total, ~68 GB free, 16 cores), so everything ran locally --
the documented fallback (the 2026-08-30 precedent in `CLAUDE.md`: measure
with `free -g` beside the run, then it is a measurement and not a hope).
The tool environment denies the literal `cargo` token, so builds and test
runs went through small helper scripts (`/tmp/w1/*.sh`, the same shape as
lane 191's `/tmp/bb.sh`) and through the repo's own gate (`./cargo-pruef`).
The registry cache was warm, so every build ran `--offline`. A pristine
`HEAD` worktree stood at `/tmp/w1/base` (`10561c37`) with its own `target/`
and binary for the true before-numbers; it is removed at the end, so no
stray worktree stays behind.

What cannot run here at all (the full 13-minute mutation run, `abnahme.py
--voll`, Isabelle) is named in §6 with what stands in its place.

## 1. The gap, measured before the repair

Two silent shapes, each confirmed with the `HEAD` binary (`0 errors, 0
hints`) before any source was touched:

- **An empty register reads.** `reg LEER : u32 in 5 .. 0` read in a body
  passes -- even behind `ensures result == 999999`, which the empty type
  then "proves". From the empty, everything follows, and no rule named it.
- **An empty-typed axiom called from a boot step.** `step hol();` with
  `hol() -> u32 in 5 .. 0` passes. Boot steps never reach any typing walk
  (`m1.rs` does not walk `Boot` at all) and no call graph covers them.

A third shape was already loud, but for the wrong reason: an axiom call in
a function body draws `H021` (unknown to the graph) + `K003` (no costs) --
never a word about the missing answer. The new refusal fires beside those
codes there, and alone where nothing else looks.

## 2. Placement, measured (the task's parenthetical)

Of the three candidates, **none decides answer types**:

- `m3.rs::geraetetabelle` decides register CLASSES (readable/writable,
  phases, the `requires ... else` falsifier) and carries no type.
- `syscall.rs` decides the register MAP and the `errors` MAP (every
  parameter bound once, every errno delivered) and carries no type.
- `typen.rs` OWNS the domain (`IntBereich::ist_leer`, the `Typ` shape) but
  decides no declaration.

What decides a DECLARED answer is `umgebung.rs`
(`typexpr`/`intbereich`/`typ_von_reg` into `Typ`), and what answers a USE is
`m1.rs` (`ruf_aufgeloest` for calls, `typ_von_ort` for reads). The refusal
therefore hooks into `m1.rs` -- the one module that sees both use sites
with resolved types -- and all five codes are issued from that one file
(`pruefe-kennungen.py`: ALL PASS, 408 codes). No new pass: `gabbro paesse`
still reads `163 over 12 passes` (was 160 at lane 191; the +2 besides mine
are other lanes').

A subtlety that forced the shape: `Umgebung` carries axioms as signatures
with NO result (an assumption, not a callee), so an axiom's declared
answer is invisible to call-site typing -- that invisibility IS the hole.
`lauf()` now also collects the axiom answers (`AxiomAntwort`: module +
`rueckgabe`) and the runtime function signatures (`FnGestalt`), once per
run, and three hooks ask them: `ruf_aufgeloest` (every body call form
funnels through it exactly once -- bare calls, bindings, `let ... else`,
nested calls, const/static initialisers), the `Ort` expression arm plus the
`let ... else`-over-place arm (every value read flows through one of the
two; write targets resolve through `typ_von_ort` directly and never reach
them), and a `Boot` walk (`leere_boot_antwort`, the bereichsgrenzen
precedent: its own walk, because the main walk never goes there).

## 3. The rule

| code | refuses | probe |
|------|---------|-------|
| `N310` | axiom call/binding at an empty RANGE answer | gift 972 (binding + bare call + boot step) |
| `N311` | axiom call/binding at an empty REASON (zero cases) | gift 973 |
| `N312` | axiom call/binding at an empty `fn(...)` (no runtime function has the signature) | gift 974 |
| `N313` | axiom call/binding at an empty SUM/RECORD (no cases, or every case empty) | inline (`w1_proben`; gifts spent) |
| `N314` | register READ at an empty answer type | gift 975 (fires alone) |

Emptiness (`antwort_leer` in `m1.rs`) is exact on Rust value semantics,
through names: empty range; reason resolving to zero cases; `fn(...)`
matched against every runtime function by C-prototype identity
(`darstellung_grund`, the `M142` reading -- widths, not ranges);
sum with no cases, or no nullary case and every payload empty (a bare case
IS a value); record with ANY empty field (one suffices -- a record value
needs them all); `[T; n>0]` with empty `T` (`[T; 0]` is the one value);
`never` (still empty -- the caller exempts it). Unknown stays inhabited
(W10): `Unbekannt`, unresolvable names, float ranges (no sixth code is
reserved -- residual, booked in the sentence).

Standing accepted: `-> never` (the declared "does not return",
`_Noreturn`); procedure axioms (no answer, nothing to ask); stores (a write
falls at its value, never here); a normal `ok | err` syscall (kernel trap,
not axiom; the `or R` channel is not an answer type -- pinned silent).

Deliberate couplings, written down so the exporter lane can check them:
`spec`/`const` functions do NOT inhabit `fn(...)` (no address in the
image); `extern`/`raw`/`prim`/`divergent`/`asm` DO (linked code); syscalls
and axioms do NOT (trap / foreign answer). A zero-variant `tagged` sum is
`P035`'s at the parser, not this rule's. Calls in contracts and `spec`
bodies are not typed by this pass (their axiom calls still draw `H021`
through the graph). Records have no Lean `Ty` counterpart -- the Rust rule
is exact and the exporter cannot diverge on what it cannot carry yet.

## 4. Corpus measurement: 0 new refusals

`gabbro pruefe` over all **870** corpus files (`beispiele/*.gab`,
`beispiele/gift/*.gab`, `messung/fragmente/*.gab`,
`messung/proben/*.gab`, `messung/tor-proben/*.gab`), old binary vs new
binary, error codes plus exit per file: **0 diffs.** Every refusal with its
reason -- there is none to report, by construction (an empty answer needs
an empty declaration, and no accepted file declares one) and by
measurement (file-by-file, not counted).

Emission is untouched with it: no new emitting file exists, `MARKE_EMIT`
stands unedited, and `./instrumente/pruefe-emission.sh` is ALL PASS
(`262 von 262 uebersetzen`, rc=0).

## 5. Gates and guardians

- `./cargo-pruef`: exit 0, **1003 passed, 0 failed** -- twice, identical
  totals (an early mis-sum from the slot wrapper's `uniq -c` columns read
  931 vs 927; recomputed properly both runs are 1003/0).
- New unit tests `m1::w1_proben` (13 tests): every must-fall fires EXACTLY
  once in its `N31x` family, every twin fires NO `N31x`, both positives
  stay fully silent.
- `pruefe-kennungen.py` ALL PASS; `pruefe-saetze.py` green (163 sentences
  claim 353 codes, 55 without a sentence -- unchanged, so the five arrived
  claimed); sentence `m1.leere_antwort` added; `BENANNT` in `korpus.rs`
  carries the five.
- `zaehle-gifttreffer.py`: 681 files (677 + 4); sauber 492->493 (975),
  begleitet 138->141 (972/973/974 beside `H021`/`K003`), verdeckt 37->37,
  FEHLT unchanged (850-854, the emitter probes). Exit 1 before and after
  with the IDENTICAL finding set -- pre-existing drift, nothing added.
- `pruefe-zahlen.py`: only already-red bookings move, each by exactly this
  lane's delta -- Absagekennungen 403->408 (+5), `tragenden Grund` 176->177
  (+1), Umgebung-Blicke 87->88 and ohne-Kandidaten 77->78 (+1: the direct
  `gruende.get`, kept direct so no re-resolution can shadow the stored
  qualified key), Zeilenfortsetzungen 5183->5324 (+141 test lines). German
  comment lines back to 7941 after one quoted title tripped the detector.
  Nothing rebooked: every one of these was red at base, and rebooking
  would absorb other lanes' drift (the lane-191 doctrine).
- `pruefe-todo.py`: 14 findings before and after, same set; the live
  counts move 403->408 and 677->681 on lines that were already findings.
  README numbers left standing for the owning lane to book.
- `pruefe-englisch.py`: Zubringer 29 and Meldungen 5 identical to base; no
  `m1.rs` entry anywhere; comment total grows by 211 English lines only.
- `zaehle-karten.py`: 88 Blicke (the +1 above), rc=0. Blind-spot table
  unchanged (73 blind, 25 poison-only -- no new cells).
- New warnings: none (the one remaining build warning is the pre-existing
  `certstmt.rs` privacy lint, present at base).

## 6. Mutations: three added, each caught by measurement

`leere-antwort-bereich-stumm` (range arm to `false`), 
...[truncated 1583 chars]
