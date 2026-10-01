# MUSE-REPORT-625: Independent review of author 624 (FloatSourceObservations)

CANDIDATE: 624 f9929e6208c0562194201b1beb159745c23306e0
VERDICT: ACCEPT
Base: e9b62edd3dd7c746ba178a436588a3ca4888cfda (per .tmp/review/SNAPSHOT.json).

Reviewer lane 625, clone `/home/simon/Dokumente/gabbro-muse/a625`, branch `muse/625`.
Owned file only: this report. No source, Spec, checker, or other-clone edits.

## Method

- Fetched `muse/624` from `/home/simon/Dokumente/gabbro-muse/a624` into FETCH_HEAD;
  hash matches `.tmp/review/SNAPSHOT.json` (`f9929e62…`, `clean: true`).
- Read the full candidate file (605 lines), the owner task, `MUSE-REPORT-624.md`,
  `BUILD-EVIDENCE.json`, and the candidate-era producers/doc
  (`Gleitkomma.lean`, `Syntax.lean:404-408`, `Semantik.lean:247-248,351,625,874-878`,
  `Typen.lean:88-114`, `X86/ScalarFloat.lean`, `X86/Gleitprofil.lean:163`,
  `X86/Codec.lean`, `dokumente/x86/FLOAT-OBSERVATION-CLOSURE.md` P1)
  in an isolated worktree `.tmp/wt624` at the exact pinned HEAD (removed after).
- Re-ran the queued wrappers there (copies of the then-absent `lean-probe`/`lean-bau`
  scripts, same `lean-slot` + `lake` invocation, warm `.lake` copied from this clone):
  `./lean-probe grammatik/Grammatik/X86/FloatSourceObservations.lean` and full `./lean-bau`.
- Static scans for forbidden tactics, discarded premises, name collisions vs HEAD.

## Findings

- Build: `./lean-probe` gives `== 0 error(s) in the COMPLETE output; exit 0`;
  full `./lean-bau` gives `exit 0`, `Build completed successfully (446 jobs)`.
  Matches the author's claimed evidence; independently reproduced.
- Axioms: float core lemmas `[propext]` or none; `eval` pins, joint witness and
  companions `[propext, Classical.choice, Quot.sound]` inherited from `Semantik.eval`;
  `null_muster_rundweg`/`cvttPaket_gleitRoh` add `Quot.sound` from the producer
  round-trip. All within the standard goal axioms; nothing new introduced.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `intro _`/`have _ :=`,
  no Prop-typed premise (only the defined comparison predicate `vergleichsGleich`).
  Every premise is used (`hx`/`hy`/`h` in `vergleichsgleich_passt`,
  `hw`/`hx` in `cvttPaket_gleitRoh`).
- Real interfaces, all confirmed at the candidate commit: `fllt`/`flle` eval arms
  are definitionally `gleitLt`/`gleitLe` (`rfl` pins genuine); `Expr.eq` takes
  only `.int` arguments (F-EQ exclusion genuine); `Gleit` carries its finiteness
  proof (`kein_gleit_nan` genuine); `gleitPasst`/`gleitRoh`/`gleitEndlich`/`bruch`
  real; `bites64_muster64`, `ucomiFlags`, `cvttPaket`, `fpRechne_klasse` real;
  `Codec.lean` has no FP/decode forms (the "no byte sequence decodes to a float
  form" audit note still holds). No self-invented semantics, no new interpreter,
  no checker/emitter/friend-file touch. Patch is purely additive (1 import line).
- Witness `null_beobachtung_zeuge` is non-degenerate and joint: one table, contract
  AND function write it (`fltWitHw`, `fltWitSchreibt`, both `rfl`), reached one-step
  `assignSlot` run ending `.ok`, slot `-0 -> +0` with decided value inequality AND
  decided `zuBits` inequality (concrete distinguishing bit operation), agreeing
  `vergleichsGleich`/`gleitRoh`/`gleitPasst`. Refusals `nan_passt_verweigert` and
  `bereich_passt_verweigert` are proved equations over actual operations.
  No signed/modular/FP/fault or byte/word conflation; payload equality never claimed.
- New connections for consumers: generic `vergleichsgleich_passt` (every range) and
  generic `cvttPaket_gleitRoh` (finite well-formed values), both precisely stated.
- No name collisions against current HEAD (names absent there; file unmerged so far).

## One blemish (not repair-blocking)

- CUTS line "Covered source operators … `gleitNarrow` …" overstates: no theorem
  mentions `gleitNarrow`. Mitigating fact: the `gleitNarrow` block arm dispatches
  exactly through `gleitPasst` (`Semantik.lean:874-878`), so the generic
  `vergleichsgleich_passt` already transfers to its dispatch — the connection is
  real but unstated. Suggested one-line follow-up (any future lane): a
  `gleitNarrow`-dispatch agreement corollary citing `vergleichsgleich_passt`, plus
  dropping `gleitNarrow` from that CUTS line until then.

## Open (as the candidate honestly records)

Generic comparison-agreement-implies-`gleitRoh`-agreement; F-EQ checker refusal (P0);
decoded-byte FP steps; sNaN/MXCSR channels; full source-to-final-loaded-bytes.

## Task assessment

Nothing in either task is wrong. Lean-only lane correctly ran no `cargo-pruef`
(no Rust files touched). The report's build/axiom claims reproduced exactly.
