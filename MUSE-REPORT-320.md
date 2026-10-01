# MUSE-REPORT-320: Independent review of candidate 319 (byte fetch/decode/step)

## Scope and method

- Reviewed ONLY the pinned snapshot copies in `.tmp/review/author-319/`
  (`MUSE-REPORT-319.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`, `PATCH.diff`,
  `grammatik/Grammatik/X86/Byteschritt.lean`, 510 lines) per
  `.tmp/review/SNAPSHOT.json` (author 319, HEAD
  `38e9a8610601810ea1bb14cedddbafe438d5192f`, base
  `ce698d8f918c5670c240903827cd6fc6c8c4ae32`, files: report + one
  additive `Grammatik.lean` import + the new file, clean tree).
  The author commit object itself is not present in this clone, so the
  hash is taken from SNAPSHOT.json; all content checks ran against the
  snapshot copies and `PATCH.diff`.
- Existing sources in this clone used only for dependency context
  (`Typen.lean`, `Codec.lean`, `Ausfuehrung.lean`, `Speicher.lean`); no
  other clone read, no code or central file edited.
- Ran `./lean-probe .tmp/review/author-319/grammatik/Grammatik/X86/Byteschritt.lean`:
  first line `== 0 error(s) in the COMPLETE output`, plus the full
  17-theorem `#print axioms` output (16 at `[propext, Quot.sound]`,
  `kanonisch_schritt_ueberein` at `[propext, Classical.choice,
  Quot.sound]`). This independently re-checks every `by decide`
  witness in this clone's dependency context. No full `./lean-bau`
  run (gratuitous for a single-file review; author's BUILD-EVIDENCE
  records `./lean-bau` exit 0, 0 errors, 382 jobs with matching axiom
  prints).

## What the candidate does (verified against code)

- New file `grammatik/Grammatik/X86/Byteschritt.lean` + exactly one
  additive import line (`import Grammatik.X86.Byteschritt`) in
  `grammatik/Grammatik.lean` (confirmed via PATCH.diff). No
  source/Spec/goal/Rust edits; file list matches the claim.
- `fetchCap = 15`; `ausfuehrbarN` checks execute permission of the
  first n bytes; `holeFetchAux`/`geholt` fetch the executable prefix
  of the ACTUAL `s.speicher.bytes` at `s.rip`, capped at 15, stopping
  before the first non-executable byte; `lesbar` is never consulted
  (confirmed: no occurrence of `lesbar` in fetch definitions;
  `Speicher` in `Typen.lean:41` carries distinct `lesbar` /
  `ausfuehrbar` fields, so the distinction is model-real).
- `fetchDekodiert` decodes the actual window with the existing
  `Codec.decode` and enforces `laenge + rest.length = fetched`,
  `laengeOk`, and `ausfuehrbarN` of the consumed prefix, else `none`.
- `byteschritt` takes ONLY the state (no caller `Decodiert`
  parameter), then the existing `Ausfuehrung.schritt`; any failure is
  `verweigert`. `ByteAusgang` has no halt constructor (weiter /
  verweigert only); `laufBytes` fuel exhaustion answers `weiter`.
- Theorems proved (all names from the report confirmed present):
  cap bounds, prefix-closure of execute permission, per-byte execute
  facts, `fetchDekodiert_entspricht` (fetch-to-decoder with checked
  facts), `byteschritt_weiter` + both refusal directions,
  `fetch_nutzt_nur_praefix` (consumed prefix executable, within
  window, window within cap), `kanonisch_schritt_ueberein` (forall
  `b : Befehl`, from the generic `roundtrip`, which in
  `Codec.lean:561` cases over all 14 `Befehl` constructors — the
  "admitted" wording in comments is conservative, not an overclaim).
- Witnesses, all `by decide` over actual byte memories at `rip`
  (never a side buffer), all re-verified by my own probe run:
  `kette_mov_store_load` (3-step MOV/STORE/LOAD, rcx = 42, data cell
  observably 0 -> 42, code at 4096 not data-readable),
  `opcode_geaendert_verweigert` (forged REX.X byte: intact steps to
  4106, forged refuses), `sprungziel_folgt_byte` (displacement byte
  16 -> target 4117, 17 -> 4118), `praefix_abgeschnitten_verweigert`
  (jump cut by permission boundary), `ohne_exec_verweigert`
  (readable-but-not-executable ret refused, readability held),
  `ret_an_grenze_ohne_ueberlesen` (1-byte ret at boundary steps to
  popped 12288 without over-read).

## Gate checks

- Forbidden tokens (word-boundary grep for `sorry | admit | axiom |
  native_decide | unsafe`): zero matches. The earlier BUILD-EVIDENCE
  rg hits are the English word "admitted" and `#print axioms`
  lines only. No `Prop`-typed premises; every theorem premise is used
  (checked each: hf/hs/hwin/hexe/hle/h all consumed); no `intro _` /
  `have _ :=`; no contract quantification; nothing called a
  semantics that cannot change memory (the memory-changing witness
  changes it); no conclusion restating a premise.
- Inhabitation: no theorem quantifies over the listed source syntax
  types (`Vertrag`, `Stmt`, `Endblock`, `ErgExpr`, `Expr`, `Args` —
  zero occurrences), and the owner task names no `ZEUGE:` target, so
  no `_zeuge` companion is formally required. The one `forall b :
  Befehl` theorem is over X86 target syntax and is jointly
  instantiated by the concrete multi-step memory-changing witnesses.
- Claim boundaries honest: CUTS block + report disclaim physical
  hardware, whole-source/whole-binary theorems, termination
  (`verweigert` = absence of transition, never normal termination),
  concurrency/atomics/interrupts/entry/ABI/relocation/costs, and
  record the OPEN arbitrary-input decoder length soundness with its
  precise statement and why fetch does not depend on it (runtime
  check + round-trip path). No new hardware/software assumptions;
  no genericity violation, no name/example-specific rule, no
  inferred ensures, no weakening.
- Report-vs-evidence cross-check: every reported definition/theorem
  name exists (30/30); axiom claims match both BUILD-EVIDENCE and my
  probe output; `./lean-probe` 0-error claim reproduced; the
  BUILD-EVIDENCE error entries are intermediate development steps on
  the way to the committed green state, not the final state (final
  entries: green probe, green full build, clean tree, commit
  `38e9a861`). File ends with CUTS + `#print axioms` per main
  theorem; English throughout.

## Findings

No material defect. Two non-blocking nits: (1) "admitted
instruction" phrasing understates `roundtrip`'s full-`Befehl`
generality — harmless conservatism; (2) candidate base
`ce698d8f` predates this clone's HEAD, but the file is purely
additive (new file + one import line) and probes green against
current dependencies, so no staleness risk.

## Verdict lines

CANDIDATE: 319 38e9a8610601810ea1bb14cedddbafe438d5192f
VERDICT: ACCEPT
