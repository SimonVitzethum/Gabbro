# MUSE-REPORT-340 — Lane 340: organisation plan A6 ScalarFloat

Branch `muse/340`, clone `/home/simon/Dokumente/gabbro-muse/a340`.
Owned paths only: `grammatik/Grammatik/X86/ScalarFloat.lean` (new),
one additive import at end of `grammatik/Grammatik.lean`, this report.

## What was there when this turn started

A preserved, uncommitted `ScalarFloat.lean` skeleton (§§1-4, ~1240 lines:
XMM file helpers + `FpZustand`/`laufAlt` extension interface, the 16
`FpBefehl` DOUBLE forms, `fpSchritt` with per-form step equations and
frames, the `fpRechne`/`ucomiFlags`/conversion source bridge) probed
green standalone. This turn added the missing task pieces (§§5-6),
the CUTS/`#print axioms` block, and the `Grammatik.lean` import.

## What was added (§5 refusal/profile, §6 witness, CUTS)

New definitions (7): `fpXmmZahl`, `fpZeugeXmm`, `fpZeugeKern`,
`fpZeugeT`, `fpZeugeT1`, `fpZeugeSpeicherNach`, `fpZeugeT2`.
New theorems (22): `fpXmmZahl_le_zwei`, `bites64_wf`,
`fpRechne_gleitRechne_zeuge`, `fpRechne_klasse_zeuge`,
`ucomiFlags_reserviert`, `ucomiFlags_nan_klasse_nur`,
`fpZeuge_tief0`, `fpZeuge_tief1`, `fpZeuge_effAddr`, `fpZeuge_fp`,
`fpZeuge_laenge`, `div_eins_durch_null`, `add_plusnull_minusnull`,
`fpZeuge_schritt1`, `fpZeugeT1_tief0`, `fpZeugeT1_speicher`,
`fpZeugeT1_effAddr`, `fpZeuge_schreib`, `fpZeuge_schritt2`,
`fpZeuge_liest`, `fpZeuge_speicher_aendert`,
`fpZeuge_div_unendlich_speichert`.

Content, mapped to the reviewer-approved direction:

- Scalar SSE2 DOUBLE only, checked `mxcsrGueltig` premise on every
  `fpSchritt` path (pre-existing; refusal theorems
  `fpSchritt_laenge_verweigert` / `fpSchritt_profil_verweigert` kept).
- One source op = one machine op: `fpRechne_gleitRechne` (pre-existing)
  plus joint divide instance `fpRechne_gleitRechne_zeuge`; no
  reassociation/FMA-contraction theorem exists anywhere in the file.
- NaN relation class-level: `fpRechne_klasse` (pre-existing) plus
  `fpRechne_klasse_zeuge`; payload non-observability lemma stays OPEN
  (CUTS). SNaN/flag reservation joint: `ucomiFlags_reserviert`
  (OF/SF cleared, AF defined-zero on every row) and
  `ucomiFlags_nan_klasse_nur` (any NaN-class operand forces the
  unordered row with reserved flags).
- Witness (joint, non-degenerate, memory-changing reached run):
  `fpZeuge_div_unendlich_speichert` — `divsd xmm0,xmm1` computes the
  divide special case `1.0/+0.0 = +inf` (`div_eins_durch_null`),
  `movsd [rax],xmm0` stores it at 8192, the word reads back
  (`fpZeuge_liest`), and footprint-top byte observably changed
  `0x00 -> 0x7F` (`fpZeuge_speicher_aendert`). Signed-zero companion:
  `add_plusnull_minusnull` (`+0.0 + -0.0 = +0.0`).
- Refusal: `fpXmmZahl_le_zwei` (every form takes at most two XMM
  operands — no 3-operand FMA, no lane-indexed packed form);
  `bites64_wf` (the word bridge admits binary64 only).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise of
  every new theorem is used. `#print axioms` for the 10 main theorems:
  all within `[propext, Classical.choice, Quot.sound]`
  (`fpXmmZahl_le_zwei`, `bites64_wf`, `fpRechne_klasse`,
  `fpZeuge_div_unendlich_speichert` use `Quot.sound` via `omega`/`simp`;
  nothing uses `Classical.choice`).

## Verification evidence

- `bash ./lean-probe grammatik/Grammatik/X86/ScalarFloat.lean`:
  `== 0 error(s) ...; exit 0` with the 10 axiom lines (all standard).
- Axiom probe via `./lean-probe` on scratch `.tmp/axiomprobe340.lean`:
  `'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms:
  [propext, Classical.choice, Quot.sound]` — unchanged.
- `bash ./lean-bau`: 385/386 targets build, including
  `Grammatik/X86/ScalarFloat.lean`; the final `Grammatik.lean`
  aggregator target crashes with
  `lean::exception: failed to create thread` (exit 134). Retried FIVE
  times with waits (up to 30 min); per-module state is green, only the
  import-all step dies.
- Control test (stash-test): with the one-line `ScalarFloat` import
  stashed (pristine tree), `./lean-bau` fails IDENTICALLY on the same
  `Grammatik` target. The aggregator failure is environmental
  (machine thread/memory contention under the lane cap), NOT caused by
  this lane's change. Disk is fine (180G free).
- Consequence per HARD RULE 8: the Lean files are NOT committed on a
  red `./lean-bau`. This report is committed alone; the verified work
  is preserved uncommitted in this clone:
  `grammatik/Grammatik/X86/ScalarFloat.lean` (new file, per-file probe
  green, exit 0, standard axioms) plus the one-line import
  `import Grammatik.X86.ScalarFloat` at the end of
  `grammatik/Grammatik.lean`. Recovery: re-add the import line,
  re-run `./lean-probe` on the file and `./lean-bau` when the machine
  allows, then commit through `./commit.sh`.

## Semantic mismatches resolved against source (not invented)

1. "Every `float` (f32) node refused at the bridge": source has NO f32
   node — `Ty.fl` is widthless and the model computes every source
   float in binary64 (`Typen.lean` header). There is nothing to refuse
   and no double-rounding paragraph exists anywhere; the bridge is
   f64-only by type (`bites64_wf`). The f32-vs-f64 counterexample stays
   owned by lane 286 (`Gleitprofil`), never duplicated here.
2. "SNaN reservation": the model `Klasse` has a single `.nan` (quiet
   vs signalling indistinguishable by construction); joint theorem
   proves unordered-row + reserved flags for every NaN-class operand.
3. Safety-corrections paragraph complied with: refusal Bools are
   validator admission (`fpEintritt`), never hardware faults; no
   alignment imposed beyond actual `read64`/`write64` permission
   behaviour (MOVSD claims no alignment requirement); no GPR narrow
   forms exist (CVTTSD2SI writes a full word via `regSet`); FP divide
   has no trap to rename (`1/0 = +inf` per model; integer DIV/IDIV
   untouched); no timing/cost claim anywhere; TSO/multi-byte
   atomicity explicitly not claimed (CUTS); `laufAlt` reuses canonical
   `schritt` untouched — no second evaluator of the 14 old forms.

## Apparatus notes (for the coordinator, not the proof)

- `lean-probe` changed mid-session (now `lean -j2 -M4096`, first line
  carries exit code). Direct `./lean-probe` invocation broke with a
  quoting error; `bash ./lean-probe` works.
- Transient `failed to create thread` crashes hit even untouched files
  (e.g. `Vektor.lean`) under load; resolved by waiting and retrying.
  One 24-error round was real (struct-update layout: no newline after
  a field comma in `{ x with ... }`; `decide` with free fvars after
  `cases`; defeq-through-def for state projections) — all fixed and
  re-verified green.
- Full `./lean-bau` green is still outstanding ONLY for the final
  `Grammatik.lean` aggregator target (resource crash, not an
  elaboration error). No commit until that is green.

## CUTS (also at the end of the Lean file)

NaN payload non-observability OPEN; SNaN/sticky-flag semantics
unmodelled; no decoder; no f32 admission; no rewrites beyond the four
arithmetic ops; no TSO/concurrency/cost claims; no interleaving of old
and new forms. Full final-byte/source/hardware correspondence OPEN.
Rule 13: no theorem quantifies over the listed source-syntax types;
`GleitOp` joint divide instances proved; the joint memory-changing
reached run is `fpZeuge_div_unendlich_speichert`.
