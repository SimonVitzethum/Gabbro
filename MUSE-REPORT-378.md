# MUSE-REPORT-378 — Independent exact-candidate A6 review of 340 ScalarFloat

Branch `muse/378`, clone `/home/simon/Dokumente/gabbro-muse/a378`.
Owned deliverable: this report only. Candidate staged privately
(`grammatik/Grammatik/X86/ScalarFloat.lean` + one additive import at end of
`grammatik/Grammatik.lean`), verified, then fully restored before this commit.
`git status` after restore: clean except this untracked report.

## Candidate identity

- `CANDIDATE: 340 de523a41904a2a16f2980256db378d1779bfb06b`
- Base `f737a6f04c22dfdd9499532e0535ad119cf2e56d`; PATCH touches exactly the
  three owned files (`MUSE-REPORT-340.md`, `grammatik/Grammatik.lean` one line,
  `grammatik/Grammatik/X86/ScalarFloat.lean` new, 1508 lines). No reserved
  path (`OptimizationRules`/`OptimizationWitnesses`), no checker/Typen/Rust/
  emitter/doc edits. My clone HEAD `3dce9fa2` is newer than the candidate base;
  the candidate was verified against current master (full build 416 jobs,
  vs author's 386 on the older base).

## What I did

1. Verified clone path/branch (`muse/378`); read `OWNER-TASK.md`,
   `MUSE-REPORT-340.md`, `BUILD-EVIDENCE.json`, `PATCH.diff`, `SNAPSHOT.json`.
2. Read the full 1508-line candidate file in four slices (§§1–6 + CUTS).
3. Static checks on the exact snapshot: forbidden tokens (`sorry`, `admit`
   as identifier, `axiom`, `native_decide`, `unsafe`) — one English false
   positive only ("to admit", line 1247); `: Prop`-typed premises — none;
   source-syntax quantification (`Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/
   `Expr`/`Args`) — comment-text only (CUTS), no premise.
4. Resolved every cited canonical name against live master source:
   `mxcsrGueltig`/`FPKontext`/`kontextReset`/`kontextReset_gueltig`/
   `muster64`/`bites64`/`ausBits_wf`/`fadd64`…`fdiv64` (`Gleitprofil.lean`),
   `ripNach`/`laengeOk`/`effAddr`/`regSet`/`schritt` (`Ausfuehrung.lean`),
   `read64`/`write64`/`zeugenSpeicher`/`read64_nach_write64`/
   `write64_erhaelt_berechtigungen`/`lesbar8`/`schreibbar8`/`addrOff`/
   `writeBytes` (`Speicher.lean`), `vLo`/`vHi`/`vecJoin` (`Vektor.lean`),
   `GleitOp` (`Syntax.lean`), `gleitRechne`/`gleitRoh` (`Semantik.lean`),
   `GFloat`/`gleitAusInt`/`Ty.fl` (`Typen.lean` — `fl` widthless confirmed),
   `Klasse` single `.nan` (`Gleitkomma.lean`). No invented source behaviour.
5. Staged the exact snapshot files privately, ran `bash ./lean-probe`
   (0 errors, 10 axiom lines all within standard) and `bash ./lean-bau`
   (green, `Build completed successfully (416 jobs)`), plus a `gabbro_ziel`
   axiom probe (unchanged `[propext, Classical.choice, Quot.sound]`).
6. Restored the tree (candidate file removed, `Grammatik.lean` checked out,
   probe scratch removed); this report is the only change committed.

## Verification results

- `bash ./lean-probe grammatik/Grammatik/X86/ScalarFloat.lean` (staged):
  `== 0 error(s) in the COMPLETE output; exit 0`, axiom lines:
  `fpRechne_gleitRechne [propext]`, `fpRechne_klasse [propext, Quot.sound]`,
  `cvttPaket_gleicht_gleitRoh [propext]`, `fpXmmZahl_le_zwei
  [propext, Quot.sound]`, `bites64_wf [propext, Quot.sound]`,
  `ucomiFlags_reserviert [propext]`, `ucomiFlags_nan_klasse_nur [propext]`,
  `div_eins_durch_null [propext]`, `add_plusnull_minusnull [propext]`,
  `fpZeuge_div_unendlich_speichert [propext, Quot.sound]`.
- `bash ./lean-bau` (staged): `Build completed successfully (416 jobs)`.
- Axiom probe on `Gabbro.Grammatik.Zielsatz.gabbro_ziel` (staged):
  `[propext, Classical.choice, Quot.sound]` — unchanged.
- Author BUILD-EVIDENCE narrative (intermediate rewrite errors fixed,
  transient `failed to create thread` environmental, stash control test)
  is consistent with a green final state; I reproduced green probe + green
  full build independently on current master.

## Task-direction coverage (all confirmed in code)

- Scalar SSE2 DOUBLE only: 15 `FpBefehl` constructors (4 RR + 4 RM arith,
  2 UCOMISD, 2 conversions, 3 MOVSD); no x87/FMA/packed constructor exists.
- Checked `mxcsrGueltig` premise (`fpEintritt`) guards every `fpSchritt`
  path first; refusal theorems for bad length/profile; refusal framed as
  validator admission, never a hardware fault.
- One source op = one machine op: `fpRechne_gleitRechne` proved by
  `cases op; rfl` — genuine, since `fadd64`… are defined as
  `Gleitkomma.add`…; no reassociation/FMA-contraction theorem anywhere.
- NaN class-level (`fpRechne_klasse` via `bites64_muster64` + `*_wf`),
  payload non-observability honestly OPEN in CUTS; SNaN/flag reservation
  joint (`ucomiFlags_reserviert`, `ucomiFlags_nan_klasse_nur`).
- Witness: `fpZeuge_div_unendlich_speichert` — `divsd xmm0,xmm1` computes
  `1.0/+0.0 = +inf` (`div_eins_durch_null`, by `decide`), `movsd [rax],xmm0`
  stores at 8192, readback + footprint-top byte change `0x00 -> 0x7F`
  (by `decide`); signed-zero companion `add_plusnull_minusnull` present.
  Two reached steps, real memory change, admitted profile throughout.
- Refusal: `fpXmmZahl_le_zwei` (no 3-operand/lane-indexed form),
  `bites64_wf` (binary64-only bridge); f32 correctly identified as
  non-existent (`Ty.fl` widthless, model binary64 — verified in
  `Typen.lean`), x87/FMA/packed syntactically absent (stated, not
  over-claimed as dynamic refusal).
- Safety-corrections complied with: no alignment imposed beyond actual
  `read64`/`write64` behaviour; full-word GPR write via `regSet` (no narrow
  claim); FP divide has no trap to rename; no timing/cost claim; no TSO or
  multi-byte atomicity claim (CUTS explicit); `laufAlt` reuses canonical
  `schritt` untouched — no second evaluator of the 14 old forms; MOV flag
  preservation and address-from-pre-state hold per equation.
- Rule 13: no source-syntax premises anywhere; joint `GleitOp` divide
  instances (`fpRechne_gleitRechne_zeuge`, `fpRechne_klasse_zeuge`) plus the
  joint memory-changing reached run above exceed the minimum.
- Physical ISA spot-checks: MOVSD-load zeroes high half / RR arithmetic
  preserves it (legacy SSE, correct); UCOMISD OF/SF/AF cleared
  (`some false` for AF, correct per Intel); CVTTSD2SI is an explicit
  source-shaped wrapper (`cvttPaket_gleicht_gleitRoh` proved) with all
  hardware correspondence blanket-OPEN — as the task ordered (`+wrapper`).
- CUTS block + `#print axioms` for all 10 main theorems present at file end.
  English throughout. Claim stays bounded; no full-compiler/validator
  language in the file.

## Non-material observations (no action required)

- Author report says "16 `FpBefehl` DOUBLE forms"; the file defines 15
  constructors (16 is the XMM register count). Wording slip only.
- CUTS could name the CVTTSD2SI silicon integer-indefinite
  (`0x8000000000000000`) vs wrapper-`0` difference explicitly, but the
  blanket OPEN hardware-correspondence statement plus the task-ordered
  wrapper make the boundary honest. Suggestion for a future lane, not a
  defect.
- Author's `lean-bau` evidence (386 jobs) predates current master
  (416 jobs); I re-verified green on current master, so this is closed.

## Open (as the candidate itself states)

NaN-payload non-observability; SNaN/sticky-flag semantics; decoder;
f32 admission; rewrites beyond the four arithmetic ops; TSO/concurrency;
cost/timing; old/new-form interleaving; full final-byte/source/hardware
correspondence. None is claimed.

CANDIDATE: 340 de523a41904a2a16f2980256db378d1779bfb06b
VERDICT: ACCEPT
