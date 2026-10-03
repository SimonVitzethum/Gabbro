# MUSE-REPORT-1010: Exact review of author 860 (constant folding rule)

CANDIDATE: 860 5fd37472b323021c3e70cc45cca5c87c4df0afa2
VERDICT: ACCEPT

Scope of the ACCEPT verdict is bounded as recorded below; the substantive
verdict itself is unchanged.

## What was done

Report-only exact review of author 860 ("Optimiser rule: constant folding rule").
Own only this file; no source, no live controls, no other clone touched.

- Verified this lane: clone `/home/simon/Dokumente/gabbro-muse/a1010`, branch
  `muse/1010` (HEAD `56537272` at session start).
- Inspected the pinned snapshot in `.tmp/review/author-860/`: `OWNER-TASK.md`,
  `MUSE-REPORT-860.md`, `PATCH.diff`, `BUILD-EVIDENCE.json`, the snapshotted
  `grammatik/Grammatik/X86/OptFoldConst.lean` (319 lines) and `Grammatik.lean`,
  plus `SNAPSHOT.json` (author 860, head `5fd37472...afa2`,
  base `4b42ac53...44a37`, 3 files, `clean: true`).
- Consulted the local hardware-reference record
  (`.tmp/HARDWARE-REFERENCES/REFERENCES.json`: Intel SDM combined volumes 1-4,
  edition 325462-093US September 2026, sha256-verified; AMD unavailable, no AMD
  claim made). No network use.
- This clone (`a1010`) does not contain `OptFoldConst.lean`; the candidate is
  not merged here. I did not re-run build wrappers on the candidate (report-only
  ownership; copying the file into `grammatik/` would exceed it). Build evidence
  below is the author's complete `BUILD-EVIDENCE.json` struggle log plus final
  green runs, cross-checked against the snapshot file text.

## Candidate scope (from PATCH.diff / SNAPSHOT.json)

Exactly 3 files: new `grammatik/Grammatik/X86/OptFoldConst.lean`, one import line
in `grammatik/Grammatik.lean`, `MUSE-REPORT-860.md`. No source/checker/Spec/goal/
emitter edits, no friend-reserved optimiser files, no new diagnostic/gift/
example/CLI numbers, no MARKE_EMIT changes. Compliant with the 2026-10-03 user
priority constraints.

## Checks performed

- Forbidden tokens: grepped the snapshot Lean file for `sorry`, `native_decide`,
  `unsafe`, `axiom` declaration, `intro _`, `have _ :=` — none present (only the
  words "admitted" in prose and `#print axioms` lines). Proofs use only `rfl`,
  `decide`, `simp`, `rw`, `omega`, `exact`.
- Axioms: final `lean-probe` lists every theorem at a subset of
  `propext, Classical.choice, Quot.sound` (the `gabbro_ziel` standard);
  `foldZulassen` and `probe_foldWort` axiom-free. `gabbro_ziel` untouched.
- Build: final `lean-probe .../OptFoldConst.lean` ==
  `0 error(s) in the COMPLETE output; exit 0`; final `./lean-bau` ==
  `exit 0; 0 error line(s)`, `Build completed successfully (484 jobs)`.
  The evidence log shows the author fixed every intermediate red state
  (including a `sorryAx` probe and several `assignSlot`-window failures) before
  the final green commit — genuine iteration, not a single-shot green.
- Premise use: `foldVerweigert_*` use `h`; `foldDiv/Rem_wert` forward the `M102`
  premises `h0`, `h1'` into `Zahl.div/rem` (a zero divisor never reaches a fold);
  `foldWort_add` uses `hW` via `omega`; `foldGleit_behält` uses both `hz` and
  `hEq` (`have e := hEq hz`); `OptFoldConst_verbindung` uses `hW` in the third
  conjunct and threads `V, O, passes, R, Γ, Λ, l, x, y, rest, σ₀, σ, ρ` into
  the statement. No `Prop`-typed premise bare, no discarded premise.
- Target + witness: `OptFoldConst_verbindung` (add fold under `Endblock.bind`
  with arbitrary continuation, concluding eval-value equality, `execEnd`
  equality, and the 64-bit word image) proved `⟨rfl, rfl, foldWort_add x y hW⟩`
  — definitional preservation, the strongest form. Companion
  `OptFoldConst_verbindung_zeuge` instantiates ALL premises jointly at `3 + 4`
  on the non-degenerate `refD` (`refEin_schreibt`) beside the reached,
  memory-changing F-machine run `MB` (`refB_erreicht`, `refB_schreibt`,
  slot `0 -> 100`). Joint, non-degenerate, memory-changing. ZEUGE satisfied.
- Refusals/negative probes: `foldVerweigert_strtod/mxcsr/weite` prove the
  DESIGN failure cases force `foldZulassen = false` on the decided Bool; probes
  `probe_foldZulassen_ok/_strtod/_mxcsr`, six value probes, `probe_foldWort`,
  and the kernel-computed `probe_foldGleit` (`0.5 + 0.25 = 0.75`) are all
  `decide`/`rfl`-closed. No refusal weakened into a warning; no `ensures`
  derived.
- Hardware review (bounded, Intel-profile only): integer folds are total except
  `div`/`rem`, which keep the source `M102` guards — no Intel `#DE` added or
  removed at this layer. Width gate `hW` (`0 ≤ x+y < 2^64`) matches the
  canonical 64-bit `Wort` read-back; narrower-width lowering is untouched and
  unclaimed. MXCSR-scope refusal (`gleicheRundung`) and host-`strtod`
  double-rounding refusal (`einfachGerundet`, single kernel `rundeBruch`) match
  the DESIGN row and the IEEE single-rounding requirement. x86 flag/REX/byte
  forms, TSO/atomicity, interrupts: correctly out of scope — this is a
  source-level pure rewrite (both sides `orte = []`-pure at this layer), and the
  file/CUTS claim nothing about bytes, flags, TSO/GX, silicon, ABI, or loader.
  `execEnd` equality under an arbitrary continuation covers downstream
  observations (faults, contracts at actual values, call logs, shared accesses,
  step-budget shape) at this layer; the formal level-(c) machine-work bound is
  honestly left OPEN per CUTS/IR-VALIDIERUNG lane 278.

## Bounded acceptance (what ACCEPT does and does not cover)

ACCEPT covers: the `FoldCert`/`foldZulassen` refusal triple, the six integer
value folds, `foldWort_add`, value-level `foldGleit_behält`, the `add`
`Endblock.bind` connection with its joint non-degenerate witness, and the
precise CUTS (no float block-window rewrite, no div/rem/neg syntax connection,
no formal `totalCost` inequality, no silicon/TSO/ABI claims). Anything beyond
that — byte encoding, flag semantics, cross-width lowering, MXCSR-state
formalisation, machine-work bounds — is explicitly not granted.

## Minor findings (not REPAIR)

1. `breiteOk = false` refusal has no named lemma (only `keineFPWeite`,
   `einfachGerundet`, `gleicheRundung` do); refusal still holds by the same
   conjunction. Trivial; suggest adding the one-line lemma in a follow-up.
2. The `FoldCert`-to-`hW` link is validator-operational, not formally bridged:
   the connection takes semantic `hW` while refusal is proved on the cert Bool.
   This is the task's intended validator-decided pattern and is documented, not
   unsound — but a future validator-correctness lane should state the
   `foldZulassen = true → hW`-style obligation explicitly.
3. Concurrency/call-log/budget preservation is argued as corollary of `execEnd`
   equality rather than proved as separate lemmas. Given the `rfl` (definitional
   identity of outcomes), this is sound here; the missing formal `totalCost`
   inequality is already cut.

## Last build result

No wrapper ran in this lane (report-only; candidate not present in this clone).
Candidate evidence: `./lean-probe grammatik/Grammatik/X86/OptFoldConst.lean` ==
`0 error(s) in the COMPLETE output; exit 0`; `./lean-bau` == `exit 0`,
`Build completed successfully (484 jobs)` (author `a860` tree, final entries of
`BUILD-EVIDENCE.json`).

## What remains open

Per the candidate's CUTS: float block-window rewrite, div/rem/neg syntax
connections, formal machine-work bound, and the full lowering/byte/TSO chain —
all with the lowering/validation lanes, not this rule. Nothing in the owner
task text beyond the minor findings above appears wrong; "read the single
accepted IR" correctly fell back to the real `Syntax`/`Semantik` fragment since
no accepted IR exists in-tree.
