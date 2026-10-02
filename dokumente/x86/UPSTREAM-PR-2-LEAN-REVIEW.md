# Upstream PR 2 Lean review: verified compiler pipeline (source to loaded image)

Lane 712, independent exact proof review. Clone `/home/simon/Dokumente/gabbro-muse/a712`,
branch `muse/712`. Materials are the pinned public snapshots under
`.tmp/UPSTREAM-PRS/pr-1` and `.tmp/UPSTREAM-PRS/pr-2` (METADATA.json, PATCH.diff,
full source trees), not live branches or author clones. No network, no outside-clone
reads. Owned files only: this document and `MUSE-REPORT-712.md`. No source was changed.

- Pinned PR2 head `987b286df9d8465714a00bab8226f7b9c7f4afc1` matches
  `.tmp/UPSTREAM-PRS/pr-2/METADATA.json` (`head` field, exact).
- PR2 base `5d5a72e5889a3063b417b955fa7824e72c52ef7c` equals PR1 head. PR2 targets the
  PR1 branch, not master. Its PATCH.diff holds 27 files only: 18 new
  `grammatik/Grammatik/X86/*.lean` files, `grammatik/Grammatik.lean` (imports), and
  8 Rust files under `crates/gabbro-check/src/x86/`. Nothing else is touched:
  no `Spec.lean`, no goal theorem, no `emit.rs`, no CLI.
- PR2 tree = PR1 tree + the 18 files (verified by directory diff; PR1's
  `OptimizationRules.lean` / `OptimizationWitnesses.lean` are byte-identical in both
  snapshots). So this review covers PR1 (optimiser premises) as part of PR2.

## Verdict

The proof work is real and carefully scoped at file level (every new file has an exact
CUTS block and `#print axioms` lines). The closing theorems have the right shape:
untrusted bytes are recomputed, never trusted; side conditions are decided inside the
checker; the source run is the real `execBlock` of the original block; witnesses are
jointly instantiated with memory-changing runs. I found **no soundness-breaking proof
bug**.

What I did find is two BUILD-BLOCKING duplicate Lean names (§7 items 1–2: the PR as
pinned does not aggregate — per-module builds pass, the full `lake build` fails),
a layer of claim precision issues (§7 items 3–7, all wording/scope), one structural
scoping gap that must be stated plainly (§6: the unified ISA and the machine-level
optimisers are proved but NOT on the verified path — the closing theorems run on the
pilot `Befehl` only), and a list of open obligations that are future work, not merge
blockers (§9). Merge is BLOCKED on the two renames; once they land (mechanical,
no theorem weakening) plus the wording fixes, a partial merge is acceptable provided
the merged scope is described as in §6 (bounded sequential pilot-model pipeline +
adjacent proved-but-unwired ISA libraries), not as full hardware coverage.

Fixture build verdict (§10): RED at the aggregator, for exactly the two duplicate
names below. All 475 dependency modules build green; the failure is real (reproduced
from exact snapshot sources via the queued wrapper) and contradicts the PR body's
full-build claim.

## 1. Closing theorems: what they say, exactly

### 1.1 `Pipeline.lean`: `pipeline_correct`, `pipeline_refuses`, `pipeline_ausgang`

- `validate c L certs src bytes` recomputes `compileProg c L certs src` from the
  source and accepts only if the candidate `bytes` EQUAL the recomputed
  `encodeAll prog`, decode back to `prog` via the independent `decodeAll`, and pass
  `datenGetrennt`. `validate_sound` extracts exactly this. There is no
  desired-correctness API: the caller supplies candidate bytes, the validator
  recomputes everything else.
- `pipeline_correct` quantifier order is correct:
  `∀ src bytes, validate = true → ∀ O passes R σ ρ s, CodeAt ∧ rip ∧ WorldRep ∧
  EnvRepr ∧ execBlock … src … = .ok σ' ρ' → ∃ n s', …`.
  The conclusion is existential over the machine run; the source outcome is a premise
  about the REAL `execBlock` of the ORIGINAL block (optimiser bridge via
  `optimise_sound`/`BlockEquiv`, §4). No contract parameter is quantified away; no
  premise is unused ornament.
- `WorldRep`/`LayoutSep`/`CodeAt`/`EnvRepr` are ambient simulation premises, not
  derived — legitimate for a per-run simulation theorem — and §2 shows they are
  jointly satisfiable (non-vacuous).
- `pipeline_refuses` covers the `.grund` route but concludes only
  `rip = exitAdr c r` with the world represented: NO stub execution, NO `rax = r`,
  NO stop. The stub sentence lives one level up (image level). See MUST-FIX 6.
- `pipeline_ausgang` (every accepted block ends `.ok` or `.grund`) closes the
  outcome dichotomy, so the `False` fallback arm of `Entspricht` is dead, not a gap.

### 1.2 Mechanics (all checked by reading, each with its refusal)

- Register discipline: `cfgOk` decides disjointness of `dst`/`tmp`/`adr`/`regs`/`frei`,
  `Nodup`, and `≠ rsp`; `cfgOk_frischListe` derives the `FrischListe` premise.
  `senkTief` threads the scratch stack `tmp :: frei` and answers `none` on exhaustion
  (no spilling) and on every non-fragment form (`mul`/`div`/`slot`/memory reads).
- Overflow: value correctness is modular (`intWort`); exact signed reading needs the
  decided window `imSigned` (`-2^63 ≤ lo ∧ hi < 2^63`), checked inside
  `senkBedT`/`vergleich` over the type indices — a recomputed side condition, not a
  caller premise.
- Branches: `senkBlock` threads byte positions through both `ite` arms;
  `sprungOk` (representability, `k < 2^31`) gates both forward jumps, and refusal-exit
  displacements are computed AND re-checked by the address equation in `senkPruef`.
  Wrapping is modular throughout (`addrOff`, `natAdresse`); no unguarded Nat
  subtraction except under the decided `pro.length ≤ c.codeBase` guard in
  `prologImageOk`.
- Entry: `prologOk` decides lengths (`n ≤ regs.length`, `n ≤ abi.length`), pairwise
  `ZugOk` (no clobber: earlier destination is neither later source nor destination),
  and `≠ rsp`; `prologImageOk` recomputes the prologue bytes and checks them in the
  image (`codeAtB`) with the underflow guard. `AbiArgs` (caller register duty) is a
  legitimate entry assumption, and `EnvRepr` is ESTABLISHED by `prolog_lauf`, not
  assumed. `zuege_lauf` sequentialisation reasoning is correct (head value preserved
  via `ZugOk.2`, later sources untouched via `ZugOk.1`).

### 1.3 `PipelineImage.lean`: `pipeline_correct_loaded`, `pipeline_refuses_loaded`, `pipeline_correct_compiled`, `pipeline_refuses_compiled`

- `pipeline_correct_loaded` premises are only checked Bools
  (`validate`, `imageOk`, `weltOk`) + `EnvRepr` + the real source run; the start state
  is the existing loader's `bildZustand`. Conclusion reaches code end WITH stop
  (`byteschritt = .verweigert`, plus the `n+1` step equation).
- `pipeline_refuses_loaded` / `_compiled` execute the checked stub and end at
  `exitAdr c r + 10` with `rax = r` and stop — this is the theorem behind the PR
  body's stub sentence, not block-level `pipeline_refuses`.
- `kompiliert_geladen` removes the image premises for compiler-produced bytes;
  `bauOk` is an explicitly SUFFICIENT decided side-condition bundle (low canonical
  half, stride ≥ 11, separations, nonempty code) — honestly scoped in CUTS as
  stronger than `imageOk` needs.

### 1.4 `PipelineEntry.lean`: `pipeline_correct_entry`, `pipeline_refuses_entry`

Entry composition over `eintrittZulassung` (existing admission machinery) with the
prologue bytes included in `bauOk` (`pro` argument) and `bildFuerP_eintritt` bridging
builder output to `prologImageOk`/`eintrittOk`. Conclusion keeps the entry stack word
readable/writable. No new trust: every image/entry fact is a decided check.

## 2. Witnesses: genuinely non-vacuous

- `PipelineWitnesses.lean`: one table (2 rows, int field, written by the function),
  `validate = true` BY COMPUTATION (`by decide`), `compile = some pwBytes`
  (`by decide`, 82 bytes), optimiser acceptance proved AND its necessity proved
  (`pw_ohne_optimiser_verweigert`: without the fold the program does not lower —
  the certificate is load-bearing, not decorative).
- `pipeline_correct_zeuge` jointly instantiates validate, `LayoutSep`, `CodeAt`,
  `WorldRep`, `EnvRepr`, the source run, AND the reached run, with slot values
  7 → 35 and 9 → 6 (memory changes); the refusal witness runs 7 → 75 with row 1
  untouched. Poison probes: tampered byte, wrong certificate, wrong pass order,
  unsupported statements, register clash, code/data overlap, distant exit, wrong
  start memory — all refused by computation.
- `PipelineImageWitnesses.lean`: `pipeline_correct_loaded_zeuge`,
  `pipeline_refuses_loaded_zeuge`, image/welt checks by computation, plus a second
  declaration witness. `ExpressionLoweringDeepWitnesses.lean` additionally exhibits a
  WRONG value when `FrischListe` is dropped (aliasing probe) — a counterexample, not
  just an unproved theorem.
- Satisfies the project's inhabitation standard (joint premises, non-degenerate
  program, memory-changing run).

## 3. Forbidden-tactic and axiom hygiene (mechanical)

Word-boundary grep over every `.lean` file in the PR2 `X86/` directory, skipping
comment lines: zero `sorry`, zero `admit`, zero `axiom` declarations, zero
`native_decide`, zero `unsafe`. (Substring hits are prose: "admission", "admitted",
"admits".) Every one of the 20 new/changed files carries a CUTS block and `#print
axioms` lines (948 code-line occurrences over 1011 theorem/lemma declarations; PR1's
two files contribute exactly the claimed 88). With no `axiom` declarations and no
`srry`-family tactics present, only the three standard axioms can occur; the fixture
build (§10) re-verifies green plus the printed axiom lists.

## 4. PR1 optimiser premises (used by PR2 via `optimise_sound`)

- `BlockEquiv b b'`: FULL equality of `execBlock` outcomes for ALL `O passes R σ ρ`
  (values, faults, memory, stops) — the strong, correct notion; `applyPipeline_sound`
  chains it with `BlockEquiv.trans`, refusal falls back to the unchanged block
  (`BlockEquiv.refl`).
- Certificates carry positions + rules; every rule's facts are recomputed:
  `constInt?_sound`, `bounds_sound`, `decideLe/Lt/Eq_sound`, `foldInt/foldBool_sound`,
  `dropCheck_sound` (check that cannot fail), `narrowEntailed_sound` (value already
  in range), `checkStrength_sound` (non-negative sub-2^64 operand, power-of-two
  divisor; signed division refused by absence — `checkStrength_sdiv/_srem` — with
  poison probes `strength_refuses_sdiv`, `strength_refuses_signed_operand`,
  `strength_refuses_overflow`, `strength_refuses_non_pow2`, `strength_refuses_wrong_k`).
- Pass order is decided (`admittedOrder`, `applyPipeline_order`). Rewrites reach loop
  bodies, retry/breaking/option/bindCall continuations; unreachable sites
  (`on tag`/`on reason`, register/float binders, `exchange`/`awaits`) are refused,
  never trusted — stated in CUTS.
- The witness program's `2 * 3` fold is essential (see §2). No premise of the
  soundness theorems is a `Prop`-typed assumption or an unused ornament.

## 5. Unified ISA and machine-level optimisation libraries

- `ISA.lean` unifies 7 families (pilot, mul/div, shifts, narrow, SETcc/CMOV, compact,
  integer core) with `familien_disjunkt` over ARBITRARY byte strings via first-three-
  byte signatures (`famOf`) — unconditional, no priority rule needed — plus
  `decodeI_encodeI` round trip and consumed-length agreement. Scalar float, vector,
  LOCK forms are excluded for needing extra state (honest CUTS).
- `ISAExecution.lean`: `laufBytesI_layout` runs placed canonical code exactly like
  the instruction list — STRAIGHT-LINE ONLY (`faelltDurchI`), with W^X integrity via
  `stepI_rahmen`. Control flow is covered only by the trace theorem `laufBytesI_spur`
  under a `SpurAn` premise that is NOT derived from any layout here. CUTS states both
  facts plainly.
- `CompactForms.lean`: ten DESIGN-§2B forms with canonical codec, per-form round
  trips, truncation/non-canonical/`rbp`-disp0 refusals, and pilot-boundary probes.
  Equivalence lemmas exist for movImm32Zx/Sx, disp8/disp0 loads/stores, jump8 (target
  equality), aluImm8 ADD/SUB/XOR/CMP — with stated boundaries (jumpIf8 taken-branch
  only; AND/OR excluded for lack of a pilot reg-reg form).
- `IntegerCore.lean`: LEA/AND/OR/TEST/NOT/NEG/MOVZX/MOVSX with exact flags via reused
  lemmas, canonical codec, six disjointness theorems. CUTS is explicit: canonical
  subset with self-consistency only, no silicon correspondence; encoder-output
  lengths only.
- `ISASelect.lean`: `waehle_korrekt` proves `OptRel (EndGl S fe)` — agreement outside
  caller-declared scratch `S`, on memory, on flags if live. The 64 → 36 byte shrink
  is computed (`by decide`). Straight-line only; RIP excluded from the agreement
  (`laufI_rip`); cross-block liveness is NOT done (scratch-deadness is the caller's
  declaration).
- `ISARelax.lean`: bounded all-wide-first relaxation with whole-layout re-validation
  (`layoutOk`) per narrowing; no optimality/fixpoint claim. The loop witness is real:
  backward rel8 jump relaxed 26 → 22 bytes and executed (`loop_bytes` by
  computation), plus stale-image and shifted-label poison probes. The labelled
  semantics is parametrised by the label map (`stepL` sets RIP from `adr`), and the
  byte machine has no halt past the image — both in CUTS.

## 6. Structural scoping gap (must be stated, not a proof bug)

`Pipeline.lean`, `PipelineImage.lean` and `PipelineEntry.lean` import ONLY
`OptimizationRules`, `SourceAssignmentLowering`, `EffectiveAddress`,
`ExpressionLoweringDeep` (+ image/loader/entry infrastructure). They do NOT import
`ISA`, `ISAExecution`, `ISASelect`, `ISARelax`, `CompactForms` or `IntegerCore`, and
the lowered instruction type is the pilot `Befehl` throughout
(`Pipeline.lean` CUTS: "a later unified ISA can replace `Befehl` at these three
points"). The Rust side mirrors this exactly (`pipeline.rs` lowers to the pilot
fragment; `opt.rs` proposes source-level certificates). Consequences:

- The proved end-to-end path (§1) covers the PILOT fragment only: slot stores of
  `lit`/`var`/`weiter`/`add`/`sub`/`neg` trees, `<`/`<=`/`=` checks, `if/else`,
  constant folding. Everything in §5 is proved but UNWIRED: no closing theorem runs
  a unified-`Instr` program produced from source, and no compact/selected/relaxed
  byte string is the output of `compile`.
- The PR body's top framing ("first complete, verified compiler path", "the whole
  path is modelled") must carry this qualifier explicitly (MUST-FIX 3). The per-file
  CUTS blocks already say the honest thing; the PR description does not yet.

## 7. MUST-FIX (blocking first, then claim/scope precision; no proof repair needed)

1. BLOCKING — duplicate `Gabbro.Grammatik.X86.waehle`: pre-existing
   `FeatureProfile.lean:72` (`HwProfil → BereitProfil → PerfMerkmal → Option …`)
   vs new `ISASelect.lean:703` (peephole `S fe p → Option q`), same namespace, both
   imported by `Grammatik.lean` (lines 422, 476). Fixture full build fails with
   `import Grammatik.X86.ISASelect failed, environment already contains
   'Gabbro.Grammatik.X86.waehle' from Grammatik.X86.FeatureProfile`.
   Minimum repair: rename the NEW one (e.g. `waehleInstr`) and update its uses,
   which are contained to `ISASelect.lean` + `ISASelectWitnesses.lean` (incl. the
   `waehle_*` theorems, `#print axioms` lines and witness `loop_waehle`). No proof
   content changes.
2. BLOCKING — duplicate `Gabbro.Grammatik.X86.layoutOk`: pre-existing
   `TableLayout.lean:80` (`List TabLayout → Bool`) vs new `ISARelax.lean:132`
   (`List Bool → LProg → Bool`), same namespace, both imported by `Grammatik.lean`
   (lines 396, 478; masked behind item 1's error). Minimum repair: rename the NEW
   one (e.g. `relaxLayoutOk`) with uses contained to `ISARelax.lean` +
   `ISARelaxWitnesses.lean`. Same containment, no proof content changes.
   (Both are the known recurring conflict class "two lanes defining the same Lean
   name: rename one". Both pre-existing files are byte-identical to the PR1 base,
   so both collisions were introduced by PR2.)
3. PR-body full-build claim is contradicted by the fixture evidence: the body says a
   full `lake build` "fails only in `Parser/ElementTiefProben.lean`" (memory limit),
   but the exact tree fails at `Grammatik.lean` import aggregation (items 1–2). The
   body's "How to test" (per-module `lake build` of four witness modules) is exactly
   the procedure that misses aggregation collisions — every one of the 475
   dependency modules builds green standalone. The merge gate must be the FULL
   `lake build` (or at minimum the `Grammatik` aggregator target), not per-module
   builds. Correct the claim and the test instructions.

4. PR body, Hardware model: "Programs placed in memory are proved to run exactly
   like their instruction list." Add the straight-line qualifier: the layout theorem
   is `laufBytesI_layout` (`ISAExecution.lean`), whose premises include
   `∀ i ∈ is, faelltDurchI i = true`. Control-flow programs are covered only by the
   trace theorem under an underived `SpurAn` premise; a branch-target layout theorem
   is open (per that file's CUTS).
5. PR body, Compact encodings: "Each one is proved to behave like the long form."
   Qualify: `jumpIf8` equivalence is target equality / taken-branch only
   (`equiv_jump8_target`, `kompaktWahl_jumpIf32_genommen`), and AND/OR have no
   equivalence (`equiv_aluImm8` excludes them — `Befehl` has no reg-reg AND/OR).
6. PR body, top framing + machine-level optimisation section: state explicitly that
   the ISA unification, compact forms, integer core, peephole selection and branch
   relaxation are proved adjacent libraries NOT on the verified source-to-image path,
   which runs on the pilot ISA only (§6). One paragraph + pointer to the
   `Pipeline.lean` CUTS wiring note.
7. PR body, main result: "If a source check fails, the machine runs a checked exit
   stub and stops with the reason in `rax`." Name the theorems that carry this:
   `pipeline_refuses_loaded` / `pipeline_refuses_compiled`
   (`PipelineImage.lean`: stub executed, `exitAdr c r + 10`, `rax = r`, stop).
   Block-level `pipeline_refuses` (`Pipeline.lean`) concludes only `rip = exitAdr`
   with the world represented — it must not be cited for the stub sentence.
8. `ExpressionLoweringDeep.lean`, `senkTief_tief_ok` docstring: headed "PLANTED
   REFUSAL" but proves a positive (`= some [...]` by `rfl`). Relabel as a positive
   depth probe.
9. PR body numbers: "all 907 axiom reports" does not match the snapshot (948
   `#print axioms` code lines over 1011 theorem/lemma declarations in the 20
   files; PR1's 88 exact). Re-count at merge time and write the exact figure with
   its counting rule. (The 137-x86-test figure IS exact: 137 `#[test]` attributes
   across `crates/gabbro-check/src/x86/*.rs`, verified by count.)

## 8. Checked and found OK (explicit non-findings)

- No caller-supplied-correctness APIs: `validate`/`imageOk`/`weltOk`/`prologImageOk`/
  `bauOk`/`eintrittZulassung` recompute from source/candidate/image; `compile` output
  implies `validate` (`validate_compile`, modulo the honestly-stated `datenGetrennt`
  completeness side condition).
- No impossible world/layout premises: all representation premises are jointly
  witnessed (§2).
- No vacuous optimiser: the fold is necessary (`pw_ohne_optimiser_verweigert`).
- No second IR or second source interpreter: lowering and optimiser act on the real
  typed syntax; `execBlock`/`eval` are the single reference. (Recorded decision
  594/606 is followed.)
- Rust is correctly OUT of the trust path ("proposes, Lean disposes" in every module
  header); golden cross-checks are Lean-generated vectors checked by Rust tests
  (tested equality, honestly stated — not a proof, not claimed as one).
- ELF is honestly scoped (per-byte permission model vs whole-page loader — stated as
  not loadable under a real OS loader yet).
- `Entspricht`'s `False` arm is dead by `pipeline_ausgang` + `senkBlock_ausgang`, not
  an uncovered outcome.
- The `rsp`-default in `abbOf`/`prologPaare` (`getD … .rsp`) cannot smuggle aliasing:
  `cfgOk`/`prologOk` decide the length and disjointness conditions that keep every
  used mapping injective and off the working registers.

## 9. Open obligations (future work; NOT merge blockers)

Bounded sequential pilot-model proof only: no G/GX concurrency leg, no time, no
termination/liveness (fuel-bounded runs), no wider source fragment (mul/div in
lowered expressions, memory reads in expressions, variable indices, spilling, calls,
source loops), no floats/vectors/LOCK on the path, no branch-target layout theorem,
no silicon correspondence for any codec, no proved Rust equality, no real-loader ELF.
Parser-to-`Block` linkage, final hardware/OS guarantees, and the unified-ISA wiring
(§6) remain open. None of this is claimed in the files' CUTS; only §7 items need
wording repair.

## 10. Build evidence

- Mechanical greps (this review, exact snapshot): no forbidden tactics, CUTS + axiom
  prints in all 20 files, PATCH scope 27 files, 137 Rust x86 tests counted.
- Fixture build: disposable tree `$TMPDIR/fixture-pr2` = exact PR2 `grammatik/`
  snapshot + copied root wrappers (`lean-bau`, `lean-probe`) + a copied warm
  `grammatik/.lake` (clone-local, never shared writable). Full `lake build` via the
  queued `./lean-bau` (shared `lean-slot`), backgrounded 2026-10-03 ~00:52 UTC
  behind two other lanes' queued jobs. RESULT (2026-10-03, complete output first
  line): `== exit 1; 3 error line(s) in the COMPLETE output` —
  `error: Grammatik.lean:44:0: import Grammatik.X86.ISASelect failed, environment
  already contains 'Gabbro.Grammatik.X86.waehle' from Grammatik.X86.FeatureProfile`
  (plus the Lean-exited/build-failed summary lines); 475/476 jobs built, i.e. every
  dependency module is green standalone and only the `Grammatik` aggregator fails.
  A namespace-aware duplicate scan of the exact snapshot sources confirms the
  `waehle` collision and a second one masked behind it (`layoutOk`, §7 item 2);
  all other same-short-name hits are namespace-distinct. Axiom-list grep over the
  build output shows only standard-axiom info lines before the failure point. The
  §7 findings rest on exact statement-level reading confirmed by this build result.
