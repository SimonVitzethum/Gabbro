# MUSE-REPORT-181: measuring `bv_decide` on bit-vector obligations

Lane 181, PLAN-ZIELSATZ.md §9 first row. All numbers below are measured on this
tree's pinned Lean (4.33.1, `grammatik/lean-toolchain`), on the local machine
after a `free -g` check (110 GB total, 57 GB free — a measurement, not a hope).
Bit-for-bit reproduction commands are in §8.

## 0. Verdict up front

**Name the per-computation axioms as assumptions. Do not kernel-check, and do
not pretend there is nothing to name.**

The reason the recommendation changed is §1: this Lean (4.33.1) already carries
the RFC #12216 model. There is no shared `Lean.ofReduceBool` in any `bv_decide`
proof measured here. Each of the 13 SAT-backed proofs carries exactly one named
axiom of the form `thm._native.bv_decide.ax_1_5`, each stating one closed
equation `verifyBVExpr <expr> <cert> = true` over stored definitions, each
enumerable by `#print axioms` and each re-checkable one by one by an
independent tool. That is the "enumerable + independently re-checkable ≈
acceptable as a named assumption list" case the task describes — measured, not
assumed.

The numbers behind the verdict:

| route | closed | cost | axioms per proof |
|---|---|---|---|
| `bv_decide`, 17 theorems (8/16/32/64-bit, incl. 32-bit multiply, CRC linearity) | 17/17 | whole file 530 ms wall; ~60–70 ms marginal per SAT proof, 270 ms for CRC linearity | 13 × one named native axiom; 4 × none (solver-free path) |
| kernel `decide +revert`, K1 shape | 4-bit yes, 8-bit yes, 12-bit yes, 16-bit yes with raised heartbeats, 64-bit infeasible | ~0.01 s / ~0.1 s / ~2.8 s / ~65 s marginal (factor ~20–25 per 4 bits) | `[propext, Quot.sound]`, no native axiom at any width |
| `bv_check` with stored LRAT | not executed (no exporter in this toolchain, §5) | — | same trust class as `bv_decide` by construction (same checker path) |

## 1. Trust model of THIS Lean (4.33.1): the per-computation axiom is present

Three verbatim observations, then the mechanism.

**1a.** A nontrivial `bv_decide` proof (LSB-clear/isolate partition, 8-bit):

```
'probe_lsb_clear' depends on axioms: [propext, Classical.choice, Quot.sound, probe_lsb_clear._native.bv_decide.ax_1_5]
```

**1b.** The axiom itself (from the deliverable file's namespace):

```
axiom Gabbro.Grammatik.BitVecProben.a1_virtio_or_sum._native.bv_decide.ax_1_5 : Std.Tactic.BVDecide.Reflect.verifyBVExpr
    a1_virtio_or_sum._expr_def_1_1 a1_virtio_or_sum._cert_def_1_1 =
  true
```

It asserts one closed Boolean equation: the reflected checker
(`verifyBVExpr`) applied to the stored goal encoding (`_expr_def_1_1`) and the
stored LRAT certificate (`_cert_def_1_1`) is `true`. Both arguments are
definitions kept in the environment — an independent tool can extract the pair
and re-evaluate it without trusting the SAT solver, the elaborator, or the
compiler that ran the check the first time.

**1c.** `Lean.ofReduceBool` still exists but is deprecated, and says so loudly:

```
warning: `Lean.ofReduceBool` has been deprecated: in-kernel native reduction is deprecated; assert native evaluations with axioms instead
Lean.ofReduceBool : ∀ (a b : Bool), Lean.reduceBool a = b → a = b
```

No proof in `BitVecProben.lean` depends on it (zero occurrences in the final
axiom log).

**Mechanism** (toolchain source, `src/lean/Lean/Meta/Native.lean`,
`nativeEqTrue`, the common basis of `native_decide` and `bv_decide`): the
tactic compiles and runs the closed `Bool` check natively, and on `true` adds
ONE axiom `e = true` named `<thm>._native.<tactic>.ax_<u>_<v>`
(`mkAuxDeclName <| '_native ++ tacticName ++ 'ax`). The `bv_decide` frontend
(`src/lean/Lean/Elab/Tactic/BVDecide/BVDecide.lean:25-28`) writes the LRAT
proof to a temp file, runs bit-blast + SAT + LRAT check, and closes through
that reflection path (`Prover/Bitblast.lean:39` calls `nativeEqTrue`).

Consequence for PLAN-ZIELSATZ.md §9: the row's caveat ("the LRAT check runs
through `Lean.ofReduceBool` … the same class as `native_decide`") is stale
against 4.33.1. The check still runs compiled code, but the residue is no
longer one shared opaque axiom: it is one named equation per proof. The row's
own conditional already names this outcome — "if the per-computation axioms
are present, the recommendation changes". They are present.

## 2. QF collection: rule, count, and the valid-core/assumption split

The docs do not label rows "QF", so the rule is stated before the count.
**QF_BV-shaped** = the V1 statement is quantifier-free over scalar values once
table domains are instantiated: propositional combinations of equalities,
order tests, shifts and masks. Rows needing `countD`, `firstD`, `reachesIn`,
or a state between pre and post are not in this shape. A single universal
over scalar values counts as QF: closing an open goal by bit-blasting IS
proving that universal, which is exactly what `bv_decide` does.

Ground truth is the machine-checked file `programmlogik/gabbrov/V1.lean`
(55 Props that `lean` accepts; the GABBROV.md §5 rebooking discussion is
classification, not sayability, and does not change the set measured here).

**Count under this rule: 33 of 55**, in two cuts:

* Purely propositional, no `∀` at all (22): L18, L19, L20, L21, L22 (F2
  register fields), L26, L30, L32 (F3 equalities), L36, L37, L38, L39 (F4
  status steps), L44, L45, L47, L48, L51 (F5), L53, L55 (F6), L58, L63,
  L65 (F7–F10).
* Scalar-universal, bit-blastable as stated (11): L08, L10 (F1), L28, L31,
  L35 (F3), L40 (F4 reset, `∀ v` over one status word), L43, L49 (F5),
  L59, L60, L66 (F7–F10).
* Per-instance QF only (domain must be instantiated first; not tried here):
  L01, L02, L06, L07, L14, L17, L23, L25, L27, L33, L41, L56, L61, L62, L64.
* Not QF in any instantiation: L03 (`countD`), L04, L05, L09, L15, L16
  (`reachesIn`), L29, L54 (`firstD`).

The external review's "26 of 55" sits between my 22 and my 33: the delta is
rule choice (how scalar-`∀` and list-bounded rows are booked), not substance.
Anyone re-running the rule against `V1.lean` gets my 33; the table above is
the search path (W7).

**The split that matters more than the count.** Most QF rows are
*assumptions about a state* (`requires` clauses, status readings, magic
comparisons) — satisfiable but not valid. `bv_decide` must REFUSE those, and
it does, with witnesses (scratch probes, kept out of the green file):

* R1, L18 shape (`TE off or RTPS set` as a universal claim): **refuted**,
  witness `g = 253#8` (TE set, RTPS clear) — correctly, since 253 is a
  reachable hardware state and the clause is an assumption about it.
* R2, L36 shape (`st = 0 → st' = 1` with free post-state): **refuted**,
  witness `st = 0#8, st' = 0#8` — correctly; a transition statement with a
  free post-state is not a tautology.

So "try `bv_decide` on each" divides the 33 into: valid cores (close them —
§3) and assumption rows (correctly rejected — record the witness, do not book
as automation failures). Conflating the two would repeat the §8.3 booking
error one level down: counting a refusal as a gap.

## 3. Measured: 17 `bv_decide` proofs + 1 kernel proof (the file)

`grammatik/Grammatik/BitVecProben.lean`: 18 theorems, standalone (imports only
toolchain `Std.Tactic.BVDecide` — no mathlib, no project imports), NOT
imported by `grammatik/Grammatik.lean` (verified: no import edge, `git status`
shows exactly one new file, `Grammatik.lean` untouched), no `native_decide`,
no `sorry`, no `axiom`. Full-file build: **exit 0, 0 errors, 530 ms wall**,
18/18 axiom reports. Every theorem was checked against an independent Python
model BEFORE being stated (CRC vectors incl. the published CRC-8/ITU check
`0xF4` for `"123456789"`, linearity over all 65 536 pairs, alignment spot
checks); `bv_decide` is measured as the closer, never as the oracle.

Sections A (doc-sourced valid cores, each with its source row) and B (kernel
idioms). Times are single-run wall for a one-theorem file; baseline
(import-only file) is 181 ms, so marginal ≈ wall − 181.

| # | theorem (source) | closed | wall / marginal | axioms |
|---|---|---|---|---|
| A1 | disjoint-OR is addition, 8-bit (V1 L36–L39; PFLICHTEN F4:773–779) | yes | 245 / ~65 ms | + 1 native axiom |
| A2 | clear-then-set sets the bit (V1 L40; F4:780–782) | yes | 238 / ~57 ms | + 1 native axiom |
| A3 | frame split/join roundtrip, 64-bit (F9:1514–1516) | yes | 242 / ~61 ms | + 1 native axiom |
| A4 | W^X per instance, 1-bit (V1 L64; F9) | yes | 241 / ~60 ms | + 1 native axiom |
| A5 | refcount down by exactly one, 16-bit (V1 L08; F1) | yes | 182 / ~1 ms | `[propext, Classical.choice, Quot.sound]`, NO native axiom (solver-free path) |
| A6 | token decrease, 8-bit (V1 L66; F10:1656) | yes | 250 / ~69 ms | + 1 native axiom |
| A7 | wrapping add had nonzero length (behind V1 L49; F5:992–993) | yes | 244 / ~63 ms | + 1 native axiom |
| A8 | masked index in range, 64-bit (M103 shape; F1:142–149) | yes | 247 / ~66 ms | + 1 native axiom |
| A9 | one-bit device write preserves other bits (F2:400 `mirrors`; F2:450–453) | yes | 246 / ~65 ms | + 1 native axiom |
| K1 | `x & (x-1)` / `x & -x` partition, 64-bit | yes | 252 / ~71 ms | + 1 native axiom |
| K2a | align-up_to-4096 is a multiple of 4096 | yes | 190 / ~9 ms | `[propext, Quot.sound]`, NO native axiom (closed by `bv_normalize` alone) |
| K2b | align-up identity on aligned, 64-bit | yes | 253 / ~72 ms | + 1 native axiom |
| K3 | `(va >> 12) & 0x1FF < 512` (F2:505–510; F9) | yes | 247 / ~66 ms | + 1 native axiom |
| K4a | CRC-8 closed answers `0x00→0x00`, `0xFF→0xF3` | yes ×2 | 203, 208 / ~22–27 ms | `[propext, Quot.sound]`, no native axiom |
| K4b | CRC-8 GF(2)-linearity over bytes | yes | 450 / ~269 ms | + 1 native axiom |
| K5 | Newton step `x·(2−x) ≡ 1 (mod 4)` for odd `x`, 32-bit multiply | yes | 254 / ~73 ms | + 1 native axiom |
| C1 | K1 shape at width 4, kernel `decide +revert` | yes | 194 / ~13 ms | `[propext, Quot.sound]` |

Totals: 17/17 `bv_decide` closed (13 via SAT+LRAT with one named axiom each,
4 via the solver-free path with none), 1/1 kernel closed. The default SAT
timeout (10 s) was never approached — the slowest marginal cost is 270 ms.
Multiplication at 32 bits costs the same as masks and shifts here; nothing in
this corpus shape stresses the solver.

Two findings inside the table:

* **A mis-stated obligation was refuted, not closed.** The first rendering of
  A1 used the premise `s &&& 0xFC = 0` (high bits clear — the mask pointing
  the wrong way); `bv_decide` returned `s = 3#8` (`3+3=6 ≠ 3=3|3`). The
  corrected premise `s &&& 3 = 0` closes. The wrong mask passed my own Python
  spot check because the check encoded the intended condition instead of the
  written one — the solver read what was written. That is the tool earning
  its keep, and the refutation is booked here rather than silently fixed.
* **`bv_decide` does not unfold plain definitions.** The CRC step as a `def`
  (and as an `abbrev`) is abstracted as an opaque UF and the proof fails with
  a spurious counterexample; `unfold crc8Byte` first closes normally with the
  usual single native axiom. Obligation statements that hide bit logic behind
  helper definitions must unfold them at the call site.

## 4. Kernel-only route: cost curve, not a single number

Same K1 shape, `by decide +revert` (closed goal, kernel reduction, no SAT, no
native code), marginal over the 181 ms baseline:

| width | closed | wall / marginal | axioms |
|---|---|---|---|
| 4 (C1, in the file) | yes | 194 / ~13 ms | `[propext, Quot.sound]` |
| 8 (scratch) | yes | 282 / ~100 ms | `[propext, Quot.sound]` |
| 12 (scratch) | yes | 2969 / ~2.8 s | `[propext, Quot.sound]` |
| 16 (scratch) | yes, but exceeds the default 200 000-heartbeat budget (~13 s, timeout at `whnf`); with `maxHeartbeats 0` closes | 65 645 / ~65 s | `[propext, Quot.sound]` |
| 64 | infeasible (factor ~20–25 per 4 bits — extrapolation says never) | — | — |

Kernel-checking buys the smallest axiom list at every width and is practical
to about 12 bits for this shape. At 16 bits it costs a minute; at 64 bits it
is not a route. Recommendation: use it for ≤12-bit spot checks only.

## 5. What was deliberately not rebuilt

* **`bv_check "proof.lrat"`** (stored certificate instead of a SAT call):
  read, not run. The checker path is the same `closeWithBVReflection` call
  (`BVCheck.lean:43`) as `bv_decide` (`Main.lean:19`), so a replayed
  certificate still verifies natively and still yields a per-computation
  axiom — it saves the SAT call, not the assumption. Unexecuted here because
  this toolchain's frontend offers no exporter: `bv_decide` writes the LRAT
  to a deleted temp file (`BVDecide.lean:25-28`), so there is no honest way to
  obtain the stored file it wants.
* **LRAT-Catcher** (arXiv 2607.00815): not available offline — no package in
  the toolchain or the lakefile (which has zero dependencies by design), no
  network to fetch it. Cited, not rebuilt, per the task. Its comparison
  (kernel reflection vs native vs cake_lpr time/memory) answers a different
  question than this lane's; nothing here contradicts it, and the native-axiom
  shape measured in §1 is the same shape its cake_lpr mode trades against
  (externally verified checker plus asserted axiom — a different trade, not a
  strictly better one).

## 6. Recommendation (with numbers)

1. **Name the per-computation axioms as assumptions** — one name per
   SAT-backed proof (13 names for the 17 proofs; the other 4 need no entry).
   They are enumerable (`#print axioms` prints each `…._native.bv_decide.ax…`
   with its full statement) and each asserts a closed, re-checkable equation
   over stored definitions. This is Strategy A one level down, and the Lean
   version question it was conditional on is answered: 4.33.1 carries it.
2. **Do not kernel-check above ~12 bits.** The curve in §4 (≈20–25× per 4
   bits, 65 s at 16 bits) rules out 64-bit production obligations. Kernel
   `decide` stays a spot-check instrument for narrow widths, not a strategy.
3. **Do not choose "neither".** 13 of the 17 proofs rest on a native axiom;
   the final log has zero `sorryAx` and zero `ofReduceBool`, but thirteen
   `…ax_1_5`. Booking the proofs while booking no assumption would be the
   silent-blind-guardian failure the project rules exist to prevent.
4. **Update the §9 row's caveat.** "Runs through `Lean.ofReduceBool`" is
   wrong for 4.33.1 (deprecated, unused here); the residue is the named
   per-computation axiom. One sentence carries the correction; the row's
   architecture (oracle plus certificate) stands.

## 7. CUTS: what this lane does not claim

* Widths above 64 bits, multipliers above one 32-bit step, and full-message
  CRC theorems (only one byte-step + linearity + two closed answers) were not
  tried; solver cost there is unmeasured.
* Domain-quantified rows (L01/L02/L06/L07/L14/L17/L23/L25/L27/L33/L41/L56/
  L61/L62/L64) need their domains instantiated before bit-blasting; the
  per-instance shape (A4/A8) is measured, the instantiation tactic is not.
* `countD`/`firstD`/`reachesIn` rows and the ordering/second-program rows are
  outside QF_BV by construction — no claim is made about them here.
* Timings are single-run wall on a quiet machine (direct toolchain binary;
  the elan shim adds seconds of wall with no CPU and was bypassed for all
  measurements). No statistical treatment; the two orders of magnitude
  between the routes do not need one.

## 8. Reproduction

* Deliverable: `grammatik/Grammatik/BitVecProben.lean` (new, 18 theorems).
  Build separately — it is outside `grammatik/Grammatik.lean`'s import list
  by design:
  `~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean grammatik/Grammatik/BitVecProben.lean`
  → exit 0, 18 axiom reports (canonical log kept at `.tmp/opencode/bitvecproben-final.log`;
  per-theorem timings were taken on one-theorem slices under `.tmp/opencode/per/`).
* Trust-model probes: `.tmp/opencode/bvprobe2.lean` (axiom list),
  `bvprobe3.lean` (axiom statement verbatim), `kernel8/12/16/16b.lean`
  (kernel curve), `refute1/2.lean` (assumption rows correctly rejected).
* Independent Python models (CRC vectors, linearity over all pairs,
  alignment, Newton step, A1 fix) were run with `python3 -c` and their
  outputs are quoted in §3; the scripts themselves were throwaway one-liners.
* `free -g` before the runs: 110 total / 57 free — local execution was a
  measurement within budget, and every run above is sub-second except the
  documented kernel-scaling probes (3 s, 65 s).
* Project-tooling verification (2026-09-14, after the file landed):
  `./lean-probe grammatik/Grammatik/BitVecProben.lean` → lean exit 0, 0 errors
  (runs under the project's `lake env`, not just the bare toolchain binary);
  `./lean-bau` → lake exit 0, 0 error lines, "Build completed successfully
  (200 jobs)" (the main build is unaffected — the file is not imported);
  `./cargo-pruef` → exit 0, 0 failing tests (no Rust touched; `./emission-pruef`
  not run — the emitter is untouched).
