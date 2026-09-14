# Translation validation — the plan

*Written 2026-09-13. The folder owner decided that this comes AFTER the goal ("the user proves
only their own logic plus hardware assumptions") is confirmed and carried into the checker and
emitter. The inputs are measurements: `messung/VERIFIKATIONSAUFWAND-2026-09-12.md` (lane 127)
and `messung/muse/MUSE-REPORT-128.md` (lane 128, the C-semantics probe).*

## 0. What is proved at the end

Take any program the checker accepts. Lean re-checks a certificate the checker printed for
that program, and the check yields three results:

1. **Model judgement.** The program satisfies the model's judgement: typing, safety, and the
   goal theorem's premise classes.
2. **Parse fidelity.** The certificate describes the *source text*, not a Rust-side
   rendering of it.
3. **Emitter fidelity.** The emitted C refines the model's semantics, up to the named
   assumptions: the C compiler, the hardware profile, and the driver for payloads.

The Rust checker is never verified. It is untrusted, and a wrong checker can only refuse
programs, never admit a wrong one. This is strategy A of lane 127.

**Direct verification of the Rust code is rejected.** Whether via Aeneas, Verus or a SPARK
rewrite, it would take about 700k proof lines (about 20 person-years), and it would prove
against a second copy of the model rather than against the Lean model.

## 1. Components and measured sizes

| # | Component | Lean lines | Basis |
|---|---|---|---|
| T1 | Certificate soundness per constructor, over all `Stmt`/`Block`/`Endblock` forms (today only `Expr`, via `zeugnis_sound`) | 5,000–8,000 | lane 127: about 40 constructors × 100–200 lines |
| T2 | Correspondence rechecker (`corrcert`) plus rulings for the 30 open C forms of `Erhaltung.lean` | 4,000–6,000 | lane 127 |
| T3 | **Parser in Lean.** The certificate starts from the source text, so Rust leaves the trusted base entirely. This replaces the unproved fidelity of the `lean.rs` export. | 3,000–5,000 | my estimate; SYNTAX.md has 167 EBNF rules |
| T4 | **C semantics** of the emitted subset (64 forms), with a UB inventory, a memory model and per-form correspondence | 7,000 / 17,000 / 30,000 (low / mid / high) | lane 128 measured about 117 lines per easy form and extrapolated in three cost classes |
| T5 | The remaining ghost-template library (about 16 of 20) | 2,000–3,000 | lane 127 |
| **Σ** | | **≈ 21,000–52,000 (mid ≈ 35,000)** | |

## 2. The binding constraint: the memory model (from lane 128)

Lane 128's memory `(table, index, field) → Int` carries exactly the five easy forms. Around
24 of the 64 forms need something that model cannot express:
- pointer arithmetic, dereference and address-of need an **aliasing model**;
- `volatile`, `_Atomic` and memory ordering need **observations**;
- `goto` needs **continuations**.

**Rule:** decide the memory model first, in one lane with a fixed design document, before any
of the 24 hard forms. The alternative is rewriting every form semantics halfway through, which
is what lane 128 warns against.

Candidate: a block-offset model in the style of CompCert, restricted to the objects the
emitter actually creates (table arrays, a few globals, stack locals). Layout comes from the
emitter's own declarations, and there is no general `malloc`, because Gabbro's arenas are
static arrays.

## 3. Order

*Revised 2026-09-13 (evening) after an external review. The first version raised five pillars
in parallel to 20-60 % each; the review's point, accepted: coverage is MULTIPLICATIVE -- the
closing theorem holds only for programs that pass every sieve -- so the state is measured by
closed chains, not by per-pillar percentages. Done before the revision: memory model
(CSpeicher), T4 passes (i)-(iii) and the reason channel (48 of 73 emitted forms), T1 for all
Expr/Stmt/Block/Endblock constructors, term identity on the Lean side, T3 lexer/parser through
items, source-to-G on 104.*

**The one metric: chain count.** How many of the corpus programs (`beispiele/*.gab`, 101 emitting
on 2026-09-13) pass the WHOLE chain: Lean parse of the source → elaboration to `P` → model
certificate accepted → correspondence certificate of the emitted C accepted. It replaces the
per-pillar numbers as the headline; the per-pillar numbers stay as diagnostics. **On 2026-09-13
it is 0** (T2 does not exist yet). **On 2026-09-14 it is 1**: `beispiele/104`, theorem
`schlusssatz_104` (§6). A guardian prints it; it only ever counts programs whose
chain Lean actually checked.

1. **Close ONE chain first: T2 minimal, for `beispiele/104`.** The correspondence certificate
   (`corrcert.rs` print format) and its Lean rechecker, restricted to the forms 104's emitted C
   actually uses -- nothing more. T2 is the only pillar that did not exist at all, and without it
   no chain closes, not even for 104.
2. **Closing theorem, stage (a): single-threaded, complete.** For a program with one active
   thread (`ziel_ort_einfaden`'s class): `certificates check` ⟹ `source parses to P` ∧ `P
   satisfies the model` ∧ `every run of the emitted C corresponds to a run of P` (the C semantics
   is deterministic, `exec_det`, so "every" is available). Witness on 104. This is the first
   point at which the chain count is 1.
3. **Widen by forms, measured by the chain count.** Every further T1 certificate shape, T4
   lemma, T5 template and T2 form is judged by how many corpus programs it moves over the line.
4. **Closing theorem, stage (b): concurrent.** DRF-SC for the C11/hardware memory model, the
   lock primitives' specification (acquire/release with happens-before) and thread creation by
   the runtime enter as NAMED PREMISES of the theorem. The argument that makes the DRF-SC
   premise applicable rather than merely plausible: `rennfrei_g_voll` proves the program data-race
   free on G, which is exactly DRF-SC's hypothesis. The simulation G-run ↔ interleaved C-run is
   research-sized (CompCertTSO, promising semantics); stage (a) does not wait for it. What is
   realistic soon is the statement with the premises in the right place; the proof over it is a
   separate, longer item.

**Three states in the C-form guardian.** `instrumente/pruefe-cformen.py` classifies every
emitted form as (i) **lemma** (a correspondence lemma exists), (ii) **named assumption** (the
form has no C meaning by construction and enters the theorem as a premise: inline asm, device
register access = the hardware profile, syscall stubs = the kernel), or (iii) **without
semantics** (red unless on the dated known-uncovered list). Two states would force the
assumption forms either to stay red forever or to have the guardian switched off -- and a
silenced guardian is the failure class this tree has booked three times.

**What still has to be read by a human.** Strategy A shrinks the trusted base from the Rust
tree to the Lean DEFINITIONS the kernel cannot judge: whether they say the right thing. That is
the external-review target, and nothing else is: the machine G (`RufMaschineG.lean`, and the
sequential `Semantik.lean` / `Maschine.lean`), the good-run predicates (`Gesittet` in
`Wettlauf.lean`, `GutO`, `RegLokal`, `SperrInvOk`), the obligation (`KoerperGutS`), the goal
predicate (`VertragAmOrtG`, `SperrInvG`), and the C semantics (`CSemantik.lean`,
`CSpeicher.lean`, `CFormen.lean` core). Measured 2026-09-13: `grammatik/` contains no `sorry`
outside comments (a plain `grep -w sorry` counts the many "no `sorry`" remarks -- that count is
not a finding).

**Not a risk any more once T3 stands:** the Rust side of term identity (differentially tested,
53 match / 0 mismatch, not proved). With the certificate anchored at the source text through
the Lean parser, a Rust print of the wrong term fails the check -- a refusal, not an admission.

## 4. Effort (Muse Spark 1.3 Contributor, measured rates)

Rates come from waves 1–5. A lane task that survives review brings about 300 Lean lines, and
rework adds a factor of 1.5–2 in runs. A run costs $0.25–0.50. For C-semantics lanes the
rework is expected above 50%, since this is new formalisation with no precedent in the
project.

| | lines | runs | API cost | wall clock (review-bound, 30–60 merges/day) |
|---|---|---|---|---|
| low | 21,000 | ≈ 110 | ≈ $30 | ≈ 4 days |
| mid | 35,000 | ≈ 190 | ≈ $70 | ≈ 7 days |
| high | 52,000 | ≈ 300 | ≈ $150 | ≈ 2 weeks |

The costs of the Opus agent for the memory model are on the Claude account and not included.

## 5. What stays an assumption, by name

- **The C compiler.** It translates the emitted subset faithfully under the manifest's flags.
  The FMA probe, the `_Static_assert` pins and the C-form census bound this assumption; they do
  not discharge it.
- **The hardware profile.** `Profil.lean`, keyed entries.
- **The GPU driver**, for SPIR-V payloads (PLAN-ERWEITUNG.md §0b), once the GPU library exists.
- **The Lean kernel.**

## 6. Chain count: 1 -- beispiele/104, theorem schlusssatz_104

*Added 2026-09-14. File: `grammatik/Grammatik/Schlusssatz104.lean`. Stage (a) of §3 item 2,
for one program. Axioms of every theorem named here: `propext`, `Classical.choice`,
`Quot.sound`; no `sorry`, no `native_decide`, no new `axiom`.*

**The statement.** `schlusssatz_104 (c : Cert104) (hc : certOkG c = true)` gives, about ONE
program -- `gP` over `gD` (`G104_referenz`), the program the Lean parser produces:

1. **Parse fidelity.** `uebersetze104 src104 = .ok (gP, gFs)`: lex, parse, elaborate, lower,
   every stage a propositional equation (the `Bool` pins of `Parser/Uebersetze.lean` became
   `rfl` equations).
2. **Model certificates.** The Lean-side print of `gP`'s two bodies IS the pasted printer
   output of `ZeugnisStmt104b.lean` (`printEnd104 (gP.rumpf f) = some cert104_f`, `rfl`), and
   `certEnd104Ok` accepts both.
3. **Model judgement.** `programmImFragmentG`, `fussOrtGB`, and for every function
   `KoerperGutS` and `InvGutS` (the per-function obligations of `ziel_ort_sperre_inv`).
4. **Every C run.** The certificate elaborates to the emitted unit (`progOf c = refCProg`); for
   `einzahlen` (depth 2) and `lies` (depth 1), from a C state related to ANY Gabbro world and
   C arguments related to ANY Gabbro arguments: the Gabbro call `rufAt gP` ends `ok` (every
   `requires`/`ensures` on the way checked), the C call has a run, and EVERY run of it ends in
   a state related to the Gabbro result (`callAt_funktional`).
5. **The machine.** `gPB` = `gP` plus the runtime's idle root: its source part is `gP` under a
   structural renaming (`gPB_ist_gP_umbenannt`, `rfl`) and behaves as `gP` through the same
   emitted C (`gPB_wie_gP_einzahlen`/`_lies`: same memory effect and answer); on every
   machine reachable from every start memory, thread 0 in every source function on every
   argument, the conclusion of the goal theorem holds (`ziel_ort_einfaden` plus `InvAmOrtG`).

The premise holds for the printed rows by `decide` (`schlusssatz_104_praemisse`); witnesses
on runs that move memory: `schlusssatz_104_zeuge` (C and Gabbro, slot `0 -> 100`) and
`schlusssatz_104_maschine_zeuge` (three machine steps, `lies`'s `ensures` at its logged
return by the theorem).

**The joints, and how they closed.**

| Joint | Before | Now |
|---|---|---|
| P identity | three programs: `gP` (parser), `r4P`/`r4D` (goal theorem), `refP`/`refD` (C, index fixed to `0`, one parameter); data agreement only | parts 1-4 are about `gP` itself; the machine needs `gPB`, related by a kernel-checked renaming and a semantic bridge through the C |
| Model certificate ↔ P | over `gD` already, soundness only `∃ Endblock` | the certificates are the print of `gP`'s bodies |
| C correspondence ↔ P | `EndCorr` about `refP` | `EndCorr`/`FnCorr` about `gP`'s bodies; the certificate carries `gP`'s locals map |
| Single thread | -- | `ziel_ort_einfaden`, every C run by determinism |

**The finding.** No G theorem applies to a machine of `gP` alone: G starts EVERY thread in
some function, and both functions of `gD` hold `M` by signature, so no start is exclusive
(`gP_kein_exklusiv`) and no function is an idle root (`gP_kein_ruhig`). The idle root is
runtime data; it enters as `gDB`/`gPB`, and assumption A4 below.

**Premises and assumptions.** The one premise is `certOkG c = true`. There is no hardware or
oracle premise for 104: the declaration has no axiom, register, device, global or `awaits`,
and the emitted unit no device access or foreign call. Named assumptions (outside Lean):
A1 the C compiler follows the C semantics of `CSemantik`/`CSpeicher`/`CFormen*`; A2 the
emitted text is the `CS` data `refCProg` (hand transcription of the quoted output; no C
parser in Lean); A3 the `Konto` layout (bounded by the `_Static_assert` pins); A4 the runtime
starts thread 0 in one source function and idles the rest; A5 the Lean kernel and the
definitions §3 lists for human review.

**What stays open.**

- The printer `corrlean.rs` still prints `refD`'s locals map (`vm = [2]`, `ks = [(1, 0)]`);
  `certG104` carries the printer's rows and layout and `gP`'s map. Moving the printer to the
  exporter's map is Rust work.
- The source text is the comment-free form `u104lex` pins (the commented file: lane 162).
- Part 4 speaks about `rufAt`, part 5 about machine G; their agreement for one active thread
  is the adequacy chain, not re-instantiated in the theorem.
- The renaming is partial and its semantic preservation is proved for 104's two functions
  only (through the C), not in general.

**For stage (b).** DRF-SC, the lock primitives and thread creation as named premises; the
simulation G-run ↔ interleaved C-run. For 104 itself `gP_kein_exklusiv` already says two
active threads are refused by the model (every function holds `M` by signature).

**For widening beyond 104** (the chain count's next steps), every piece keyed to `gD`
must become generic: the lowering (`lowerProg`, lane 162), the correspondence certificate
(`certOkG` fixes 104's rows; a row-list checker over all printed forms is T2 proper), the
body printer `printEnd104` (104's shapes), the idle root (either the exporter emits one, or
`gDB` becomes a generic declaration extension with a generic renaming), and the per-program
computations `rufEin_ok`/`rufLies_ok`, which stand in for a general theorem "the
per-function obligations imply `rufAt` ends `ok`".
