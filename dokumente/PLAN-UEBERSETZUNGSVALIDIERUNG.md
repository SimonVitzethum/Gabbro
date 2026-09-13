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
it is 0** (T2 does not exist yet). A guardian prints it; it only ever counts programs whose
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
