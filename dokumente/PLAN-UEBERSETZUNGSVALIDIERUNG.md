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

1. **Memory model**, design and Lean core. One lane with a fixed target; an Opus agent,
   because it is the riskiest piece.
2. **T4 in three passes:**
   - (i) the 15 forms that neighbour the five already done, about 1,500 lines;
   - (ii) the 20 medium forms, about 5,000 lines;
   - (iii) the 24 hard forms on the new memory model, about 10,000 lines.

   Every pass ends with the correspondence lemma per form, and with a guardian that fails when
   the emitter emits a form that has no semantics.
3. **T1 and T2 run in parallel with T4.** They do not depend on the C semantics except where
   T2 rules the C forms.
4. **T3, the parser in Lean**, runs in parallel and on its own.
5. **Closing theorem:** for every accepted program, `certificate checks by decide/kernel` implies
   `source parses to P` ∧ `P satisfies the model` ∧ `emitted C refines P`. It comes with a
   witness on `beispiele/104-referenz.gab`, the reference program.

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
