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
`schlusssatz_104` (§6.4). **On 2026-09-15 it is 2 of 111**: `beispiele/104` and `beispiele/108`,
each a Lean-checked instance of the GENERIC closing theorem `schlusssatz` (§6). A guardian prints
it; since 2026-09-15 it counts a chain as closed only for a program with a Lean-checked instance
of the generic theorem (`instrumente/zaehle-kette.py`).

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
- **The runtime, for noninterference** (`dokumente/NICHTINTERFERENZ.md` §10) -- the SAME list as
  the lock primitives and thread creation of §3 item 4, not a second one: threads start only at
  declared (labelled) roots; the scheduler chooses by a fixed timetable, or by a rule that reads
  only the observer's view (`nichtinterferenz_planer`); a slot whose thread cannot step is left
  idle, not given away; the lock primitive (a ticket lock) reveals nothing but held or free.

## 6. Chain count: 2 -- beispiele/104 and beispiele/108, theorem schlusssatz (generic)

*Added 2026-09-15. Stage (a) of §3 item 2, GENERIC: one theorem for every single-threaded
program whose chain data check. Files: `grammatik/Grammatik/KorrespondenzAllg.lean` (T2
proper), `Schlusssatz.lean` (the theorem), `Kette104.lean` + `Kette104Satz.lean` and
`Kette108.lean` (the two chains), `SchlusssatzZeuge.lean` (witnesses). Axioms of every theorem
named here: `propext`, `Classical.choice`, `Quot.sound` (`korrOk_faellt`: `propext`,
`Quot.sound`); no `sorry`, no `native_decide`, no new `axiom`. `lake build` of the whole
library on `ki-pc-fisch-101`: 236 jobs, green.*

### 6.1 The statement

A CLOSED CHAIN for a source text `src` is a value `K : Kette src` (Schlusssatz.lean) -- every
field a Lean proposition about the program, or data:
* `uebersetzt : uebersetzeAllg src = .ok ⟨K.u, K.E.P, K.fs0⟩` -- the GENERIC Lean pipeline
  (lex, parse, the lane-162 preprocessing, elaborate, the generic lowering `lowerAllg` onto the
  declaration `declOf u` built from the source) produces the code the rest is about;
* `E : Einheit (declOf u)` -- the program as the goal theorem's unit (Zielsatz/Spec.lean); its
  code is the parser's, its lock invariants, axiom ensures, declared starts and initial memory
  are data read next to the source (the exporter does not fill them, Spec NOT CLAIMED);
* `akzeptiert : akzeptiert_pruefer.akzeptiert E fs ls cs = true` -- the checker's Bool, (a);
* `nutzer : NutzerPflicht E` -- the user's logic and start obligation, (b);
* `EL : EmitLay (declOf u)`, `zert : KCert (declOf u)`, `zertOk : korrOk EL fnNr zert E.P fs =
  true` -- the emitter's layout and the correspondence certificate, checked (T2).

`schlusssatz (K : Kette src) O hH orc XR hXR bin tief hA1 sp init hA4`, with the NAMED
hypotheses about the world outside Lean: `hH : HardwareAnnahmen O K.E.Q` (the goal theorem's
(c)); `hXR : XR.Funktional` (foreign calls of the C side deterministic; the covered forms emit
none); `hA1 : ∀ f st vs st' rv, bin f st vs st' rv → CallAt K.EL.lay orc XR (kProg K.zert) (tief
f) (fnNr f) st vs st' rv` (A1 with A2 and A3: every run of the binary's `f` is a run of the C
semantics of the unit the certificate elaborates to, at the emitter's layout, at the call depth
its call tree needs); `hA4 : EinFadenStart K.E sp init` (A4 single-threaded: the loader's memory
is the declared initial memory, every thread but `0` idles in the runtime's root, thread `0`
runs what the driver calls -- nothing, or one function whose `requires` holds with the driver's
arguments). It concludes the six parts of the old §6, generically:

1. **Parse fidelity**: `src` translates to `K.E.P`.
2. **The certificates**: the checker's Bool holds and means `AkzeptiertSpec`; the
   correspondence certificate checks against `K.E.P`.
3. **The model judgement**: `NutzerPflicht K.E` (every body at every budget, owed invariants at
   value and reason exits, the start obligation).
4. **Every C run**: for every function, call depth `n` and budget, from a C state related to
   ANY Gabbro world and C arguments related to ANY Gabbro arguments: when the Gabbro call
   `rufAt K.E.P O passes n f` ends in no model error, the C call has a run and EVERY run of it
   ends related to the Gabbro outcome (`korrOk_jeder_lauf`: `korrOk_fnCorr` + `exec_det`).
5. **The machine**: `K.E.P.mitRuhe` (the goal theorem's generic idle root) behaves as `K.E.P`
   at every depth (`rufAt_mitRuhe` -- the generic `gPB_wie_gP`); on every machine reachable
   from the single-threaded start, at every budget: `SpurInv`, the contracts at every logged
   event, the lock invariants, no thread stuck at a `logik` check, progress at a check, the
   owed invariants at returns, the root function's `ensures` at its completion and no reason
   exit of it (`einfaden_ziel`, from `ziel_ort_einfaden_ende` -- no machine fact re-derived by
   hand); and for every start of the goal theorem's runtime shape (the DECLARED starts,
   concurrently) every leg of `Ziel` (`gabbro_ziel`).
6. **Every run of the binary**: under `hA1`, from related starts, when the Gabbro call at depth
   `tief f` ends in no model error, every run of `bin f` ends related to it.

### 6.2 T2 proper: `korrOk` (KorrespondenzAllg.lean)

ONE decidable check for every program: `korrOk EL fnum c P fs` walks every body with its
printed rows and decides, statement by statement, that the row is the emitted form of the
statement -- replacing `certOkG`, which compared with 104's rows. Covered: slot stores through a
pointer or at a named table (`assignDurch`, `assignSlot`), stores to a local (`assignVar`),
direct calls with their arguments, `let`, `(void)x;`, `return` of an expression or of nothing,
falling off a `void` body; expressions: literals, locals, widenings, slot loads through a
pointer or at a named table, table pointers. Every other form makes the Bool `false`.
Soundness at EVERY call depth (`korrOk_fnCorr`, by induction on the depth through `cCorr_ruf`);
each row is one existing T4 lemma, the one new lemma is the argument passing of any call
(`argsTo_of`). The locals map is the EXPORTER'S (Gabbro variable `j` is C local `vm[j]`,
pointer parameters are ordinary variables); a callee's map must be its C parameter list.
Seen failing (`korrOk_faellt`): a wrong field offset, a wrong stored value, `refD`'s
index-fixed map, a missing call row.

**The printer** (`crates/gabbro-check/src/corrlean.rs`) prints a third section, `KCert` with the
exporter's map (no `MODEL DATUM`), one line per function; named-table loads and stores
(`T_speicher.slots[i].f`, C block = the table's position) are rows now (they were refusals).
The two older sections (104-cut `Cert104`, `GRow` bodies with `refD`'s map) are unchanged.

### 6.3 The count: 2 of 111, and where the other 109 stop

| Program | Chain | Witness |
|---|---|---|
| `beispiele/104-referenz.gab` | `kette_104` (Kette104.lean, Kette104Satz.lean) -- the REAL text with comments (`src104real`, byte-identical to the file); no declared start; the user's logic re-proved over the parser's declaration (`ein4_R`, `lies4_V`) | `kette_104_zeuge`: `einzahlen(k, 0, 7)` from the zero state through the GENERIC theorem -- the Gabbro call ends `ok` with the slot `0 -> 100`, every C run ends with the C cell at `100` |
| `beispiele/108-disjoint-start-locks.gab` | `kette_108` (Kette108.lean) -- the real text; its two DECLARED concurrent starts, accepted by the checker | `kette_108_zeuge`: `read_a()` from a memory with `42` returns `42` in Gabbro and EVERY C run returns `42`; `kette_108_nebenlaeufig`: the declared concurrent start meets (d), so part 5's `Ziel` applies |

Where the other 109 tracked programs stop, measured in Lean (`uebersetzeAllg` evaluated over
every file, `zaehle-kette.py --lean` column (a)): **20 at the parser** (10 `reserved head
forall`, 4 `wanted ;`, 2 `wanted {`, 2 `@version expected`, 1 `fn without body`, 1 `expression
expected`) and **89 at elaboration** (69 an item without G form, 12 a unit without a table, 7 the
type `bool`, 1 a `requires` clause without G form); none at the lowering. So the binding sieve
is (a), the Lean parser and elaborator (T3): every program past it has a closed chain. The
later sieves in the order of the chain -- the model's checker and the user's proof (in the
chain instance), the C-form census (d), the correspondence certificate (e) -- were not reached
by any other program; their per-program columns stand in the counter's output as diagnostics.
Measured with `zaehle-kette.py --lean` on `ki-pc-fisch-101` (this branch, 111 tracked
programs): sieve totals (a) 2, (b) `lean-g` 10, (c) `certificate` 15, (d) C forms 60, (e)
generic `KCert` printed and pasted 2; first stopping sieve of the 109 open programs: (a)
elaboration 89, (a) parser 20.

**A finding on the way (the census, not the chain).** The emitter now writes 104's call as
`(void)lies(k, i);` (the quote in `CFormenZeuge.lean` of 2026-09-13 reads `lies(k, i);`).
`pruefe-cformen.py` read the `(void)` parenthesis as the argument list and `lies(` as a call
INSIDE an expression, which put 104 into state (iii) (`expr:call`) and would have kept its
chain open on a census artefact. Repaired in `classify_exprs` (the cast is stripped before the
arguments are taken; both spellings are the same C call with its answer discarded, C11
6.3.2.2, and the same CS node `.call fc args none`); the census stays green, 10 `expr:call`
occurrences in 5 programs moved out of state (iii), and `zaehle-kette.py`'s speech test now
plants both a `(void)f(a);` and a call inside a condition. For A2 it means: the hand quote of
the emitted text is stale in SPELLING (not in meaning) -- one more reason for a Lean C parser.

### 6.4 The by-hand theorem of one program: `schlusssatz_104` (2026-09-14)

*File: `grammatik/Grammatik/Schlusssatz104.lean`, unchanged; it stands beside the generic
theorem (it speaks about `gP` over `G104_referenz.gD`, the 104-keyed lowering, and carries the
three-step machine witness). The text below is the 2026-09-14 booking.*

**The statement** (restated 2026-09-14, second round: the named assumptions that are Lean
propositions are hypotheses, and the `forever` budget is quantified).
`schlusssatz_104 (c : Cert104) (hc : certOkG c = true) binEin hA1ein binLies hA1lies init hA4`,
where `hA1ein : ∀ st vs st' rv, binEin st vs st' rv → CallAt gEL104.lay tvOrc tvXR refCProg 2 0
st vs st' rv` (likewise `hA1lies` at depth 1, function 1) is A1 with A2 and A3 as one hypothesis
over the binary's behaviour `binEin`/`binLies` (parameters), and `hA4 : LaufzeitStart init`
(every thread but `0` idles in the runtime's root) is A4. It gives, about ONE program -- `gP`
over `gD` (`G104_referenz`), the program the Lean parser produces:

1. **Parse fidelity.** `uebersetze104 src104 = .ok (gP, gFs)`: lex, parse, elaborate, lower,
   every stage a propositional equation (the `Bool` pins of `Parser/Uebersetze.lean` became
   `rfl` equations).
2. **Model certificates.** The Lean-side print of `gP`'s two bodies IS the pasted printer
   output of `ZeugnisStmt104b.lean` (`printEnd104 (gP.rumpf f) = some cert104_f`, `rfl`), and
   `certEnd104Ok` accepts both.
3. **Model judgement.** `programmImFragmentG`, `fussOrtGB`, and for every function
   `KoerperGutS` and `InvGutS` AT EVERY `forever` BUDGET (`gP_koerperS_alle`), and the call
   semantics does not depend on the budget (`gP_rufAt_passes`), so every `rufAt … 0 …` below
   holds at every budget.
4. **Every C run.** The certificate elaborates to the emitted unit (`progOf c = refCProg`); for
   `einzahlen` (depth 2) and `lies` (depth 1), from a C state related to ANY Gabbro world and
   C arguments related to ANY Gabbro arguments: the Gabbro call `rufAt gP` ends `ok` (every
   `requires`/`ensures` on the way checked), the C call has a run, and EVERY run of it ends in
   a state related to the Gabbro result (`callAt_funktional`).
5. **The machine.** `gPB` = `gP` plus the runtime's idle root: its source part is `gP` under a
   structural renaming (`gPB_ist_gP_umbenannt`, `rfl`) and behaves as `gP` through the same
   emitted C (`gPB_wie_gP_einzahlen`/`_lies`: same memory effect and answer); on every
   machine reachable from every start memory, at every budget, from EVERY start `init` with
   `LaufzeitStart init`, the conclusion of the goal theorem holds -- now with `StartEndeG` and
   `KeinStartGrundG`, so the root function's `ensures` at its completion is part of the
   machine statement (`ziel_ort_einfaden_ende`).
6. **Every run of the binary** (under `hA1ein`/`hA1lies`): from a related start, every run of
   `binEin`/`binLies` ends related to the Gabbro result, which is the same at every budget.

The premise holds for the printed rows by `decide` (`schlusssatz_104_praemisse`); witnesses
on runs that move memory: `schlusssatz_104_zeuge` (C and Gabbro, slot `0 -> 100`) and
`schlusssatz_104_maschine_zeuge` (three machine steps, `lies`'s `ensures` at its logged
return by the theorem, and the root `einzahlen` finished with its `ensures` by `StartEndeG`);
the premises jointly: `schlusssatz_104_praemissen` (the C semantics itself as the binary's
behaviour, `bootInit` as the start).

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

**Premises and assumptions.** Premises: `certOkG c = true`; `hA1ein`/`hA1lies` (A1+A2+A3 as a
refinement hypothesis on the binary's behaviour); `hA4` (A4). There is no hardware or oracle
premise for 104: the declaration has no axiom, register, device, global or `awaits`, and the
emitted unit no device access or foreign call. What stays OUTSIDE Lean (no Lean proposition):
A1 that `binEin`/`binLies` ARE the compiled binary's behaviour (the compiler); A2 that the
emitted TEXT means `refCProg` -- a Lean C parser for the emitter's subset with `parseC text =
some refCProg` by `decide` would replace it by "the compiler's front end reads the subset as
`parseC`", a part of A1; A3 reduces to A1 + A2 (the `_Static_assert` pins are checked by the
compiler) plus one missing lemma (the C semantics reads a `RecLay` only through the pinned
numbers); A4 that the real runtime starts in a `LaufzeitStart` shape (the driver is not
emitted); A5 the Lean kernel and the definitions §3 lists for human review.

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

*Status of these items on 2026-09-15, after the generic theorem (§6.1-6.3):* the printer prints
the exporter's map (third section, `KCert`); the chains run on the REAL texts with comments
(`src104real`, `src108`); the lowering, the correspondence check and the idle root are generic
(`lowerAllg`, `korrOk`, `P.mitRuhe` with `rufAt_mitRuhe`); `printEnd104` is no longer a link of
the generic chain -- the model judgement is the checker's Bool `Akzeptiert` plus the user's
proof. The adequacy cut (part 4 vs part 5) and stage (b) stand as they did.

### 6.5 What stays open (generic theorem)

- **Sieve (a) is the binding one.** 109 of 111 programs stop at the Lean parser (20) or
  elaborator (89) (§6.3). Widening the chain count now means widening T3 -- the `elabU`
  fragment (tables only, `u32` ranges, writes, calls, a trailing return) and the lowering --
  and, behind it, the forms `korrOk` covers (§6.2: `if`, `traverse`, compound assignments,
  globals, `let` of a call, arithmetic are T4 lemmas already, one arm each).
- **The unit's data.** `Kette.E`'s lock invariants, axiom ensures, declared starts and initial
  memory are written next to the source by the chain's author (the exporter fills none of
  them); a wrong `starts` is a different program, visible in the chain file.
- **The user's logic is per program.** `NutzerPflicht` is proved per chain (104: the argument
  of `gP_einzahlen_R` again, over the parser's declaration; 108: two returns). That is the
  goal's intent -- "the user proves only their own logic" -- not a gap; but the chain count
  moves only with such proofs.
- **Part 4 is conditional** on the Gabbro call ending in no model error (a failed contract,
  the call-depth bound `abstieg`, a hardware answer); the model judgement does not yet say
  that `rufAt` at the call tree's depth ends `ok` -- the two witnesses compute it.
- **A2 and the rest of A1/A3/A4** stay outside Lean exactly as in §6.4; the emitted TEXT is not
  parsed in Lean (`kProg` is the certificate's elaboration, not the file's).
- **The adequacy chain** (one active thread of G against `rufAt`) is not re-instantiated; the
  concurrent conclusion of part 5 is the MODEL's (`gabbro_ziel`), not the C's -- stage (b).
