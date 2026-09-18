# Translation validation — the plan

*Written 2026-09-13. Simon decided that this comes AFTER the goal ("the user proves
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
   separate, longer item. **Closed for ONE program on 2026-09-15** (§7: `schlusssatz_124`, the
   simulation by blocks between synchronisation points, over every SC run of the emitted C of
   `beispiele/124`); the generic part (semantics, premises, race transfer) is program-independent.

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
  not discharge it. **Since 2026-09-15 its FRONT END is what is assumed, not a transcription:**
  for the two closed chains the emitted TEXT is pinned in Lean and PARSED there (§6.6, A2
  discharged), so what remains is "the compiler's front end reads this subset as `parseC`
  does" -- a part of this entry, no longer an entry of its own.
- **The hardware profile.** `Profil.lean`, keyed entries. **Since 2026-09-16 a SECOND
  hardware profile stands beside it, for a certified unit that touches a DEVICE**
  (`GerAnnahme`, KorrespondenzAllg.lean §1c): the register's window is declared `mmio` at the
  emitter's offset and width (`fenster`); the address expression the certificate carries
  evaluates to that cell (`adr` -- a THEOREM for the direct-base spelling `(volatile uint8_t
  *)(uintptr_t)BASE + K`, an ASSUMPTION for the emitter's own `d->basis + K`, which says the
  handle local carries the window's base); the declared Gabbro type fits the cell (`passt`);
  **the C device oracle and Gabbro's `Orakel.regLies` answer the same machine** (`einig` --
  this is `regLies_step`'s `hdev` and `pruefe-cformen.py`'s `stmt:reg-load` row, lifted from
  one program point to the unit); and a raw word that DOES fit the declared type encodes back
  to itself (`rund` -- a theorem for an integer register). Beside them, one clause of the
  state relation: **the device windows the unit declares are MAPPED** (`EmitLay.devs`,
  `corrW`'s third clause). *What a device chain claims is in §6.9, and what it does not claim
  is in the same place.*
- **The GPU driver**, for SPIR-V payloads (PLAN-ERWEITUNG.md §0b), once the GPU library exists.
- **The Lean kernel.**
- **The runtime, for noninterference** (`dokumente/NICHTINTERFERENZ.md` §10) -- the SAME list as
  the lock primitives and thread creation of §3 item 4, not a second one: threads start only at
  declared (labelled) roots; the scheduler chooses by a fixed timetable, or by a rule that reads
  only the observer's view (`nichtinterferenz_planer`); a slot whose thread cannot step is left
  idle, not given away; the lock primitive (a ticket lock) reveals nothing but held or free.
  In Lean (since 2026-09-15, §7.4): `LaufzeitC` = `FadenStartC` (thread creation) and the lock
  specification `sperrAbstrakt` (`sperrAbstrakt_nur_eigen`: nothing but held or free); the two
  scheduler entries are premises of noninterference only.
- **DRF-SC** (§7.4): `DRFSC`, ONE proposition, a hypothesis of `schlusssatz_124`: for a race-free C
  program every real execution has the observation of an SC interleaving of synchronisation-free
  blocks. Its hypothesis, race freedom, is PROVED from machine G (`rennfreiC_aus_sim`).

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

**Widened on 2026-09-15** (`messung/muse/OPUS-BERICHT-KORROK.md`). The check was NARROWER THAN
ITS OWN STOCK OF PROVED LEMMAS -- `ecorr_add` … `ecorr_shr`, `ecorr_lt` … `ecorr_eq`,
`ecorr_nicht`, `ecorr_und`, `ecorr_oder`, `ecorr_glob`, `scorr_assignGlob` and the four `Zucker`
compound assignments were all proved and all fell through `_ => false`. **21 expression arms**
(`true`/`false`, plain globals, `+ - *`, `/ %` signed and unsigned, `& | ^ << >>`, `< <= ==`
each also in its swapped C spelling `> >=`, `&& || !`) and **2 statement arms** (`g = e;` on a
plain file-scope scalar; the compound assignment `x op= e`, which IS `assignVar` of a binary
expression and elaborates to the same C statement) moved inside, each over an existing
`ecorr_*`/`scorr_*`. `exOk` now covers **27 of the 42 `Expr` constructors** (was 6), `stOk`
**5 of the 27 `Stmt` constructors** (was 4). The ONE new lemma is `ecorr_geSwap`, and it is
`ecorr_cmp` with its operator fact. `KorrespondenzWeitZeuge.lean` carries a positive probe AND a
PLANTED DEFECT for every arm -- a computation type too narrow for the result, a `>`/`>=` without
the operand swap, `INT_MIN / -1` not excluded, the wrong local, the wrong global block, an
`_Atomic` global taken for a plain one -- plus the witness of `ecorr_geSwap` at BOTH answers.
**The chain count did NOT move**, and could not: sieve (a) binds (§6.3, §6.5). Two things
measured on the way: `Zucker.gt`/`ge`/`ne` are `lt`/`le`/`nicht ∘ eq`, so `>`/`>=` are row
shapes of the `lt`/`le` arms and `!=` is NOT the cheap arm §5.3 of the emitter report took it
for; and the PRINTER is now narrower than the check (`gcx` prints only `+ - *` and `== < <= >`).

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

> **Re-measured 2026-09-15** over **113** tracked programs, after the exporter lane
> (`messung/muse/OPUS-BERICHT-EXPORT.md`): **(a) 2, (b) 12, (c) 15, (d) 60, (e) 2**; first
> stopping sieve of the 111 open programs: (a) elaboration 91, (a) parser 20.
> **CHAIN COUNT 2 of 113 — unchanged, and it could not change**: sieve (a) binds, and this
> lane touched only sieve (b). *An export is not a chain.*
>
> **Re-measured again 2026-09-15**, after the `tagged`/record lane
> (`messung/muse/OPUS-BERICHT-LINEAR.md`): **(a) 2, (b) 15, (c) 15, (d) 60, (e) 2**; first
> stopping sieve of the 111 open programs: (a) elaboration 91, (a) parser 20.
> **CHAIN COUNT 2 of 113 — unchanged again, and for the same reason.**
> The three programs sieve (b) gained are `120-tagged-construction`,
> `121-tagged-static-init` and `34-markierter-wert`, all through `Ty.sum`.
>
> > **And a rule for reading this census at all, measured in that lane.** Its rows are
> > FIRST refusals, and a first-refusal count is **not** a count of programs a lane would
> > gain. The two largest class-(i) rows were the `linear` types (10 programs) and the
> > record types (14). A probe that skipped only those two declarations and re-ran the whole
> > sweep found that **every one of the 24 stops at a SECOND wall from another group** — a
> > `walk`, a `backed` table, a device, a foreign body, an `option` field, an `assume`, an
> > `atomic`, a shared lock hold, the `mmio` address space, an array field. *Closing either
> > group completely would have moved sieve (b) by ZERO*, and the record group turned out to
> > be two groups with different classes (carrier: (i), built; value: (ii), `Ty` has no
> > product former). **Coverage is multiplicative in the sieves AND inside sieve (b).**

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
emitted TEXT means `refCProg` -- **done for the GENERIC chain on 2026-09-15** (§6.6:
`parseC ctext104 = some (kFuns zert104)` by kernel reduction), which leaves "the compiler's
front end reads the subset as `parseC`", a part of A1; the by-hand theorem of this section
still speaks about `refCProg` and is the one place where the transcription stands; A3 reduces to A1 + A2 (the `_Static_assert` pins are checked by the
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
simulation G-run ↔ interleaved C-run. (Done for `beispiele/124` on 2026-09-15, §7.) For 104 itself `gP_kein_exklusiv` already says two
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
  fragment (tables only, `u32` ranges, writes, calls, a trailing return) and the lowering.
  *Widening `korrOk` does NOT move the count while (a) binds, and on 2026-09-15 it was
  measured not to:* 23 arms were added and the count stayed at 2.
- **What `korrOk` still refuses, after the 2026-09-15 widening** (§6.2), each with its reason
  rather than a promise:
  * ~~**`if`/`else` and `traverse`**~~ and ~~**`let x = f(…)`**~~ -- **closed 2026-09-15**, see
    §6.7 below.
  * **A `traverse` whose bound is not a literal.** `scorr_traverse` wants `ev hiC` to be the
    table's count at EVERY C state, and the only C expression the check can decide that of is
    a literal; a header that computes its bound is a refusal.
  * **`!=`**, **`(T)(e)` as a C wrapper** (`ecorr_cast` proved) and **`_Atomic` globals**
    (`ecorr_globAtomar`, `scorr_assignGlobAtomar` proved) -- each named at the site
    (`KorrespondenzAllg.lean`, CUTS) with the reason it is not one arm.
  * **Floats** have no `ecorr_*` at all and `CX` has no float operand a `GRow` could carry.
- **The printer is narrower than the check** since 2026-09-15: `gcx` (`corrlean.rs`) prints
  only `+ - *` and `== < <= >`, so `/ % & | ^ << >>`, `&& || !`, `true`/`false`, plain globals
  and `storeGlob` have no printer path. That is Rust work; until it is done those arms are
  exercised only by the probes.
- **The arena stops at the EXPORTER, no longer at the specification** (2026-09-15,
  `OFFEN.md` O14, `SATZKARTE.md` §33). `alloc`/`reset` had no `Stmt` constructor at all; since
  `Grammatik/ArenaZucker.lean` they are sugar over `Block.narrow` + `Stmt.assignSlot` +
  `Stmt.assignGlob` over a table of `count = hi` slots and a `used` global -- the pair the
  emitter itself writes. ~~**What is missing is `lean_g.rs`**, which refuses an arena declaration
  BY NAME instead of synthesising that pair~~ — **the exporter builds the pair since
  2026-09-15** (`messung/muse/OPUS-BERICHT-EXPORT.md`): a table of `count = hi` with one field,
  a global `A_used : int 0 hi`, `def gArena_A : ArenaForm gD`, and `Stmt.arenaReset` /
  `Block.arenaAlloc` / the slot read `A[i]`; a probe with all four forms exports and compiles
  under Lean. **`beispiele/98` and `99` still stop at sieve (b)**, at two statement SHAPES that
  are refused by name: an `alloc` without `else` (the model form always carries a full-arena
  branch and the emitted C carries none), and an `alloc` at the top level of a body (a `Block`
  former where an `Endblock` is wanted — the same wall `let x = f()` hits). *Because the form is
  sugar, `gabbro_ziel` already covers an arena program: no new `Stmt` case and no re-proof.*
- **The unit's data.** `Kette.E`'s lock invariants, axiom ensures, declared starts and initial
  memory are written next to the source by the chain's author (the exporter fills none of
  them); a wrong `starts` is a different program, visible in the chain file.
- **The user's logic is per program.** `NutzerPflicht` is proved per chain (104: the argument
  of `gP_einzahlen_R` again, over the parser's declaration; 108: two returns). That is the
  goal's intent -- "the user proves only their own logic" -- not a gap; but the chain count
  moves only with such proofs.
- **Part 4's condition, HALVED on 2026-09-15** (Opus lane `staerker`, §6.8, report
  `messung/muse/OPUS-BERICHT-STAERKER.md`). The condition was "the Gabbro call ends in no
  model error"; the model has exactly two error classes.
  * **The HARDWARE class is gone, and provably**: the five forms whose outcome is `hardware`
    (axiom call, axiom bind, register read in either shape, `awaits`, `forever`) are all
    outside `korrOk`'s covered set, so no certified body carries one, so `rufAt` never ends
    in one -- at every depth, every budget, every world, every argument list, against every
    oracle (`korrOk_rufAt_ohneHardware`). The theorem carries it as a new CONCLUSION 4b.
  * ~~**The WRITER'S LOGIC class stays**~~ -- **REDUCED TO ONE FRAME FACT on 2026-09-15**
    (Opus lane `kongruenz`, §6.9, report `messung/muse/OPUS-BERICHT-KONGRUENZ.md`). The
    congruence lemma named here was built (`HandlerKongruenz.lean`). With it, at an entry
    meeting the callee's `requires`, the ONLY `logik` outcome `rufAt` has left is the
    `abstieg` -- `vorbedingung`, `nachbedingung`, `invariante` and the body-own
    `schleife`/`vorzustand`/`bereich` all fall to `KoerperGutS` and `InvGutS`
    (`rufAt_nurAbstieg`). Carried as a NAMED hypothesis: `RufRahmenTreu`, the FRAME half of
    `RespektiertRahmen` for `rufAt` at every world. The CONTRACT half is PROVED
    (`rufAt_vertraege`), so the gap is one fact and not two, and it is about LOCKS alone
    (`rufRahmenTreu_ohneSperren`: for a declaration with no lock it is free -- witness on
    chain 108, `nurAbstieg_zeuge_108`). The `abstieg` residue is now a computation at ONE
    depth (`rufAt_stabil_ab`). Theorem `schlusssatz` gained clause 4e.
  * **And premise (c) does NOT do the hardware work** -- `HardwareAnnahmen` constrains the
    oracle only where the raw answer fits the declared type. Witness with every premise met
    and the call still stopping: `befund_hardware_bleibt` (`RufOhneHardwareZeuge.lean`).
- **A2 is DISCHARGED for both chains** (§6.6, 2026-09-15): the emitted TEXT is pinned and
  parsed in Lean, and `cProgC ctext = kProg zert` is a theorem. The rest of A1/A3/A4 stays
  outside Lean exactly as in §6.4.
- **The adequacy chain** (one active thread of G against `rufAt`) is not re-instantiated; the
  concurrent conclusion of part 5 is the MODEL's (`gabbro_ziel`), not the C's -- stage (b).
  **Measured 2026-09-15** (§6.8): FOUR things stand between part 4 and part 5, and the
  covered FRAGMENT is not one of them -- every certified body is in the adequacy fragment
  (`korrOk_endR`, `KorrOkAdaequat.lean`). The other three: `rufG_adaequat_ruf` realises
  `rufRumpf`, not `rufAt` (which also checks the contracts AND READS their carriers, so the
  two differ on the TRACE, and the trace is what `SpurInv` is about -- booked as
  `befund_vertrag` in `RufAdaequatRufG.lean` §13); `Tief P A n` carries the same depth
  residue as part 4's condition; and the adequacy is EXISTENTIAL, about a machine whose
  thread already stands on the body with a non-waiting caller frame. **The cost is not the
  build**: `RufAdaequatRufG` is already in `Schlusssatz`'s transitive import closure, and
  the bridge file above costs 5,9 s and 0,89 GB. **The congruence lemma the first item
  needed exists since 2026-09-15** (§6.9); it does NOT close this item, and the report says
  why: it relates two runs of the SAME body text, and `rufAt` vs `rufRumpf` differ in the
  body's WORLD (the contract reads), not only in the handler's answers.

### 6.6 A2 discharged: the emitted TEXT is parsed in Lean (2026-09-15)

*Files: `grammatik/Grammatik/CParser/` (`CLexer.lean`, `CParse.lean`, `CProben.lean`,
`Bruecke.lean`), `CText104.lean`, `CText104Zeuge.lean`, `CText108.lean`, two theorems at the
end of `Kette104Satz.lean`. Guardian: `instrumente/pruefe-ctext.py`. Theorem map:
SATZKARTE §28. Report: `messung/muse/OPUS-BERICHT-CPARSER.md`.*

**What it replaces.** The C side of the closing theorem is `kProg K.zert`, the unit the
CORRESPONDENCE CERTIFICATE elaborates to. That the emitted TEXT means the same thing was
assumption A2 -- a hand transcription, and §6.3 records it going stale in spelling once
already. Now `parseC : List Char → Option (List CFun)` reads the emitted subset in Lean, and

    a2_104 : parseC ctext104 = some (kFuns zert104)
    a2_108 : parseC ctext108 = some (kFuns zert108)

hold by kernel reduction (`rfl`), with `ctext104`/`ctext108` pinned line by line and
byte-identical to `gabbro emit` (the guardian re-emits and compares, 2733 bytes). From them,
`cProgC ctext = kProg zert` and `schlusssatz_text` -- `schlusssatz` with its A1 premise
stated about the TEXT. A2 is not an assumption of the two chains any more; what remains is
part of A1 (§5).

**The subset, and why it is small.** `parseC` reads exactly the forms the two chains' emitted
C uses -- the prelude with its two `_Static_assert` pins (both REQUIRED), integer `#define`s,
the two table `typedef struct`s, `static T T_speicher;`, a foreign `void f(void);`, `static`
declarations and definitions, and the statements `(void)x;`, a slot store through a pointer
or at a named table, a direct call with or without `(void)`, `return;`/`return e;` over
literals, locals and slot reads. Everything else is `none`. Measured over the emitted C of
the whole corpus: **4 of 113 programs are inside the subset** (104, 108, 118, 52); the census
`instrumente/pruefe-cformen.py` names what the other 109 use. Widening it means type
inference for arithmetic (`CX.bin` carries a computation type C only implies), a pinned
numbering for locals that are not parameters, and one arm each for `if`, loops and the
register forms -- but sieve (a) stays the binding one for the chain count (§6.5), so a wider
C parser buys no chain today.

**The cost, and what it says about O13.** Kernel-reducing the parse first cost 44,6 GB, and
the parser was not the reason: in Lean 4.33 `String.toList` goes through the array
representation, and forcing the FIRST character of a 1419-byte string LITERAL costs 33,7 GB.
The same text as a `List Char` of 45 short pieces costs 3,3 GB. `dokumente/OFFEN.md` O13
carries the rest of the measurement, because the Gabbro-side pins lex a `String` the same way.

**O13 is CLOSED since 2026-09-15**, and the Gabbro side's 72 GB turned out to be only partly
this: the chain sources are pinned as characters now (`SRC-BEGIN` blocks, `String.ofList`,
the bridge `lex_ofList`), but the dominant cost was ONE theorem -- `uebersetzt4`/`uebersetzt8`
unfolding `uebersetzeAllg` at a CONCRETE source, which made simplification whnf `lex src…`
and run the decoder in the kernel. `uebersetzeAllg_von_zeichen` (Schlusssatz.lean) does that
unfolding once, at a variable. The whole library now builds from an empty build directory in
**5 min 20 s at a peak of 6,86 GB**; `Kette104` costs 0,92 GB, `Kette108` 0,87 GB.

### 6.7 The certificate's BLOCK structure: `if`, `let` of a call, `traverse` (2026-09-15)

*Files: `grammatik/Grammatik/KorrespondenzAllg.lean` (the staged check and its soundness),
`grammatik/Grammatik/KorrespondenzBlockZeuge.lean` (new: the probes). Theorem map:
SATZKARTE §30. Report: `messung/muse/OPUS-BERICHT-BLOCK.md`.*

**What was missing was the recursion, not a lemma.** `scorr_ite`, `scorr_traverse` and
`bsem_bindCall` had all been proved in `CFormenI.lean`/`CFormenM.lean`; the three rows that
need them (`GRow.ite`, `GRow.forTrav`, `GRow.call` with a destination) fell through
`stOk`'s `_ => false`, because their Gabbro side is a `Block` and `enOk` walks only
`Endblock`.

**The staging**, as §6.5 said to build it and as it now stands:

    stOk0   the flat arms of before -- no recursion at all
    blOk    a `Block` against a row list, self-recursive on the ROWS
    stOk    stOk0 plus the arms whose row carries rows (`ite`, `forTrav`)
    enOk    unchanged

`stOk` and `blOk` are ONE `mutual` over `GRow` / `List GRow` -- the nested-inductive shape
`growRow`/`growsCS` and `rowFreshOk`/`rowsFresh` already have in `Korrespondenz.lean`. (The
§6.5 note guessed that Lean would not take two functions in one mutual here; measured, it
does, as long as one of them is over `GRow` and the other over `List GRow`.) The descent is
on the ROW, so the check stays STRUCTURAL: no fuel, no well-founded recursion, and `decide`
still reduces it in the kernel. *This is the opposite of O13's second pathology, and
deliberately so: a mutual recursion through a FUEL argument compiles to a mutual `Nat.brecOn`
and is exponential in the fuel.* The SOUNDNESS runs on a plain measure (`rowSize`), which a
proof may do because a proof never reduces.

**What the arms decide**, each ending in the lemma that was already there:

| row | Gabbro | ends in | decided, not assumed |
|---|---|---|---|
| `GRow.ite cc t e` | `Stmt.ite` | `scorr_ite` | the condition, and BOTH arms row by row |
| `GRow.call fc args (some (y, τc))` | `Block.bindCall` | `bsem_bindCall` | callee number, `y` fresh, `declOk`, `callMapOk`, `argsOk`, and the rows after the binder under the PUSHED map |
| `GRow.forTrav x t (.lit N) rows m'` | `Stmt.traverse` | `scorr_traverse` | `N` is the table's count, `x` fresh, the type holds `0 .. N`, and the body does not write `x` |

Coverage: `stOk` **5 → 7 of the 27 `Stmt` constructors**; `blOk` is new and reads **4 of the
17 `Block` constructors** (`nil`, `cons`, `bind`, `bindCall`); `enOk` unchanged. `korrOk_fnCorr`
and `korrOk_jeder_lauf` keep their statements word for word, and every new arm has a positive
probe AND a planted defect.

**The chain count did not move, and could not**: sieve (a) still binds (§6.3, §6.5).

### 6.8 Part 4's condition, halved: no hardware error, and the residue named (2026-09-15)

*Opus lane `staerker`. Files: `grammatik/Grammatik/RufOhneHardware.lean` (new),
`RufOhneHardwareZeuge.lean` (new), `KorrOkAdaequat.lean` (new), `KorrespondenzAllg.lean` §5,
`Schlusssatz.lean`, `Kette104Satz.lean`, `CParser/Bruecke.lean`, `Kette108.lean`,
`CText108.lean`. Theorem map: SATZKARTE §35. Report:
`messung/muse/OPUS-BERICHT-STAERKER.md`. Axioms of every theorem named here: `propext`,
`Classical.choice`, `Quot.sound` (the purely computational ones: `propext`, `Quot.sound`);
no `sorry`, no `native_decide`, no new `axiom`. Chain count re-measured with
`zaehle-kette.py --lean` over 113 programs: **(a) 2, (b) 15, (c) 15, (d) 60, (e) 2, CHAIN
COUNT 2 -- unchanged.*

**The theorem got THREE new conclusions and lost no hypothesis.** `schlusssatz`'s premise
list is character-for-character the one of §6.1; the conclusion gained 4b, 4c and 4d
between parts 4 and 5. `schlusssatz_104` and `schlusssatz_124` are untouched.

| new clause | says |
|---|---|
| 4b | `∀ passes n f σ ρ e, rufAt K.E.P O passes n f σ ρ ≠ .hardware e` |
| 4c | an error outcome of `rufAt` is a `logik` outcome -- the writer's logic, alone |
| 4d | `(rufAt … (n+1) f σ ρ).istFehler = false → ReqAmEintritt K.E.P f σ ρ` |

**Why 4b is a theorem and not an assumption.** The `Hardware` outcome has five sources and
every one is a syntactic form (`RufOhneHardware.lean`): `axiomCall`/`bindAxiom`
(`annahme`), `regLies` (`register`, `geraet`), `regLiesElse` (`register`), `awaits`
(`sichtbarkeit`), `forever` (`fortschritt`). `Hardware.ieee` is no longer produced at all
(verdict F1). The check `hardwareFrei` refuses exactly those five; its soundness
(`Endblock.hardwareFrei_ok`) is the twin of `Endblock.logikFrei_ok`; and since `rufAt`'s
OWN error branches are all `logik`, the handler premise `OhneHardware` carries itself by
induction on the DEPTH (`rufAt_ohneHardware`) -- no premise about the oracle or the user.
`korrOk` refuses all five (they have no `GRow` at all), read off the check by the same
induction `stOkBl_sound` runs on (`korrOk_hardwareFrei`).

**The finding that goes with it, with a witness program** (`befund_hardware_bleibt`): the
goal theorem's premise (c) `HardwareAnnahmen` does NOT rule the hardware error out. Its
axiom leg `AxVertragO` constrains the oracle only WHERE the raw answer fits the declared
result type. On `axP` (`AxiomVertrag.lean`) -- in the checker's fragment, footprint checked,
`KoerperGutA` proved for every function against every oracle of the class -- the oracle
`axOBoese` (same answer world as `axO`, raw answer `99` outside `int 0 3`) meets `GutO`,
`RegLokal` and `AxVertragO` (the last VACUOUSLY), and `rufAt axP axOBoese passes (n+1)
zaehle σ .nil = .hardware (.annahme inc)` at every depth and budget.

**What is left of the condition, and the one lemma that would close it.** `logik`:
`vorbedingung`, `nachbedingung`, `invariante`, `abstieg`, and the body-own `schleife`,
`vorzustand`, `bereich`. The user's obligation covers every body-own `logik` outcome
(`KoerperGutS` clause 2) and the caller duty (clause 1), but NOT for the handler `rufAt`:
`OhneVorbedingung` fails at any key whose `requires` is false, `OhneLogik` fails at depth
`0` (`abstieg`), and `RespektiertRahmen` promises the callee frame at EVERY world while
`rufAt_gut` gives it only at worlds meeting `HeldB`. **The missing piece is one congruence
lemma** over `execStmt`/`execBlock`/`execEnd` in the handler: two handlers whose answers
are equal or both errors give body outcomes that are equal or both errors, with the error
TAG carried. It would also give `rufAt`'s depth monotonicity (an outcome that is not an
`abstieg` is the outcome at every larger depth) and is the first half of a `rufAt` ↔
`rufRumpf` bridge -- three open items on one lemma, estimated 400-500 Lean lines over
~50 constructors plus the three loop combinators.

### 6.9 The handler congruence, and part 4's `logik` condition (2026-09-15)

*Files: `grammatik/Grammatik/HandlerKongruenz.lean`, `RufTiefe.lean`, `RufLogik.lean`,
`KorrOkOhneLocks.lean`, `RufLogikZeuge.lean` (all new), `Schlusssatz.lean`,
`CParser/Bruecke.lean`. Theorem map: SATZKARTE §36. Report:
`messung/muse/OPUS-BERICHT-KONGRUENZ.md`.*

**The lemma, stated before it was proved.** For an error-mark set `Er`, if two handlers
`R₁`, `R₂` answer at every key either the same outcome or -- on `R₁`'s side -- an ERROR
whose mark lies in `Er`, then for every statement, block and terminal block the run under
`R₁` is the run under `R₂`, or it is an error whose mark lies in `Er`. One-sided on
purpose: a symmetric form has no premise for depth monotonicity, where `rufAt n` answers
`abstieg` and `rufAt (n+1)` answers `ok`.

**What each side condition serves.** The lemma has no side condition at all beyond the
handler premise. The side conditions live in the CONSUMERS:

| condition | which open item it serves |
|---|---|
| none | depth monotonicity `rufAt_stabil_ab` -- clause 4e(i) |
| `RahmenO`/`RegLokal`/`AxVertragO` on the oracle | the classes `KoerperGutS`/`InvGutS` quantify over -- 4e(ii) |
| `HavocOk S U`, inhabited under (b) | `execEndH`'s environment move -- 4e(ii) |
| `(P.rumpf f).ohneLocks`, from `korrOk_ohneLocks` | `execEndH = execEnd` -- 4e(ii) |
| ~~`RufRahmenTreu P (rufAt …)`~~ | was the residue for one day; **proved**, see §6.10 |

**Clause by clause: what disappeared from part 4's condition.**

| kind | before | after |
|---|---|---|
| `hardware` (five forms) | discharged 2026-09-15 (§6.8, 4b) | discharged |
| `vorbedingung` of a CALLEE | open | discharged (`KoerperGutS` clause 1, caller duty) |
| `nachbedingung` | open | discharged (`KoerperGutS` clause 1, body triple) |
| `invariante` | open | discharged (`InvGutS`) |
| `schleife`, `vorzustand`, `bereich` | open | discharged (`KoerperGutS` clause 2) |
| `vorbedingung` of the CALL ITSELF | open | it IS the hypothesis `ReqAmEintritt` (clause 4d says the condition implies it) |
| `abstieg` | open | **stays**, and is now stable upwards: 4e(i) makes it a computation at ONE depth |

**What resisted, exactly, and for how long.** `RespektiertRahmen` is a conjunction; its
CONTRACT half is proved for `rufAt` (`rufAt_vertraege`) and its FRAME half was not.
`rufAt_gut` (`Satz.lean`) proves the frame at worlds meeting
`HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt`; part 4 quantifies
over ANY world, including worlds holding locks out of the function's floor. The estimate in
this section -- "removing the premise means a second long induction over the semantics" --
was right, and §6.10 is that induction.

**The other consumer, checked against the lemma BEFORE it was built.** The congruence does
NOT close the `rufAt` ↔ machine-G item of §6.5. It relates two runs of the same body text
from the same world; `rufAt` and `rufRumpf` differ in the WORLD the body runs from and
returns to (the contract reads), not in a handler's answers, so the premise
`HandlerUnter Er` cannot be formed for that pair. What the lemma does give that item is the
depth half of the `Tief` residue (4e(i)).

### 6.10 A chain for a program that touches a DEVICE (2026-09-15)

*Opus lane `geraet`. Files: `grammatik/Grammatik/KorrespondenzGeraetZeuge.lean` (new),
`Korrespondenz.lean` (three rows), `KorrespondenzAllg.lean` (`GerTafel`, `regAdrOk`,
`GerAnnahme`, the three device judgements, the arms, §5 guarded), `CSpeicher.lean`
(`EmitLay.devs`, `corrW`'s third clause), `CFormen.lean` (`DecidableEq CX`),
`Schlusssatz.lean`, `KorrOkAdaequat.lean`. Theorem map: SATZKARTE §37. Report:
`messung/muse/OPUS-BERICHT-GERAET.md`. Axioms of every theorem named here: `propext`,
`Classical.choice`, `Quot.sound`; `#print axioms gabbro_ziel` unchanged; no `sorry`, no
`native_decide`, no new `axiom`.*

**THE SENTENCE THE CHAIN CLAIMS.** *If the profile holds and the register answers inside its
declared type, every run of the emitted C corresponds.* Nothing about the device is claimed:
not that it answers, not that it answers the truth, not that it keeps the promise its own
declaration states.

**What `korrOk` carries now.** Three of the five hardware forms:

| Gabbro form | row | C | judgement |
|---|---|---|---|
| `Stmt.regSchreib` (`R = e;`) | `GRow.storeReg` | `(*(volatile uintN_t *)(cp)) = e;` | `gerSchreib_step` (a `StmtCorr`) |
| `Block.regLies` (`let x = R;`) | `GRow.loadReg` | `T x = (*(volatile uintN_t *)(cp));` | `bsem_regLies` (a `BlockSem`) |
| `Block.regLiesElse` (`let x = R else (c) { return e; }`) | `GRow.loadRegElse` | the read, then `if (!(c)) { return e; }` | `bsem_regLiesElse` |

The `requires … else` channel is the interesting one: **a broken device promise becomes a
BRANCH in the program rather than a stop.** `Hardware.geraet` cannot arise from it at all, and
the `else` arm must correspond like any other row. What is left of the residue is the one
outcome no program can catch -- an answer outside the declared TYPE (`Hardware.register`),
where there is no value to branch on.

**The premise list, and where each premise sits.** `korrOk` gained a LAST parameter
`GT : GerTafel D` -- the emitter's device numbers as plain data, with a default of the EMPTY
table (`ein := false`) under which every device row is refused. So the two closed chains call
`korrOk EL fnum c P fs` unchanged, character for character, and `gerAnn_leer` proves the empty
table meets the profile vacuously: **the generic theorem lost no hypothesis it had.**
`korrOk_fnCorr` and `korrOk_jeder_lauf` gained ONE: `GerAnnahme EL orc O GT` (§5).

**What it COST, and the premise that was refused.** `korrOk_rufAt_ohneHardware` (§6.8, clause
4b of `schlusssatz`) now carries `GT.ein = false`. It has to: a certificate with a register
READ row carries `Block.regLies`/`.regLiesElse`, and those are two of the five sources of a
hardware outcome. *The device chain and clause 4b are the two sides of one coin, and the coin
is now visible in the premise list instead of being spent silently.* `korrOk_endR`
(`KorrOkAdaequat.lean`, the adequacy-fragment bridge) carries the same premise, for a
different reason: `BlockR` HAS both device constructors, but `BlockR.regLiesElse` is stated at
`l = false` while that induction runs at every `l`. **Both are OPEN by name.**

**The one line that is not in the certificate.** A device window is not memory, and `corrW`
says nothing about one (`CFormenH.lean`'s own CUT). The premise *"in every related state the
window is mapped"* cannot be an assumption of the profile -- **as an assumption it is FALSE**
whenever the declaration has a register, since any related state can have the window unmapped
and stay related. So the mapping went where it belongs: `EmitLay` declares the unit's device
windows (`devs : Nat → Bool := fun _ => false`) and `corrW` carries
`∀ d, EL.devs d = true → st.live (.dev d) = true`. Cost, measured: `corrW` has **300**
occurrences in `grammatik/`, and **17** had to move.

**The witness** (`KorrespondenzGeraetZeuge.lean`): one `mmio` device, two registers
(`ST @0x00 class r requires ST <= 8`, `CTRL @0x04 class rw`), one function carrying **all
three** device forms; `gZert_ok` decides the certificate true; `gZert_sieb` refuses **seven**
planted defects (the device table switched off, the wrong register, the wrong cell width, the
promise read as its opposite, the `else` branch dropped, the `else` answer changed, and a
plain local read where the volatile one stands); `gZert_ohneTafel` shows the DEFAULT
certificate call refuses the same program; `gerZeuge_nichtHardwareFrei` shows the body is not
`hardwareFrei`, i.e. the `korrOk` of before could not have certified it; `gerAnn` is a TERM,
so the profile is inhabited and the chain is not vacuous; `gerZeuge_kette` and
`gerZeuge_lauf` are the chain for that program at every depth and budget.

**The semantic merge break with §6.9, and the repair.** `korrOk_ohneLocks` walks the same rows
and ended in a catch-all that assumed every remaining row meets `Block.cons`; the device rows do
not, and the merged tree read `h.1` off a `false`. Repaired with three explicit branches and NO
guard: all three rows carry no `locks` -- `Stmt.regSchreib` is a leaf, `Block.regLies` hands the
question to `rest`, and `Block.regLiesElse`'s `sonst` half is free because the check admits only
`Endblock.ret` there. The four `ohneLocks` theorems gained `GT` and hold for EVERY device table,
so they are stronger than before; `korrOk_ohneLocks`'s `GT` is implicit and §6.9's clause 4e
needed no edit. *The one line that would make it false is named at the site: a widened `else`
channel could hold a `locks`.*

**The corpus, measured (§1 of the report).** 25 of 113 programs carry one of the five forms;
13 declare a `device`; the corpus holds **22 plain register reads, 1 read with `else`
(`beispiele/44-register-einmal-lesen.gab:103`, the only one), 14 stores, 11 `awaits`,
11 `forever` and ZERO axiom calls** -- a driver call over the ABI is not in the corpus at all.
**No register-bearing program reaches sieve (b):** all 25 stop at sieve (a), the Lean parser
and elaborator. **CHAIN COUNT 2 of 113, unchanged, and it could not change** -- this lane
touched sieve (e) only, while sieve (a) binds.

### 6.11 Sieve (d) was 60 because the guardian could not see a C TYPE -- it is 55 (2026-09-15)

*Opus lane `aggregat`. Files: `instrumente/pruefe-cformen.py`, `instrumente/zaehle-kette.py`.
Ledger: `dokumente/OFFEN.md` `O16`. Report: `messung/muse/OPUS-BERICHT-AGGREGAT.md`. No Lean
and no Rust was touched; `#print axioms gabbro_ziel` and `gabbro_ziel` are untouched by
construction.*

**The finding.** `pruefe-cformen.py` built its row key from the statement TEXT. `return
c.len;` and `return (Nachricht){ .marke = Nachricht_Kurz, .last.Kurz = x };` were the same row
`stmt:return-expr` -- state (i), lemma `scorr_ret`/`ergCorr_run`. But `CTy` is `int | ptr` and
`CVal` is `int | ptr | undef` (`CSpeicher.lean` §1-§2), so **no `GRow` can carry a struct by
value** and neither lemma is about one. *A guardian that books a form under a lemma that does
not cover it is worse than one that reports it uncovered.*

**The repair, and what it moved.** The classifier reads the unit's aggregate typedefs, every
function's C return type and every body's aggregate-typed names, and classifies by the
DESTINATION of a value: return slot (`stmt:return-aggregate`), fresh local
(`stmt:bind-aggregate`), memory (`stmt:store-aggregate`), parameter
(`stmt:call-aggregate-arg`). Measured by running the guardian of `HEAD` and the repaired one
over the same emitted C, statement by statement:

| | before | after |
|---|---|---|
| forms seen | 77 (51 lemma, 4 assumption, **22** uncovered) | 81 (51 lemma, 4 assumption, **26** uncovered) |
| occurrences | **1905** lemma, 187 assumption, **400** uncovered | **1886** lemma, 187 assumption, **419** uncovered |
| verdict | GREEN | **RED: 4 new uncovered forms** -- then GREEN with the four dated `2026-09-15` in `KNOWN_UNCOVERED`, which is the guardian's own mechanism for a named absence |
| sieve (d) | **60** of 113 | **55** of 113 |
| chain count | 2 | **2 -- unchanged** |

**19 occurrences in 15 programs left state (i) for state (iii)**, and 2 more moved inside
state (iii). The five programs that lose sieve (d) are `80`, `94`, `95`, `100`, `101`; nine
more carry an aggregate and were already failing (d) for other reasons.

**The extension was PRICED AND REFUSED, by a sweep and not by the census row.** A probe in
which the four rows carry a lemma name -- *the obstacle removed* -- was put in place and the
whole 113-program sweep re-run: **(b) 15, (c) 15, (d) 60, (e) 2**, i.e. sieve (d) returns to
60 and **nothing else moves**. Of the 15 programs that export, **not one** fails (d) on
aggregates alone; `120-tagged-construction` fails on the tagged-union READ side besides
(`switch (m.marke)`, `m.last.F`), uncovered since 2026-09-13 with its own reason. The five
programs an aggregate C model would repair at (d) are stopped **two sieves earlier**, at (b),
by `LG001 assume …`/`requires profile has no G form` and by `LG001 function … is not \`impl\``.
**Carrying aggregates in the C model unblocks ZERO corpus programs**, and the chain count
could not move either way: sieve (a) passes 2 (`104`, `108`), both aggregate-free.

> **The thing sieve (d) measures got smaller and the thing it measures got truer**, and those
> are the same event. A number that falls because the instrument started seeing is not a
> regression; the 60 was the regression, and it stands booked four times in the live ledgers
> (§6.3 twice, §6.8 once, `SATZKARTE.md` §35 once) and in five lane reports. Those are dated
> protocol and are NOT rewritten -- **55 is the number from 2026-09-15 on.**

### 6.12 The frame at every world: the last piece of part 4's condition (2026-09-15)

*Files: `grammatik/Grammatik/RahmenTreu.lean` (new), `RufLogik.lean`, `RufLogikZeuge.lean`,
`Schlusssatz.lean`, `CParser/Bruecke.lean`. Theorem map: SATZKARTE §37. Report:
`messung/muse/OPUS-BERICHT-RAHMEN.md`.*

**The question §6.9 left.** Is `RufRahmenTreu P (rufAt P O passes n)` -- an `ok` answer of
the model's own call handler keeps the callee's declared frame and gives back every lock it
took, at EVERY world -- true, false, or true only where `HeldB` holds? Three routes were
open: derive `HeldB` for reachable worlds, prove the frame without `rufAt_gut`, or find a
world where it fails.

**The measurement that picked the route.** `Gut` (Satz.lean) bundles three facts, and only
the third needs the lock discipline:

| fact | where the `HeldB` premise is spent |
|---|---|
| `Rahmen` -- writes stay inside the contract | nowhere: each write carries its own `hw : V.schreibt t = true` |
| `σ'.haelt = σ.haelt` -- every lock given back | nowhere: `gut_nimmt_gibt` proves this half without its `hn` argument |
| every event GOOD, trace consistent | everywhere: `Ereignis.gut` of an access is `darf ∧ HeldIn`, of a `nimmt` the rank order |

So route (c) is **false** -- the statement holds at every world -- and route (b) is the
honest one: `RahmenTreu.lean` re-runs `Satz.lean`'s induction over the whole grammar with
the third fact deleted from the CONCLUSION and hence the premise from the statement. The
reason the held set survives is worth naming: `offen (gibt L :: nimmt L h :: s)` is
`(L :: offen s).erase L`, and `List.erase` takes the FIRST occurrence -- the one `nimmt`
just put there. A world that already holds `L` is not well-disciplined and `Gut` rightly
refuses it, but the frame and the held set survive it.

**What the new file proves.** `Treu W G σ σ'` = `Rahmen W G σ σ' ∧ σ'.haelt = σ.haelt`;
`stmt_treu`/`block_treu`/`end_treu`/`arms_treu`/`grund_treu` over the mutual grammar, the
three loop combinators beside them, and `rufAt_treu` by induction on the depth. Premises:
`TreuR R` for the handler and `TreuO O` for the oracle -- the first two conjuncts of `GutO`,
i.e. H1. NOT needed: `StufenOk`, `GutO`'s trace shape, `HeldB` anywhere.

**What disappeared from `schlusssatz`.** Clause 4e(ii) lost its hypothesis: it now reads
"at an entry meeting the callee's `requires`, the only `logik` outcome of `rufAt` is an
`abstieg`", unconditionally, for every certified chain. The premise list of `schlusssatz` is
unchanged; `schlusssatz_104`, `schlusssatz_124` and `gabbro_ziel` are untouched. So of part
4's condition, what is left is the depth residue of 4e(i) ALONE, and that is a computation
at one depth, not a promise.

**Witness on a LOCKED program.** `Kette104.nurAbstieg_zeuge_104`: 104 declares the lock `M`
and both its functions `requires Held(M)`, so the entry's static resource context names
`Res.held m4` -- and the world the chain's own witness runs from holds nothing
(`heldB_faellt_104`, proved). At that world `rufAt_gut` says nothing at all. The witness
carries the frame read on the function that may NOT write (`lies`, `D4.schreibt lies4 t4 =
false`) at a world whose slot stands at `100`, so the frame clause forbids something that
could have happened.

## 7. Stage (b), the concurrent closing theorem -- beispiele/124, theorem schlusssatz_124

*Added 2026-09-15. Files: `grammatik/Grammatik/CNebenlaeufig.lean` (generic: semantics,
premises, transfer theorems), `Korpus124.lean` (the G program of 124 and the goal theorem on
it), `Schlusssatz124.lean` (the emitted C, the simulation, the theorem, the witness),
`CTicket.lean` + `Schlusssatz124Ticket.lean` (the runtime's ticket lock, which turns the lock
premise into a theorem: §7.7). Axioms of
every theorem named here: `propext`, `Classical.choice`, `Quot.sound` (`c124_direkt`:
`propext`; `sperrAbstrakt_rahmen`, `sperrAbstrakt_nur_eigen`: none); no `sorry`, no
`native_decide`, no new `axiom`.*

### 7.1 Which program, measured

Six corpus programs start more than one thread (07, 59, 108, 109, 124, 125). Measured on
2026-09-15 with a binary built from this tree: the exporter `gabbro lean-g` covers only 108
(07: `LG001` type `Pa`; 59: `LG001` a lock form; 109: `LG001` `entry`; 124: `LG003` the
`requires` of `setze`; 125: `LG001` `static`), and the correspondence printer
`gabbro corr-lean` covers none (104 forms only). 108 takes no lock, so no interleaving of it
contends. **124** is the smallest program with two threads and a lock that has a G form -- the
hand model `mP` of `MehrfadenZeuge.lean`. That model's `pruefeA` returns nothing and reads
nothing, while the source's (and the emitted C's) returns `privA.slots[0].stand`; the C's read
of `privA` would then have no G access to cover it. `Korpus124.lean` therefore writes the G
program from the source's BODIES (`kP`, functions `setze`, `pruefeA`, `hauptA`, `hauptB`), and
proves every premise group of the goal theorem on it: `kP_akzeptiert` (`decide`),
`kE_nutzerPflicht`, `kO_hw`, and `k124_ziel` (`gabbro_ziel` with the concrete checker).

**Finding (contracts).** The source's `setze` promises only `konto.slots[0].stand == x`. With
that `ensures`, the release check of `hauptA`'s `locks L { setze(30); }` fails for a callee
answer the contract admits (`konto[1]` free), so premise (b) of the goal theorem does not hold
for 124 as written. `kP` keeps `mP`'s `ensures konto[0] == konto[1] && konto[0] == x` (what the
body meets). Contracts do not change the C; the corpus file is unchanged here.

### 7.2 The semantics (`CNebenlaeufig.lean`)

A configuration (`KonfC`) is the shared C state of `CSpeicher.lean`, one thread state per
`Faden`, and the holder of every lock of the runtime. A running thread (`CFaden.an k ρ`) is
its root function's continuation and locals; a thread never created or returned is `aus`. A
step (`SchrittC E LP K t ℓ K'`) is taken by ONE freely chosen thread -- every schedule is a run,
so the semantics is sequentially consistent: split a sequence (`teile`); leave the root body
(`ende`); call the runtime's lock primitive (`sperre`, meaning `LP`); or run ONE
synchronisation-free statement as a block with the existing sequential semantics (`block`,
`rueck`: `Exec` with `CallAt`, determinism `exec_det`).

**Why blocks between synchronisation points, not one step per access.** The sequential C
semantics is big-step, and the block rule reuses it unchanged with every T4 lemma. The C11
model gives meaning only to race-free programs, and for those every execution is SC and
serialisable at the granularity of synchronisation-free regions (DRF-SC and its region
corollary: Adve and Hill 1990, Boehm and Adve 2008; Batty et al. 2011 for C11); the premise
`DRFSC` is stated at exactly this granularity, with race freedom at the same granularity as
its hypothesis. And a C block is a contiguous segment of G steps of ONE thread -- a G
interleaving among others -- so the simulation is a forward simulation into G's
interleavings, never a reordering argument.

**Footprints** (`fussR`, `fussW`): the objects a block's syntax names, to its call depth, and
the ones named in store targets. On the direct fragment (`CS.direkt`, `CEinheit.direkt`:
pointers formed only from named objects, integer locals, no stack objects, no volatile,
atomic or foreign access but the lock primitive) the pointer every load and store uses lies in
an object its expression names (`ev_zform_blk`). `c124_direkt` (`decide`).

**Race freedom** (`RennfreiC E LP K0`): on every SC run, two steps of different threads whose
footprints share an object that one of them writes are ordered through a lock (`GeordnetC`:
release by the first thread, later acquire by the second, in between).

### 7.3 The statement

```
schlusssatz_124 (passes : Nat) (LP : SperrSem) (K0 : KonfC)
    (hLZ : LaufzeitC c124 [2, 3] st0 K0 LP)          -- the runtime list
    (Echt : BeobC → Prop) (hDRF : DRFSC c124 LP K0 Echt) :   -- DRF-SC
  ∃ w, K0 = startC c124 w st0 ∧ Laufzeit kE (speicherR kSp) (kInit w) ∧
    RennfreiC c124 LP K0 ∧
    (∀ K, ErreichbarC c124 LP K0 K → ∃ M, RufErreichbarG PR OR passes (M0 w) M ∧
       R124 w K M ∧ Ziel PR kE.S.mitRuhe OR passes (M0 w) M) ∧
    ∀ b, Echt b → ∃ K M, ErreichbarC c124 LP K0 K ∧ beobC K = b ∧
       RufErreichbarG PR OR passes (M0 w) M ∧ R124 w K M ∧ Ziel … M
```

`c124` is the emitted C as data (functions `setze`, `pruefeA`, `hauptA`, `hauptB`; `L_nimm`/
`L_gib` as the lock primitive of lock 0; the text is quoted in the file header), `PR`/`OR` are
`kP.mitRuhe`/`kO.mitRuhe`, `R124 w K M` relates memory (`corrW` under the emitter's layout
`kEL`), locks (the C holder of lock 0 is the G thread holding `L`) and every thread (C
position ↔ G residue). Read in the C memory (`schlusssatz_124_c`): on every reachable
configuration, a free lock means `konto[0] == konto[1]` (the leg `sperrInv`), and a returned
`hauptA` thread means `privA[0] == 7` (the leg `startEnde`).

### 7.4 The premises, by name

| premise | Lean | content | who supplies it |
|---|---|---|---|
| DRF-SC | `DRFSC E LP K0 Echt` (ONE proposition, a hypothesis) | if the C is race free, every observation of a real execution (`Echt`: the compiled program under the C11 model and the hardware profile) is the observation of an SC block interleaving | the C11 DRF-SC theorem with its region corollary, and the compiler's mapping of C11 synchronisation to the hardware profile; named, not proved |
| thread creation | `LaufzeitC.faeden` = `FadenStartC` | threads only at declared roots, each root at most once, from the declared initial memory, no lock held | the runtime (the boot/driver code, not emitted); the same entry as `Laufzeit` (d) and NICHTINTERFERENZ §10 |
| lock primitive | `LaufzeitC.sperre` (every `LP` step is a `sperrAbstrakt` step) | `L_nimm` only on a free lock, making the caller its holder; `L_gib` only by the holder; program memory untouched | **PROVED for the ticket lock since 2026-09-15** (`CTicket.lean`, §7.7): `ticketLP_sperrAbstrakt`. It stays a premise of the GENERIC `schlusssatz_124` (any `LP`); for the lock the runtime has, `schlusssatz_124_ticket` carries it no longer |
| lock primitive, the NI half | `sperrAbstrakt_nur_eigen` ("reveals nothing but held or free") | whether a call can proceed depends on that lock's holder entry and nothing else | **NOT true of the ticket lock** (`ticket_mehr_als_frei`, §7.7): a waiting thread sees its queue position. It is a theorem about the SPECIFICATION; the safety statement does not use it, and NICHTINTERFERENZ §10 must not read it as a statement about the implementation |
| the holder releases | not in `LaufzeitC`: a property of the EMITTED PROGRAM | every `L_gib()` call is made by the thread that holds the lock | the checker's lock discipline (the emitter writes `L_gib()` only where the holder stands). The runtime does NOT check it: `gib_ohne_wache` (§7.7) exhibits two holders after one unheld release |
| (a)-(d) of the goal theorem | `kP_akzeptiert`, `kE_nutzerPflicht`, `kO_hw`, `laufzeit_w` | the checker, the user's logic, the hardware, the G start | discharged inside: 124 has no axiom, register or device, so (c) is empty (`kO`), and (d) follows from `FadenStartC` (`laufzeit_w`) |

**The list is ONE list.** `LaufzeitC` bundles the runtime entries of PLAN §5 and
NICHTINTERFERENZ §10. That list's two scheduler entries (a fixed timetable or an
observer-only rule; a blocked slot left idle) are premises of noninterference only: every
schedule is an SC run here, and the statement holds for all of them.

### 7.5 What is proved, and why DRF-SC applies

* **Generic** (`CNebenlaeufig.lean`, for every unit and every G program): a simulation
  certificate `SimC` -- a relation, holding at the starts, such that every SC step from a
  reachable related pair is matched by a segment of G steps of the same thread that ends
  related and fits the step (`SegPasst`: every footprint object is a carrier some G step of
  the segment accesses, every written one a carrier some step writes; a G release or acquire
  lies only in the segment of the corresponding C lock call) -- lifts every C run to a G run
  (`sim_lauf`, `sim_erreichbar`); with G's `RennfreiBis` it gives `RennfreiC`
  (`rennfreiC_aus_sim`: a C conflict lifts to a G conflict inside the segments, G orders it
  through a guard lock, and the G release/acquire map back to C lock calls in the right
  order); `schluss_b` is the closing schema.
* **For 124** (`Schlusssatz124.lean`): `sim124` covers EVERY SC run from every start the
  runtime premise admits (any assignment of the two roots to threads). The G segments per C
  block: a store is one leaf (`gBlatt`); `L_nimm()` is the unfold and the take of `locks`
  (`gNimm`); `setze(n)` is call, two leaves, return and the empty rest (`gSetze`); `L_gib()`
  is the release and the empty rest (`gGib`); `(void)pruefeA()` is call and return, the return
  reading `privA` (`gPruefe`); splits and the end of a root are no G step. The C side of each
  block runs from any related state (`cStore_lauf`, `cSetze_lauf`, `cPruefe_lauf`) and, by
  `exec_det`, every run of it is that one.
* **Why DRF-SC is applicable, not merely plausible**: its hypothesis `RennfreiC` is the second
  conclusion, proved from G's race freedom (`Ziel.rennfrei`, from `rennfrei_g_voll`) through
  the footprint coverage of the certificate.

**Witness** (`schlusssatz_124_zeuge`): every premise jointly (the specified lock primitive,
thread creation at the two roots, DRF-SC with the SC observations as the real ones), the C
race free by the theorem, and a concrete 20-step SC run: thread 0 takes the lock; thread 1
reaches `L_nimm();` and CANNOT step while thread 0 holds it; thread 0 releases, thread 1 takes
the lock; both return; at the end the lock is free and the C memory shows `konto[0] ==
konto[1]` and `privA[0] == 7` -- by the theorem, read through the relation -- where `privA[0]`
was 0 at the start. **Witness of the race transfer** (`rennfreiC_zeuge_124`): the same run as an
indexed SC run of 20 steps; its two critical sections (step 10, thread 0's `setze(30);`, and
step 15, thread 1's `setze(70);`) conflict on `konto_speicher`, and the race freedom proved from
G orders them through a lock (thread 0's `L_gib();` at step 12, thread 1's `L_nimm();` at 13).

### 7.6 What is open, each step named

1. **Region serialisability (inside `DRFSC`).** Stated in the premise, not proved: for a
   race-free program, every interleaving at the granularity of single memory accesses has the
   observation of a block interleaving (`SchrittC`). Proving it needs a fine-grained C
   semantics (one step per load/store) and the commutation argument; the premise would then
   shrink to the C11 DRF-SC theorem proper.
2. **Footprint soundness in general (`FussTreu`).** For a unit `E` direct on its functions:
   every derivation `E.laeuft s st ρ o` performs its loads only at objects of
   `fussR E.Pr E.tiefe s` and its stores only at objects of `fussW E.Pr E.tiefe s`. Stating
   it needs an access-instrumented `Exec`; its key lemma, that the pointer a direct pointer
   expression computes lies in an object it names, is proved (`ev_zform_blk`). This is what
   makes `RennfreiC` (syntactic footprints) at least C11 race freedom.
3. ~~**The ticket lock refines `sperrAbstrakt`.**~~ **DONE 2026-09-15** (`CTicket.lean`,
   `Schlusssatz124Ticket.lean`; §7.7 below). What is left of it: the run-level race-freedom
   conclusion (`RennfreiC`) is carried at the granularity of `SchrittC`, not of the ticket
   lock's four instructions -- transferring it needs the stutter-free compression of a
   `LaufT` into a `LaufC`, which is index arithmetic and is not written. Reachability and the
   two C-memory legs ARE carried (`schlusssatz_124_ticket`).
4. **A checker for concurrent correspondence certificates** (T2 for stage (b)): `sim124` is
   constructed for 124; a checker that produces a `SimC` for every accepted program from a
   printed certificate does not exist.
5. **The G program from the source.** The exporter refuses 124 (`LG003`); `kP` is written by
   hand, so stage (a)'s parse fidelity (part 1 of `schlusssatz_104`) has no counterpart for
   124; and the source's `setze` contract is too weak for (b) (§7.1).
6. **The emitted text as data.** `c124` transcribes the printed C by hand (the joint A2 of
   stage (a)). The Lean C parser of §6.6 exists since 2026-09-15 and discharges A2 for the two
   stage-(a) chains; **124 is NOT among them** -- its emitted C uses the lock primitive, a
   local binding and an `if`, all outside `parseC`'s subset, and `c124` is a `CEinheit` of the
   concurrent semantics rather than a `KCert`. Closing this item means widening `parseC` by
   those forms AND a `parseC`-to-`CEinheit` bridge.
7. **Semantics extensions.** A lock call is a step only at the top of a root's continuation,
   not inside a loop, a branch or a callee; foreign calls other than the lock primitive and
   volatile accesses are outside the direct fragment; a root whose block never ends (a
   `forever` loop) has no step, so the statement says nothing about it. **Atomics**: a
   top-level atomic statement is its own SC step (a block of one `Exec` rule), but an atomic
   access is neither exempt from `RennfreiC` (it counts like a plain access: conservative) nor
   a source of ordering (`GeordnetC` orders through locks only), and `SegPasst` cannot cover
   an `atomic` carrier -- the release/acquire ordering of `publish`/`awaits` (A10) is the next
   extension, and until then a program whose threads meet only through atomics is outside
   what stage (b) certifies.

**The chain count stays 1.** 124 closes stage (b), but it does not pass columns (a) (Lean
parse), (b) (`lean-g`) and (e) (a printed, Lean-checked correspondence certificate) of
`instrumente/zaehle-kette.py`; the count is about closed chains, and this one is closed by
hand-written model and C data at those two ends.

### 7.7 The lock primitive stops being a premise (2026-09-15)

*Files: `grammatik/Grammatik/CTicket.lean` (the lock, generic),
`grammatik/Grammatik/Schlusssatz124Ticket.lean` (124 with the lock inlined, and the contended
witness). Axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound` or less; no
`sorry`, no `native_decide`, no new `axiom`.*

**Which step was the smaller one, measured.** Two routes were open: write the ticket lock in
the interleaved C semantics, or bridge to the ticket lock already in the tree
(`Lebendigkeit.lean`, `FifoSperre`). The second is NOT the smaller step, and the measurement
says why: `FifoSperre` is a predicate over INFINITE scheduled runs of machine G
(`PlanLauf`, `AnSperre`, `offen …spur`) -- it shares **no** definition with the vocabulary of
stage (b) (`Halter`, `SperrOp`, `SperrSem`, `KonfC`), it constrains the ORDER of acquisitions
and not their SAFETY, and it is an assumption rather than an implementation: it never names
the two counters. Bridging would have meant a G-to-C lock-order correspondence on top of
writing the counters anyway. The lock is therefore written where the premise stands, in the C
semantics -- 4 rules, one per instruction the implementation has -- and the FIFO property of
`Lebendigkeit` comes out as a THEOREM of it in local form (`ticket_fifo`: while an earlier
ticket is outstanding, a later one cannot be served).

**The implementation, as the trust base supplies it** (the emitter writes only the two
prototypes, `emit.rs` `ItemArt::Lock`): two `_Atomic unsigned` per lock; `L_nimm` is
`my = fetch_add(&next, 1)` then a spin on `load(&now) != my`; `L_gib` is
`store(&now, now + 1)`. Four instructions, four rules (`TSchritt`): `zieht`, `dreht` (a spin
load that finds `now != my`, changing nothing), `tritt` (the spin load that finds `now == my`:
the acquire completes), `gibt`.

**What is proved.** `TInv` (the counters never cross; drawn tickets are distinct and lie in
`[now, next)`; while somebody is inside `L`, every drawn ticket is strictly above `now`)
survives every instruction (`tinv_schritt`) and holds at the start (`zStart_inv`); from it,
**mutual exclusion** (`ticket_ausschluss`, `erreichbarT_exklusiv`), **non-reentrancy**
(`ticket_nicht_wiedereintritt`), **FIFO** (`ticket_fifo`) and **the refinement**
(`ticketLP_sperrAbstrakt`: every abstract step the lock induces is a `sperrAbstrakt` step --
the clause `LaufzeitC.sperre`, now a theorem). `SchrittT` runs the emitted C with the lock
inlined; `schrittT_proj` projects every step onto a stutter or a step of
`SchrittC E sperrAbstrakt`, and `erreichbarT_erreichbarC` carries that to every reachable
configuration. For 124: `schlusssatz_124_ticket` -- mutual exclusion, `konto[0] == konto[1]`
while nobody is inside, `privA[0] == 7` after `hauptA` returns -- **with no premise about the
lock**.

**The theorem got stronger, and here is exactly how.** `schlusssatz_124` is UNCHANGED (it
quantifies over every `LP` and carries `LaufzeitC`); nothing was removed from it.
`schlusssatz_124_ticket` is its instance at the lock the runtime has, and the premise text
that is gone there is, word for word,
`sperre : ∀ t op h h', LP t op h h' → sperrAbstrakt t op h h'`. What REMAINS a premise:
`FadenStartC` (thread creation at the declared roots), the `forever` budget, and -- for a
statement about the real machine rather than the SC semantics -- `DRFSC`.

**Two findings, witnessed.**
1. **The ticket lock reveals MORE than held or free** (`ticket_mehr_als_frei`). Two concrete
   states with the same abstract holder table (the lock free in both) and one thread whose
   acquire completes in one and cannot complete in the other, because another thread drew the
   earlier ticket. `sperrAbstrakt_nur_eigen` is a theorem about the specification and does not
   transfer. Harmless for the SAFETY statement -- the implementation has FEWER runs, which is
   the direction the refinement needs -- but the NI-facing entry of NICHTINTERFERENZ §10 may
   not be read as a statement about the implementation: a waiting thread can measure its
   position in the queue, and that is the arrival order of the other threads.
2. **The release performs no check** (`gib_ohne_wache`). `L_gib` increments `now` for whoever
   calls it. The guard of the rule `gibt` is the CALLER's position between its `L_nimm` and its
   `L_gib` -- a guarantee of the checker's lock discipline, not of the runtime. One unheld
   release while a holder is inside lets the next ticket in: two holders, invariant gone. So
   the `.gib` half of the refinement is discharged only for well-nested callers. The runtime
   could carry it alone by keeping the holder's identity in the lock and comparing on release
   (one more word, one more branch per release) -- which is exactly the check W6 declines to
   emit because the checker already decided it.

**The witness** (`ticket_zeuge_124`, non-degenerate, contending): a 23-step run of the emitted
C with the lock inlined. Thread 1 draws ticket 0, thread 0 ticket 1; at that configuration the
lock is FREE (`halter 0 = none`, nobody inside) and **thread 0 still cannot take it** -- every
step it can make leaves its C configuration where it was (`spinnt_nur`) -- while
`sperrAbstrakt` would admit its acquire (exhibited in the same statement). Thread 1 enters
(step 11), thread 0 spins on, thread 1 runs `setze(70)` and releases, and only then does
thread 0 enter (step 15): the acquisitions are in TICKET order, not in arrival-at-the-spin
order. Both return; at the end nobody is inside the lock, `konto[0] == konto[1]` and
`privA[0] == 7` -- both **by the theorem**, read through the relation, where `privA[0]` was 0
at the start.

**Cost, measured on `ki-pc-fisch-101` (`gabbro-opus-tick`):** full `lake build` 251 jobs green;
the two new files build in well under a second together (0,39 s and 0,28 s), so the library's
build cost is unchanged.
