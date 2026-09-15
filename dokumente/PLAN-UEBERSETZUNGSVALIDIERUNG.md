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
  not discharge it.
- **The hardware profile.** `Profil.lean`, keyed entries.
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

## 6. Chain count: 1 -- beispiele/104, theorem schlusssatz_104

*Added 2026-09-14. File: `grammatik/Grammatik/Schlusssatz104.lean`. Stage (a) of §3 item 2,
for one program. Axioms of every theorem named here: `propext`, `Classical.choice`,
`Quot.sound`; no `sorry`, no `native_decide`, no new `axiom`.*

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
simulation G-run ↔ interleaved C-run. (Done for `beispiele/124` on 2026-09-15, §7.) For 104 itself `gP_kein_exklusiv` already says two
active threads are refused by the model (every function holds `M` by signature).

**For widening beyond 104** (the chain count's next steps), every piece keyed to `gD`
must become generic: the lowering (`lowerProg`, lane 162), the correspondence certificate
(`certOkG` fixes 104's rows; a row-list checker over all printed forms is T2 proper), the
body printer `printEnd104` (104's shapes), the idle root (either the exporter emits one, or
`gDB` becomes a generic declaration extension with a generic renaming), and the per-program
computations `rufEin_ok`/`rufLies_ok`, which stand in for a general theorem "the
per-function obligations imply `rufAt` ends `ok`".

## 7. Stage (b), the concurrent closing theorem -- beispiele/124, theorem schlusssatz_124

*Added 2026-09-15. Files: `grammatik/Grammatik/CNebenlaeufig.lean` (generic: semantics,
premises, transfer theorems), `Korpus124.lean` (the G program of 124 and the goal theorem on
it), `Schlusssatz124.lean` (the emitted C, the simulation, the theorem, the witness). Axioms of
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
| lock primitive | `LaufzeitC.sperre` (every `LP` step is a `sperrAbstrakt` step) | `L_nimm` only on a free lock, making the caller its holder; `L_gib` only by the holder; program memory untouched; reveals nothing but held or free (`sperrAbstrakt_rahmen`, `sperrAbstrakt_nur_eigen`) | the runtime's ticket lock; the same entry as NICHTINTERFERENZ §10 |
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
was 0 at the start.

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
3. **The ticket lock refines `sperrAbstrakt`.** `LaufzeitC.sperre` is a premise; a proof
   would give the runtime's `L_nimm`/`L_gib` as C with atomics and show that their
   fine-grained runs project to `sperrAbstrakt` steps.
4. **A checker for concurrent correspondence certificates** (T2 for stage (b)): `sim124` is
   constructed for 124; a checker that produces a `SimC` for every accepted program from a
   printed certificate does not exist.
5. **The G program from the source.** The exporter refuses 124 (`LG003`); `kP` is written by
   hand, so stage (a)'s parse fidelity (part 1 of `schlusssatz_104`) has no counterpart for
   124; and the source's `setze` contract is too weak for (b) (§7.1).
6. **The emitted text as data.** `c124` transcribes the printed C by hand (the joint A2 of
   stage (a); a Lean C parser would replace it).
7. **Semantics extensions.** A lock call is a step only at the top of a root's continuation,
   not inside a loop, a branch or a callee; foreign calls other than the lock primitive,
   volatile and atomic accesses are outside the direct fragment; a root whose block never
   ends (a `forever` loop) has no step, so the statement says nothing about it.

**The chain count stays 1.** 124 closes stage (b), but it does not pass columns (a) (Lean
parse), (b) (`lean-g`) and (e) (a printed, Lean-checked correspondence certificate) of
`instrumente/zaehle-kette.py`; the count is about closed chains, and this one is closed by
hand-written model and C data at those two ends.
