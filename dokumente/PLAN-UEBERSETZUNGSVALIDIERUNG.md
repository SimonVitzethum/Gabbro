# Translation validation: from source to the final binary

*Rewritten 2026-10-17. It absorbs `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` (the derivation plan, now §9) and
`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` (the optimiser specification, now §8), and compresses the dated
C-backend proof record of §§6–7. Section numbers 0–7 are the ones code comments cite; see §10
for the renames.*

## Status in one paragraph

**Nothing of the final-byte chain exists.** No hardware model is complete, no validator for a
loaded binary exists, no producer is trusted. What exists is: the goal theorem over the model
(`gabbro_ziel`), model certificates per program (`gabbro obligations --g`), the GabbroV bridge
for the user's logic, a closed **legacy chain for the C backend** (two programs, §6–§7, retained
as historical evidence and regression), proved generator templates (`gabbro templates`: 41 entries,
**30 proved**, 8 designed, 3 carried), a certificate printer for the LLVM backend that currently
does not elaborate in Lean (§9), and a written optimiser specification with no code (§8).
Backend truth (2026-10-17): the **LLVM backend is current** (untrusted, `LLVM-BACKEND.md`); the C11
emitter is deprecated (decided 2026-10-07, `ARM-PLAN.md`); the x86-64 hardware model was stopped
and **archived** on 2026-10-10 (git branch `archive`, commit `7c693cb7`); the selected target is
**AArch64 (Armv9-A) on the Sail Arm model** with the multicore memory model added in Lean
(`PLAN-HARDWARE.md` §2.3, `ARM-PLAN.md`). `TODO.md` §5 states it: validation comes **much later**,
behind a complete CPU model, and must then run automatically for **all** programs.

---

## 0. What is proved at the end

```
source text -- Lean parser/elaborator --> model program P and obligations
     |                                      |
     +-- untrusted Rust backend --> final binary image + certificate
                                            |
                              Lean decoding and validation
                                            |
                       generic refinement theorem to P / GX
                                            |
                              existing goal theorem
```

For EVERY source text and final image the validator accepts, one generic Lean theorem must give:
parse fidelity, the model judgement, and correspondence of every admitted machine execution to
the model. User-logic duties are computed in Lean from the source and discharged through the
GabbroV bridge. **No function name, example number or per-program model may decide acceptance;**
per-program proof instances are witnesses, not the trust path.

The input is the *actual executable bytes*, data layout, entries and resolved relocations. A
proof about an instruction listing is insufficient; the loaded mapping must equal the validated
image, including relocation at load time, and entry state and later control transfers must meet
the validated calling and memory conventions. Unvalidated external code cannot enter a finished
chain through a declaration alone.

The Rust compiler, optimiser, register allocator and encoder stay **untrusted**: their output may
carry hints and certificates, Lean reconstructs or checks every obligation through a proved
checker, and wrong output is refused. This is a target, not a property of today's compiler. No C
compiler, LLVM pass, assembler or linker correctness belongs to the chain: whatever forms the
image has its final output checked.

## 1. Components and present status

| Piece | Task | Present status (2026-10-17) |
|---|---|---|
| **T3** | Lean source parser and elaborator compute `P`, layouts and duties | `grammatik/Grammatik/Parser/` (lexer, expressions, statements, `Uebersetze`) and the GabbroV front end (`GvParserFragment*`, `bruecke/Bruecke/Quelle.lean`). Sieve (a) was 5 of 148 programs on 2026-09-30 (tag `milestone-2026-09-30-parser-generic-chain5`); narrow fragment, **binding sieve** of the chain count |
| **T1** | Generic soundness of the certificate: typing, safety, goal premises | model certificates per constructor (`Korrespondenz/Zeugnis/`), `target/zertifikate/REGISTER.txt` (generated on demand) (**34 CERTIFIED / 211 UNCERTIFIED** lines, 2026-10-17). An accepted program outside both lists or a stale row turns `cargo test` red (`tests/zertifikate.rs`) |
| **T4** | Target instruction semantics, byte decoder, byte-addressed memory, per-access memory model | **AArch64: in construction** (`arm/`, `PLAN-HARDWARE.md` §2.3, ~5 900 Lean lines; no decoder, no Sail bridge, no branches/FP, memory model not assembled). x86-64: archived |
| **T2** | Sound validator from the final image to `P`/GX | none for a binary. Legacy: `korrOk` (decides a C certificate statement by statement, §6.2) |
| **T5** | Generic runtime, entry, lock, call and hardware templates bound to the target semantics | `gabbro templates`: 41 entries, 30 proved against **C or abstract machine** semantics (`Bausteine/Schablonen/*`, `CTicket.lean`, `SyscallArm*.lean` mirrors the AArch64 Linux call ABI as data); machine-code correspondence open |

`CSpeicher`, `CSemantik`, `CParse`, `korrOk` and `CNebenlaeufig` describe the C backend. Their
closed chains do **not** establish correspondence for any binary. Changing the target does not
make an uncovered construct verified.

## 2. Machine profile and instruction selection

Target-neutral design, first target AArch64. Use a deliberately bounded 64-bit profile; model the
architecture (Armv9-A), not one implementation: whatever the manual calls IMPLEMENTATION DEFINED
or UNPREDICTABLE stays **free** (all allowed results, never one observed value); implemented
`FEAT_*` extensions are a named profile as data, and generated code may use only instructions in
the chosen profile. Unsupported encodings are refused. Variable-length decoding is part of the
proof work on x86; AArch64's fixed 32-bit encoding removes it but not the decode proofs.

Select coverage from ALL source operations and backend emission paths, including runtime and
hardware forms, never from instructions found in example binaries. Families to justify one by
one: data and addresses (moves, extensions, address calculation: widths, layout, bounds);
integers (add/sub, multiply/divide, logic, shifts, carry: overflow, division, stop behaviour);
control (compare, conditional select/branch, call/return: flags, entry targets, stack, ABI);
atomics (LSE and exclusive pairs, acquire/release, barriers: each source ordering and retry
loop); floating point (scalar, bind rounding, exceptions, NaN and control state to the kernel IEEE
model); hardware and entries (only forms the source inventory needs; wrappers and named hardware
behaviour); optional SIMD/profile extensions only with their own availability and correspondence
proofs. There is no claim that the fewest instructions give maximum speed.

Instruction selection does not change the memory ceilings or termination policies; the planned
opt-in unbounded region concerns Turing completeness in the abstract model, not a weaker guarantee.

## 3. Concurrency: reuse Gabbro's model, prove the hardware bridge

**Reuse W / GX / thread machine and `gabbro_ziel`** (`Speichermodell/Maschine/{Sicht,MaschineW,
GXMaschine}.lean`, `Speichermodell/Atomar/AtomarW.lean`, `Zielsatz/Kern/Spec.lean`: `SchwachX`,
`ZielX`, `GabbroZiel`; proof `Zielsatz/Atomar/BeweisAtomar.lean`). Existing race freedom,
contract, lock, lifecycle and progress proofs are the source-side foundation, not a second
concurrency language. The abstract ticket-lock results in `CBackend/Semantik/CTicket.lean` may be
reused; the concrete instruction sequence needs its own proof.

**The missing theorem goes from machine behaviour to allowed model behaviour**: a relation from
per-access executions of the validated image (AArch64: the axiomatic model of `arm/`) to W and
then GX, or directly to GX with every required goal property preserved. Do not assume W is
already a proved model of any hardware; equality of execution sets is not needed, covering is.
The bridge must account for: byte-addressed memory, layout, widths, overlap, alignment, tearing
and the profile's atomicity (private stack and spill slots cannot create races); store buffers or
the Arm ordering relations, forwarding, coherence, acquire/release and exclusives/LSE (successful
and failed compare-exchange differ; W's `seq_cst` = release/acquire is an abstraction with
stated limits); every ordinary and atomic access and its footprint (a block or sequence is not
indivisible just because it is one model operation: grouping needs a commutation proof);
locks, retry loops, start/join, publication, interrupts and call boundaries; finite and infinite
executions (stuttering only under a progress argument; a spinning implementation cannot vanish in
projection); declared costs against validated machine costs and named hardware bounds
(instruction counts are not time bounds). MMIO, DMA and cache attributes need their own named
hardware semantics. An OS, scheduler or runtime routine is user/binding logic whose code and
contract must be covered, not a new hardware assumption.

The old C theorem's `DRFSC` and `LaufzeitC` premises stay properties of that theorem and do not
discharge the bridge. The memory design must not wait until a sequential instruction model is done.

## 4. Order, gates and measurement

1. **Freeze the semantic scope** from source and emitter paths (every reachable operation,
   lowering, width, order, entries, runtime helpers). Examples are witnesses, never the definition.
2. **Define the machine and memory relation first**: decoding, byte memory, per-access ordering,
   ownership/layout, frames, entries, relation to W/GX; review against the real architecture text.
3. **Generic pilot through actual bytes**: integer data, memory, control, calls, with a rejection
   witness for altered bytes. All lemmas quantify over arbitrary supported programs and layouts.
4. **Close concurrent mappings early**: ordinary access, atomic order and locks against W/GX with
   forbidden-outcome probes; never assume blocks execute atomically.
5. **Extend by semantic families** (floating point, dynamic regions, hardware access, entries,
   linking, optional profiles), each with target semantics, validator soundness and template
   correspondence before admission.
6. **Close the generic final-image theorem**: source fidelity, duties, all executed code,
   layout and relocations, calling conventions, concurrent refinement, cost transfer; review
   finite and infinite executions; state every remaining hardware premise.

Prove register allocation, spills and optimisations through checked correspondence certificates,
not by trusting the Rust passes or building a second model of the source language: **the typed
source (`Syntax`/`Semantik`) plus checked target blocks is the reference; no persistent SSA IR,
no second interpreter** (decision of lanes 594/606, 2026-10-01; §8). Measurement: report semantic
families and generic theorems plus final-byte chains the proved validator accepted. Corpus chain
counts are coverage diagnostics. The retired `zaehle-kette` (2026-10-17; not guarded today) measured **C chains** and must not
be relabelled a binary validator. An effort estimate needs a measured generic pilot (decoding, a
memory access, an atomic/lock mapping, final-image binding); instruction count alone misses
layout, flags, allocation, concurrency, floats and progress.

## 5. Trust and preservation

Intended logical trust base: the Lean kernel and its standard axioms (`propext`,
`Classical.choice`, `Quot.sound`), the reviewed source/machine/decoder definitions, and explicitly
named hardware behaviour (including execution of the validated bytes and required timing bounds).
Definition adequacy needs human review: the kernel accepts a theorem about the definitions, not a
claim that they match silicon. A Lean port of Sail text is self-consistency with the Sail text.

OS services, thread start-up, locks, runtime code and foreign bindings remain user logic with
checked contracts and implementation correspondence. Unsupported features stay refused by
validation; source acceptance or a model certificate is not final-image acceptance. Preserve
memory safety, race freedom, contracts, lock discipline, costs and every claimed goal leg; no
`sorry`, `admit`, `native_decide` or new axiom; a reviewed `Spec.lean` diff if the goal statement
moves (the target switch alone does not move it).

**Proved templates** (T5, `gabbro templates`; tooth 1: no entry without a measured need, tooth 2:
a seat per proved template, tooth 3: every proved template binds its premises to a pass): the
generator-written pieces (`tor.nie`, `tor.fehlbar`, `tor.region`, `tor.trampolin`, `tor.kind`,
`start.nolibc`, `arena.dyn`, `sperre.ticket`, `region.leeren`, `faden.laufzeit`, the module and
bare-metal families `arena.modul`, `modul.lebenslauf`, `faden.modul`, `metall.*`) have Lean files
in `grammatik/Grammatik/Bausteine/Schablonen/`. They are proved against the **C** semantics or an
abstract machine; moving them to machine bytes is the T5 work still open.

---

**Historical C-backend validation record (§§6–7).** Dated statements, measurements, assumptions
and open C tasks, kept for audit and reuse. They are superseded as a work order by §§0–5; none is
evidence of a binary chain.

## 6. Stage (a): the generic C chain (`schlusssatz`), beispiele/104 and 108

*Added 2026-09-15; the stage names "(a)" (single-threaded, §6) and "(b)" (concurrent, §7) are the
ones cited from Lean headers as "§3 item 2" and "§3 item 4" of the earlier plan version.* Files:
`grammatik/Grammatik/Korrespondenz/Allgemein/KorrespondenzAllg.lean` (T2 proper),
`Korrespondenz/Kette/Schlusssatz.lean` (the theorem), `Kette104*.lean`, `Kette108.lean`,
`SchlusssatzZeuge.lean`. Axioms of every named theorem: the standard three.

### 6.1 The statement

A **closed chain** for `src` is `K : Kette src`: the generic Lean pipeline `uebersetzeAllg`
(lex, parse, preprocessing, elaborate, `lowerAllg`) produces the code; `E : Einheit (declOf u)` is
the program as the goal theorem's unit; `akzeptiert_pruefer.akzeptiert E … = true` (premise (a));
`NutzerPflicht E` (premise (b)); and `korrOk EL fnNr zert E.P fs = true` for the emitter's layout
and correspondence certificate (T2). `schlusssatz (K : Kette src) O hH orc XR hXR bin tief hA1 sp
init hA4` takes the named world hypotheses (hardware `HardwareAnnahmen`, deterministic foreign
calls `XR.Funktional`, `hA1`: every run of the binary's `f` is a run of the C semantics of the
certified unit, `hA4`: single-threaded start) and concludes: **(1)** parse fidelity, **(2)** the
checker Bool and the certificate check, **(3)** the model judgement, **(4)** every C run ends
related to the Gabbro outcome (`korrOk_jeder_lauf`), **(5)** the machine (`K.E.P.mitRuhe`,
every leg of `Ziel` via `gabbro_ziel`), **(6)** every run of the binary, under `hA1`.

### 6.2 T2 proper: `korrOk`

One decidable check for every program: it walks every body with its printed rows and decides,
statement by statement, that the row is the emitted form of the statement. Sound at every call
depth (`korrOk_fnCorr`, induction through `cCorr_ruf`); each row is one existing T4 lemma.
Widened 2026-09-15 from 6 to 27 of 42 `Expr` constructors and from 4 to 5 of 27 `Stmt`
constructors, every arm with a positive probe and a **planted defect**. Seen failing
(`korrOk_faellt`): wrong field offset, wrong stored value, a missing call row. The printer for the C
correlation (`gabbro corr-lean`) is removed with the C emitter (2026-10-17).

### 6.3 The chain count and where programs stop

Closed chains (instances marked `CHAIN-INSTANCE` in Lean): `beispiele/104-referenz.gab`
(`kette_104`, real text with comments, witness `kette_104_zeuge`) and
`beispiele/108-disjoint-start-locks.gab` (`kette_108`, two declared concurrent starts). Three more
are marked `CHAIN-GENERIC` in `bruecke/Bruecke/Instanzen/` (69, 73, 130; generic `ketteAllg`).
Counts are **diagnostics**: 2 of 129 on 2026-09-26; the retired `zaehle-kette` without `--lean` on
2026-10-17 read "0 of 170 closed (Lean not re-run)" with sieve totals (b) 28, (c) 16, (d) 66 —
**a Lean-run measurement was not repeated for this document.** The sieves, in order: (a) Lean
parse and elaboration of the generic pipeline (the binding one), (b) `lean-g` export, (c)
`gabbro certificate` prints every body, (d) every emitted C form is in state *lemma* or *named
assumption* (the retired `pruefe-cformen`), (e) the generic correspondence certificate prints without
`KREFUSAL`. **Coverage is multiplicative in the sieves and inside sieve (b):** a lane probe that
skipped the two largest first-refusal groups found every one of the 24 programs stopped at a
second wall, so closing a group completely can move the count by zero. First refusals are not
programs gained.

*A guardian finding that moved a number the right way:* the retired `pruefe-cformen` keyed rows by statement
text, so `return c.len;` and `return (Nachricht){…};` were one row, covered by a scalar lemma that
says nothing about a struct (`CTy` is `int | ptr`). Re-keyed by destination, sieve (d) fell from
60 to 55 and the uncovered forms rose by four — *a number that falls because the instrument
started to see is not a regression; the 60 was.* Carrying aggregates in the C model would have
unblocked zero programs.

### 6.4 The by-hand theorem of one program: `schlusssatz_104`

Kept in `Korrespondenz/Kette/Schlusssatz104.lean` (2026-09-14), restated with the named
assumptions as hypotheses: parse fidelity by lex/parse/elaborate/lower equations; the model
certificates are the print of `gP`'s bodies; the model judgement at every `forever` budget; every
C run of `einzahlen`/`lies` ends related to the Gabbro result; the machine `gPB` (`gP` plus the
runtime's idle root, related by a kernel-checked renaming) satisfies the goal conclusion for every
`LaufzeitStart` start. **Finding:** no G theorem applies to a machine of `gP` alone, since G starts
every thread in some function and both functions hold `M` by signature, so there is no idle root
(`gP_kein_exklusiv`, `gP_kein_ruhig`): the idle root is runtime data (`gDB`/`gPB`, assumption A4).
What stays outside Lean: A1 (the binary *is* the compiled behaviour), A2 (the emitted text means
`refCProg`; **discharged for the generic chain by `parseC`, §6.6**), A3 (layout pins; reduces to
A1+A2 plus one lemma), A4 (the runtime starts in a `LaufzeitStart` shape), A5 (kernel and
definitions). No hardware or oracle premise for 104 (no axiom, register, device, global or `awaits`).

### 6.5 What stays open (generic theorem)

- **Sieve (a) binds.** Widening `korrOk` does not move the count while the Lean parser and
  elaborator (T3) stop most programs; measured: 23 arms added, count unchanged.
- **`korrOk` still refuses** a `traverse` with a non-literal bound, `!=`, a `(T)(e)` wrapper and
  `_Atomic` globals (each with a proved lemma but no row), floats (no `ecorr_*`, no float operand).
- **The arena stops at the exporter**, no longer at the specification: `alloc`/`reset` are sugar
  over `Block.narrow` + `Stmt.assignSlot` + `Stmt.assignGlob` (`Bausteine/Arena/ArenaZucker.lean`),
  the exporter builds the pair; `beispiele/98`/`99` stop at two statement *shapes* (an `alloc`
  without `else`; an `alloc` at the top level of a body).
- **The unit's data** (lock invariants, axiom ensures, declared starts, initial memory) are written
  next to the source by the chain's author; **the user's logic is per program** (that is the goal's
  intent, not a gap).
- **Part 4's condition** (the Gabbro call ends in no model error) was halved twice, see §6.8, §6.9,
  §6.12: the hardware class is gone provably; what is left is the `abstieg` residue, a computation
  at one depth.
- **The adequacy chain** (one active thread of G against `rufAt`) is not re-instantiated; four things
  stand between part 4 and part 5 (the fragment is not one of them): `rufG_adaequat_ruf` realises
  `rufRumpf` not `rufAt` (the traces differ, `befund_vertrag`), `Tief P A n` carries the depth
  residue, and the adequacy is existential. The congruence lemma of §6.9 does not close it.

### 6.6 A2 discharged: the emitted text is parsed in Lean

`CBackend/Parser/{CLexer,CParse,CProben,Bruecke}.lean`, `CBackend/Semantik/CText104*.lean`,
`CText108.lean`; guardian: the retired `pruefe-ctext` (not guarded today). `parseC : List Char → Option (List CFun)`
reads the emitted subset (prelude with two `_Static_assert` pins, integer `#define`s, table
structs, `static` declarations, `(void)x;`, slot stores, direct calls, `return` over literals,
locals and slot reads) and `a2_104 : parseC ctext104 = some (kFuns zert104)` holds by kernel
reduction, `ctext104` byte-identical to `gabbro emit`. From it `cProgC ctext = kProg zert` and
`schlusssatz_text`. Measured over the corpus then: 4 of 113 programs inside the subset. **Cost
lesson (OFFEN O13, closed):** kernel-reducing a `String` literal went through the array
representation (33.7 GB for the first character of a 1 419-byte literal); the same text as a
`List Char` of short pieces costs 3.3 GB; the dominant Gabbro-side cost was one theorem unfolding
`uebersetzeAllg` at a concrete source (`uebersetzeAllg_von_zeichen` unfolds it once, at a variable).
The whole library then built from empty in 5 min 20 s at 6.86 GB peak (2026-09-15).

### 6.7 The certificate's block structure

`stOk` and `blOk` form one `mutual` over `GRow`/`List GRow` (structural, no fuel: *a mutual
recursion through a fuel argument compiles to a mutual `Nat.brecOn` and is exponential*); arms for
`if` (`scorr_ite`), `let x = f(…)` (`bsem_bindCall`) and `traverse` (`scorr_traverse`, with a
literal bound equal to the table count, fresh `x`, body not writing `x`). `stOk` 5 → 7 of 27
`Stmt` constructors; `blOk` reads 4 of 17 `Block` constructors.

### 6.8 Part 4's hardware class is provably empty

`korrOk` refuses the five forms whose outcome is `hardware` (axiom call/bind, register read,
`awaits`, `forever`), so `rufAt` never ends in one (`korrOk_rufAt_ohneHardware`, conclusion 4b);
`Hardware.ieee` is no longer produced. **Finding with a witness (`befund_hardware_bleibt`):**
premise (c) `HardwareAnnahmen` does *not* rule the hardware error out — `AxVertragO` constrains the
oracle only where the raw answer fits the declared type, and an oracle with an out-of-range raw
answer meets every premise vacuously while `rufAt` stops at every depth and budget.

### 6.9 The handler congruence

If two handlers answer at every key either the same outcome or, on the first side, an error whose
mark lies in a set `Er`, then every statement, block and terminal block runs the same under both
or errors with a mark in `Er` (`Logik/Vertraege/HandlerKongruenz.lean`, one-sided on purpose so
depth monotonicity has a premise). Consequences: `abstieg` is stable upward (`rufAt_stabil_ab`,
`Logik/Ruf/RufTiefe.lean`), and `vorbedingung` of a callee, `nachbedingung`, `invariante`,
`schleife`, `vorzustand`, `bereich` are discharged by `KoerperGutS`/`InvGutS`. It does **not**
close the `rufAt` ↔ machine G item: those differ in the *world* the body runs from (contract
reads), not in a handler's answers.

### 6.10 A device chain

`korrOk` carries three of the five hardware forms (`Stmt.regWrite`, `Block.regRead`,
`Block.regReadElse`): *if the profile holds and the register answers inside its declared type,
every run of the emitted C corresponds* — nothing about the device is claimed. The `requires …
else` channel is the interesting one: a broken device promise becomes a **branch**, so
`Hardware.geraet` cannot arise from it. `korrOk` gained a last parameter `GT : GerTafel D`
(default: the empty table, under which every device row is refused, so the two closed chains
call it unchanged). The premise "the window is mapped" cannot be an assumption of the profile (as
an assumption it is false whenever there is a register); it moved into `EmitLay.devs` and
`corrW`'s third clause (17 of 300 `corrW` occurrences changed). Price: `korrOk_rufAt_ohneHardware`
now carries `GT.ein = false`. Witness `KorrespondenzGeraetZeuge.lean` carries all three forms and
refuses seven planted defects. Corpus: 25 of 113 programs carry one of the five forms; none passed
sieve (a).

### 6.11 Sieve (d) was 60 because the guardian could not see a C type

See §6.3: re-keyed by destination (return slot, fresh local, memory, parameter), 60 → 55.

### 6.12 The frame at every world

`Logik/Vertraege/RahmenTreu.lean`: `Treu W G σ σ' = Rahmen ∧ σ'.haelt = σ.haelt` is proved over the
whole grammar with the third fact of `Gut` (events good, trace consistent — the only part needing
`HeldB`) deleted from the *conclusion*. So the frame holds at **every** world (route "find a
counterexample" was false; `List.erase` removes the first occurrence, the one `nimmt` just put
there). `schlusssatz` clause 4e(ii) lost its hypothesis; of part 4's condition only the depth
residue of 4e(i) remains. Witness on a locked program: `nurAbstieg_zeuge_104`.

## 7. Stage (b): the concurrent C theorem, beispiele/124

*2026-09-15.* Files: `CBackend/Semantik/CNebenlaeufig.lean` (generic), `Korrespondenz/Korpus/Korpus124.lean`,
`Korrespondenz/Kette/Schlusssatz124.lean`, `CBackend/Semantik/CTicket.lean`,
`Korrespondenz/Kette/Schlusssatz124Ticket.lean`.

**7.1 Program.** Six corpus programs start more than one thread (07, 59, 108, 109, 124, 125). 124 is
the smallest with two threads and a lock that has a G form. The exporter refused it (`LG003`, the
`requires` of `setze`), so `kP` is hand-written from the source bodies; the source's `setze`
contract is too weak for premise (b) as written (the release check fails for a callee answer the
contract admits), so `kP` keeps the stronger model contract.

**7.2 Semantics.** A configuration `KonfC` is the shared C state, one thread state per `Faden`,
and the holder of each lock. A step `SchrittC` is taken by one freely chosen thread: split, leave
the root body, call the lock primitive, or run one **synchronisation-free statement as a block**
with the existing big-step semantics. Every schedule is a run, so it is sequentially consistent;
blocks between synchronisation points are justified by DRF-SC and its region corollary (Adve–Hill
1990, Boehm–Adve 2008, Batty et al. 2011). Footprints `fussR`/`fussW` name objects to call depth;
`RennfreiC` demands conflicting steps of different threads be ordered through a lock.

**7.3 Statement.** `schlusssatz_124` concludes: the start is `startC`, `Laufzeit` holds, `RennfreiC`,
every reachable C configuration is related (`R124`) to a G machine with `Ziel`, and every
observation of a real execution is that of a block interleaving. In the C memory: a free lock
means `konto[0] == konto[1]` and a returned `hauptA` means `privA[0] == 7`.

**7.4 Premises by name.** DRF-SC (`DRFSC E LP K0 Echt`, one proposition: the C11 DRF-SC theorem plus
the compiler's mapping of C11 synchronisation to the hardware profile — named, not proved); thread
creation (`FadenStartC`, the runtime); the lock primitive (`LaufzeitC.sperre`, **proved for the
ticket lock** since §7.7, still a premise of the generic theorem); the holder releases (a property
of the emitted program, the checker's lock discipline — the runtime does not check it,
`gib_ohne_wache`); (a)–(d) of the goal theorem discharged inside (124 has no axiom, register or
device).

**7.5 What is proved.** Generic: a simulation certificate `SimC` lifts every C run to a G run
(`sim_lauf`), with G's race freedom it gives `RennfreiC` (`rennfreiC_aus_sim`). For 124: `sim124`
covers every SC run from every start the runtime premise admits; a 20-step witness shows thread 1
blocked while thread 0 holds the lock, the race freedom order through the lock, and the final
memory facts by the theorem.

**7.6 Open, each step named.** (1) Region serialisability inside `DRFSC` needs a fine-grained C
semantics and the commutation argument. (2) Footprint soundness in general (`FussTreu`) needs an
access-instrumented `Exec`. (3) The run-level race-freedom conclusion at the granularity of the
ticket lock's four instructions needs the stutter-free compression of a `LaufT` into a `LaufC`
(index arithmetic, not written). (4) A **checker** for concurrent correspondence certificates
(T2 for stage (b)); `sim124` is built by hand. (5) The G program from the source (parse fidelity
has no counterpart for 124). (6) The emitted text as data: `c124` is hand-transcribed; 124 is not
in `parseC`'s subset. (7) Semantics extensions: a lock call is a step only at the top of a root's
continuation; foreign calls and volatile accesses are outside the direct fragment; a `forever` root
has no step; atomics are neither exempt from `RennfreiC` nor a source of ordering.

**7.7 The lock stops being a premise.** Two routes: bridge to `FifoSperre` in `Lebendigkeit.lean`
(a predicate over infinite scheduled runs sharing no vocabulary with stage (b); not the smaller
step) or write the ticket lock in the C semantics (four rules `zieht`, `dreht`, `tritt`, `gibt`:
`fetch_add(&next, 1)`, spin on `load(&now) != my`, `store(&now, now + 1)`). The second was chosen.
Proved: `TInv` survives every instruction, mutual exclusion, non-reentrancy, FIFO (`ticket_fifo`)
and the refinement `ticketLP_sperrAbstrakt`; `schlusssatz_124_ticket` carries no lock premise. **Two
findings, each with a witness:** the ticket lock reveals more than held-or-free
(`ticket_mehr_als_frei`: a waiting thread can measure its queue position), so the non-interference
entry `sperrAbstrakt_nur_eigen` is a statement about the specification, not the implementation;
and the release performs no check (`gib_ohne_wache`): one unheld release lets the next ticket in,
so the `.gib` half is discharged only for well-nested callers.

---

## 8. Optimiser specification (absorbed from `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`)

**Status: SPECIFICATION only.** Written 2026-10-01 (lane 331) for the direct x86-64 compiler, first
friend delivery 2026-10-02. **Every Lean file it names lived under `grammatik/Grammatik/X86/`
(`Opt/Regeln/OptimizationRules.lean`, `OptimizationWitnesses.lean`, `Opt/Schleifen/{InvariantenOpt,
AufrufOpt,StaerkeReduktion}.lean`, `Kern/Wort.lean`, `Speicher/*`, `TSO/*`, …) and is not on
master since 2026-10-10**; it is on the branch `archive`. Nothing below is implemented or proved on
master; the rule library was "proved-pending-review" and never independently reviewed. The design
is target-neutral and is kept because it is the contract a future AArch64 optimiser must meet.

### 8.1 What an optimiser may assume, what it must preserve

Assume: the goal theorem with standard axioms; user logic as `LogikPflicht + StartPflicht` for
every budget (runtime/OS/binding contracts are user logic); only named hardware behaviour; source
semantics = the real `exec`; source concurrency W/GX with the atomic rely; the checker verdict is
the Lean Bool `Akzeptiert`. Preserve, for every accepted unit: values (finite and infinite runs);
faults — every source fault still faults, at a source-blamed place, through the declared channel,
in source order; memory observations including concurrent ones; IEEE behaviour (no reassociation,
no free FMA, no width change); control state (flags, rounding, condition outcomes); contracts at
their place with actual values (never `forall`-d away, never compiler-guessed); call logs and
`FolgeG` order including inlined calls; race freedom, lock discipline, visibility; progress
classes and stop kinds (no fairness or termination invented); source budget refusal, channel and
order.

### 8.2 Trust path and identity

```
accepted source unit -> obligations computed in Lean from the source
  -> direct checked lowering: source-anchored blocks to machine blocks/bytes
  -> untrusted Rust passes + certificates (evidence only)
  -> executable Lean Bool validators, proved sound once, generically
  -> final bytes in a checked image -> revalidation of the FETCHED bytes against the mapping
```

Outcome: a validated optimised image or **refusal** — never "optimised but unchecked", never a
warning. **One source of truth for meaning:** the typed source AST with `exec`. No persistent SSA
language, no second interpreter, no "optimiser IR" beside a "lowering IR"; Rust-side CFG/SSA
artefacts are transient hints. CFG, dominators, liveness, footprints and colouring are
validator-recomputed claims over explicit block/edge lists. The small representation interface is
lane 570's `SourceMemory` pattern (`repOk`, `zahlWort`/`wortZahl` round trips, `layoutOk`,
`regionDisjunkt`); every new width adds rows, never a fork. IR287's algorithms may migrate as
guidance; its interpreter and trusted well-formedness checker are not adopted. Until a lowering
row is proved, its forms refuse.

### 8.3 Rule inventory (status as of the archived tree)

| Group | Rules | Condition that keeps it sound |
|---|---|---|
| Fold / propagate | C1 literal fold (`⊕` total at the type), C2 copy, C3 checked op with provably true side condition (check kept as a ghost precondition), C4 wrapping vs checked | overflow keeps its channel: `2^63 + 1` at `signed 64` does not fold silently |
| Simplify | S1 branch pruning at a decided condition, S2 unreachable block, S3 sparse conditional propagation | only when the validator recomputes the truth; "true by contract" without a decided literal does not prune (that would be a compiler-guessed `ensures`) |
| GVN / CSE | V1/V2 pure expressions | purity recomputed; a faulting expression reused twice faults once, which changes behaviour; loads are §3.7 business |
| Dead code | D1 pure unused, D2 store never read (whole-unit footprint) | store seen by another thread, a device or a lock-protected reader is live; flags-live is part of liveness |
| Checks | B1 bounds, B2 `narrow` (kept unless the range already fits at this version), B3 overflow | range fact at **this** SSA version; `p[i]` checked at entry then `i := i + k` is not covered |
| Strength | R1–R3 `* / % 2^k` to shift/mask for provably nonnegative operands with `k < width`; **R4 signed div/rem refused** (truncation ≠ shift); **R5 reassociation/FMA refused** | side conditions decided by `decide`/range |
| Alias | A1 disjoint accesses commute, A2 store-to-load forwarding, A3 unknown ⇒ no motion | alias answer is a proved three-state `Disjoint`/`Same`/`Unknown`; name inequality is not disjointness |
| LICM | L1 pure, L2 load | L2: no store to the footprint in the loop, no fault-order change, no crossing of a lock/atomic/call boundary; hoist first, then unroll |
| Floating point | F1 exact literal fold at one width with RNE; F2–F4 **refused** (reassociation, contraction, `f32↔f64` motion, NaN/flag-dependent rewrites) | bridge incomplete: default REFUSE |
| Flags / peepholes | P1 flag fusion, P2 address modes with no-wrap proof, P3 layout, P4 spill/fill | an undefined flag is never treated as false; `cmov` with memory still faults; division is never speculated; shift counts mask |
| Inlining | I1 direct call with the ghost pair spliced (entry + return with **actual** values, `FolgeLog` preserved), I2 devirtualisation only through a legal-entry proof, I3 dropping contracts/budget/reason **refused** | the inlined body still consumes its source budget |
| Unroll / tails | U1 bounded unroll with remainder loop, U2 tail jump | an unrolled loop that refuses at iteration `n` still refuses at `n` |
| SIMD | **default refuse**; scalarisation (packed code the validator cannot check replaced by checked scalar code) is the only conservative direction | needs per-lane source correspondence, first-faulting lane = scalar order, tearing rules, budget transfer, vector tail |

Pass order (a later pass may assume only validated output and recomputed facts, never logs):
fold/propagate → CFG simplify → GVN/CSE (pure only) → check removal → strength → alias motion/load
reuse → LICM → inlining → unrolling/tails → peephole/select/layout/allocation. Numeric caps are
"measure then choose"; no invented constants.

### 8.4 Facts, concurrency, budget

**Invariant lifetime.** A rewrite may use only facts available at its site: the source invariant at
its guaranteed place (`VertragAmOrtG`, `InvAmOrtG`, `InvRuheG`, `InvSichtG`, `SperrWechselG`,
`SperrSichtG`) with actual values. An entry fact is never used inside a writer or held section;
no compiler-guessed contracts; call ghosts carry actuals. Mandatory (`COMPILER-SCHLUSSPLAN.md`):
no check removal, folding, motion or load reuse without a cited invariant/range/region premise at
the exact place.

**Concurrency (TSO bridge OPEN).** Using W/GX lemmas for target steps without the bridge is
unsound and forbidden. Nothing moves, removes, merges or reorders across: any atomic (any width or
ordering), any lock acquire/release, any fence, any call that may synchronise (unknown body ⇒ may
synchronise), any device access, any interrupt enable/disable. *"Race-free ⇒ remove all fences" is
not a rule*: DRF is a source property and fences carry visibility the bridge has not yet
transferred. RMW sequences are indivisible; a CAS keeps its retry loop (no "always succeeds
eventually"); ordering tokens are preserved exactly (**stronger is not safe**: it can deadlock
where weaker progressed); a shared-atomic reread is not stable; a local fence drains the own
buffer only; a fact proved under one core assignment does not transfer.

**Budget, stops, work, time** are three separate quantities. Every source stop kind (hardware,
flag, budget, `nieZurueck`) corresponds to a target behaviour through the same channel in the same
order; cheaper code is no licence to extend acceptance; optimisation work is never debited from the
source budget; dead-call elimination only when the call is proved fault-, effect- and log-free.

### 8.5 Certificates, pipeline, handoff

Each validator is an executable Lean function proved sound **once, generically** — the refinement
is *derived* from the check, never assumed as a simulation premise. A certificate carries only
WHERE and WHICH rule (map, versions, entailment names); the validator recomputes every fact.
Renames are checked total and injective on live names; per-function proofs carry global summaries
(may-write, may-call, contract reuse); a per-function result with an unchecked link is a refusal.
A wrong certificate refuses; the conservative route (keep the check, keep the call, scalarise) is
itself validated and is never a warning; **required validation failing refuses the compilation.**

Fast compilation includes the Lean checks: interned IDs, one copy each of shared analyses with
revision/dependency invalidation, deterministic bounded work (fixed worklists, fuel per pass,
linear-scan allocation, spills to provably private slots), caches that are untrusted and
re-validated, deterministic fallback for optional passes only, warm Lean batching, and **final
revalidation of the fetched bytes** against the loaded mapping (every executed byte, file offsets,
virtual addresses, load bias, relocation operands, runtime/binding/entry bytes). Latency of
validated bytes and unvalidated bytes are reported separately. Test matrix: generic soundness
statements with a joint `_zeuge`, poison certificates and positive probes per rule, project gates
unchanged; performance figures were unknown then and are unknown now.

A friend contributor was to own the rule library and the two reserved files, not the umbrella,
the goal statement, central proofs or the validator skeleton; acceptance contract: generic
theorem, witness, poison probes, `#print axioms` standard, no second IR. (The file says both that
the friend "is not claimed to have started" and, in its §13, that a first delivery of 2026-10-02
exists; the delivered files were in the archived tree, their author is not named.) First delivery: constant fold, range-decided check removal, entailed `narrow`, target-word strength
reduction, and the pass-order check, with certificate paths into loop bodies — `Option`-valued
validators (the source syntax has no decidable equality) that rebuild the output from input plus
certificate, and `ExprEquiv`/`StmtEquiv` stated over the exact single-thread `Ausgang`; the G/GX
transfer of these rules (a removed check removes a G step, an interleaving point and its time) was
open.

**Obligations O1–O10 (all open):** direct lowering representation rows; per-pass certificates and
validators; full source → machine lowering with a refusal catalogue; per-access target execution
and the memory-model refinement into W/GX; stack/ABI/entries/regions/runtime/binding coverage of
all reachable bytes; IEEE/control-state correspondence; budget accounting and work/time transfer;
closing validator soundness with finite/infinite coverage and negative probes; Rust implementation
of the reviewed Lean interfaces (Lean first); full integrated validation and performance
measurement. Performance goal against equivalent C built with GCC `-O3`: minimum 80 %, target
110 % (Simon, 2026-10-07; `ARM-PLAN.md`); **unmeasured; no all-programs claim**; invariant
analysis is mandatory, not optional.

---

## 9. The path from the grammar to the checker and emitter (absorbed from `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`)

*Written 2026-09-09; status check 2026-10-17.* **Principle:** `grammatik/Grammatik/Kern/Syntax/Syntax.lean`
is the specification of the checker and `Kern/Semantik/Semantik.lean` of the emitter: a program is
accepted when it *is* a term of `Syntax.lean`, and generated code is correct when it does what
`exec` does. Nothing is a new judgment; judgments that exist in Lean are transferred.

**Plan, not built.** The plan: a crate `gabbro-ableitung` elaborating the AST into the attributed
family of `Syntax.lean`, each hypothesis field carried as a `Zeugnis` (range fact, guard, write
right, rank, linear balance, call fit with the exact `Held`, declaration fact, mark in hand), the
resource context Λ **computed** per site (`Held` of the signature, minus consumed, plus allocated,
`locks L {…}` adds `Held(L)`, `advances` moves a mark), the derivation printed as Lean and
accepted by `lake env lean` ("Lean accepting the file *is* the statement that the program is a
sentence of the grammar"), then an emitter that lowers *constructors* with one C pattern each and
the twelve outcome sites (`gabbro_logik`/`gabbro_hardware` as the runtime's only two exits), a
`TESTBUILD` trace recorded into per-thread ring buffers with a `Gesittet` check (W1 consistency,
W2 every event good, W3 exclusion at every `nimmt`, W5 unshared carriers touched by one thread),
a differential test of `exec` against the emitted C, and the retirement of every pass rule that
maps to a constructor hypothesis (steps U1–U8). Pass rules map as: M1 → `Expr` range
hypotheses, M2 → the Λ index, M3 → `durch`/`assignDurch` guards, M4 → loop constructors, locks →
`darf`/`gdarf`, effects → `V.schreibt`, registers → `regLies`/`regSchreib`/`transition`.

**What exists on 2026-10-17:**

| Plan item | State |
|---|---|
| derivation datum | `crates/gabbro-check/src/ableitung.rs` is the **effects/costs derivation** (`gabbro derived`, `gabbro effects`), *not* the Syntax.lean elaboration; there is no `gabbro-ableitung` crate (`ls crates`: three crates) and no `gabbro ableite --lean` |
| the Rust-to-Lean seam | `gabbro lean`, `gabbro lean-g` (exporter, `lean_g.rs`), `gabbro obligations --g`: partial (REGISTER: 34 CERTIFIED, 211 UNCERTIFIED, each UNCERTIFIED with its first refusal `LG001`–`LG007`) |
| Sugar twin | `Kern/Syntax/Zucker.lean` exists; there was never a `pruefe-zucker` |
| the retired `pruefe-deckung` (extended with a rule → constructor column) | the script guarded a different thing (now `cargo test -p gabbro-check --lib lean::deckung_tests`): the hand-written Lean mirrors `Form`/`Reason` of `programmlogik/Gabbro/Coverage.lean` against `lean.rs`. The planned third column is not built |
| `pruefe-ableitung`, `vergleiche-bedeutung`, `gabbro spur` | **never existed** (the retired guardian set of 2026-10-17 had none of them) |
| `TESTBUILD` | exists as a build flag (`gabbro emit|llvm --testbuild`, items marked `when TESTBUILD`); the trace recorder and the `Gesittet` checker are not built |
| Pass retirement (U8) | not started; the Rust passes remain the checker, the Lean Bool `Akzeptiert` decides premise (a) for certified programs |

Outcome table of the plan (kept as design): `logik` outcomes are obligations in the shipping build
and runtime checks under `TESTBUILD`; `hardware (annahme|fortschritt|ieee|register|geraet|
sichtbarkeit)` is a runtime held-against-type check or a named assumption with a falsifier. The
**stays-outside list** is unchanged: when a handler runs (`entry … dispatch`, `via idt`, `masks
irqs`: `H102` stays a pass over the declaration), the cost model (`K001`–`K009`), and the C compiler
and the machine.

### 9.1 The LLVM certificate (`gabbro llvm-cert`)

`gabbro llvm-cert [--target=x86_64|aarch64] [--unit] <file.gab>` prints, from the same checked
lowering run as the IR, the data a refinement needs: target triple and layout, functions (name,
parameters, return, linkage), named types, system-call gates (number, registers, out register,
clobbers, template), entry, the `narrow` successes behind each `llvm.assume`, arenas, locks and
thread roots. It carries no IR (a test asserts no `define i32` and no `target triple` in it).
**Measured 2026-10-17: the output does not elaborate in Lean**, contrary to `LLVM-BACKEND.md`
§7's "elaborates with plain `lean`": each `def … :=` is followed by `-- name := …` comment lines
and a second `:=` (`llvm.rs:444–452`), and `lean` reports `unexpected token ':='; expected term`
at every definition; the tests check substrings only. There is also no Lean consumer of these
definitions in `grammatik/` or `bruecke/`, and the `help` text still promises "the COMPLETE IR as
Lean text". Status: a candidate record, not a certificate.

**What validating the LLVM path costs** (evaluation, `LLVM-BACKEND.md` §5 condensed): the design of
§0 does not change — an LLVM middle end is one more untrusted byte producer. New surface is small
and per target: one correspondence lemma per gate shape (plain call, `never` call) plus the entry
lemma `_start` (stack, entry register state, exit/never-return), priced like the C stub lemmas. The
optimiser is priced per *property*, not per pass: the validator checks that the final bytes refine
the source, so the cost is the per-access memory bridge (shared with the native plan) plus loop and
`llvm.assume` reasoning strong enough to follow optimised code. The x86-64/AArch64 agreement
automated in `instrumente/teile/baue-llvm.sh` (run by `instrumente/pruefe-llvm.py`) is a standing falsifier for backend bugs at zero proof cost.
Not claimed: no validated binary exists; `korrOk` is C-only; the per-access bridge is open.

---

## 9a. Binding order of 2026-10-17: every lowering in Lean, a complete Lean parser, benchmarks last

**Simon's orders.** (1) Every lowering must exist in Lean — this is a duty, not an option. (2) A complete
Lean parser. (3) The benchmark against GCC comes only when the compiler lowers much more and strong
optimisations are in. Language and syntax follow the Lean model first (CLAUDE.md); a lowering of an existing
form changes no language, but it is not accepted until its Lean part exists.

**What 'in Lean' means here.** The Rust lowering (`llvm.rs`, `llvm/*.rs`) stays an untrusted producer. A
lowering is *in Lean* when (a) the target fragment of LLVM IR has a Lean syntax and a Lean semantics, (b) the
lowering of the form is a Lean function from the model's source form to that IR, with a printer to `.ll`
text, and (c) there is a theorem that the IR's behaviour refines the source form's behaviour in machine G
(or, for hardware-only forms, a named assumption with its exact text). The Rust output is then checked
against the Lean function byte for byte (differential validator in the Lean guardian), and the Rust code is
a fast copy of a specification, not a second source of truth.

**Track L: refinement down to the binary, in two halves (Simon, 2026-10-17).** Lowering to LLVM IR brings little: LLVM is
outside the validated chain. Only refinement all the way to machine bytes counts. That needs a CPU model, which Simon builds
in parallel (`arm/`); Track L does NOT start it and builds no AArch64 interface, encoder or toy CPU. It builds the half that
needs no CPU model:
1. **A target-independent low-level language of our own** in Lean (`Grammatik/Code/`; not LLVM): word-sized registers or
   locals, byte memory with the GX interface for atomics, ALU operations with explicit width and wraparound,
   compare/branch/loop, call/return with a frame, atomics with orderings, a stack; with its semantics.
2. **The lowering from machine G to it** as a Lean function and the **refinement theorems**: expressions, straight-line code,
   `ite`, calls (L1); memory forms: arenas, `free`, stack and recursion (L2); concurrency: locks, `publish`/`await`, threads,
   refined into GX (L3); hardware forms with named assumptions (L4).
The first LLVM-flavoured draft (`Grammatik/Llvm/`, ~6 000 lines) is the template and is deleted once `Code` supersedes it.
**ISA neutrality (Simon, 2026-10-17): `Code` must serve x86-64, AArch64 and RISC-V models without extra work per ISA.** Hence: no
condition flags or register classes (unbounded locals, fused compare-and-branch); word width and endianness are parameters; nothing
relies on behaviour where the ISAs differ (division by zero, shift amounts at or above the width, `INT_MIN / -1`, unaligned access:
each is an explicit precondition of the op, proven from G's ranges, never a defined result); atomics are the five orderings on
aligned word cells with RMW as one abstract op; calls use an abstract frame. One plain structure lists exactly what any CPU model
must provide for the later `Code`-to-bytes refinement (byte memory with the GX atomics, wraparound arithmetic at word width, the op
preconditions, the fence/atomic mapping); it is a statement of obligations, not an ISA model.

**Out of scope until the CPU model exists:** `Code` to bytes (instruction selection, encoding, relocation, image mapping) and the
Lean validator for the Rust backend's bytes; the report of Track L states which properties of `Code` that step will need. The
LLVM backend stays as the running reference compiler. Estimate for the half: 25 000-40 000 Lean lines.

**Track L: lowerings in Lean (phases, each ends with a theorem and a guardian stage).**
1. **L0 `Code` model.** `Grammatik/Code/Model/` (direction of 2026-10-18: not LLVM, ISA-neutral, no CPU model
   on the way). Built and proved: types and values, byte-addressed block memory with aligned access only and
   the word width and byte order as the parameter `Conf` (64-bit little and 32-bit big endian both run in
   the witness), the small-step semantics with an oracle at the atomic load only (linked to the weak-memory
   interface and `Speichermodell.Ordnung`), SC determinism, a kernel-computed witness, and `Need`, the
   list of obligations a CPU model must provide for `Code -> bytes` (the same for x86-64, AArch64, RISC-V).
2. **L1 core lowering.** Built and proved (`Lower/`, `Refine/`): expressions (`lowerE_ok`), statements, blocks,
   end blocks (`lowerS_ok`, `lowerB_ok`, `lowerEnd_ok`: slot, pointer, global and variable assignment, `if`,
   `let`, `check`, `return`) and the function prologue (`prologue_ok`, `lowerFn`). Open: calls, loops, `match`,
   `narrow`, division and shifts (the lowering emits none until G's ranges prove the precondition).
3. **L2 memory forms.** Arenas, `grow`, `free`/free list (`ArenaFrei.lean` is its model), sampling, the page
   return; stack and recursion lowering. ~6 000–9 000.
4. **L3 concurrency.** Ticket lock, reader/writer lock, masked acquisition (the lock refinement of the open
   item 'lock primitive not proved'), `publish`/`await` as release/acquire, threads and `child` with handed
   stacks; refinement into GX. ~8 000–12 000.
5. **L4 hardware forms.** `entry` (x86_64 IDT stubs, aarch64 vectors), `asm` bodies, port space, `device`
   registers, system-call gates: each with its named hardware assumption, no invented semantics.
   ~4 000–6 000. `boot` and `entrust` stay refused until the language gives them a semantics in the model.
6. **L5 certificate and validator.** `llvm-cert` consumed in Lean; the validator runs in the Lean guardian.
   ~2 000–3 000.
Total Track L: ~36 000–54 000 Lean lines. Order: L0, L1, then L2–L4 in parallel, L5 last.

**Track P: a complete Lean parser** (`Grammatik/Parser/`, today 22 700 lines for the fragment tables, locks,
`impl fn` with pointer/index/range parameters, comparison contracts, straight-line bodies, direct calls).
Missing: loops and `traverse`/`retry`/`forever`, `match`/`let else`/option and sum forms, atomics, arenas and
`free`, `entry`/`boot`/`syscall` gates/`asm`, floats, `format`/bit fields, `walk`/`group`/invariants,
generics-free but module/`use` structure, `extern`/`library`, hardware profile items, `const`/`spec fn`.
Plan: close the grammar rule by rule against `SYNTAX.md` (189 rules), each rule with a printer, a round-trip
proof and an elaboration into `UProg`/`Deklaration`; a coverage matrix (rule × parser × printer × elaboration)
is the measure, not a count of examples. Elaboration replaces the Rust exporter `lean_g.rs` (5 958 lines,
then deleted). ~20 000–35 000 lines. Order by corpus weight: control flow, matches, atomics, arenas, then the
hardware items.

**Shared prerequisite.** The model changes first (CLAUDE.md): new G forms come from `PLAN-DYNAMISCH.md` 8a
(free list, invariants over live slots) and from the missing hardware-form semantics.

**Benchmark against GCC `-O3`: after Track L reaches L3 and the optimisation phase below.** Not before; today a
measurement would compare a compiler that refuses a fifth of the corpus.

**Optimisation (before the benchmark).** The `opt -O3` of LLVM is outside the validated chain. Strong
optimisation inside the validated chain means either validating LLVM's output (Alive2-style, per function)
or doing the passes in Lean; decide after L1. Meanwhile the checker-derived facts (`!range`, `noalias`,
`llvm.assume`, `!tbaa`) are the optimisations Gabbro has that C does not.

## 9b. Track P coverage matrix (measured 2026-10-17)

Instruments: `grammatik/Grammatik/Parser/Cover/Census.lean` (lexes, parses in depth and elaborates every
`beispiele/*.gab`, reports the first failing items of each file), `Cover/Proben.lean` (33 decided probes of the
forms read since phase 1, generated by `instrumente/teile/gen-parser-proben.py`, each form with a negative twin) and
`instrumente/parser-deckung.py` (the 190-row rule matrix below; `--run` re-measures). Columns: reader `S`
structured, `P` partial (a spelling refused or a part dropped), `R` raw words kept, `X` none; printer `E` =
`druckToks`/`druckTyp`/`druckAnw`/`druckItem` exists; rtrip `P` = round-trip theorem for the printable (`gut`) shapes,
`M` = measured (decided witnesses with negative twins in `Print/Proben`, and the census columns `rt=` function bodies
and `ri=` leaf items, no theorem); elab `U` = `elabU`/`lowerAllg` lowers it; corpus = files using the rule's head word.

| measure | start (5abb6e08) | phase 1 | phase 2 (1)+(2) | phase 2 (3) first slice | phase 2 (4) |
|---|---|---|---|---|---|
| files that lex | 170 / 170 | 170 / 170 | 170 / 170 | 170 / 170 | 170 / 170 |
| files that parse as a whole | 116 / 170 | 153 / 170 | 170 / 170 | 170 / 170 | 170 / 170 |
| files that elaborate (`elabU`), all of them also lower | 9 / 170 | 9 / 170 | 9 / 170 | 13 / 170 | **19 / 170** |
| exporter-certified programs (29 in `beispiele/`; the register file is gone, the list is in git at 3068f537) elaborated | 9 / 29 | 9 / 29 | 9 / 29 | 13 / 29 | **19 / 29** |
| rules, reader S / P / R / X (190 rules) | 127 / 27 / 22 / 14 | 144 / 18 / 22 / 6 | 158 / 11 / 22 / 0 | 158 / 11 / 22 / 0 | 159 / 12 / 20 / 0 |
| rules with a printer, a round trip (proved P + measured M) | 28, 28 | 28, 28 | 28, 28 | 28, 28 (expressions only) | **174, 34 + 140** |
| rules with an elaboration | 58 | 58 | 58 | 59 | 66 |
| function bodies / printable items of the corpus that print and read back as the same tree | n/a | n/a | n/a | n/a | **429 / 429, 1287 / 1287** |

Phase 2 (3), first slice: `masks irqs` (`ULock.masks` -> `D.maskiert`), entry `via` (`UProg.handler` -> `Programm.unterbricht`), `concurrent` roots ahead of the dispatch roots, nested modules, and the dropped `deadline ... arch ... falsifier` clause lift 108, 166, 59 and 165 (13 of 29). Open in this phase: statics, `let`/`check`/`traverse`, atomics, tagged types, lock invariants and gates (each needs its G form in `declOf`: `Glob`, `Inv`, `Ax`, `Ty.sum`, or a variable context in `lowSeqL`), and the printers and round trips.

Phase 2 (4), measured 2026-10-18 (Track P, second continuation). (a) `let` of a number, `if`/`else if`/`else`, `return`/
`leave`/`next` inside blocks and `traverse over slots of T by unvisited` elaborate and lower: the lowering functions take
their scope (`Γ`, the parameter table) as arguments, so a `let` grows it for the rest of the block (`Block.bind`,
`Endblock.bind`; the binding carries the COMPUTED range of its value, the annotation is a check), `lowSeqL`/`lowStructL`
read runs of statements for every loop flag `l`, and a `return` inside a block stands only where the held list is the
contract end (not under `locks`). 1164, 190 and 193 lift. (b) Statics: `UGlob`, `Expr.glob`, `Stmt.assignGlob`,
`Deklaration.Glob := Fin n`; the call rule checks the written statics; `sp0Of` starts each static at its initialiser
(`sp0GlobWert`, refusal `sp0_glob_luecke`); the theorems that assumed `Glob = Empty` are redone generically
(`GvStartPflicht`, `GvLuecken`). 187 lifts; 121 waits for tagged types. Payload-free atomics (`atomic A : T`, `A = v publishes nothing;`, a read
as `Expr.glob`) are the same carrier with `atomar := UGlob.atomic` and `Stmt.publish` with the empty payload: 162 and
116 lift; a payload, `observed by` and a plain store to an atomic have no G form (refused by name). The measuring-lane wrapper elaborators
`elabU02`..`elabU05` (they dropped statics, prototypes, format and reason items) are deleted. (c) Printers: `Print/Stmt`
(types, every statement form), `Print/Item` (every one of the 35 item kinds), the spelling of the predicate forms in
`druckToks`. (d) The English
rename of the elaborator's data types, fields and refusal strings (`tabs`, `locks`, `roots`, `names`, `kinds`, `held`,
`lockBeg`, `ifBeg`, ...). (e) The first statement-level round-trip THEOREM (`Round/RundlaufAnw`..`3`):
`rundlauf_block_einfach` -- a block of `return`/`leave`/`next` and number `let` over `gutPrim` expressions prints and
reads back through `parseBlock` as the same tree (witness `rundlauf_block_einfach_zeuge`, planted defect
`schliesse_ende_noetig`: `schliesseBlock` reads a trailing `return` as the ender). Open in this phase: the
statement theorem beyond the straight-line core (assignments, calls, `if`, nested blocks:
measured only), atomics, tagged types, lock invariants and gates.

Findings. (1) The expression round trip is a theorem on the `gut` shapes (`Rundlauf3` names the nesting blocker); the
statement and item round trips are measured, and the `SExpr.ext` forms now have a spelling in `druckToks` (decided per
form in `Print/Proben`, outside `gut`). (2) Elaboration is the bottleneck, not the reader: 85 parsed
files stop at an item kind with no G form (`globT` 34, bodiless `fn` 29, `atomic` 13, `reason` 12, `device` 11,
`assume` 10 ...) and 7 at a statement. (3) Of the 20 exporter-certified programs not yet elaborated, 13 need G
forms: `masks`/entry-via (59, 165, 166), `concurrent` roots (108), atomics (116, 162), statics (121, 187), tagged
types (34, 120), `let`/`traverse`/early `return` (1164, 190, 193); the other 7 (118, 119, 124, 157 lock invariants;
174, 181, 182 gates) parse now and wait for `Inv` and gate elaboration. (4) The lexer table lacked five words
(`grow`, `pb`, `blw`, `free`, `target`); `SYNTAX.md` had no rule for `start { f, g };` (now `startstmt`, 190 rules).
(5) Still lossy in the reader: call-argument labels (`P(a: 1)`), `pub`, the `retry`/`forever` headers (the `traverse`
header is structured since phase 2 (4)), `narrow` targets, `awaits`/`publishes` payloads, `exchange` transforms, `asm`
and `bank` bodies (`R`).

| rule | group | reader | printer | rtrip | elab | corpus files | note |
|---|---|---|---|---|---|---|---|
| `ident` | lex | S | . | . | . |  | `lex`, total (`lex_total`) |
| `letter` | lex | S | . | . | . |  |  |
| `digit` | lex | S | . | . | . |  |  |
| `hexdigit` | lex | S | . | . | . |  |  |
| `int` | lex | S | E | M | . |  | `Token.num` (value only: the spelling is lost) |
| `dec` | lex | S | . | . | . |  |  |
| `hex` | lex | S | . | . | . |  |  |
| `bin` | lex | S | . | . | . |  |  |
| `float` | lex | S | . | . | . |  |  |
| `string` | lex | S | . | . | . |  | `Token.text`; the expression reader has no string primary |
| `char` | lex | S | . | . | . |  |  |
| `quote` | lex | S | . | . | . |  |  |
| `newline` | lex | S | . | . | . |  |  |
| `comment` | lex | S | . | . | . |  |  |
| `path` | lex | S | . | . | . |  | `nimmPfad` |
| `pathseg` | lex | S | . | . | . |  |  |
| `identlist` | lex | S | . | . | . |  |  |
| `regbind` | lex | S | . | . | . |  | `SRegBind` |
| `program` | item | S | E | M | U |  | `parseTopTief`; `elabU` takes tables, locks, impl fns, consts, entries |
| `item` | item | S | E | M | U |  | `SItemTief`, 32 constructors |
| `buildgate` | item | S | E | M | . | 1 | `gateT` |
| `bootdecl` | item | S | E | M | . | 1 | `bootT` |
| `bootstep` | item | S | E | M | . | 1 | `SBootSchritt` |
| `entrydecl` | item | S | E | M | U | 9 | `SEingang`; `elabU` reads only the dispatch roots |
| `entrustdecl` | item | S | E | M | . | 1 |  |
| `entryextra` | item | S | E | M | . | 10 |  |
| `syscalldecl` | item | S | E | M | . | 17 | literal, `via V` and `syscall V;` forms |
| `sysbind` | item | S | E | M | . | 17 |  |
| `syscontract` | item | S | E | M | . |  |  |
| `syspair` | item | S | E | M | . | 37 |  |
| `targetdecl` | item | S | E | M | . | 11 | `goalT`; the lexer table gained `target` |
| `targetbind` | item | S | E | M | . | 11 | `goalT` bindings |
| `errmap` | item | S | E | M | . | 17 | `errno [= n] => R` |
| `accdecl` | item | S | E | M | . | 2 | `accT` |
| `moduledecl` | item | P | E | M | U | 170 | `modT`; `pub` is dropped |
| `usedecl` | item | S | E | M | . | 2 |  |
| `constdecl` | item | S | E | M | U | 67 | `konstT` |
| `constexpr` | item | S | E | P | U |  | an `SExpr` |
| `constwert` | item | S | E | M | . |  | nested rows (`SKonstWert` (`one`, `rows`)) |
| `arraylit` | item | S | E | M | . | 3 | nested rows |
| `staticdecl` | item | S | E | M | U | 43 | `aligned`, array initialiser lists; `pub` dropped |
| `typedecl` | item | S | E | M | U | 59 | `typT`; elab reads range aliases |
| `markorder` | item | S | E | M | . | 3 |  |
| `typeexpr` | type | P | E | M | U |  | `STyp`; struct, variants, fn pointer ride raw |
| `stringty` | type | S | E | M | . | 8 | `STyp.str` |
| `stringkopf` | type | S | E | M | . | 8 | `STyp.str` |
| `indexty` | type | S | E | M | U | 46 | `STyp.index` |
| `nevertype` | type | S | E | M | . | 31 |  |
| `intty` | type | S | E | M | U | 164 |  |
| `uint` | type | S | E | M | U | 163 |  |
| `int` | type | S | E | M | U | 8 | second definition of `int` (signed sugar) |
| `nonzero` | type | S | E | M | . |  |  |
| `floatty` | type | P | E | M | . | 1 | read as an atom plus `in`; no float elaboration |
| `frange` | type | P | E | M | . | 1 |  |
| `fexpr` | type | P | E | M | . | 1 |  |
| `boolty` | type | S | E | M | U | 60 |  |
| `range` | type | S | E | M | U | 77 |  |
| `array` | type | S | E | M | . | 19 | `STyp.reihe` |
| `structty` | type | R | E | M | . | 25 | balanced, uninterpreted |
| `field` | type | R | E | M | . |  | inside a struct type: raw; inside `format`/`slot`: `SFeld` |
| `fieldty` | type | R | E | M | . |  |  |
| `bitpos` | type | S | E | M | . | 18 |  |
| `variants` | type | R | E | M | . | 10 | balanced, uninterpreted |
| `fnptr` | type | R | E | M | . | 4 | balanced, uninterpreted |
| `fncontract` | type | S | E | M | . |  |  |
| `entryfn` | type | P | E | M | . | 1 | `STyp.entry`: parameter words raw |
| `typelist` | type | S | E | M | . |  |  |
| `params` | type | S | E | M | U |  |  |
| `fnptrparams` | type | R | E | M | . |  |  |
| `fnptrparam` | type | R | E | M | . |  |  |
| `ptrty` | type | S | E | M | U | 67 | rights kept as one string (`rw+own`, `own@h`) |
| `space` | type | S | E | M | U |  |  |
| `rights` | type | S | E | M | U |  | `parseRechte` |
| `right` | type | S | E | M | U |  | `parseRechte` |
| `expr` | expr | S | E | P | U |  | `SExpr`; `druckToks`, `parse_druck_*` for `gutKern`..`gutEmb` |
| `orexpr` | expr | S | E | P | U |  |  |
| `andexpr` | expr | S | E | P | U |  |  |
| `cmpexpr` | expr | S | E | P | U |  |  |
| `bitexpr` | expr | S | E | P | U |  |  |
| `addexpr` | expr | S | E | P | U |  |  |
| `mulexpr` | expr | S | E | P | U |  |  |
| `unary` | expr | S | E | P | U |  |  |
| `fnvalue` | expr | S | E | P | . | 16 | `fnref` |
| `primary` | expr | S | E | P | U |  | string literal and `count` read; both `ext` |
| `stringlit` | expr | S | E | M | . | 3 | `ext .text` |
| `countexpr` | expr | S | E | M | . | 1 | `ext .count` |
| `reasonval` | expr | S | E | P | . | 8 | `SExpr.why` |
| `optionexpr` | expr | S | E | P | . | 12 | `call` named Some |
| `paren` | expr | S | E | P | U |  |  |
| `call` | expr | S | E | P | U |  |  |
| `arglist` | expr | S | E | P | U |  |  |
| `arg` | expr | P | E | P | U |  | the label of `P(a: 1)` is dropped |
| `builtin` | expr | S | E | P | U | 20 |  |
| `oldexpr` | expr | S | E | P | U | 4 | `SExpr.alt` |
| `place` | expr | S | E | P | U |  |  |
| `placesuffix` | expr | S | E | P | U |  |  |
| `placelist` | expr | S | E | P | U |  |  |
| `pred` | pred | S | E | P | U |  | `parsePred`; forms outside the core ride `ext` |
| `orpred` | pred | S | E | P | U |  |  |
| `andpred` | pred | S | E | P | U |  |  |
| `notpred` | pred | S | E | P | U | 29 | `=>` is `ext .imp` |
| `atompred` | pred | S | E | P | U |  |  |
| `heldpred` | pred | S | E | P | U | 32 | rides `ruf "Held"` |
| `quant` | pred | S | E | M | . | 11 | `SExpr.ext .all/.any` (layout at `XKind`); no printer: `ext` has no spelling in `druckToks` |
| `domain` | pred | S | E | M | . | 22 | the eight domains, as names and place operands of `ext` |
| `member` | pred | S | E | M | . |  | `ext .mem` |
| `reach` | pred | S | E | M | . | 2 | `ext .reach` |
| `predlist` | pred | S | E | M | U |  |  |
| `fndecl` | fn | S | E | M | U | 167 | `FnSig` + `SAnw`; elab: `impl fn` only |
| `asmrumpf` | fn | R | E | M | . | 3 | `asmT`, body raw |
| `asmops` | fn | R | E | M | . |  |  |
| `asmop` | fn | R | E | M | . |  |  |
| `inductlist` | fn | R | E | M | . | 1 | raw string |
| `induct` | fn | R | E | M | . |  |  |
| `efflist` | fn | S | E | M | U |  |  |
| `eff` | fn | S | E | M | U | 166 |  |
| `breakstmt` | stmt | S | E | M | . | 2 | `waive` |
| `block` | stmt | S | E | P | U |  | `SAnw.block` |
| `endblock` | stmt | S | E | P | U |  |  |
| `endstmt` | stmt | S | E | P | U | 137 |  |
| `stmt` | stmt | S | E | M | U |  | `SAnw`; no printer; `start { }` is read but SYNTAX.md has no rule for it |
| `leavestmt` | stmt | S | E | P | U | 10 |  |
| `nextstmt` | stmt | S | E | P | U | 4 |  |
| `advstmt` | stmt | S | E | M | . | 3 |  |
| `awaitload` | stmt | P | E | M | . | 8 | payload list raw |
| `exchstmt` | stmt | R | E | M | . | 6 | transform raw |
| `xform` | stmt | R | E | M | . | 6 |  |
| `letstmt` | stmt | S | E | P | U | 88 | the type ascription is read (`bind`, `bindElse`, `bindLib`, `alloc`) |
| `assign` | stmt | S | E | M | U |  | slot writes only in elab |
| `stateassign` | stmt | S | E | M | . | 0 |  |
| `exprstmt` | stmt | S | E | M | U |  | direct calls only in elab |
| `ifstmt` | stmt | S | E | M | U | 56 | `cond`, `elsif` |
| `matchstmt` | stmt | S | E | M | . | 23 | `cases` |
| `matcharm` | stmt | S | E | M | . | 23 | `arm` |
| `narrowstmt` | stmt | P | E | M | . | 22 | target range kept as raw words |
| `allocstmt` | stmt | S | E | M | . | 7 | `alloc` |
| `resetstmt` | stmt | S | E | M | . | 6 | with `at i count n` |
| `growstmt` | stmt | S | E | M | . | 1 | `SAnw.grow` |
| `freestmt` | stmt | S | E | M | . | 1 | `SAnw.free` |
| `childstmt` | stmt | S | E | M | . | 4 | `SAnw.child` |
| `startstmt` | stmt | S | E | M | . | 2 | `SAnw.start`; written into SYNTAX.md 2026-10-17 |
| `libcall` | stmt | R | E | M | . | 2 | region skipped balanced |
| `libregion` | stmt | R | E | M | . |  |  |
| `translatordecl` | stmt | S | E | M | . | 7 | `transT` |
| `loopform` | stmt | P | E | M | U | 26 | header raw |
| `traverse` | stmt | S | E | M | U | 15 | header raw |
| `retry` | stmt | R | E | M | . | 9 |  |
| `forever` | stmt | R | E | M | . | 10 |  |
| `table` | decl | S | E | M | U | 74 | `tableT`; elab: integer fields |
| `treedecl` | decl | S | E | M | . | 8 |  |
| `kante` | decl | S | E | M | . |  |  |
| `occdecl` | decl | S | E | M | . | 1 |  |
| `opdecl` | decl | S | E | M | . | 154 |  |
| `opname` | decl | S | E | M | . |  |  |
| `walkdecl` | decl | S | E | M | . | 1 | `SWeg` |
| `slotdecl` | decl | S | E | M | U | 73 |  |
| `slotfeld` | decl | S | E | M | U |  |  |
| `arena` | decl | P | E | M | . | 7 | `max`, `pb`/`blw` read; `pub` dropped |
| `slottype` | decl | S | E | M | . | 7 |  |
| `invariant` | decl | S | E | M | . | 15 |  |
| `costexpr` | decl | S | E | M | . | 9 |  |
| `format` | decl | S | E | M | . | 6 | `@version` read |
| `reason` | decl | S | E | M | . | 28 | `whyT` |
| `state` | decl | S | E | M | . | 1 | `stateT` |
| `device` | decl | S | E | M | . | 13 | `devT` |
| `mirrors` | decl | S | E | M | . | 4 |  |
| `bank` | decl | R | E | M | . | 1 | `bank` |
| `regdecl` | decl | S | E | M | . | 13 | `SReg` |
| `regklasse` | decl | S | E | M | . |  |  |
| `regphasen` | decl | S | E | M | . |  |  |
| `regfeld` | decl | S | E | M | . |  |  |
| `carrier` | decl | S | E | M | . | 2 |  |
| `transition` | decl | S | E | M | . | 5 | `STrans` |
| `transset` | decl | S | E | M | . |  |  |
| `placeshift` | decl | S | E | M | . |  |  |
| `shiftplace` | decl | S | E | M | . |  |  |
| `atomicdecl` | conc | S | E | M | . | 14 | `atomT` |
| `publishstmt` | conc | P | E | M | . | 14 | payload list raw |
| `nutzlast` | conc | R | E | M | . |  |  |
| `lockdecl` | conc | S | E | M | U | 44 | `invariant` read (`lockT` 7th field) |
| `lockstmt` | conc | S | E | M | U | 42 | `locks` |
| `rcudecl` | conc | S | E | M | . | 3 |  |
| `observestmt` | conc | S | E | M | . | 3 |  |
| `gruppedecl` | conc | S | E | M | . | 1 |  |
| `concurrentdecl` | conc | S | E | M | U | 6 | `concT` |
| `assume` | assume | S | E | M | . | 31 |  |
| `axiom` | assume | S | E | M | . | 3 |  |
| `profiledecl` | assume | S | E | M | . | 2 |  |
| `requiresprofile` | assume | S | E | M | . | 2 |  |
| `profileentry` | assume | S | E | M | . |  |  |
| `check` | assume | S | E | M | . | 3 |  |

rules: 191 rows, 190 distinct rule names (SYNTAX.md defines 190; `int` is defined twice)
reader   P=12, R=20, S=159
printer  .=17, E=174
rtrip    .=17, M=140, P=34
elab     .=125, U=66
rules with all four columns present (round trip: proved on `gut` shapes (P) or measured (M)): 62
corpus: 170 files; lex ok 170; whole-file parse ok 170; elab ok 17; lower ok 17

rules: 191 rows, 190 distinct rule names (SYNTAX.md defines 190; `int` is defined twice)
reader   P=12, R=20, S=159
printer  .=73, E=118
rtrip    .=73, M=84, P=34
elab     .=125, U=66
rules with all four columns present (round trip: proved on `gut` shapes (P) or measured (M)): 57
corpus: 170 files; lex ok 170; whole-file parse ok 170; elab ok 17; lower ok 17

rules: 191 rows, 190 distinct rule names (SYNTAX.md defines 190; `int` is defined twice)
reader   P=12, R=20, S=159
printer  .=73, E=118
rtrip    .=73, M=90, P=28
elab     .=125, U=66
rules with all four columns present (round trip: proved on `gut` shapes (P) or measured (M)): 57
corpus: 170 files; lex ok 170; whole-file parse ok 170; elab ok 17; lower ok 17

---

## 10. Cited section numbers

| Old reference in code | Now | Where it is cited |
|---|---|---|
| `PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3 item 2 / "stage (a)" | §6 | `Korrespondenz/Allgemein/KorrespondenzAllg.lean:6`, `Kette/Schlusssatz.lean:4`, `Kette/Schlusssatz104.lean:4` |
| §3 item 4 and §7 / "stage (b)" | §7 | `CBackend/Semantik/CNebenlaeufig.lean:4`, retired `pruefe-cformen` |
| §1 / "section 1" (T3) | §1 | `Parser/{Lexer,Ausdruck,Anweisung}.lean`, `Korrespondenz/Zeugnis/ZeugnisStmt*.lean` |
| §3 / "section 3" (chain count) | §6.3 | retired `zaehle-kette`, retired `pruefe-cformen` |
| §6.4, §6.5, §6.10 | unchanged | retired `pruefe-ctext`, `KorrOkAdaequat.lean:6`, `CText104.lean:11`, `KorrespondenzGeraetZeuge.lean:27`, `Kette/Schlusssatz.lean:528` |
| §7, §7.6 | unchanged | `Kette/Schlusssatz124.lean:4`, `Kette/Schlusssatz124Ticket.lean:4` |
| *(no section named)* | | `Bausteine/Schablonen/Schablonen*.lean:4`, `CBackend/Semantik/CTicket.lean:4`, `CBackend/Parser/CLexer.lean:4`, `Zielsatz/Kern/Spec.lean:1140` |
| `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §1.3, §2.1 | §9 | `Korrespondenz/Zeugnis/Zeugnis.lean:6,31`, `crates/gabbro-check/src/emit.rs:9582` |
| `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` | §8 | no reader found by `grep` in `crates/ instrumente/ grammatik/` |

Absorbed and safe to delete once the references above are rewritten: `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`,
`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`. The Lean headers that cite `PLAN-UEBERSETZUNGSVALIDIERUNG.md` with no
section keep working because the file stays.
