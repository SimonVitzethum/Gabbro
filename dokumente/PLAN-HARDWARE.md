# Hardware: what the language carries, what is assumed, what is open

*Rewritten 2026-10-17 from a 3 078-line German measurement diary (2026-09-01 to 2026-09-04,
git history of this file). Every claim below was checked against the tree on 2026-10-17 or
carries its date and the words "not re-measured". Old section numbers are mapped in §15.*

**Scope.** Two questions, one document: (1) how far does Gabbro's claim reach at the metal,
and where does it end in a named assumption instead of a proof; (2) which hardware *model*
exists in Lean, which was dropped, and which is being built. The goal statement itself lives
in `grammatik/Grammatik/Zielsatz/Kern/Spec.lean` (header = the one list of named assumptions
and of what is NOT CLAIMED); the proof status lives in `BEWEIS.md`. This file does not
restate either.

---

## 1. What "no `unsafe`" can mean

Two readings, and only one is reachable.

- **Not reachable: no trust base.** Every chain ends in a sentence nobody derives from
  something else (this device sits at this address; this memory orders as the manual says).
  A trust base of zero does not exist in any system; Verve's is small, named and machine-checked.
- **Reachable, and the real content: no construct that switches checking off.** Rust's `unsafe`
  is an unbounded switch. Gabbro's `assume … falsifier` and `axiom … falsifier` are the opposite:
  one named statement with a way to refute it. `parse.rs` states the rule: *there are no unsafe
  windows; what touches the machine stands in `axiom`, `raw fn` or `prim fn` — named and counted.*

> The difference is not safe versus unsafe but **countable versus uncountable.** What remains
> is work on a number: how many assumptions, how big each, and how many have a probe that runs
> on the architecture where the assumption could break.

The honest sentence is therefore: *no construct disables a check; the lowering must also not
guess.* The second half is the generator question of §6, and since the C emitter is deprecated
and the LLVM backend untrusted (§6), the end of that road is the final-byte validator
(`PLAN-UEBERSETZUNGSVALIDIERUNG.md`).

---

## 2. What exists where (state 2026-10-17)

### 2.1 In the language

| Surface | State |
|---|---|
| Address spaces in the pointer type `ptr<space, right> T` | `normal mmio dma code boot port` (`SYNTAX.md`, `space` production) |
| `device D(base) at <space> { reg R : T @off class K … }` | access classes (`rw`, `r`, `w`, …), phase classes (`class rw in setup, r in live` over a `linear ghost type … order {…}`), `w1c` as a class, `wrapping`, `requires … else` as a fallible read (`beispiele/44`), `depends { carrier, … }` naming the device-state carriers a register's answer may rest on (`N258`) |
| `assume name [arch X] "text" falsifier probe` / `unfalsifiable "why"` | grammar `SYNTAX.md` §12; **`arch` is built** (`beispiele/02`, `06`, `60`) |
| `axiom f(…) effects {…} falsifier probe` | the hardware or foreign call with its frame |
| `entry <name> vector N arch X { regs in/out, preserves, clobbers, stack …, dispatch f }` | register convention as a type; `H102` forbids a thrown entry taking an unmasked lock |
| `asm { "…" in {…} clobbers {…} }` bodies | named, counted window with effects, costs and an `arch` guard (`beispiele/36`, `67`) |
| `syscall` items | the program's own gates; **no OS is built in** — an OS call is a generic gate whose contract the program or its binding declares |
| `walk … levels n { node, down, invariant … }` | structure and termination of page-table-shaped trees |

Counts, re-measured 2026-10-17: **98 `assume` lines** over `beispiele/*.gab` and
`messung/*/*.gab` (31 of the 170 top-level examples carry at least one). 36 of the 98 are
program-level contracts of gates (`linux_*`, `metal_*`, `faden_start_vertrag`,
`fremd_faden_vertrag`), the rest are device or platform statements (`cr3_leert_den_tlb`, `dma_kohaerent`, `ipi_kommt_an`,
`kern_bleibt_unter_jeder_aenderung_abgebildet`, …). `gabbro assumptions <file>` prints the manifest.

### 2.2 In the goal theorem

Premise (c) is `HardwareAnnahmen O E.Q := GutO O ∧ RegLokal O ∧ AxVertragO E.Q O`:

- `GutO` — the oracle that answers axiom calls respects the declared write frame, keeps the held
  locks, and records its declared writes as events;
- `RegLokal` — a register read answers from the carriers its declaration names (`depends`); the
  visibility answer of `awaits g` depends on `g` alone;
- `AxVertragO` — wherever a raw answer fits the declared result type, the declared `ensures` holds.

Premise (d) `Laufzeit` is the loader plus the runtime's thread creation (A4). What stays outside
(NOT CLAIMED, header of `Spec.lean`): termination and waiting bounds, stack depth, the C and the
hardware beyond the named list, weak memory beyond DRF-SC except the atomic rely, floats beyond
the kernel IEEE model, starvation freedom, invariants inside a running writer.

Consequence worth stating: **the Lean model contains no CPU.** A hardware assumption in (c) is
a sentence about an oracle, not a statement derived from an instruction set.

### 2.3 Hardware model in Lean: x86-64 (stopped), AArch64 (in construction)

**x86-64: stopped 2026-10-07, archived 2026-10-10.** Commit `7c693cb7` moved
`grammatik/Grammatik/X86/` (357 Lean files, about 265 000 lines), `dokumente/x86/`,
`DIRECT-COMPILER*.md` and `crates/gabbro-check/src/x86/` to the git branch `archive`. What the
archive holds is a 14-form pilot decoder/executor, byte-addressed memory, a per-access x86-TSO
store-buffer model, image/relocation/stack fragments and the optimiser rule library specified in
`PLAN-UEBERSETZUNGSVALIDIERUNG.md` §8. It never became a complete byte-connected machine: encoder
round-trip is not hardware correspondence, and the TSO-to-W/GX bridge was never proved. Seven
GabbroV files in the `X86` namespace stayed on master (`GvTreeParent`, `GvLuecken`,
`GvStartPflicht`, `GvAtomRely`, `GvBaum`, `GvVerkettung`, `GvAtomKoerper`): they have no x86
content. *Reason given (`ARM-PLAN.md`): the x86 model was too laborious to complete.*

**AArch64: the selected target** (`ARM-PLAN.md`, decided 2026-10-07). Basis: the Sail model of the
Arm architecture, `rems-project/sail-arm` (`arm-v9.4-a`, 37 `.sail` files, about 466 000 lines),
cloned read-only outside the repository. Sail gives sequential instruction semantics and system
registers; it gives **no multicore**, so the relaxed-memory model is added in Lean. The Sail
compiler is not installed here, so the sequential part is ported **by hand, each definition
citing the Sail file and line it translates**, to be compared one-to-one with a Sail-generated
Lean later. Such a port is self-consistency with the Sail text, not hardware correspondence;
whatever the Arm manual calls IMPLEMENTATION DEFINED or UNPREDICTABLE stays free, and
implemented `FEAT_*` extensions are to be a named profile as data (vendor neutrality, also for a
Snapdragon-class core).

The code is the separate Lake project `arm/` (Lean 4.33.1, no Mathlib, no dependency;
`arm/Arm.lean` is the umbrella). State by `wc -l`, 2026-10-17: about 5 900 Lean lines in
`arm/Arm/**`; no `sorry`/`axiom`/`native_decide` found by `grep`. **Not rebuilt for this
document** (no `lake` run): the build status below is quoted from the agent reports.

| Area | Files | What is there | Honest limit |
|---|---|---|---|
| Vocabulary | `Basic`, `Mem/Event` (frozen) | `Ev`, `Rel`, `Exec`: events, `po`, `rf`, `co`, `addr/data/ctrl`, `rmw` | — |
| Executions | `Mem/Trace`, `Mem/Exec`, `Mem/Dep` | instruction effect trees to events; well-formedness `Exec.wf` (rf/co/po/dep/rmw); dependency detection by perturbation | register data flow is hidden in Lean continuations, so syntactic dependencies are invisible to any function of events (proved in `Dep`); register reads answer zero in replay |
| Axiomatic model | `Mem/Axiomatic`, `Mem/Model` | `fr`, `rfi/rfe/fre/coe`, `dob` (six clauses), `obs`, `ob`; axioms `internal`, `external`, `atomic`; `consistent` is the conjunction; verdicts for MP, SB, LB, R, S, 2+2W under an empty plug-in | clauses are reproduced **from the author's knowledge of Arm ARM B2.3 / `aarch64.cat`, not from a measured copy** (no `.cat` file or ARM text on this machine); confidence by clause is tabled in the report, `(addr\|data);rfi` and the ISB clause medium, completeness of `dob` unknown |
| Atomics | `Mem/Atomics`, `Isa/AtomicOps` | exclusive monitors as a state machine (spurious STXR failure free), LSE atomics, `aob`, spin-lock mutual-exclusion witness | granule modelled as byte-range overlap; LDXP/CASP pair shapes not distinguished |
| Barriers | `Mem/Barriers` | `bob`: DMB full/ld/st, DSB data classes, acquire/release/RCpc, rel-acq, ISB control leg; `plain_never_bob` | shareability domain v1 (`nsh`/`osh` order nothing); DSB completion and ISB fetch halves have no event; no SB/SSBB |
| Instruction fetch | `Mem/IFetch` | write → DC CVAU → DSB → IC IVAU → DSB → ISB → fetch recipe; five planted drops each allow a stale fetch | single-core fixtures, no PoU/PoC, no shareability |
| Litmus bench | `Lit/Prog`, `Lit/Enumerate`, `Lit/Tests` | litmus language, candidate-execution enumerator, 17 tests as data with forbidden/allowed outcomes | 8-byte accesses only; **`runAll` is defined but not applied to an assembled model** |
| Sequential ISA | `Isa/Monad`, `Addr`, `LoadStore`, `AtomicOps`, `Int*`, `Integer`, `Interp` | execute-level semantics for integer data-processing, loads/stores/addressing, exclusive pairs, LSE atomics; a concrete interpreter with test vectors; each with planted-wrong cases | wrappers over `decide`-checked cores, not proved against Sail; SCTLR gating, translation, faults abstracted |

**Not there, and named so that nobody assumes it:**

- no branches/system registers/exceptions, no floating point or SIMD, **no decoder, no Sail bridge,
  no coverage ledger** (`arm/Arm/Sail` does not exist; reports 13–15 of the plan do not exist);
- **the model is not assembled:** `aob` (`Atomics`) and `bob` (`Barriers`) exist as functions of an
  `Exec`, but no file builds an `OrderingParts` from them, so `consistent` has only ever been run
  with the empty plug-in. The expected flips (MP/SB become forbidden with `bob`, LB stays allowed)
  are written in the report, not demonstrated;
- `Mem/MixedSize.lean` (byte view and single-copy atomicity) is **not imported** by `Arm.lean`;
- no connection between `arm/` and `grammatik/` (goal theorem, W/GX); the per-access bridge from
  AArch64 executions to W/GX is open;
- no differential test against a real core (planned after the model; `qemu-aarch64` covers
  instruction semantics only).

### 2.4 Source-side weak memory (exists, proved)

W (view-based weak memory), GX (W with the shared-atomic reads the goal's atomic rely admits)
and the thread machine are in `Speichermodell/Maschine/{MaschineW,GXMaschine,Sicht}.lean` and
`Speichermodell/Atomar/`. The statement `SchwachX` (the weak machine adds no behaviour beyond GX
steps) is part of `gabbro_ziel`. **W abstracts `seq_cst` as release/acquire; that is not a proved
total SC order.** Nothing here is a model of x86 or Arm; the target bridge is the open item of
`PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3.

---

## 3. The four hardware points

### 3.1 MMIO — nearest to done

Fixed address, exact width, `volatile`, access classes and phase classes, one read per binding
(`beispiele/44`), the `~` width trap (inner cast) handled. Measured 2026-09-01, not re-measured:
all four emitter sites write the typed complement.

Open:

- **RMW on a device is three emitter steps and atomicity is stated nowhere.** For a register a
  device changes concurrently, read-modify-write is simply wrong. `w1c` is a class now, so a
  W1C RMW is refused; a `modify` construct that tells W1C and shared registers apart would
  continue the phase-class idea (`R012` removes only cases wrong without any interruption).
- **`device … at port` — LLVM backend defect, measured 2026-10-17.** The C emitter lowers a port
  access to `in`/`out` (since 2026-09-02, `beispiele/65`, `objdump` shows `out %al,$0x43`). The
  LLVM backend does **not** refuse it: `gabbro llvm beispiele/65-port-space.gab | grep 'load volatile'`
  prints plain volatile memory loads at `base + offset`. That is the original "the generated code
  reads RAM" bug in a new producer, and it breaks the rule "refuse by name, never guess" (`Y10x`).
  Not repaired here; it belongs in `LLVM-BACKEND.md` §6 until it is.
- `asm` bodies (the instruction level: `invlpg`, `sfence`, `mfence`, TLBI/DSB, shootdown) lower in
  the C emitter and are refused in the LLVM backend (`Y102`, `beispiele/67`). The *bytes the device
  sees* stay an assumption; `gabbro certificate` counts the lines, and that count is the statement.

### 3.2 DMA — the core is visibility, not coherence

Ownership transfer to a device is `consumes` plus a phase class (`beispiele/66`: two `linear type`
markers, one per side, so that *writing while the device owns the buffer* is refused as well as
the wrong order — `gift/671`–`673`, `N030` reads fields since 2026-09-03).

The finding that stands: **an assumption that is a conjunction with one falsifier is two
assumptions.** `dma_kohaerent` bundled *coherence* (device and core see the same cells) and
*ordering* (two volatile accesses become visible in program order). They do not follow from each
other and both depend on the architecture: on AArch64 a descriptor write to coherent normal memory
followed by a doorbell write to device memory can become visible in the wrong order without `DSB`,
and C11 `volatile` is no barrier there. **Built:** `assume … arch X`; `beispiele/02-geraet.gab`
now carries `dma_kohaerent` and `dma_sichtbarkeit_in_reihenfolge`, each `arch x86_64`.

Open:

- **Deriving barriers from address-space changes** (`DSB ST`/`sfence` between a write to `normal`
  and a write to `dma`/`mmio`). The six address spaces are in the type, the information is there,
  nothing derives from it. This would be something no other language does; not started.
- The falsifier of an `arch aarch64` assumption must run **on AArch64**, or it tests nothing
  (`ARM-PLAN.md` direction); no such probe exists.
- That a device touches a buffer only in the agreed window is a statement about foreign hardware:
  `consumes` plus phase is the right encoding of the intent and will never be a proof.
- Shared user memory between capabilities is outside the language (same cut as seL4); it belongs
  as one line in `BEWEIS.md`.

### 3.3 Interrupts — contract complete, body not in the language

`entry` states register convention, preservation, clobbering, stack and nesting as a type. The
goal covers same-core interrupt deadlock for the handlers a unit declares (`KernHaltE`,
`Programm.unterbricht`, `via idt`); `H102` fires only on `via idt` and the LLVM backend refuses
`entries` (`Y102`, TODO §4). Open: a handler body written in Gabbro with the contract proved
rather than asserted (`preserves`/`clobbers` are claims about foreign code while the dispatcher
is outside), `O19-Rest` in `TODO.md` (handler on handler, re-entry, G has no cores).

### 3.4 Page tables — three layers, measured against the wrong thing first

Count the uses of a construct before writing a rule over it, **and ask whether they go wrong in
the same direction.** `walk` has five declarations that are not five page tables: two x86 page
tables (`beispiele/07`, `messung/fragmente/F09`), a filesystem inode block tree
(`messung/grammatik/blocklauf`), two grammar probes. A rule on `walk` that means "page table" is
wrong for three of five. *Two uses that mask each other are worse than ten that do the same.*

`runs online` without a generated check is **booked as a `W` obligation** (`gabbro pflichten`,
`W` register: "invariant owed by no function", **4** for `beispiele/07` today), not refused: the
word names three classes and only one fails.

Evidence from Caprock (`../caprock-messbasis`, branch `arch/x86_64`, commit `a1bf707`, read-only;
numbers from 2026-09-01, only the `write_entry` call-site count (14) re-checked):

| Layer | Finding | State |
|---|---|---|
| **1 TLB** | 51 page-table entry writes (37 in `mmu.rs`, 14 through `write_entry` in `vtd.rs`). Change/removal of a live entry: 6 functions, 6 invalidate. ADD of a new entry: 13 functions, 7 never invalidate on purpose. The IOMMU half already routes every write through `write_entry`, "which never returns without a flush" — the construct, written in Rust and enforced by a comment. **The rule belongs at the KIND of change, not at the write**; at the write it would be redundant for removals and wrong for additions. Whether not-present → present needs invalidation is an architectural statement (Intel permits caching not-present entries; AArch64's safe answer differs) | assumption written (`beispiele/06`: `neuer_eintrag_verdraengt_nichts arch x86_64`, falsifier `sonde_praesent_ohne_invalidierung`); construct **not built** — `walk` does not distinguish ADD from CHANGE |
| **2 Preservation** | W⊕X is a property of the *change*, and the induction "one PTE write violates only at its own entry" is **false**: effective W is the conjunction of `RW` over the path, so one interior write can move up to 512³ leaves it never touched. Whether that matters depends on what `m.schreibbar` means (the leaf's own bit, or the effective permission), and nothing in the tree decides it. A second break needs no hierarchy: fields the domain *synthesises* (`m.va`, `m.level`, `m.index`) change under a graft without a bit changing. 1 of the 5 corpus invariants depends on them. The way out (induction over paths) is blocked: `D018` refuses `ancestors of` on a `walk`, and the bound behind it is not computed | `D020` built (field of a mapping must exist, `gift/570`); construct **not built**; ordered behind (a) deciding `m.schreibbar`, (b) `ancestors of` over a `walk`, (c) its bound |
| **3 Self-reference** | The kernel changes the mapping it runs under. No site, comment or document of Caprock writes down which region must survive every change; the load-bearing clause is about a *trace* (every intermediate state, an interrupt can arrive between two entry writes) and no `ensures` can say it | booked as `assume kern_bleibt_unter_jeder_aenderung_abgebildet … falsifier sonde_kern_entmappt`; **do not build a construct** — two of three clauses would look complete while the third is what seL4 also only assumes |

---

## 4. Named assumptions: how they must be shaped

1. **A statement needs a falsifier** (`N031`): an assumption no probe could contradict is not a
   statement. `unfalsifiable "why"` is the explicit exception and is counted.
2. **One falsifier per claim.** Conjunctions are split (the DMA case, §3.2). *Open:* count how
   many of the 98 have the same shape.
3. **Architecture parameter** — `assume … arch X` is built; **the falsifier runs on that architecture.**
4. **Two levels, measured 2026-09-01 over the then 159 files, not re-measured:** *device*
   assumptions (`SRTP=1 → RTPS=1`, `dma_kohaerent`) should stand once per device; *platform*
   assumptions (timer interrupts, `CR3` drops non-global entries, release-store visibility, IPI
   delivery) once, period. Then 14 of 40 `assume` sites were copies, and the copies were exactly
   the general ones: "the timer interrupts" stood six times because **there is no place where a
   platform statement can stand once.** The proposed form is `platform x86_64 { assume … }` and
   `device Virtq { assume … }` blocks that programs inherit instead of copying — **not built**
   (no such production in `SYNTAX.md`). The fixable mark is *platform assumptions per program:
   zero; device assumptions per device: once*; it was falsified on its first measurement.
5. **`progress` and `assume` are the same thing in two lists** (an environment assumption with a
   watchdog as falsifier). A single trust list is the stated direction (§9); not built.
6. **The operating system is user logic, never an assumption** (Simon, 2026-09-30). A system or
   kernel call is a gate whose contract the program or its binding declares; only hardware
   behaviour is a named assumption. Consequence in the corpus: the `linux_*`/`metal_*` `assume`
   lines above are the *program's own* gate contracts with falsifiers (`sonde_write`, …), not
   baked-in OS knowledge.
7. **The assumption count per program n+1 must not grow with the program.** Today no mechanism
   ships a checked device description together with its assumptions as a reusable unit; until
   one exists, every new driver lengthens the trust base. Import must *carry* assumptions
   instead of copying them (`gabbro link` already demands the same hardware assumptions on both
   sides, `N505`).

---

## 5. Where the trust base sits

Until 2026-08-31 the `assume` list was booked as the trust base. That was wrong: the trust base
is the *generator* — a few thousand lines of Rust without proof. The measured form: twelve
wildcard branches in the emitter and six pairs of independently correct parts that were never
wired together. One line under all four hardware points was `breite_von`: `_ => 8` meant a new
integer word silently became `volatile uint64_t *` on a device while `pruefe` said `0 errors`.

**Repaired and checked 2026-10-17:** `emit.rs::ganzzahlwort` is one table of eight words,
`breite_von` is derived from it and answers `None` (→ `C001` by name) for everything else;
`umgebung.rs::breite_von` is its twin; tests in `emit.rs` pin them (`jedes_ganzzahlwort_hat_eine_breite`,
`erzeuger_und_pruefer_sagen_dieselbe_breite`, `jede_breite_hat_ein_lese_und_ein_schreibwort`). `_ => None` was
deliberately kept (a `_` that yields a plausible *value* is the silent byte; one that yields
nothing hands the decision to the caller). *The earlier booking was itself wrong twice*: the count
was a mix of four commands running the same pass, and the root line was recorded as "silent" where
it fired 146 times — **a counter that aborts at the first hit measures the wrong question**
(`panic!` → `eprintln!`; see `HISTORIE.md`).

Pattern behind it (the "build profile", six instances in two days): *parts arise singly and
correctly, the wiring arises never — it belongs to no construct and therefore to no lane.*
Candidates for a counter: two registers over one set; one construct describes, a second should
preserve (`walk` vs PTE writes); checker assumes, emitter says `C001`; an offer that is no duty.
The lint "no `_` over a language enum" is the sibling of `forbid(unsafe_code)`; not enforced in CI.

**Today's producers:** the C11 emitter is deprecated (§7), the LLVM backend is untrusted and
refuses by name, and the end state is a Lean-checked validator over the final image. The
trust-base question of this section is therefore transferred, not closed.

---

## 6. Hardware certificate and templates

A certificate that is not injective certifies nothing: before 2026-08-31 five domain forms
(`ElementeVon`, `KetteIn`, `Schlange`, `SlotsVon`, `Threads`) collapsed into one `"traverse"`
label, so two different programs got the same MD5. Repaired in `e5e555d` (nine reasons, not nine
labels; `tests/zeugnis_injektiv.rs` measures both directions). *Open: injective for the traversal
domains, not in general.* The generated runtime pieces (locks, thread runtime, arena runtime,
interrupt descriptor table, metal entry) are proved templates; the register is
`gabbro templates` (`PLAN-UEBERSETZUNGSVALIDIERUNG.md` §5).

---

## 7. Backend truth in one place

- **LLVM backend** (built 2026-10-14/15): Gabbro lowers directly to LLVM IR text for x86-64 and
  AArch64, no C anywhere, static binaries without libc; untrusted, refuses by name (`Y101`–`Y106`).
  See `LLVM-BACKEND.md`.
- **C11 emitter:** deprecated. Decided 2026-10-07 (`ARM-PLAN.md`), restated 2026-10-15
  (`AGENTS.md` §3: no guide for language or checker work); the emission check stopped being a push
  gate on 2026-10-17. Its refusals (`C001`) stand untouched.
- **Native binary refinement** needs a complete Lean CPU model first (`TODO.md` §5, "much later").

---

## 8. Vocabulary is the proof-cost curve

The proof burden grows with the **vocabulary**, not with program size, because totality is paid
for with vocabulary: every new recursion form needs a new construct instead of a termination
proof. The trade is made everywhere and was not counted until 2026-09-01.

Ratchet (`instrumente/zaehle-wortschatz.py`, run 2026-10-17): **248 words** (17 reserved, 231
contextual); `MARKE_WOERTER = 248`, reserved mark 17, and **`MARKE_OHNE_GRUND = 212` while the tool
counts 213 words without a reason block at the entry: the tool prints `RATSCHE GEBROCHEN`**
(a word was added without its reason, or a reason block moved; the guardian is red at the base
of this consolidation, not repaired here); 247 used in 435 corpus files,
1 reserved only (`masked`); proof debt **1 lowering theorem for 248 words** (`ops relabel`). A
new word names the word it replaces or the measurement showing no existing form carries it.
`SYNTAX.md` still prints "245 table words + 4 Sonderformen" in its status table: unreconciled.

What the ratchet taught:

- `decreasing` → `decreases` (the proof witness belongs to the *contract*, not to the *run*):
  222 → 221 words, no new one; positions stayed 333, so expression was exchanged, not lost.
- Quantifier domains are the largest single item and were the proposed target of a "declared
  reachability domain" rule. **Calculated and not built:** the production has eleven terminals
  not seventeen; only four of nine forms are reachability over a table field (the rule reaches 35%
  of the sites); `tree/parent/child/sibling` cannot fall (they feed the `relabel` generator and
  its Isabelle proof); and there were not seventeen lowering theorems to replace, there was **one**.
  The real argument was the *bound* (`domaenenschranke` has two callers, `kosten.rs` and
  `m1.rs`), not the vocabulary. *The `domain` production lists nine alternatives (`slots of`,
  `chain`, `descendants of`, `ancestors of`, `queue`, `fields of`, `elems of`, `threads`,
  `mappings of`) while `SYNTAX.md` says "eight, closed": unreconciled.*
- **No hand-written lemmas in source** is a design ceiling and the riskiest decision: it breaks
  only when the corpus is large. The exit exists (`pflichten --lean`, duties leave the language
  *named*); writing it down as a statement turns the abandoned duties into a reach number
  instead of a defeat.
- **Parametricity: measured, closed until the corpus grows.** Over 77 real programs
  (no `gift/`, `proben/`, `grammatik/`): 68 `table`/`format` declarations, 62 distinct field
  skeletons, 5 repeated, mostly the same teaching example in two files. The denominator decides
  the answer (with poison files: 226 declarations, 34 repeats). Repeat when Caprock translates
  completely.

---

## 9. Writing load versus proof load

*Measured 2026-09-01 over 64 files / 1 054 clause sites; counts moved since.* Two thirds of
what a Gabbro author wrote was **bookkeeping** (effects 462, costs 211, touches 25, `let`
annotations 7: 705), 18% own logic (188: contracts 82, termination 65, ranges 26, invariants
15), 9% hardware (93: register classes 35, `assume` 35, `reserved` fields 23), 6% derivable but
open (68). Target mark: **705 → 0 with 188 kept.** Three corrections that taught:

- **462 was not reconstructible.** Over `beispiele/`: 439 `effects` entries on function
  declarations (359 on functions with a body, 80 on `extern`/`prim` — those 80 are trust surface
  and can never reach zero); 538 by text count; which 64 files §21 meant is lost. The reliable
  number is **359 comparable entries.**
- **`costs` first would have been wrong**: it counts ops in the *emitted C* and so inherits every
  open spot in the generator invisibly; `effects` is a source analysis and cannot be spoiled by
  it. Built: `crates/gabbro-check/src/ableitung.rs`, `gabbro derived|abgeleitet`,
  `gabbro effects|wirkungen` (`--ursprung`, `--sperrrang`, `--eng`, `--vergleich`), `gabbro fmt
  --explicit|--elide`. "No declaration fell": omitted clauses are derived; the mark is unmoved.
- **The lattice argument was false.** "Effects form a finite lattice, so the fixpoint over
  cycles converges" fails: `aufrufgraph::ersetze` creates new places across a call edge, and in a
  cycle `k.wert → k.kind.wert → …` grows. The derivation therefore **widens** (a place deeper than
  four steps is cut to its prefix, sound because `deckt` works on prefixes; fired 0 times in the
  corpus). The conclusion survived, the argument did not. Retained withdrawals of the same
  experiment: a "59 of 359 carry nothing" figure was **retracted, not corrected** — the hull
  inherits the callee's padding and so hides the error it should find; and `H012` reads a held lock
  as an *acquisition* while `H007` reads it as a *permission* (`requires Held(X)` is not an
  acquisition): exactly one place in the whole tree is freed by the narrower set, and it had to be
  built (`messung/proben/460-…`, `gabbro effects --sperrrang`).
- **Padding is the rule, not the exception.** 87% of 682 `costs` promises had slack (397 over 50%;
  `zaehler_erhoehen` computed 6 against 2 048). 61% of sites could double their body without any
  `costs` guard firing. The proposed cure — a measured number under a guardian — covers *fewer*
  sites (179 against 210 written, the rest are bodiless `extern`/`prim`) but in the stronger
  direction (any movement either way). Not built; maintenance cost not measured.
- `effects` over-declaration is silent and inconspicuous (`reads u.slots` on a table never
  touched). `H011` already catches an unused `locks`; the open route is `requires Held(…)`.

**Proof side** (not measured by the mark above), 2026-09-01: obligations with a register 112 of
159 files (47 files carry none — a unit with errors carries no register), body channel 145 of 381
carried, 1 lowering theorem of 65 emitted forms (later: 51 C forms with a lemma, 4 named
assumptions, 27 without semantics, `pruefe-cformen.py`). Those numbers fed the later decision to
validate the final binary instead of proving emitter forms one by one.

**One trust list, not three.** Assumption lines in source, refusals of the generator, emitted
forms without a lowering theorem say the same thing in three places without a common
denominator. The proposal — a translation produces exactly one trust list, so "what must I believe
to trust this binary" is one command — is not built.

---

## 10. Against SPARK/Ada, and what was borrowed

SPARK proves a property you write; Gabbro makes the property a *grammar* property (an offset
without a length is not writable). Different failure modes: SPARK leaves an obligation open and
visible, Gabbro makes it unsayable and the author leaves the language (`extern`, `asm`,
`assume`). The cost moves from per program to per construct, and **the vocabulary is the
amortised specification**: the bet pays if many programs use few constructs. Ada's guarantee is
for the source and GNAT is qualified; Gabbro's must pass through its own generator, which is why
the generator is in the trust base (§5). Not adopted: Ada's visibility rules, private parts,
inheritance, generics. Better here: `pragma Assume` is weaker than `assume … falsifier`.

Borrowings, state 2026-10-17:

| Idea | State |
|---|---|
| `Depends` — which *output* depends on which *input* (information flow, a weak non-interference almost free) | **not built.** The word `depends` in Gabbro names device-state carriers of a register (lane 140); it is not information flow |
| Derived types (scalar newtypes: physical vs virtual address, slot vs object index) | `index into T` and `opaque`/`N030` cover part; no scalar newtype form found in `SYNTAX.md` |
| Descent path — a duty that statically fails becomes a *named runtime refusal* in the language instead of `extern` | not built; would turn `extern` from "indistinguishably wide" into three counted steps (proved, checked at run time, outside); needs a count of how many `extern`s fall in the middle step |
| Named restriction profiles (Ravenscar) | not built. `profile` / `requires profile` exist (`SYNTAX.md` §12.2) but name a *hardware* profile (`rounding`, `fp_contract`, `memory_model`, `interrupt_routing`), not a language subset |

The comparison test "Caprock structure in both languages, count specification lines per
generated line" was replaced by the *kind* criterion of §9 (a ratio measures program size too);
the seL4 calibration point is 20:1, of which about 0.5 abstract specification and 19.5 proof.

---

## 11. Retractions that stay (they teach)

| Claim | What happened |
|---|---|
| `phase` generalised (one word replaces four special rules) | calculated 2026-09-01 and **rejected**: one word would fall not four; two of four sites already had the construct, one needed none; the lowering theorem is zero, not one (ghost marks lower to nothing); the four counts had been taken over poison files. Typestate is `M2`, "an derivation, not a construct", and stands there correctly |
| `ghost` versus `witness` | not a word: `typedecl` already distinguishes by omitting `ghost`; what is missing is three `C001` in the generator, and no new word closes a `C001` |
| "String output is impossible" (`B2`) | retracted within the hour: arbitrary strings work through `ptr<normal,r> Kette` + length. The *question* was then wrongly framed as a signature issue; a `[u8; N]` carries a length and `const char *` a terminator. Rule: **bind what carries its end in the signature, not what looks for it in the data** (`N052`; `M115` enforces `n <= KAP` at each call). `void *` is admitted in parameters, not in results |
| "String is untouchable by Gabbro" for `char` at `extern` | same rule, `S3`; open: whether `N046` should admit `[u8; N]` for `char *` when written |
| "Exactly one item remains in category C" (ownership transfer) | was the remainder of an enumeration with no written denominator; two items; both closed 2026-09-03 (`beispiele/66`, `N030` on fields) |
| "Proof of fifth mark: 75 % → 87 % → 90 %" | not comparable: 75% had no denominator; later **30 of 30 capabilities with categories**, valid for *one* driver (`virtio-net`), 20 as "written-measurable" not "written". It rose because a pass read one more spot, not because the language improved |
| Barrier is a hardware blocker | false: `publishes … release` lowers to `atomic_store_explicit(…, release)`; C11 expresses acquire/release; what C cannot is an *instruction level*, not a memory model |
| `at port` waived / no lowering | lowered 2026-09-02 once a corpus program needed it ("no construct without measured demand — and no refusal without measured defect"); LLVM backend: see §3.1 |

---

## 12. Onboarding and delivery items (2026-09-01..03 measurements)

Not re-run unless dated otherwise.

- **Entry:** `gabbro new hallo` → `gabbro build hallo.bau` → `./target/hallo/hallo` prints `Hi`,
  no hand-written C driver (closed 2026-09-02; the README's quick start is the current form).
- **Newcomer path:** eight attempts to write "add two numbers" fell to one after `gabbro new`,
  the tutorial and five "did you mean" hints; the five paper cuts live in
  `crates/gabbro-syntax/tests/sprechprobe.rs` and the poison files `gift/620`–`624`. The test that
  remains is a second human.
- **English first names** for 12 subcommands and 12 flags, additive; `crates/gabbro-cli/tests/fahnen.rs`
  reads the *source*, not a list.
- **`H = 0`** (fragments through emit → compile → run → compare to a hand value): decided to
  *close*, not book; F09, F01, F05 closed 2026-09-03; F03 open. The guard `zaehle-fragmente.py`
  prints the current count (`messung/fragmente/README.txt` is read by `pruefe-zahlen.py`).
- **WASM:** `cargo build --target wasm32-wasip1 -p gabbro-cli --release` builds a 3.0 MiB module
  with no dependency; `build` is out of scope (no child process in WASI). **Never run** (no
  `wasmtime` on the machine). VS Code extension plan: stage 1 = diagnostics from `check`,
  stage 2 = a TextMate grammar generated from `kw.rs`, stage 3 = `costs` inlay hints.
- **AUR package** (2026-09-01 plan): zero external crates, `Cargo.lock` has no registry, the
  tarball builds `--frozen --offline` in 10.7 s; `LICENSE-ADDENDUM.md` must ship; `depends`
  was `gcc` only for `gabbro build`'s C path. With the LLVM backend this changes (`opt`, `llc`,
  `ld.lld`); the checksum can only be taken after the tag is pushed. Not packaged.

---

## 13. Network stack stage 4 (`messung/netz/`)

**Subject:** Ethernet → ARP → IPv4 → UDP echo, written against RFC 791/826/768/1071 and
checked against **published vectors** (classic IPv4 header, RFC 1071 §3), with a deliberately
different Python counter-calculation (`instrumente/zaehle-netz.py`). A comparison against one's
own figure is no comparison; the decisive probe is the sum over a header that already holds its
checksum, which must be 0. `messung/netz/README.txt` quotes the run (`3 von 3 Proben grün`) and
**is machine-read by `pruefe-zahlen.py`** (a pattern on that quoted line): do not translate or
delete the transcript block. The yield, as of 2026-08-20/21:

1. unary `!` had no lowering and the clean corpus had zero occurrences (corpus is written *per
   construct*; `!` is what one writes in a program) — built, `beispiele/46`; unary minus
   deliberately *not* (C keeps unsigned, M1 says `i32 in -4294967295 .. 0`, `gift/219`);
2. `-> T or R` lowered wrongly in two ways at once (returned a value from a `bool` function with
   `__attribute__((const))`, so GCC dropped the store) while `pruefe` said 0 errors;
3. a `reason` value had no producer (the emitter now says so inside the C);
4. "read the same bytes as big-endian 16-bit words" is not writable (`format` refuses a `[u16;10]`
   field): the word assembly happened in C, outside the language.

Edge decided *before* building: a byte view must not open an alias question (one view writes,
the others read, switching is an event — `SYNTAX.md` §3). `echo_beantworten` already contains the
case (`w` reads the same twenty bytes `k` writes). Since then `own`/`R014`/`R015` were built:
`R014` refuses two pointer arguments with one root; an untraceable pointer is *unknown* and
equals every root; `R015` names the boundary assumption (slices 1–4, 2026-10-17, Lean model
`ParamGetrennt`, `ObjGetrennt`). Whether the byte-view case itself is now refused: **not
re-measured**. Not in scope of the stack: TCP, fragmentation, `ihl > 5`, timers.

---

## 14. How to re-measure

```
python3 instrumente/zaehle-wortschatz.py            # §8
gabbro pflichten <file> | grep '^W'                # §3.4 (invariants owed by nobody)
gabbro assumptions <file>                          # §4
gabbro llvm beispiele/65-port-space.gab | grep 'load volatile'   # §3.1 defect
gabbro derived <file>; gabbro effects <fn>        # §9
python3 instrumente/zaehle-netz.py                 # §13
(cd arm && lake build)                             # §2.3, via the lane wrapper `./arm-bau`
```

## 15. Old section numbers (cited by code comments)

| Old | Now | Cited from |
|---|---|---|
| §5 (page tables, Layer 2) | §3.4 | `domaene.rs:1529,1604`, `tests/korpus.rs:205`, `tests/rechenwerk.rs:7735`, `saetze.rs:1385`, `beispiele/gift/570` |
| §11 (vocabulary ratchet) | §8 | `kw.rs:9`, `instrumente/zaehle-wortschatz.py:6,26` |
| §21 (705/188 mark) | §9 | `messung/proben/460-…gab` |
| §24, §25 (effects lattice; derived set retrievable) | §9 | `ableitung.rs:32`, `crates/gabbro-cli/src/main.rs:214`, `main.rs:3450` |
| §42 (`phase`) | §11 | `SPRACHE.md:110` |
| §48 (fifth mark, ownership transfer) | §11 | `beispiele/66` |
| §49 B3 (newcomer path), B6 (`H = 0`) | §12 | `tests/sprechprobe.rs:296`, `gift/620`–`624`, `dokumente/FRAGMENTE.md` |
| §51 S2 (`spec fn` cannot state a frame condition) | §9 / `BEWEIS.md` | `beispiele/06-annahmen.gab:65` |

Absorbed and now safe to delete: `dokumente/PLAN-HARDWARE.md` … `dokumente/PLAN-HARDWARE.md` (summarised in
§2.3; their `CUTS` sections are the "honest limit" column). **Not safe to delete:**
`messung/netz/README.txt` (machine-read) and `messung/netz/udp-echo.gab` (cited by tests).
