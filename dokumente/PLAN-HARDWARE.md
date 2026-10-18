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

Ratchet (measured by the retired `zaehle-wortschatz`, run 2026-10-17; not guarded today): **248 words** (17 reserved, 231
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
assumptions, 27 without semantics, by the retired `pruefe-cformen`). Those numbers fed the later decision to
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
  *close*, not book; F09, F01, F05 closed 2026-09-03; F03 open. The retired `zaehle-fragmente`
  printed the count (2026-10-17; not guarded today; `gabbro pruefe messung/fragmente/F0N.gab` re-measures one fragment).
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
different Python counter-calculation (the retired `zaehle-netz`, 2026-10-17). A comparison against one's
own figure is no comparison; the decisive probe is the sum over a header that already holds its
checksum, which must be 0. the retired `messung/netz/README.txt` quoted the run (`3 von 3 Proben grün`) and
was machine-read by the retired `pruefe-zahlen` (2026-10-17); no guardian reads the transcript now. The yield, as of 2026-08-20/21:

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
# §8: the vocabulary ratchet was measured by the retired zaehle-wortschatz (2026-10-17); not guarded today
gabbro pflichten <file> | grep '^W'                # §3.4 (invariants owed by nobody)
gabbro assumptions <file>                          # §4
gabbro llvm beispiele/65-port-space.gab | grep 'load volatile'   # §3.1 defect
gabbro derived <file>; gabbro effects <fn>        # §9
# §13: the network-stack vectors were run by the retired zaehle-netz (2026-10-17); not guarded today
(cd arm && lake build)                             # §2.3, via the lane wrapper `./arm-bau`
```

## 15. Old section numbers (cited by code comments)

| Old | Now | Cited from |
|---|---|---|
| §5 (page tables, Layer 2) | §3.4 | `domaene.rs:1529,1604`, `tests/korpus.rs:205`, `tests/rechenwerk.rs:7735`, `saetze.rs:1385`, `beispiele/gift/570` |
| §11 (vocabulary ratchet) | §8 | `kw.rs:9`, the retired `zaehle-wortschatz` |
| §21 (705/188 mark) | §9 | `messung/proben/460-…gab` |
| §24, §25 (effects lattice; derived set retrievable) | §9 | `ableitung.rs:32`, `crates/gabbro-cli/src/main.rs:214`, `main.rs:3450` |
| §42 (`phase`) | §11 | `SPRACHE.md:110` |
| §48 (fifth mark, ownership transfer) | §11 | `beispiele/66` |
| §49 B3 (newcomer path), B6 (`H = 0`) | §12 | `tests/sprechprobe.rs:296`, `gift/620`–`624`, `dokumente/FRAGMENTE.md` |
| §51 S2 (`spec fn` cannot state a frame condition) | §9 / `BEWEIS.md` | `beispiele/06-annahmen.gab:65` |

Absorbed and now safe to delete: `dokumente/PLAN-HARDWARE.md` … `dokumente/PLAN-HARDWARE.md` (summarised in
§2.3; their `CUTS` sections are the "honest limit" column). `messung/netz/README.txt` was retired on 2026-10-17;
`messung/netz/udp-echo.gab` is still cited by tests.

---

## 16. The hardware-neutral compiler: every system call, register, trap and memory source is the user's (design 2026-10-18)

**Rule (Simon, 2026-10-18, final):** the compiler contains no system call, no register name and no trap
instruction, not even in one small per-target table. `LLVM-BACKEND.md` §11 measured where `llvm.rs` still
breaks that rule (A1-A12) and proposed eight language changes (L1-L8). This section is the DESIGN of those
changes, made in the Lean model first (CLAUDE.md order); the surface spellings are PROPOSALS for `SYNTAX.md`.
**Nothing here changed the Rust parser, checker or compiler**, and `Zielsatz/Kern/Spec.lean` is untouched.

**Status in one table** (state of the tree at the commit that carries this section):

| Item | Design (this section) | Lean model | Statement touched? |
|---|---|---|---|
| L1 region provider (`pool`) | 16.2 | `Hardware/Anbieter/Region.lean`, `Arena.lean` proved, witnessed, planted defects | no |
| L2 trap clause | 16.3 | `Hardware/Tor/Abi.lean` proved, witnessed for 3 ISAs + a made-up one | no |
| L3 process exit | 16.4 | `Hardware/Tor/Ende.lean` §1 proved (`-> never` already exists) | no |
| L4 thread start, join, stack | 16.5 | `Ende.lean` §2 (join order), `Arena.lean` §3 (stack + guard) | no (text of premise (d)) |
| `Code` side of L1/L2 | 16.6 | `Code/Gate/{Gate,Provider,Bruecke,Zeuge}.lean` | no (`Code` is not in the statement) |
| L5 entry stubs | 16.7 | design only | no |
| L6 mask, ports | 16.7 | `Code/Gate/Maske.lean` (the mask IS a gate), design for ports | no |
| L7 register classes | 16.8 | `Abi.lean` (`RegName`) | no |
| L8 targets as data | 16.9 | `Abi.lean` (`ZielDaten`); the `Profil` entries are design only | no |
| neutrality | 16.10 | `Hardware/Neutral.lean`: `gabbro_ziel_zusatz`, `gabbro_ziel_leer` | no |

`gabbro_ziel` is still on exactly `propext`, `Classical.choice`, `Quot.sound` (`#print axioms` on the new
theorems: subsets of the three). No new module imports into an old one; every new theorem is in a NEW file.

### 16.1 The one idea

A gate is already "an axiom with a contract" (`D.Ax`, `AxVertragO`, `GutO`): the semantics does not know what
a `syscall` is. What the compiler still knew was how to REACH the environment: which instruction traps, which
register carries the number, where memory comes from, how the process ends, how a thread starts. All of that is
DATA about the environment, and the environment is the user's: so it moves into the program, next to the
contract it belongs to, and the hardware assumption that was implicit in a compiler table becomes a NAMED
assumption of a user item (`assume … falsifier …`), as every other hardware fact already is.

**Three consequences that decide the shape of everything below:**

1. *A new form is either pure lowering data or a named assumption, never new machine-G semantics.* Where a form
   needs semantics (the exit gate does not return, a thread's stack is released after its end), the existing
   vocabulary has it (`-> never` and the stop kind `nieZurueck`; the thread machine's spawn and join).
2. *No default.* A gate without a trap clause, a program with `at port` and no declared port space, an arena
   without a pool are REFUSED. A default would be a table in the compiler under another name (no legacy rule).
3. *Strongest variant for safety and power:* where a design question had two answers, the one that assumes
   LESS of the environment and lets the user express MORE was chosen (the reasons stand at each decision, `D1`…).

### 16.2 L1 — the region provider: `pool`

**Surface (proposal for `SYNTAX.md`):**

```ebnf
pooldecl = [ "pub" ] "pool" ident "{"
             "get"  path ";"                 (* reserve:  fn(bytes) -> ptr<normal, rw> u8 [or R] *)
             "fill" path ";"                 (* commit:   fn(r, bytes) -> u32                    *)
             [ "back" path ";" ]             (* page return, region stays: fn(r, bytes) -> u32  *)
             [ "drop" path ";" ]             (* end of the region:         fn(r, bytes)         *)
             "page" constexpr ";"            (* the commit granule in bytes                      *)
             "assume" ident ( "falsifier" ident | "unfalsifiable" string ) ";"
           "}" ;
arena      = … [ "from" ident ] ";" ;        (* the arena's storage is a reservation of pool `ident` *)
```

`path` names ordinary Gabbro functions (the binding library's `gabbro_os_reserve`, `gabbro_os_commit`,
`gabbro_os_seiten_zurueck` are exactly this trio; a fourth, `drop`, is new in the binding). Words: `pool`,
`get`, `fill`, `back`, `drop`, `page` (≤5 letters each), `from` exists. A freestanding program binds the same
roles to its own page allocator; no role names an OS.

**Machine-G semantics.** None new. The three roles are ordinary gates (`D.Ax`) whose answers machine G takes
from the oracle. G models an arena as a TABLE of `max` slots (`ArenaDyn`, `DynForm`); where the bytes come from
is below G, exactly as before (premise (d), `Laufzeit.reserve`/`.commit`). The provider contract is the HARDWARE
ASSUMPTION about the gates' joint behaviour: `Hardware/Anbieter/Region.lean` is its model.

**The model (`Region.lean`).** State: the live reservations (address ranges) and, per address, "holds resident
memory". Events with the contract as the premise of each step:
`hole n b` (reserve: the answer `[b, b+n)` is page aligned and DISJOINT from every live reservation),
`fuell lo hi` (commit: a page-aligned range inside one live reservation becomes resident),
`zurueck lo hi` (page return: the range stops being resident, the reservation stays),
`gib r` (end: the reservation ends, nothing of it stays resident, its addresses may be handed out again).
Proved: the invariant `Gut` (non-empty, pairwise disjoint reservations; resident ⊆ reserved) survives every step
(`gut_nach`, `lauf_gut`); **no RAM before use**: a reserve changes nothing resident (`hole_ram_gleich`) and the
new range holds no resident byte (`hole_neu_aus`, `hole_neu_null` — this NEEDS freshness and the invariant,
which is why freshness is part of the contract); **no RAM without a commit**: on every run from nothing a
resident address lies in the range of some commit of the run (`ram_gefuellt`, `kein_zugriff_ohne_fuell`);
distinct live reservations never share an address (`lebend_getrennt`). Planted defects: an overlapping answer,
a commit outside every reservation, a reserve that makes pages resident (`ueberlapp_verweigert`,
`fuell_draussen_verweigert`, `hole_mit_ram_sichtbar`).

**Arenas through the provider (`Arena.lean`).** `ArenaGut`: the arena's reservation `[b, b + spanne)` is live,
every committed slot byte is resident, and resident memory inside the reservation reaches no further than the
PAGE-ROUNDED committed prefix. The arithmetic is the existing proved template arithmetic (`ArenaLaufzeit`:
`spanne`, `commitStart`, `commitEnde`, `arena_commit_bereich`); the prefix is the existing `DynArena`
(`dynGrow`, ceiling `M`). `arena_start` (after the reserve the invariant holds with an empty prefix),
`arena_grow_geht` (`dynGrow A n = some B` is realised by ONE commit of exactly the template's range, that step
is legal under the contract, the invariant holds for `B`), `slot_resident` (every slot below the prefix is
readable and writable), `arena_exklusiv` (the arena's bytes lie in no other live reservation),
`gib_nichts_resident`, and the witness `arena_zeuge` (six 8-byte slots on 16-byte pages: after two grows the
slots are resident and an address past the rounded prefix is not). Planted defect: a grow past the ceiling asks
for a commit outside the reservation and the contract refuses it (`grow_ueber_decke_verweigert`).
**This is the 2b property of the guardian (`pruefe-llvm.py`: RAM stays untouched until used) as a THEOREM about
any pool, where it was a measured property of `mmap(PROT_NONE)` + `mprotect`.**

**Thread stacks (`Arena.lean` §3).** A stack is a reservation whose lowest `gd` bytes (the GUARD) are never
committed; it grows by `fill` above the guard (`stapel_waechst`). An overflow into the guard is an access to a
non-resident address — a hardware stop, never a silent write (`stapel_wache_kein_zugriff`) — and the guard
belongs to no other reservation (`stapel_wache_exklusiv`). A commit that starts inside the guard is the planted
defect (`fuell_in_wache_bricht`). A frame larger than the guard can skip it: that is the NOT CLAIMED stack depth
of the goal statement, unchanged, now with the named reason.

**What the goal gets.** The named hardware assumption `<pool>_ok` (the pool's `assume`): "the four gates,
in sequence, behave as the provider machine under granule `page`". Nothing OS-specific enters the statement.
The two places the premise could live and the decision are in 16.11.

**What changes where.**

| Place | Change |
|---|---|
| `Deklaration` | nothing required for the goal; for the exporter a `pool`-role marker is lowering data kept beside the unit (16.11) |
| `Stmt`, `Res`, `Block` | nothing: `alloc`/`grow`/`reset`/`free` keep their forms |
| `Akzeptiert` / the checker | the pool shape check (the three gates exist with the role signatures; `from P` names a declared pool; `page > 0`; the assumption is present and falsifiable); region extents are held by the EXISTING `N571`/`N463`. These checks protect the LOWERING, not G-safety |
| lowering | `arena_bereit` and the commit/release paths call the pool's gates; no `mmap`, no `mprotect`, no number |

**Decisions.**

* **D1 — four roles, not three.** `get`, `fill` mandatory; `back` and `drop` optional. The audit named
  reserve/commit/release; the model has TWO releases because they differ in effect: returning pages keeps the
  reservation (the arena `reset … at i count n` page return), ending it makes the addresses reusable (thread
  stack, whole arena). One gate for both would need a mode argument and would hide the difference in the
  contract. A pool without `drop` never frees: arenas live to the end of the process, which is the hosted
  behaviour today.
* **D2 — "no RAM before use" is a CONTRACT of `get` and `fill`, stated as frames and ranges.** Not a property
  of an OS. `get` writes no resident-state carrier (the model: `hole_ram_gleich`); `fill` makes resident exactly
  the commit range. The existing frame premise `GutO` (answers stay inside the declared write frame) already
  carries the first half once the resident state is a ghost carrier outside `get`'s `writes`.
* **D3 — the commit makes memory readable and writable, with NO claim about its contents.** On Linux a fresh
  page reads as zero, but the language reads no cell before it stores (an `alloc` stores its value first;
  `reset` clears through `region.leeren`). A weaker assumption is a stronger theorem: `Code/Gate/Provider.lean`
  lets the commit give the cells ANY content.
* **D4 — a commit may be refused.** Out of memory below the ceiling is real: the contract allows answer `1`
  with memory unchanged, and the program's `else` runs (`fuellSpec`).
* **D5 — `page` is a constant the program chooses, not a number the kernel reports.** A granule that is a
  multiple of every real page of the target is always accepted (`64 KiB` is safe on 4K/16K/64K systems); the
  contract "`fill` accepts ranges aligned to `page`" is part of the named assumption and has a falsifier. The
  alternative (a runtime page query gate) keeps working for the proofs (`arena_spanne_passt` takes the page as
  a parameter) and is a compatible extension, not needed now.
* **D6 — extents are held by the EXISTING region machinery.** `get`'s `-> ptr … or R` with `ensures bytes <=
  lenof(result)`; `fill`/`back`/`drop` with `requires bytes <= lenof(r)` (`N571`, `N463`, `N464`). No second
  extent mechanism.

**Open (not claimed).** (i) The bridge "ghost-carrier contract ⇒ `PStep`" (16.11, O-H1). (ii) Machine G has no
byte pointers (`LG002`): a program with a region answer stays outside the certified register exactly as before
(OFFEN O37); the `Code`-side bridge is 16.6.

### 16.3 L2 — the trap clause (and A6, A7)

**Surface:**

```ebnf
sysbind = "number" constexpr "in" reg "trap" string          (* NEW: the register and the instruction *)
          "regs" "in" "{" … "}" "regs" "out" "{" … "}" { "stack" ident }
          "clobbers" "{" [ identlist ] "}" "errors" "{" … "}" ;
```

`syscall write(…) abi linux arch aarch64 number 64 in x8 trap "svc #0" regs in { x0 = fd, x1 = buf, x2 = len }
regs out { x0 } clobbers { } …`. `trap` takes a string: the instruction text in the target's assembler, handed
to LLVM inline assembly UNREAD; `in x8` names the register the number is loaded into. The same two words stand
in `target T … { V = sysbind … }` bindings (12.3). **Not optional** (decision 2 of 16.1).

**Machine-G semantics: none.** The meaning of a gate call is its contract (`Ax`: parameters, answer, frame,
`ensures`). The clause is LOWERING data: `Tor.mitFalle_bed` (replacing the clause changes no meaning),
`loese_text_unabh` (the register assignment before the trap does not read the text).

**The model (`Abi.lean`).** `RegName` (a register is an opaque name — the generalisation of the x86-only
`SysReg` enumeration of `Syscall.lean`), `Falle` (text + number register), `TorAbi` (number, clause, input map,
answer register, clobbers) with `TorAbi.gut`: input registers distinct, no parameter bound twice, the answer
register not clobbered (the old `N063`-`N065`), PLUS the number register is neither an input nor a clobber (it
may equal the answer register: x86_64 `rax`). `belegung` is the register assignment before the trap;
`belegung_nodup` (one value per register: arguments and the number never collide), `belegung_nummer`,
`belegung_param`. `sysabi_zu_tor`: the existing x86_64 `SysAbi` is an instance. Witnesses: Linux `write` on
x86_64 (`rax`, `syscall`) and aarch64 (`x8`, `svc #0`) and a MADE-UP third architecture (`a7`, `ecall`)
(`schreib_gut`, `schreib_deckt`, `belegung_zeuge`) — the third needs no compiler change, which is the point.
Planted defects: a clobbered answer register, a doubled input register, a number register that is also an
input (`defekt_aus_zerstoert`, `defekt_ein_doppelt`, `defekt_nummer_ist_eingabe`).

**What the CPU model must supply (`Need`).** `Code/Gate/Gate.lean` (16.6): the trap sequence runs, and every way
it ends is an outcome the gate's contract allows — which IS the gate's named assumption, nothing more. The text
is not interpreted by any Lean or Rust component; whether it does what the user says is the assumption's
falsifier.

**Lowering (A6, A7 become pure lowering).** `call asm sideeffect "<trap text>", "<constraints>"(args)` where the
constraints come from the declared registers: input `{reg}`, output `={reg}`, clobbers `~{reg}`, plus
`~{memory}` whenever the gate's `effects` are not `pure`. The instruction sequence AFTER the gate that
`llvm/stapeltor.rs` writes per target (the `test`/`jnz`, `cbnz`, realignment, frame-pointer clear) is the USER's:
the child path of a `stack` gate (`child { … }`) is ordinary Gabbro code (`N446`-`N452` already check its shape);
what the stub needs per ISA (clear the frame pointer, align the stack) is either written in the child block with
`asm { … }` or is not needed (LLVM aligns calls itself).

**Decisions.**

* **D7 — the number register is named in the clause, not inferred from `regs in`.** The number is a value the
  program supplies at a fixed register, but it is not a Gabbro parameter; keeping it out of the parameter map
  keeps `N065` ("every parameter exactly once") unchanged.
* **D8 — no default instruction per `arch`.** A default is the table the rule forbids. The cost is one more
  clause per gate (or per binding variable, 12.3, where it is written ONCE per target).
* **D9 — text in the target's DEFAULT assembler dialect.** LLVM inline assembly uses the target's default
  (AT&T on x86). A program that wants Intel syntax says so once, in the profile (16.9: `asm intel;`). No
  per-gate dialect.
* **D10 — the clobber list is honest by assumption.** A trap that destroys a register it does not list is a
  falsification of the gate's assumption, not a checker case; the checker cannot read the text.

### 16.4 L3 — the process-exit gate

**Surface:** `proc _start run main exit sys_exit;` — an item. `_start` is the SYMBOL of the generated entry
function (user data: the linker's entry name differs per platform); `main : fn() -> i32` (or `u8`) is the
declared start; `sys_exit` is an ordinary gate declared `-> never` (the language has `Ty.never`, and the stop
kind `nieZurueck` for "the call does not return"): `fn(code : i32) -> never`. Words: `proc`, `run`, `exit` (≤5).

**Semantics: none new.** `main` is a declared start (`E.starts`, `concurrentdecl`) with no parameters; the
`StartEndeG` leg of the goal already says every declared start RETURNS; what happens after the return is the
generated entry's one gate call. `Hardware/Tor/Ende.lean` §1 models exactly that: `startSpur`: a returning `main`
gives its steps, then ONE end event with `main`'s own result as the code (`start_code`), nothing after
(`start_ende_gut`); a `main` that never returns makes no end event — the stub never invents an exit
(`start_ohne_rueckkehr`). Planted defects: a stub that falls off the end and one that keeps going after the gate
returns (`ohne_exit_kein_ende`, `nachlauf_nicht_ende_gut`). Witness `start_zeuge`.

**Lowering (A5 becomes pure lowering).** An LLVM function with the declared symbol, calling `main`, then the
exit gate with the result, then `unreachable`. The kernel enters a process with a stack pointer that is 16-aligned
on x86_64 while a normal function expects the return-address slot: the function carries LLVM's generic
`"stackrealign"` attribute (accepted on every target, a no-op where the entry convention equals the call
convention). No `naked` function, no per-architecture asm.

**Decisions.**

* **D11 — `-> never` is the exit marker; no new `ends` clause.** The audit proposed a gate marked "process
  exit"; the language already distinguishes a gate that does not return. Exiting a THREAD (16.5) is the same
  form. A second marker would duplicate it.
* **D12 — no `argc`/`argv`.** A program that wants the initial stack's contents reads it through a gate of its
  own; the entry passes nothing. (Compatible extension: `proc … args G` later.)

### 16.5 L4 — thread start, join, stack: `task`

**Surface:**

```ebnf
taskdecl  = "task" ident "{" "pool" ident ";" "spawn" path ";" "end" path ";" "join" path ";"
                             "stack" constexpr ";" "guard" constexpr ";" "}" ;
startstmt = "start" "{" path { "," path } "}" [ "on" ident ] ";" ;      (* `on T` is new *)
```

`spawn` is a user gate with a `stack r` clause (12.1: the clone handoff, `N446`-`N452`) — its number, registers,
trap clause and flags (the Linux `clone` flags are DATA IN THE USER'S GATE, not in the compiler); `end` is a
`-> never` gate that ends the calling THREAD; `join` is an `atomic` carrier whose contract is: the spawn gate
stores a non-zero id BEFORE the child runs and the environment clears it AFTER the child's last step.
`stack`/`guard` are byte constants; the stack comes from pool `P` (16.2).

**Semantics.** None new in G: the thread machine already has spawn and join; the generated runtime template is
a sequence of existing forms: `get(stack + guard)`, `fill` the top part, the spawn gate with the stack top in its
`stack` register, in the child `f(args)` then `end`, in the parent the id; the wait is `await join == 0`; after
it, `drop` the stack. The ORDER the template relies on is `Hardware/Tor/Ende.lean` §2:
`JoinGut` (stack released only after the `await` returned, which returned only after the clear, which came after
the child's end; the child takes no step after its end) gives `kein_kind_nach_gib` (no child step follows the
stack release); defect `join_defekt` (a wait that returned before the clear), witness `join_zeuge`. The
mechanics of the Linux instance (trampoline, join word) are the already proved `SchablonenFaden.lean`
(`trampolin_kind`, `faden_warte_korrekt`); the generic order theorem is its user-gate form.

**What the goal gets.** The named assumption `<task>_join_ok` (clear after end; the child starts on the handed
stack) is part of premise (d)'s runtime assumption `Laufzeit.start`/`.einmal` read as gate contracts instead of
compiler behaviour; stack depth stays NOT CLAIMED (guard = hardware stop, 16.2).

**Lowering (A3, A4 become pure lowering).** `senke_start`, `KLON_FLAGGEN`, `FADEN_REGION` and the continuation
stacks of `stackless.rs` use the pool and the spawn/end gates; the hand-written per-ISA trampolines disappear:
the child path is Gabbro code behind the existing `child` region.

**Decisions.**

* **D13 — the join is a user carrier with a contract, not a futex.** What waits efficiently (a `futex`) is a
  second user gate the `await` may call (`await W == 0 via wait_gate`); correctness never depends on it.
* **D14 — the stack is dropped only after the join.** The child still runs its exit gate on that stack after the
  last user step; releasing earlier is a use-after-release. `kein_kind_nach_gib` is the proof, `join_defekt` the
  reason the clear must come from the ENVIRONMENT (the kernel's `CLONE_CHILD_CLEARTID`), not from the child.
* **D15 — a spawn gate whose environment cannot clear the word** gets no `drop` role in its pool (stack leak, no
  safety loss): `drop` is optional (D1).

### 16.6 The `Code` side (L1/L2)

`Code` is ISA-neutral: no instruction, register or number. A user gate lowers to a CALL of a function number
past the module's own, with a contract. (`Code/Gate/`)

* `Gate.lean`: `GateSpec` (precondition = the gate's `requires`; post-relation over memory/arguments/answer),
  `GateStep`, `StepG := Step ∨ GateStep`, `ReachG`. `step_stuck_am_tor`: the plain step is STUCK at a gate call,
  so the extension is conservative; **`stepG_gdw_step`, `reachG_gdw_reach`: on a module without gate calls
  (`GateFrei`) `StepG` is `Step` and `ReachG` is `Reach` — programs that do not use gates keep their meaning.**
* `GateNeed` — **what a CPU model must provide for user-declared traps**, in the style of `Model/Need.lean` and
  `Conc/MaskNeed.lean`: a CPU state type, `Rel`, and per gate a relation `Trap k d vs x y` ("the CPU runs the
  user's trap sequence of gate `k`, answer to local `d`"). Two obligations, exactly the gate's named assumption:
  `ausfuehrbar` (the sequence runs) and `erlaubt` (every way it ends is an outcome the contract allows,
  delivered as declared). Nothing names an instruction, a register class, a number or the trap text.
  **`gate_verfeinert`: a CPU run of the trap corresponds to a `GateStep`, and the result state holds the result
  configuration.** (`WohlAnruf`: a call that wants a result is a call of a gate that answers.)
* `Provider.lean`: the roles over `Code` memory: `holeSpec` (a fresh BLOCK, nothing written), `fuellSpec` (the
  range gets some content, or the commit is refused with memory unchanged), `gibSpec` (the block ceases to exist;
  every later access is stuck, `gib_haengt`). Facts: `hole_frisch`, `hole_andere`, `fuell_lokal`, `gib_weg`.
* `Bruecke.lean`: the provider's ADDRESS-level contract and `Code`'s BLOCK-level memory describe one world:
  `Entspricht s m rho` (every live block sits at a live reservation, non-empty, injective). `entspricht_hole`,
  `entspricht_gib`, `entspricht_ram` (commit/page-return keep it), and **`entspricht_getrennt`: two distinct live
  `Code` blocks have disjoint address ranges — the block structure's "allocations never alias" is, for memory
  that comes from a provider, a CONSEQUENCE of the provider's freshness contract, not an extra assumption about
  the machine.** Witness `bruecke_zeuge` (two reserves, disjoint), planted defect `aliasing_verweigert`.
* `Zeuge.lean`: a reference CPU meets `GateNeed` (`ref_need`; the contracts of the three roles are inhabited for
  every precondition, `erfuellbar`); a CPU whose `get` trap returns an existing block violates it
  (`schlecht_verletzt`); `tor_zeuge` runs `gate_verfeinert` on a module that calls the `get` gate, all premises
  jointly.

### 16.7 L5 entry stubs, L6 masks and ports

**L5 — entry stubs.** Today the compiler writes complete per-ISA stubs as `module asm`
(`llvm/eintritte.rs`: x86_64 IDT stubs with `fxsave`/`iretq`, aarch64 `VBAR_EL1` table with `eret`/`q0-q31`).
Two user-supplied routes, both named assumptions, no ISA text in the compiler:

```ebnf
entryextra = … ( "conv" string | "stub" string string ) ;
```

* `conv "x86_intrcc"` — the entry function is emitted with the LLVM calling convention the USER names (LLVM
  generates the register save and the return instruction itself). The convention name is data; the trust base is
  LLVM's, named in the manifest (`llvm_cc_<name>`).
* `stub "<save text>" "<restore text>"` — the user's prologue and epilogue text around the generated call of the
  `dispatch` function (a naked wrapper in module assembly).

Exactly one of the two. The register convention the entry already declares (`regs in/out`, `preserves`,
`clobbers`, `stack`) is held by the checker as before; **that a user text honours it is the entry's named
assumption** (`assume` — already compulsory at `entrust`; for `entry` the form `entry … assume stub_ok …` is the
spelling). Machine G is unchanged (`Programm.unterbricht`, `via idt`, the `KernZ` mask layer, 8a.4). What the
proved `SchablonenMetallIdt` template gave (the generated stub is right) becomes an assumption of the user's
text; the checker keeps the shape rules (`H102` and the entry shape checks).
**Decision D16:** both routes, because each is the strongest where the other is not available: LLVM has no
interrupt convention for aarch64 (text route), and for x86/RISC-V the convention route assumes less than
hand-written text.

**L6 — masks.** The interrupt mask is ALREADY an abstract instruction of `Code` (`Instr.imsk`, `Conc/Mask*.lean`,
8a.4) with the named hardware assumption `MaskHw`; the compiler lowered it with a table (x86 `pushfq; cli; popq`,
aarch64 `mrs daif; msr daifset`). Proposal: `mask via xmask;` — an item naming an `asm` function
`xmask(w : u64) -> u64` whose contract is the EXCHANGE (returns the old mask word, installs `w`). `lock … masks irqs`
lowers to `xmask(1)` before the ticket take and `xmask(saved)` after the release (`maskOn`/`maskOff`).
**`Code/Gate/Maske.lean` proves that this gate IS `imsk`:** `maskSpec` has exactly one outcome
(`maskSpec_eindeutig`) and it is the one `stepI` of `imsk` computes (`maskSpec_ist_imsk`, `imsk_ist_maskSpec`), so
`imsk` needs no instruction of its own and `MaskHw` (H1 the cell IS the register, H2 an interrupt only on an
unmasked core, H3 a masked core does not switch threads) stays the gate's named assumption.

**L6 — port space and other non-memory spaces.** `ptr<port, …>` and `device … at port` lowered to x86 `in`/`out`
(`llvm/portraum.rs`; refused on aarch64). Proposal: the SPACE is declared with its accessors, by width:

```ebnf
spacedecl = "space" ident "{" { ( "rd" | "wr" ) typeexpr path ";" } "}" ;
```

`space pio { rd u8 inb; wr u8 outb; rd u16 inw; … }` where `inb : fn(addr : u16) -> u8` and
`outb : fn(addr : u16, v : u8)` are ordinary `asm` functions (named, counted, with effects and their own
`assume`). A register read/write of a device `at pio` lowers to a call of the accessor of its width; a width
without accessor is refused. The words `port`, `mmio`, … remain space NAMES; only `normal`/`mmio`/`dma`/… that
lower to plain load/store need no declaration. **No built-in port space:** a program with `at port` and no
`space port { … }` is refused. Machine G is unchanged: a register access keeps `Block.regRead` and `rzusage`; only
the lowering changes. A CPU without such a space (aarch64) simply declares none.

### 16.8 L7 — register classes

`asm { "…" in { rdi = x } out { rax = r } clobbers { rcx } }` already names registers; what the compiler still
held was the one-letter shorthand (`a b c d S D` → `{rax}`…) and the aarch64 `x`-names. Proposal: **register
names are opaque identifiers** (`RegName`, `Abi.lean`) validated against the `regs { … }` list of the profile
(16.9), emitted as LLVM `{name}`; the one-letter shorthands are REMOVED (no legacy). Operands that need no fixed
register use the pseudo-name `any` (LLVM's generic `r` class, valid on every target). Pure lowering plus a
checker rule (the name occurs in the profile's list: `TorAbi.passtZu`). `defekt_fremdes_register` is the planted
defect (an aarch64 gate on an x86 target).

### 16.9 L8 — targets as data

**Surface:** keyed `profile` entries (12.2 already holds the one hardware profile and `arch x86_64;`):

```ebnf
profileentry = … | "llvm" string ";" | "data" string ";" | "word" constexpr ";"
               | "order" ( "little" | "big" ) ";" | "regs" "{" identlist "}" ";" | "asm" ( "att" | "intel" ) ";" ;
```

`profile { arch aarch64; llvm "aarch64-unknown-none"; data "e-m:e-i8:8:32-…-S128"; word 64; order little;
regs { x0, x1, …, x30, sp, nzcv }; }`. `llvm` is the triple and `data` the datalayout, handed to LLVM unread;
`word`/`order` are what `Code.Conf` is parameterised by; `regs` is the register alphabet of 16.8. A new
architecture is a Gabbro file.

**Model (`Abi.lean`).** `ZielDaten` (triple, layout, word, order, registers) with `gut` (a word `Code` can be
parameterised by: 32 or 64; distinct register names), `conf` (the `Code.Conf` it determines: nothing about it is
fixed to one ISA; `conf_folgt` checks a big-endian 32-bit and a little-endian 64-bit target), witnesses for
x86_64, aarch64 and a 32-bit big-endian target (`ziele_gut`, `schreib_passt`). Planted defect: a 48-bit word is
no target (`defekt_wort_48`). **The consistency of the layout string with `word`/`order` is a CHECKER rule**
(both are user data): a mismatch is refused by name. Lean does not parse the layout; the pointer width and byte
order the checker reads out of it must equal the declared ones.

**Where it goes in the Lean model.** `Kern/Syntax/Profil.lean` keys are `ProfilSchluessel` with `Nat` values;
the textual and list entries need two new entry constructors (`text (key) (val : String)`,
`liste (key) (vals : List String)`) beside `modus`/`frei`. That is a change to `Profil.lean` and its
`bindung_fuegt_nichts_hinzu`-style theorems (every `match` on `AnnahmeEintrag`), not to the statement (`Profil`
is not in `Spec.lean`); it was NOT made in this task: `ZielDaten` is the stand-alone model of the data, and the
`Profil` extension is the first step of the follow-up (16.12).

**Decision D17 — `data` is required, not computed.** LLVM can derive a datalayout from a triple, but an
`opt` run on a module without one assumes the default (64-bit pointers), which is wrong on 32-bit targets; the
program says it, the checker compares it with `word`/`order`.

### 16.10 Neutrality: what the goal theorem gets

`Hardware/Neutral.lean` states and proves that the new forms add NAMED ASSUMPTIONS and nothing else:

* `GabbroZielZ Z` — `GabbroZiel` with one more premise `Z D O` on the oracle (the extra named assumptions); the
  conclusion is word for word `GabbroZiel`'s.
* **`gabbro_ziel_zusatz`: for EVERY family `Z` the statement holds** (more named assumptions never break the
  theorem).
* **`gabbro_ziel_leer`: `GabbroZielZ (fun _ _ => True) ↔ GabbroZiel`** — a program that uses none of the new
  forms has exactly the statement of before.
* `AnbieterAnnahme` — the pool's contract as a premise over the provider log; vacuous for the empty log
  (`anbieter_leer`), closed under prefixes (`anbieter_praefix`), falsifiable by a finite trace
  (`anbieter_verletzt`: two overlapping answers) — which is what a pool's `assume … falsifier …` names.

`gabbro_ziel` stays on `propext`, `Classical.choice`, `Quot.sound`. In the header's list of named hardware
assumptions the compiler's implicit knowledge of Linux disappears and `<pool>_ok`, `<task>_join_ok`, each gate's
assumption, each stub/mask/space assumption appear: all in the user's source, all with falsifiers. Nothing in the
statement is OS-specific.

### 16.11 What would touch the statement: PROPOSAL only (nothing applied)

**Result of the design: no item REQUIRES a `Spec.lean` change.** Reasons, item by item:

* L2, L3, L7, L8: lowering data, resp. existing vocabulary (`-> never`, `nieZurueck`).
* L4: the thread machine already has spawn and join; premise (d)'s text (`Laufzeit.start`/`.einmal`) names the gate
  contracts instead of compiler behaviour — a documentation change in the header of `Spec.lean`, not a type change.
* L5, L6: named assumptions (`Hardware.annahme`), the mask layer's `Spec` diff is the existing proposal 8a.4.
* L1: the pool contract can live in the EXISTING premise (c). The oracle is `Orakel.wirkt : ∀ a, World → Env → World × Int`:
  a function of the WORLD, so a history-based premise (`AnbieterAnnahme` over a log) is not directly a premise on
  the oracle. The language's own way to carry state across calls is a GHOST carrier (`ghost table`, like
  `os.fds`): the pool's live ranges and its resident map are ghost tables declared in the pool's binding, the
  gates' `effects { writes … }` frames separate `get` (writes the ranges, NOT the resident map) from `fill`
  (writes the resident map), `GutO` carries the frame half of the contract ("no RAM before use": `get` writes no
  resident state), and a post-state `ensures` carries the invariant half (`Gut`: reservations pairwise disjoint,
  resident ⊆ reserved) through `AxVertragO`/`AxVertragOP` (precondition = the `requires`). Old-state relations
  ("the live set grows only by the new range") are not expressible in a post-state `ensures`
  (`AxEns : World → result → Bool`) — they hold as the frame plus the invariant.

**If a sharper statement is wanted** (optional, to be reviewed as a diff together with the combined diff of
`PLAN-DYNAMISCH.md` 8a.3):

1. `Deklaration` gets role data with defaults, so the ~84 `Deklaration … where` fixtures stay unchanged (the
   `agruende := fun _ => 0` precedent): `rolle : Ax → Option (Nat × Rolle)` (pool number and role) and
   `seite : Nat → Nat := fun _ => 1`. They are NOT `DeklBasis` fields (the basis holds only table/global data):
   compatible with `Deklaration extends DeklBasis`, and the arena structures parameterised by `DeklBasis` are
   untouched.
2. `HardwareAnnahmen O Q` gets a conjunct `PoolAnn`: along every run the pool's role calls (their answers are the
   oracle's) form a legal provider run, i.e. `AnbieterAnnahme` of `Hardware/Neutral.lean` over the projection of
   the run's gate answers. `gabbro_ziel_zusatz` is the proof that this is a pure strengthening of the premises:
   the old statement follows from the new for every `Z`. A run-level projection needs the answer in the call log
   (`FolgeG` is about the ORDER of calls; whether the call log carries the answers is to be checked): that is the work item.
3. Premise (d) loses `Laufzeit.reserve`/`.commit` as free-standing runtime facts: they are the pool contract.

**Open obligations (named, not hidden).** O-H1: the bridge "ghost-carrier contract ⇒ `PStep`" (declare the
canonical ghost tables as a `Deklaration` fixture and prove each pool-gate transition under frame + invariant is a
`PStep`). O-H2: the run-level projection of 2. O-H3: `Profil.lean` text/list entries (16.9).

### 16.12 Order of the follow-up work, and what stays open

1. **Checker (after the Lean verdicts, CLAUDE.md order):** the new items and clauses in the parser and checker
   (`pool`, `trap`, `proc`, `task`, `space`, `mask`, `conv`/`stub`, profile entries), each with its sentence in
   `saetze.rs`, a poison probe and a positive probe; remove the one-letter register classes and every default.
2. **Compiler:** replace `laufzeit_tor`/`laufzeit_ruf`/`runtime_args`, `arena_bereit`, the `stackless.rs` helpers,
   `senke_start`, `emit_start`, `senke_tor_ruf`/`sammle_tor`, `stapeltor.rs`, `eintritte.rs`, `masken.rs`,
   `portraum.rs`, `assembler.rs` register tables and `ZIEL_X86_64`/`ZIEL_AARCH64` by the user data; port the
   Linux profile into `bibliothek/linux/` (+ a freestanding aarch64 sample) so the four guardian programs still run
   on x86_64 and aarch64 with the same result. Guardian `pruefe-llvm.py` stage 2b then measures the USER's
   gates against the `<pool>_ok` assumption.
3. **Lean:** O-H1, O-H2, O-H3; the user-gate form of `SchablonenFaden`'s join theorem is stated at the level of
   events (`JoinGut`); its derivation from the spawn gate's contract as `GateNeed` over the thread machine is
   open. The `Code`-side bridge for FILL/BACK (the block structure has no resident bit) is the stated limit of
   `Bruecke.lean`: it covers reserve and release, and shows commit/page-return keep the correspondence.
4. **NOT claimed here:** that any user text does what its gate says (the falsifiers do that); stack frames larger
   than the guard; a pool whose `get` answers extents larger than asked beyond what `lenof` declares; the
   layout/word consistency (checker rule, not Lean).
