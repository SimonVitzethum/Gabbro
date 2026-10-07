# AArch64 compatibility of the language model, the goal theorem and the validation plan (agent B)

*Date 2026-10-07. Branch of the worktree `agent-a19c1708f1b0c6cb6`, based on `35a5bd21`. Scope: the
Lean model of the language (`grammatik/` outside `X86/` and `GabbroV/`), `dokumente/`, `messung/`,
`DIRECT-COMPILER*.md`. Nothing here proves anything, and no Lean was built (no Lean file was
changed). Every claim carries file:line. **[read]** = I read the cited text. **[infer]** = my
reasoning from what I read. **[recall]** = from my knowledge of the Arm architecture or the
literature, NOT checked against a file on this machine (the Arm axiomatic model of agents 07-10
did not exist in this worktree yet: `arm/Arm/Mem/` holds only `Event.lean`).*

## 0. Result in six lines

1. **The goal theorem is not x86-specific.** Premise (c) `HardwareAnnahmen` is three
   architecture-free clauses (`GutO ∧ RegLokal ∧ AxVertragO`, `Spec.lean:1677-1678`), (d) is a
   loader/runtime statement (`Spec.lean` `Laufzeit`), and the weak-memory leg `SchwachX`
   (`Spec.lean:2200`) is stated over the C11-style view machine W, not over TSO. x86 enters
   `Spec.lean` only in prose: M7 (`:1012-1013`), the target/QEMU remarks (`:1014-1015`, `:1051`),
   and one parenthesis (`:1090`).
2. **The x86-TSO part is entirely in the BRIDGE, which is not built for any target.** The only
   TSO-to-W/GX material is under `X86/` (`X86/Bruecke/TsoGxRefine.lean:1-20`, `TsoRunInduction.lean`);
   it covers a lowered fragment without LOCK/shared atomics and says so.
3. **W is a promise-free C11 view machine, so TSO is a subset of W, but Arm is NOT a subset of W**:
   Arm allows load buffering of plain `LDR`/`STR`, W has none (`Sicht.lean:36-38`). The Arm bridge
   therefore should not be "Arm execution to W run" but **"Arm execution to GX run by a DRF argument"**
   (section 3). This works because GX answers every shared-atomic read freely and the Lean checker
   already refuses unguarded plain payload hand-off (`Spec.lean:855-861`).
4. **What silently relied on TSO** (section 3.4): the `publishes`/`awaits` payload hand-off the Rust
   checker accepts and the Lean checker refuses (uncertified programs); the plan sentence "release/acquire
   need no fence on TSO"; the unfalsifiability of ordering assumptions on x86 (`Spec.lean:1089-1091`);
   device/DMA ordering; spin hints; LL/SC progress; code-patching coherence.
5. **x86-only items in the Lean tree outside `X86/`** are few and all in the legacy C-backend /
   runtime-template layer: `SysReg` and the `write` ABI (`Kern/Semantik/Syscall.lean:25-58`), the
   clone witness, six `Bausteine/Schablonen/*` files, port I/O in `CSpeicher.lean`, and the profile
   witness `arch = x86_64`. The core semantics (`Kern/`, `Logik/`, `Nebenlaeufigkeit/`, `Speichermodell/`,
   `Zielsatz/`) contain no x86 instruction, register, MSR, `cpuid`, paging or port I/O.
6. **One doc edit made** (commit `60810efd`). Nothing else was safe to change: the remaining x86 text
   is accurate x86 text.

## 1. Inventory

Search method: `grep -rciE` for `x86|TSO|intel|amd64|cpuid|MSR|4-level|pml4|store buffer|rflags|mfence|sfence|xchg|rsp|rax`
over `grammatik/Grammatik` minus `X86/` and `GabbroV/`; 19 files hit (the rest of the tree is clean).
Then the documents. Classes: **G** generic, **R** x86-flavoured but replaceable, **X** x86-only.

### 1.1 Lean outside `X86/` and `GabbroV/`

| Item | Where | Class | What it presumes / what Arm needs |
|---|---|---|---|
| Goal statement, premises (a), (b) | `Zielsatz/Kern/Spec.lean:1-60`, `:2288`, `:2311` | G | nothing architectural. [read] |
| (c) `HardwareAnnahmen` = `GutO ∧ RegLokal ∧ AxVertragO` | `Spec.lean:1677-1678`; prose `:866-880` | G | frame/contract of foreign code and devices. No ISA. [read] |
| (d) `Laufzeit` (loader, starts, once) | `Spec.lean:1693-1704` (structure at `:1693`); prose `:900-945` | G | "thread creation is the runtime's" (`:944`). No ISA. [read] |
| `SchwachX` (weak machine adds no behaviour outside shared atomics) | `Spec.lean:2194-2206`; block `:484-537` | G at the statement; **R at the justification** | The statement is a theorem about W. What links W to a CPU is the five assumptions (section 2). [read] |
| W: promise-free timestamp view machine of RC11, `Ordnung = entspannt | freigabe`, `seq_cst` as release/acquire | `Speichermodell/Maschine/Sicht.lean:18-38`, `:60-64` | G (C11 level) | no store buffer, no x86. Does **not** contain load buffering (`:36-38`). [read] |
| DRF proof `schwach_ist_g` | `Speichermodell/Maschine/DRF.lean:1-45` | G | uses only lock acquire/release views and thread-locality; "NOTHING about `atomic` carriers beyond what `fuss` demands" (`:20-22`). [read] |
| GX: `RufSchrittGX` presents any memory outside... at the shared atomics `Tg` | `Speichermodell/Atomar/AtomarLauf.lean:33-40` | G | `(∀ c, ¬ Tg c → TraegerGleich σ M.speicher c)`: at `Tg` the presented `σ` is unconstrained. [read] |
| `Programm.unterbricht`, `KernPlan`, `KernHaltE`, `masks irqs` | `Spec.lean:548-602`, `:591`, `:1225` | G in the model; **R at the realisation** | "interrupt handler enters only where no other thread of its core holds a `masks irqs` lock". Arm: PSTATE.I (DAIF) masking. The leg is `unterbricht`-driven, but the exporter sets `unterbricht` from `entry … via idt` (`dokumente/OFFEN.md:1126-1127`) -- the trigger word `idt` is x86 vocabulary (Rust side; `H102` now accepts any `via` word, `OFFEN.md:1158-1164`). [read] |
| Keyed profile modes incl. `arch`, `speichermodell` | `Kern/Syntax/Profil.lean:24-30`; witness `arch = x86_64` `:408-411`, `:474-476` | G (key), X (witness only) | `val : Nat` code; `zeugeArch = 1`. Arm needs a second code, no model change. [read] |
| `SysReg` = x86_64 GPRs; `schreibAbi` = `write` number 1 in `rdi,rsi,rdx`, answer `rax`, clobbers `rcx,r11` | `Kern/Semantik/Syscall.lean:25-58` | **X** | The comment says "`aarch64` stays sealed, so there is no second register file" (`:25-26`): stale after 2026-10-07. Arm Linux: `svc #0`, number in `x8`, args `x0-x5`, answer `x0`, the Linux syscall numbers differ (`write` is 64). `SysAbi` itself (`:30-44`) is generic; only `SysReg` and the table are x86. **R** (replace/extend `SysReg`). [read; Arm Linux ABI = recall] |
| Clone witness: `rdi/rsi`, answer `rax` | `Kern/Semantik/CloneHandoff.lean:101-106`, `:132-135` | X (witness) | witness over `SysReg`; moves with it. [read] |
| `CTy.size`/`natLay` "x86-64 SysV" layout | `CBackend/Semantik/CSpeicher.lean:71`, `:290-292`, `:1915` | **R** | natural alignment + tail padding; LP64. Same rule on AAPCS64 for the emitted types (recall, not measured). Doc twin fixed in commit `60810efd`; Lean comments untouched. |
| Port I/O in the C memory model (`portOf`, `portIn`, `portOut`) | `CBackend/Semantik/CSpeicher.lean:837-850`; `dokumente/C-SPEICHERMODELL.md:160-163` | **X** | Arm has no port space. Device access is MMIO (Device memory). |
| Templates `start.nolibc` (`and $-16,%rsp; call main; ud2`, SysV entry alignment) | `Bausteine/Schablonen/SchablonenOhneLibc.lean:11`, `:23`, `:28`, `:133-169` | **X** (legacy C backend) | Arm: SP 16-aligned at all times (hardware check when enabled), return address in `x30`, no push by `call`. The proved arithmetic does not transfer. [read; Arm = recall] |
| Templates `tor.trampolin`, `tor.kind` (`syscall`, `rax==0` child, `andq $-16,%rsp`, `call *`) | `Bausteine/Schablonen/SchablonenFaden.lean:10-11`, `:51-60`, `:70-80`, `:199-220` | **X** | clone returns 0 in the child in `x0` on Arm; stack alignment rule differs. |
| Templates metal thread switch (`ldmxcsr`, `fldcw`, six pops, `ret`, `rsp`) | `Bausteine/Schablonen/SchablonenMetallFaden.lean:27-28`, `:258-290` | **X** | callee-saved set, FP control (`FPCR`/`FPSR`) and the switch differ. |
| Template metal IDT gate | `Bausteine/Schablonen/SchablonenMetallIdt.lean:19`, `:27` | **X** | Arm: exception vector table `VBAR_ELx`, 16 entries of 0x80 bytes (recall). |
| Other metal/module templates | `Bausteine/Schablonen/SchablonenMetall.lean`, `...MetallSperre.lean`, `...Modul.lean` | not read in full | mention `vector`/IRQ; classify when the metal runtime is ported. Not checked. |
| Parser tests with `rax/rdi/arch x86_64` | `Parser/ElementTiefProben.lean` (28 hits), `Parser/AnweisungProben.lean` (13), `Parser/UebersetzeProben2.lean` (5), `Korrespondenz/Korpus/Korpus59.lean:18`, `:537`, `Parser/ElementTief.lean:387-404` | G (syntax tests with x86 sample text) | test text only. |
| Float kernel (`Bausteine/Gleitkomma/Gleitkomma.lean`) | whole file; NaN cases `:72-79`, `:216-237` | G | IEEE binary formats, finite-only user values. No x87/SSE in Lean. The x86 residue is in the assumption doc, below. |
| `Speichermodell/**`, `Nebenlaeufigkeit/**`, `Logik/**`, `Kern/**` (except `Syscall.lean`), `Nichtinterferenz/**`, `Zertifikat/**` | whole directories | G | zero hits of the search patterns. |

### 1.2 Documents

| Item | Where | Class | Note |
|---|---|---|---|
| Direct-compiler target decision "x86-64 bytes", T4 "x86 instructions, byte decoder, per-access x86-TSO" | `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md:1-6`, `:50`, `:103`, `:126` | X by decision, now superseded by `ARM-PLAN.md` | **§§0, 1, 4, 5 are mostly architecture-neutral in structure** (parse fidelity, untrusted backend + Lean validator, loaded mapping, relocation re-decoding, W/GX reuse, no `sorry`). Only T4, §2 (instruction families) and the TSO sentences are x86. Not edited: the replacement wording is the coordinator's decision. |
| W/GX reuse "do not assume the existing W is a proved model of x86" | `PLAN-UEBERSETZUNGSVALIDIERUNG.md:100-110` | G sentence | says exactly the right thing for Arm too. |
| "Ordinary coherent RAM uses the selected x86-TSO profile; MMIO, DMA, cache attributes require their own named semantics" | `PLAN-UEBERSETZUNGSVALIDIERUNG.md:126-128` | R | on Arm the same split is needed and matters more (Device vs Normal memory ordering). |
| Goal plan header "proving the per-access x86-TSO bridge" | `dokumente/PLAN-ZIELSATZ.md:5-6` | X by decision | header only. |
| `OFFEN.md` O19 (handlers), O26 (lock orders), O31/O32 (targets, metal), O25 | `OFFEN.md:1120-1135`, `:1445-1470`, `:1545-1612`, `:1371` | O26/O25 G; O19 G+R; O31/O32 X | O32 is the QEMU-x86 bare-metal runtime (Multiboot, ACPI MADT, INIT-SIPI-SIPI, LAPIC, `sti;hlt;cli`: `OFFEN.md:1576-1583`). |
| `DIRECT-COMPILER-DESIGN.md` §5 (TSO refinement, LOCK CMPXCHG/XADD, MFENCE/SFENCE, "release/acquire need no fence on TSO"), §3-4 (ISA table, SSE2), §6 (SIMD) | `DIRECT-COMPILER-DESIGN.md:397-436`, `:290-395` | X | §§1, 7-12 (trust chain, optimisation with premises, fast compile/validate, measurement, portability) are generic; §12 (`:778-813`) already says no OS/ISA dependency in the semantic core. |
| `DIRECT-COMPILER.md` | 988 x86/TSO/Intel hits | X (progress record) | history; not touched. |
| `GLEITKOMMA.md` assumption list: item 2 "on x86, in SSE2, never on the x87 stack"; items 6-7 mention MXCSR/FPCR | `dokumente/GLEITKOMMA.md:97-98`, `:106-111` | item 2 X (replaceable: AArch64 has no extended precision, `FLT_EVAL_METHOD==0`), 6-7 R | Arm instance: `FPCR` RNE, `FZ=0`, no contraction (compilers contract by default on AArch64 GNU mode: **[recall]** -- the profile key `fpKontraktion` already exists, `Profil.lean:24-26`). NaN payloads are already outside the assumption (`:114-116`), which is the part where x86 and Arm differ most. |
| `SPRACHE.md` §4: `assume c11_release_acquire arch x86_64 ...` **and** `arch aarch64` both written | `dokumente/SPRACHE.md:2045-2054` | G (both architectures exist as syntax) | falsifier `probe_mp_aarch64`, `probe_mp_x86`. |
| `SPRACHE.md` hardware catalogue A9-A22 (`cli/sti`, `hlt`, `pause`, `in/out`, `rdmsr/wrmsr`, `cpuid`, `rdtsc`, `fxsave`, `clflush+sfence`, `lfence/mfence`, TSO/C11, `swapgs`, Multiboot, linker) | `SPRACHE.md:2285-2298` | X | each has an Arm analogue: `msr daifset/clr`, `wfi`, `yield`/`wfe`, none (no port space), `mrs/msr` system registers, ID registers (`ID_AA64*`), `CNTVCT_EL0`, no `fxsave` (SIMD state is plain registers), `DC CVAC`+`DSB`, `DMB/DSB`, the Arm memory model, none, boot protocol. The catalogue style (one row per construct with a falsifier) is generic. |
| `PLAN-HARDWARE.md`: page tables, `invlpg`, `outb`, Caprock has both archs | `PLAN-HARDWARE.md:218-231`, `:408-420`, `:465-486`, `:2587-2619` | X for the examples, G for the structure | It already records that the `DSB` ordering between a normal-memory descriptor and a Device-memory doorbell is an Arm-only hazard (`:218-221`) and that `assume` needed an `arch` parameter (`:224-228`; since fixed by B40, `SPRACHE.md:2056-2057`). The W⊕X hierarchy counter-example (`:465-486`) has an Arm analogue [recall]: descriptor attributes `APTable`/`XNTable`/`PXNTable` are hierarchical too. |
| `C-SPEICHERMODELL.md` | `:4-5` (header), `:160-165` | header X, layout R | layout sentence edited (commit `60810efd`). |

## 2. The hardware assumptions: how general, and what is the Arm instance

### 2.1 The list as the header states it

`Spec.lean` has two lists. **THE ONE ASSUMPTION LIST** (`:866-945`) holds the (c) and (d) entries, and
the section "Not premises, but assumptions of the reading" (`:1138-1181`) holds five named assumptions
of the memory-model reading. NOT CLAIMED is at `:1360-1470`.

| Assumption | Statement | Phrased for any architecture? | Arm instance |
|---|---|---|---|
| (c) `GutO` | an axiom (foreign body) writes only its frame, keeps held locks, leaves accesses in the trace (`:867-870`) | yes | same; foreign code is `extern fn`/`asm`. |
| (c) `RegLokal` | a register read answers from the device's declared carriers (`:871-880`) | yes; **but** "register/MMIO read" must be a read of Device memory with the ordering the binding declares | Device-nGnRE etc. accesses are ordered among themselves per Device region (recall); the named restriction (a register that changes on its own) is the same. |
| (c) `AxVertragO` | axiom answers meeting their declared `ensures` (`:881-897`) | yes | same. |
| (d) `Laufzeit.lader/.start/.einmal/.reserve/.commit` | loader, thread creation, arena reservation/commit (`:898-960`) | yes; the text names Linux gates and QEMU-x86 images only as examples | same text, other gate bodies. |
| (1) W over-approximates RC11 for the orders the emitter writes, at G's step granularity (`:1145-1152`) | **a C11 statement** | yes at the C level | For the direct backend it is replaced by "W (or GX) covers the target" (section 3). |
| (2) the compiler and the hardware implement C11 atomics and orders as specified; `exchange` lowers to ONE RMW (`:1153-1157`) | C11 statement | yes, but the direct backend deletes the C compiler from it; then it is the bridge, a theorem | Arm lowering: relaxed → `LDR/STR`; acquire → `LDAR` (or `LDAPR`); release → `STLR`; `seq` → `LDAR/STLR` ; `acq_rel` RMW → `LDADDAL/CASAL/SWPAL` (LSE) or `LDAXR/STLXR` loop. [recall] |
| (3) every lock primitive `_nimm` is acquire, `_gib` release (`:1158-1168`); own primitives checked by `N481-N483` (`OFFEN.md:1445-1470`), driver locks by POSIX | yes | The runtime's ticket lock is written with explicit C11 orders (`laufzeit/metall/metall.h:68-77`), `laufzeit/sperre.gab:17-21` declares `NEXT relaxed`, `NOW acquire` and advances with release. These map to `LDAR`/`STLR` on Arm, and `LDAR`/`STLR` are RCsc, stronger than C11 acquire/release, so the assumption still holds. [infer] |
| (4) carriers are the locations (`:1169-1170`) | yes | needs natural alignment and single-copy atomicity per carrier width. Arm guarantees single-copy atomicity for aligned accesses up to 8 bytes (16 only with FEAT_LSE2) [recall]. The language has `aligned N` (`N570`, `AGENTS.md` §7 table), but no checker rule yet ties carrier width and alignment to the target. |
| (5) unrecorded reads (foreign code, devices, register reads, `awaits` visibility) see G's last executed write (`:1171-1181`) | yes in text | **the one most exposed to Arm**: a device or DMA engine does not see a normal-memory store without a barrier (`DMB`/`DSB`), and Device writes do not order against Normal writes (`PLAN-HARDWARE.md:218-221`). On x86 this is `sfence`/`clflush` (`SPRACHE.md:2294`). Must become a named assumption per binding, with the barrier sequence in the user's binding code. |
| NOT CLAIMED "the C and the hardware", "W is exactly RC11" | `:1363`, `:1374-1376` | yes | add "W is not Arm-complete (no load buffering)". |
| `KernPlan` (handler entered only where no other thread of its core holds a masked lock) | `:548-602`, `:1225`, `:1366-1371` | yes | `PSTATE.I` set while a `masks irqs` lock is held; entry to and return from an exception are context-synchronisation events (recall). A runtime/binding fact. |

### 2.2 Verdict on (c)

(c) as stated needs **no change** for Arm. What changes is the content users supply: contracts of
Device-memory access routines and DMA publication (assumption 5). That is the language's job
(user logic), consistent with "the OS is user logic, never an assumption" (`AGENTS.md` §3).

### 2.3 The weak-memory leg: what exactly must be proved for Arm

**Proposal only; `Spec.lean` is not edited.**

What the Lean statement says is `SchwachX` (`Spec.lean:2194-2206`): from every W state reached from the
weak start over `M0`, every W step is a GX step on the presented memory, and the presented memory is G's
outside the shared atomics. The proof (`DRF.lean`) shows the **view of the thread at every read has reached
the newest message** of every carrier the thread reads that is not a shared atomic: thread-local carriers by
single ownership, guarded carriers by the lock's view (`DRF.lean:28-37`). Therefore the memory-model facts used are:

* (F1) a lock take is an acquire of the lock's last release, a release publishes the holder's whole view;
* (F2) per-location coherence: a thread never reads older than what it has seen at a location (`corr_verboten`, `Sicht.lean:45-47`);
* (F3) a write by the single writer of a thread-local carrier is seen by that thread's later reads (read-own-write);
* (F4) nothing else: in particular no ordering of plain data through atomics (refused, `Spec.lean:855-861`),
  and no RMW atomicity claim is needed for GX because GX leaves every shared-atomic read free
  (`AtomarLauf.lean:33-40`). [infer; GX definition read, the consequence for RMW not proved here]

Arm instance, **to be proved over the Arm model in `arm/Arm/Mem/`** (relation names are the Arm ARM
B2.3 ones, **[recall]**; verify against agent 07's definitions):

1. *Internal visibility* (F2, F3): `acyclic(po-loc ∪ co ∪ rf ∪ fr)` gives per-location coherence. Direct.
2. *External visibility* `acyclic(ob)`, `ob = obs ∪ dob ∪ aob ∪ bob` (F1): a lock release is `STLR`/`LDADDL`
   (L), the next take reads it with `LDAR` (A): `rfe` from a release write to an acquire read, plus the `bob` edges
   `po; [L]` and `[A]; po`, put every access before the release (`ob`) before every access after the take.
   So: *for any two accesses ordered by the lock hand-off, the first is `ob`-before the second.* Needs
   the RCsc/RCpc choice stated: `LDAPR` gives only RCpc `[A_Q]; po`; (F1) needs only that, W is
   RCpc-like, so both work.
3. *Atomicity* `empty(rmw ∩ (fre; coe))` -- only if the RMW atomicity of W (`SchrittW.rmw`,
   `Speichermodell/Maschine/MaschineW.lean:123-170`) is wanted. GX does not need it for the goal [infer].
4. *Single-copy atomicity* of each carrier access: aligned, natural width (assumption 4).
5. *DRF theorem on the Arm model*: if all `ob`-unordered conflicting non-atomic pairs are absent in every
   SC execution of the validated image, then every Arm execution is explained by an SC execution (the memory
   read of a non-atomic carrier is the `co`-latest write). **This is the theorem W provides at source level
   (`schwach_ist_gX`) and what the Arm bridge must provide at machine level.** It is a published-class
   result for properly synchronised Arm programs [recall; I did not find or check a Lean statement]; in this
   repository nothing proves it yet.

**The load-store reordering point.** The sentence in the task is right: Arm reorders load→store and
store→store of plain accesses, which TSO forbids. Two different facts must not be mixed:

* W already allows *more* reordering than TSO: relaxed message passing is reachable in W (`mp_rlx_erlaubt`,
  `Sicht.lean:44-47`). So TSO ⊂ W; this is why the x86 plan could target W. [read]
* W lacks **load buffering** (`Sicht.lean:36-38`: "no promises, hence no load buffering, which RC11 forbids
  as well"). **Arm permits load buffering of plain loads and stores** unless a dependency or barrier orders
  them [recall]. So an Arm execution of two threads `r1=x; y=1 || r2=y; x=1` with relaxed atomics can return
  `r1=r2=1`; W cannot. Consequence: *"every Arm execution is a W run" is false in general* for relaxed
  accesses, and cannot be repaired without promises (Promising-Arm style) in W. The Gabbro goal does **not**
  need it: relaxed shared atomics are answered freely by GX (all values of the type, the rely of
  `NutzerPflichtA`), and plain data is only communicated under locks. So the bridge should go **directly
  Arm → GX** (the plan allows "or directly to GX", `PLAN-UEBERSETZUNGSVALIDIERUNG.md:103-105`). [infer]
* Related, **to verify**: compiling C11 relaxed atomics to plain `LDR/STR` on Arm is accepted practice; its
  correctness proofs (IMM, Podkopaev et al. POPL 2019) are, as far as I remember, stated against a C11 variant
  that allows load buffering, not against RC11's `po ∪ rf` acyclicity. So the old assumption (1) ("W
  over-approximates C11 (RC11)") is *not* a statement about Arm hardware via C11. [recall; unchecked]

**Proposed text for a future `Spec.lean` header change (comment only, for a reviewed diff):**
assumption (1) for a direct Arm image reads: *"every execution the Arm model admits for the validated image
is covered by a run of GX (not necessarily of W): reads of non-shared-atomic carriers return G's value, reads
of shared atomics return a value of their type."* Assumption (2) is replaced by that theorem. Assumptions
(3)-(5) keep their text with the Arm lowering named. NOT CLAIMED gains: "W is not an over-approximation of Arm
(load buffering)", "LL/SC retry bounds (below)". Do not edit before the bridge exists.

## 3. The bridge

### 3.1 What it was for x86 (read)

`PLAN-UEBERSETZUNGSVALIDIERUNG.md:100-122` and `DIRECT-COMPILER-DESIGN.md:397-436`: per-access forward simulation
x86-TSO → W (`x86 behaviours ⊆ W`), then `schwach_ist_gX` into `SchwachX`. Built part: `X86/Bruecke/*`, e.g.
`TsoRunInduction.lean:1-25` (a finite trace of store, committed read, forwarded read, drain steps yields a W run;
no LOCK/RMW, no shared atomics), `TsoRmwBridge.lean:1-22`, `TsoGxRefine.lean:1-20` (conditional refinement to GX
with the DRF/checker premises of `schwach_ist_gX` explicit). The TSO-specific structure is the **store buffer**:
a read either forwards from the own FIFO or reads committed memory; "the stale-view case is stated honestly: no
global value for an unflushed store" (`TsoReadBridge.lean:11-12`). That per-step operational shape does not exist
for Arm.

### 3.2 What it becomes for Arm

The Arm model of agents 06-10 is axiomatic (candidate executions with `po, addr, data, ctrl, rf, co, rmw`:
`arm/Arm/Mem/Event.lean:46-58`), not a step machine. So the bridge is a **theorem about candidate executions**:

> For a validated image `I` and an Arm candidate execution `X` of `I` that satisfies the axioms, there is a GX
> run `ρ` (of the unit's thread machine) such that every plain-carrier read of `X` returns the value `ρ` has
> there, every shared-atomic read returns a value of its type, and the call log / observable sequence of `X`
> equals `ρ`'s.

Proof architecture (inferred; nothing of it exists):

1. **From the axiomatic execution to an interleaving.** Choose a linear extension of `ob ∪ po` restricted to
   one chosen representative, or argue by reduction: because of the checker's footprint discipline each G step
   touches only (thread-local ∪ lock-guarded ∪ shared-atomic) carriers. Between a take and a give of a lock, the
   guarded carriers are only touched by the holder; `ob` orders the holder's accesses after the previous holder's
   release and before the next take. Linearise the sections as units at their lock hand-offs. That is the
   Lipton-style grouping the plan already demands ("an instruction sequence cannot be treated as indivisible
   merely because it represents one model operation", `PLAN-UEBERSETZUNGSVALIDIERUNG.md:117-119`), but on Arm
   the instructions *inside* a section may be performed in any `ob`-compatible order -- the proof must show
   that nobody outside can tell, which holds because the only observers are `ob`-ordered after the release.
2. **Per-access mapping.** Table of the order words (section 3.3).
3. **Read values.** A read of a non-atomic carrier returns, by internal + external visibility and (1)-(2), the
   `co`-latest write that is `ob`-before it, which in the linearisation is the last write: G's value. This is
   `liest_neueste` (`DRF.lean:140`) in axiomatic form.
4. **Shared atomics:** nothing to prove beyond type-correctness of the value (alignment, width).
5. **Stutter/progress:** failed `STXR`, spurious `LL/SC` failure and spin loops stutter; progress is the next item.

Which Arm relation corresponds to which part of W / GX:

| W / GX / language construct | Arm model relation | Note |
|---|---|---|
| W history per location, timestamp = modification order (`Sicht.lean:18-30`) | `co` | per-location total order. |
| W read "any message at or above the thread's view" (`Lesbar`, `Sicht.lean:133`), `corr_verboten` | internal visibility `acyclic(po-loc ∪ co ∪ rf ∪ fr)` | the coherence half. |
| Thread view; lock view; "take joins lock view, release joins thread view" | `rfe` from a release write to an acquire read + `bob` (`po;[L]`, `[A];po`) inside `ob` | RCsc by `LDAR/STLR`; `LDAPR` is RCpc. |
| `ordVon`: tables and plain globals `entspannt`; atomic by declaration (`MaschineW.lean:82-84`) | plain `LDR/STR` | on Arm plain accesses are unordered except `po-loc`, addr/data/ctrl dependencies. |
| `SchrittW.rmw` (`exchange` writes directly above the message read; `Speichermodell/Maschine/MaschineW.lean:123-170`) | `rmw` + atomicity axiom; `LDADD/CAS/SWP` (LSE) or `LDAXR/STXR` pairs | LL/SC exclusivity: a failed `STXR` leaves no write. |
| GX shared-atomic read: `σ` unconstrained at `Tg` (`AtomarLauf.lean:33-40`) | any `rf` source, including load buffering | covers what W cannot (LB). |
| `ZeitAbX`/time and `fortschritt` | no memory relation | wait-freedom is not promised; see 3.4 (6). |
| language `publishes`/`awaits` (`SPRACHE.md:1647-1676`): `publishes` forces ≥ release, `awaits` ≥ acquire, `relaxed` only for `publishes nothing` | `STLR`/`LDAR` (or `LDAPR`) with the visible-place set as the payload | a lowering rule, a checker-side V-rule (`V009`, `V010`), and a `ob` argument. |
| language `atomic … acquire|release|seq|relaxed` (`SPRACHE.md:1335`) | `LDAR/STLR` / `LDAPR` / `LDAR+STLR` (RCsc covers `seq`) / `LDR/STR` | the emitter's current map is in `Sicht.lean:6-14` (C11 level). |
| lock `_nimm`/`_gib` | take: `LDADDA`/`LDAXR+STXR` on `next`, spin `LDAR` on `now`; give: `STLR` | `laufzeit/sperre.gab:17-21`, `laufzeit/metall/metall.h:68-77` are explicit-order C; the direct backend must pin the same orders. |
| thread start/join | `spawn` = thread creation by the runtime (`Laufzeit`); join word cleared with release, read with acquire (`Spec.lean` M6, `:1008-1012`) | a runtime obligation: `STLR` of the join word, `LDAR` by the waiter, plus whatever the OS gives for `clone`/thread creation. |
| `seq` (modelled as release/acquire; no SC-order fact claimed, `Spec.lean:1374-1377`) | `LDAR/STLR` are RCsc, stronger than needed | sound; DMB ISH full barriers never needed by the language as emitted (no `atomic_thread_fence`, `Sicht.lean:12-13`). |
| `masks irqs` | `DAIFSet` on `#2`-style masking [recall] | not a memory relation; context-synchronisation event on exception entry/return. |

### 3.3 Where `publishes`/`awaits`/`atomic` order words map to instructions

| Source word | Store | Load | RMW (`exchange … update`) |
|---|---|---|---|
| `relaxed` / no word | `STR` | `LDR` | `LDADD`/`SWP`/`CAS` without suffix, or `LDXR`+`STXR` |
| `acquire` | (stores of an acquire atomic are relaxed in the emitter, `Sicht.lean:6-9`) `STR` | `LDAR` (`LDAPR` ok) | `…A` form (`LDADDA`, `CASA`) |
| `release` | `STLR` | `LDR` | `…L` form |
| `seq` | `STLR` | `LDAR` | `…AL` form (`LDADDAL`, `CASAL`) |
| `publishes {payload}` (store) | forces ≥ `STLR` | | |
| `awaits {payload}` (load) | | forces ≥ `LDAR`/`LDAPR` | |
| `publishes nothing` / no `awaits` | free (`STR`) | free (`LDR`) | |

[the right-hand instructions are recall; the left-hand column is `SPRACHE.md:1335`, `:1673-1676` and `Sicht.lean:6-14`]

### 3.4 Constructs whose guarantee silently relies on TSO

Checked against the files, not against a running binary.

1. **`publishes`/`awaits` with an unguarded plain payload.** The Lean checker refuses such programs (`Spec.lean:855-861`: "the
   publish/await hand-off of an UNGUARDED payload across threads is refused, not covered"; `OFFEN.md:1371` O25),
   but the Rust checker accepts them under the V-rules (`SPRACHE.md:1647-1700`), and they are then UNCERTIFIED
   (`Spec.lean:70-88`). Their guarantee ("here `FP_STATES[owner]` is readable", `SPRACHE.md:1657-1660`) is exactly
   release/acquire message passing. The only memory model fact it needs is MP-RA, which x86 gives with plain `MOV`
   (`DIRECT-COMPILER-DESIGN.md:422-424`: "Release/acquire need no fence on TSO (plain aligned MOV already orders)").
   **Arm: lowering `publishes`/`awaits` to plain `STR`/`LDR` is wrong.** There is no Lean statement guarding this
   for either target; for Arm the direct backend must emit `STLR`/`LDAR` and the bridge must prove it.
2. **The unfalsifiability of ordering assumptions on x86**: `Spec.lean:1089-1091` ("any run on x86 could FALSIFY a
   dropped ordering (it cannot -- x86 gives acquire and release away"). The falsifier `probe_mp_x86`
   (`SPRACHE.md:2047-2050`) can never fail. On Arm the message-passing litmus with relaxed accesses is observable
   in practice [recall], so `probe_mp_aarch64` becomes a real falsifier. Good news, and a reason to run them on
   Arm hardware, not only on a model.
3. **Device and DMA publication** (assumption 5, `Spec.lean:1171-1181`; `PLAN-HARDWARE.md:218-221`;
   `SPRACHE.md:2294` A17 `clflush + sfence`): ordering between Normal memory and Device memory needs `DMB`/`DSB`
   on Arm; the hardware does not give it. A binding that is correct on x86 without a barrier is wrong on Arm.
4. **`accumulates … per cpu`** (relaxed cells, merged on read, `SPRACHE.md:1444`) and `rdtsc` as an order
   (A15, `SPRACHE.md:2290`): not TSO-reliant for the goal; the merge reads cells without a snapshot on both
   architectures. `rdtsc` → `CNTVCT_EL0` needs an `ISB` for ordering [recall]; the language already says
   "never an order".
5. **Spin hints.** `pause` (A11, `SPRACHE.md:2286`) is "semantics-free". Arm `yield` is a hint too; `wfe` needs a
   matching `sev` or an exclusive-monitor event, so a `wfe`-based spin is a *different* construct with a
   progress assumption (`SPRACHE.md` `progress assume holder_releases`, `:2648`).
6. **LL/SC progress.** Source `exchange` is emitted as one RMW and CAS loops "retried until it succeeds"
   (`Spec.lean:1153-1157`). With LSE instructions (mandatory in Armv9-A) it is one instruction, as on x86. With
   `LDXR/STXR` a loop's forward progress depends on the architecture's constrained-loop rules and on no
   intervening memory access [recall]. The goal claims no waiting bound (`Spec.lean:1360-1361`; the x86 plan
   says the same, `DIRECT-COMPILER-DESIGN.md:419-424`), so no claim breaks; cost transfer (`ZeitAb`) must not assume a bounded
   retry count for LL/SC.
7. **Self-modified or relocated code.** `PLAN-UEBERSETZUNGSVALIDIERUNG.md:19-27` demands that the loaded mapping
   equal the validated image "including any relocation performed at load time". On x86 the instruction cache is
   coherent with data stores for the executing core; on Arm a patched instruction needs `DC CVAU; DSB; IC IVAU;
   DSB; ISB` before it is fetched [recall]. Validation must either refuse load-time code patching or model the
   maintenance sequence; "the bytes in memory equal the validated bytes" is not enough.
8. **Unaligned and wide accesses.** x86 plans rely on "aligned 32/64-bit MOV are single-copy atomic"
   (`DIRECT-COMPILER-DESIGN.md:403-407`). Arm gives the same for aligned natural widths (not for unaligned
   exclusives and acquire/release: they fault) [recall]. Same rule; the Arm profile row is a different table.
9. **Float NaN payloads**: outside the assumption already (`GLEITKOMMA.md:114-116`); Arm default-NaN mode (`FPCR.DN`)
   and propagation differ from x86 SSE2. No claim is lost, but the user-visible bit pattern of a NaN differs.
10. **`seq_cst`** is modelled as release/acquire and no SC-order claim is made (`Spec.lean:1374-1377`), so the
    store-buffering outcome is allowed; on Arm `LDAR/STLR` are RCsc and forbid it. Sound direction.

Not TSO-reliant (checked): the lock legs, thread-locality, `exchange` atomicity in the goal (see 2.3), the
interrupt-handler leg, time (`ZeitAb` counts G steps, `Spec.lean` `ZeitAbX`).

## 4. Small edits

| Commit | File | Change |
|---|---|---|
| `60810efd` | `dokumente/C-SPEICHERMODELL.md:165` | "x86-64 SysV rule" → "natural-alignment LP64 rule (x86-64 SysV; AAPCS64 gives the same ... not measured here)". |

Not edited, and why:

* `grammatik/**` comments (`Syscall.lean:25-26` "aarch64 stays sealed", `CSpeicher.lean:71,292,1915`): stale-looking
  comments, but editing Lean files forces a rebuild of dependents in the shared slot; they are comment-only and
  can ride with the first real Lean change in those files. Suggested wording for `Syscall.lean:25-26`: replace
  the sealed remark with "an AArch64 register file is a second type, added when the Arm Linux profile is written".
* `Spec.lean`: not touched by instruction (proposal in 2.3).
* `PLAN-UEBERSETZUNGSVALIDIERUNG.md`, `PLAN-ZIELSATZ.md`, `DIRECT-COMPILER-DESIGN.md`: they state decisions that
  `ARM-PLAN.md` supersedes; their re-labelling is the coordinator's, not a "generic called x86" case.

## 5. What this review did not do

* No Lean build. All Lean statements were read, none re-proved; `#print axioms` was not run.
* `Bausteine/Schablonen/SchablonenMetall.lean`, `SchablonenMetallSperre.lean`, `SchablonenModul.lean`,
  `SchablonenArena.lean`, `SchablonenT5*.lean` were listed but not read in full.
* Rust (`crates/`) was not reviewed (outside the area), except that its x86 vocabulary appears in the cited
  `OFFEN.md` rows (`via idt`, `arch x86_64`, `linux_x86_64` bindings `Spec.lean:1051`, syscall numbers in
  `bibliothek/linux/linux.gab`).
* The Arm statements marked [recall] are from memory of the Arm ARM and the literature and must be checked
  against agent 07's model and the Arm text before anything is built on them. The biggest one: **the DRF theorem
  on the Arm axiomatic model (2.3 item 5)** and **the load-buffering consequence (2.3, W cannot be the target)**.
