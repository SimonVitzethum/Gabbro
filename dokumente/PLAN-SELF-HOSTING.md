# PLAN-SELF-HOSTING — checker and compiler written in Gabbro, computing in Gabbro

*Simon, 2026-10-25. Nothing here is started. It supersedes `PLAN-LONG-RANGE.md` §3 (the versions of 2026-10-18 and of the
morning of 2026-10-25 are in git). The back-end decision of 2026-10-18 stands: LLVM stays the back end; the self-hosted
compiler emits LLVM IR.*

## 0. The rule of this plan

**Lean specifies and proves; Gabbro computes.**

* **Lean** holds the model (machine G, `AkzeptiertX`, the lowering `Code/Lower`, the generator's definitions, the
  adequacy theory of `CHECKER.md` §16) and the proofs. Its kernel checks proofs. Lean evaluates nothing on the trust
  path: no `#eval`, no `lake exe` driver, no kernel evaluation of a test run. The one exception is stage 0 of the
  bootstrap (§2), used to start and to cross-check, never to produce a result that a theorem rests on alone.
* **Gabbro** does every computation: checking, compiling, generating the test sets M, N and R, running them, comparing,
  counting coverage, searching witnesses for open cells, validating IR. Each of these is a Gabbro program, accepted by
  the checker, and proved against its Lean specification with GabbroV.
* The Lean drivers that compute today (`gen-abdeckung`, `gen-zellen`, `gen-fein`, the Lean pipeline as a driver, the
  `Code` validator as an executable) are replaced by Gabbro programs and deleted when those reach parity
  (CLAUDE.md: no legacy).

## 1. The programs

| Program | Computes | Proved against (Lean spec) |
|---|---|---|
| `gpruef` | the checker: lex, parse, elaborate, the ten components of `AkzeptiertX` | `pruefSpec src` := the Lean pipeline (`uebersetzeAllg`) then `AkzeptiertX` |
| `gkomp` | the compiler: the front end shared with `gpruef`, then LLVM IR | `kompSpec p` := `Code/Lower` of the elaborated program, refinement `Code/Refine` |
| `ggen` | the test sets: M (valid, `Gutes`), N (refused by exactly component `c`, `Schlechtes c`), R (text-level refusals), by exact size, and their printed texts | the Lean generators `genGueltig`, `genBad c` with their soundness and completeness theorems (`Gen/Erzeuger/Gueltig.lean`), the printer `Gen/Druck` |
| `gabdeck` | coverage: the cells (`Gen/Abdeckung/Zellen`) and fine cells (`Gen/Fein`) each program covers, the open cells, the greedy cover, the witness search | `zellenStimmen`, `feinZellen_uF`, `deckung` |
| `glauf` | the campaign: runs `gpruef`/`gkomp` over M ∪ N ∪ R, compares each verdict with the label and each IR with `gvalid`, writes the ledger | the comparison predicates of §4 |
| `gvalid` | per-program IR validation: the IR `gkomp` produced against the lowering of the model | the `Code/Refine` decision procedure |

Every one of them is an ordinary Gabbro program: accepted by `AkzeptiertX` (so `gabbro_ziel` gives memory safety, race
freedom, contracts), proved terminating, deterministic and correct with GabbroV.

## 2. Bootstrap: stage 0 translates, a verified x86-64 runner runs (Simon, 2026-10-26; changed 2026-10-28)

| Part | Written in | Runs on | Does |
|---|---|---|---|
| stage 0 | Lean, the package `stage0/` | native (Lean executable), once per program | translates an accepted Gabbro program into the IR `S0IR` (§2.1); runs nothing |
| the runner | x86-64 machine code, its bytes proved in Lean (§2.2) | x86-64, Linux | runs `S0IR`: every run is a run of the thread machine over GX (proved); raw Linux syscalls for IO; Gabbro threads on OS threads |
| stage 1 | full Gabbro | the runner | `gpruef` and `gkomp` (the checker and the compiler of §1) |

* **Decisions (Simon, 2026-10-28).** There is no interpreter written in Gabbro. Lean stage 0 only translates Gabbro into
  `S0IR`; it does not run programs. `S0IR` runs on a small x86-64 runner whose machine code is formally verified (the
  precedent is seL4's binary verification). No LLVM, no C and no unvalidated code is on the bootstrap path: it would
  void every guarantee, and stage 0 would have no reason to exist. The runner is x86-64, not AArch64: the available
  AArch64 machine is 5-10 times slower, and the AArch64 model `arm/` is far from complete.
* **Stage 0 therefore needs the whole language:** the Lean front end over the full syntax (shared with GabbroV's
  source level), and the forms its subset gate refuses today (atomic statics, the open region, device registers) once
  the model carries them.
* **Speed target:** the runner runs `gkomp` compiling its own source (≈ 500 000 lines) in under one hour, with the
  optimisations that `gkomp` itself performs. Measured base of the Lean-run stage 0 (2026-10-28, `54a9b3d7`): about
  93 us per input byte on the upper-casing probe, roughly 10^5 machine steps a second, every step under one world
  lock, plus a full replay. Needed: about 3 * 10^5 - 10^7 steps a second for `gkomp` without optimisations, about
  3 * 10^7 - 4 * 10^8 with `-O3`-class optimisations done by `gkomp` itself (estimates, 2026-10-28).
* **Syscalls are raw.** A Gabbro `syscall` item is executed as that Linux system call (`syscall` instruction in the
  runner). Named assumption: the system call does what its Gabbro contract says (the boot oracle of the hardware
  assumptions, `HardwareAnnahmen`).
* **Threads are OS threads.** Each Gabbro thread runs on its own OS thread of the runner (raw `clone`, raw `futex`;
  no Lean runtime inside the runner). Named assumptions: the system calls keep their contracts; the CPU implements
  the x86-64 model for the instructions the runner uses.
* **Stage 1 is the goal of §1.** `gkomp` run by the runner compiles its own source; the compiled `gkomp` compiles itself
  again (fixpoint), and the diverse double compilation compares the runner's run with the native binary.

**State of stage 0 (2026-10-26, `stage0/Stage0/`).** Today `stage0` still RUNS programs; that path is the reference
until the runner runs `gkomp`, then it is deleted (no legacy) except what the proofs of §2.1 reuse (`Schnell/`, the
replay theorem). `stage0` is a Lean executable (`cd stage0 && lake build`;
`stage0 [--schritte N] [--passes N] PROGRAM.gab`). It runs the stages of `uebersetzeAllg`, refuses what `AkzeptiertX`
refuses (`akzeptiertU`), refuses device registers and the open region (its provider is not yet fresh in the model),
and accepts a foreign body only as a `syscall` gate bound on this machine (`Tor/Bindung.lean`). The run is on the thread
machine `RufMaschineG`: `Schritt/` computes one step of a thread together with its rule (`Zug`, all 84 rules of
`RufSchrittG`), `Lauf/` starts `main` on thread 0 and the program's roots (`entry`, `concurrent`, `start { .. }`) on
threads 1, 2, .. (`anfaengeVon`, `startG`). `Tor/LaufIO.lean` runs it in two phases: every machine thread on an OS
thread of its own, each step under one futex world lock, every question answered by the raw system call outside the
lock (`c/syscall.c`, the booked wall); then the schedule is replayed under the log of the observed answers.
`nachspiel_ist_lauf`: every output is read from a machine reachable by `RufSchrittG` from the start machine under the
oracle that answers with the observed results, in which thread 0 has ended. A program without gates gets its input
in `io.ein`/`ein_len` and leaves its output in `io.aus`/`aus_len` (`boot`, kernel-evaluable; witness `Zeuge.lean`).
The probes `stage0/proben/` run in stage 7 of the Lean guardian. Built since: the fast machine (`Schnell/`, a normal
form proved to simulate the thread machine), an array memory written in place, the program tabulated once
(`Lauf/Memo`). Open: (a) `S0IR` and the lowering (§2.1); (b) the runner (§2.2); (c) the provider freshness repair of
the open region in the model; (d) the front end and the subset gate over the whole language; (e) the Rust exporter
`lean_g.rs` still writes `aschreibt := false` for every gate and refuses a gate's `writes`, which the Lean front end
and the model accept.

### 2.1 The stage-0 IR `S0IR` — design (2026-10-28)

**Purpose.** Stage 0 lowers an accepted G program ONCE into an `S0IR` image; the runner of §2.2 executes it. `S0IR`
is not a new semantics: it has a small-step semantics in Lean, proved against machine G, and every run of the runner
is proved to be a run of the thread machine (`RufSchrittG`) over GX, so the goal theorem applies to it unchanged.
Built from the syntax of `Kern/Syntax/Syntax.lean` (64 `Expr`, 46 `Stmt`/`Block`, 21 `Endblock` formers) and the
outcomes of `Kern/Semantik/Semantik/T1.lean`.

**The governing rule: the IR is as SMALL as possible** (Simon, 2026-10-28). Every handler of the runner is machine
code that must be proved, at 20-30 times the lines of the code itself. So whatever can be expressed by a sequence of
IR instructions is LOWERED in Lean (cheap to prove) and never added to the runner: locks, budgets, reasons, switches,
unsigned and wide arithmetic, floats, byte buffers, contract checks and stops are all lowerings. The price is speed
(more IR instructions per G step, §2.1.8); the runner stays a few hundred machine instructions.

**Proof budget** (Simon, 2026-10-28): the runner's proofs (x86-64 subset, handlers, loader, threads, `runner_tso`)
may take up to 60 000 lines of Lean; 80 000 is the hard limit. Inside that budget an instruction is added to the
base set only for speed that a measurement asks for, and only if it needs no new hardware assumption (§2.1.3, speed
set).

#### 2.1.1 Two modes

Machine G checks at run time: `requires` at every call (`Logik.vorbedingung`), `ensures` and the owed invariants at
every return (`nachbedingung`, `invariante`), loop invariants at every pass boundary (`schleife`), `state` pre-states
(`vorzustand`), float ranges (`bereich`). An invariant over a table is a loop over the whole table at every return.
* **Certified mode (the mode `gkomp` runs in).** The image comes with the program's certificate: its user logic
  (`NutzerPflichtA`) proved with GabbroV. Exactly the checks whose failure the certificate excludes are not emitted;
  theorem `ir_erase`: under the certificate the erased program has the same runs. Which stop kinds a certificate
  excludes is read from `NutzerPflichtA`, never assumed.
* **Checked mode.** Every check G makes is emitted, as ordinary IR code. For diagnosis and for programs without a
  certificate. An `old(T.slots[i].f)` whose index depends on the result saves the whole field at entry.
  The implemented IR fragment currently captures one `old` occurrence per function in immutable frame
  header slot 3, after `requires` and before the body. Parameters start at slot 4. Postcondition arithmetic,
  equality, strict comparison and Boolean conjunction/disjunction read the saved word; every normal return
  still checks the contract (stop 102 on failure). Globals and table cells with literal indices, including
  range widening, are supported. Additional occurrences and nonliteral table indices are explicitly refused.
  G evaluates an `oldS` index with the current world and supplied environment while reading its cell from the
  entry world; capturing a result-dependent cell therefore remains open rather than freezing that index.
  Numeric source `old(global)` uses the local `stage0/Stage0/Senke/Ausdruck/Old/Source.lean` bridge:
  shared elaboration resolves names and types, the bridge restores the existing G `oldG` node at its source
  occurrence, and the complete `AkzeptiertX` runs on that final program before image generation.
Budget stops are never erased: `abstieg` (call depth), `fortschritt` (`forever` passes) and `retry` exhaustion are
outcomes of G for some budget and stay exact.

#### 2.1.2 Memory and values

* **One flat memory of 64-bit words at real addresses.** The runner maps the image at a fixed address; tables (one
  array of words per field), statics, open tables, the thread stacks and a staging area for system calls all lie in
  it at addresses the lowering fixes. An address is the machine byte address of a word (a multiple of 8), so a load
  is one machine load and a pointer handed to the kernel is just a word.
* **Values** are words: `int lo hi` in 64 bits as two's complement, beyond 64 bits as `k` limbs (the lowering counts
  them per program); `bool` 0/1; `opt n` `-1` or the index; `sum cs` a tag word and a payload word; `why n` its number;
  `never` no word; `fnptr n` the function's number; `ptr t rw` NO word (`thru`/`assignThru` name the table statically,
  `D.tabNr n = some t`: the pointer is a capability without run-time content); `ref t` the cell's address in the open
  table; `arr τ n` consecutive words; `str n` a length word and one word per byte; `fl lo hi` the binary64 bit
  pattern — float arithmetic is SOFT-FLOAT, lowered to integer IR code proved against the kernel IEEE model, so the
  runner has no float instruction and the runner needs no FPU assumption.
* **Ghost, not in `S0IR`:** the trace `spur`, the call log, entry worlds `s0`, the run log, marks (`advances`,
  `retires`), `breaking`. The simulation relation reconstructs them, as the compact trace of `Schnell/` does.

#### 2.1.3 The instructions (24 opcodes)

Every operand `a b c d` is a slot of the current frame (a word at `fp + 8·a`); `k` is a signed 32-bit immediate, `L` an
instruction index. Fixed encoding: four little-endian 32-bit fields (opcode, three operands), 16 bytes; no
variable-length decoding to prove.

| # | Instruction | Meaning | x86-64 |
|---|---|---|---|
| 1 | `const d k` | `d := k` (sign-extended; wider constants by `shl`/`or`) | `MOV` |
| 2 | `mov d a` | `d := a` | `MOV` |
| 3-5 | `add sub mul d a b` | modulo 2^64 | `ADD SUB IMUL` |
| 6-7 | `div rem d a b` | `Int.tdiv`/`tmod` (G's `sdiv`/`srem`; `div`/`rem` on operands ≥ 0 agree); the typing rules exclude 0 and the overflowing quotient | `CQO; IDIV` |
| 8-10 | `and or xor d a b` | bitwise | `AND OR XOR` |
| 11-12 | `shl shr d a b` | `b` in 0..63 (typing), `shr` logical | `SHL SHR` |
| 13 | `lt d a b` | signed `<`, result 0/1 (unsigned: `xor` both with 2^63 first) | `CMP; SETL; MOVZX` |
| 14 | `eq d a b` | `=`, result 0/1 | `CMP; SETE; MOVZX` |
| 15 | `ld d a` | `d := M[a]` | `MOV` |
| 16 | `st a b` | `M[a] := b` | `MOV` |
| 17 | `lea d k` | `d := fp + 8·k` (the address of a frame slot, for frame aggregates and system-call buffers) | `LEA` |
| 18 | `jmp L` | jump | `JMP` |
| 19 | `brz a L` | jump if `a = 0` | `TEST; JZ` |
| 20 | `call a k` | call function number `a`; the callee frame starts at slot `k` of this frame (the arguments and the hidden parameters are already there); return address and caller `fp` saved in the callee frame's first two words | -- |
| 21 | `ret` | back to the caller (results are left in the callee frame's result slots, which the caller reads) | -- |
| 22 | `cas d a e n` | atomically: if `M[a] = e` then `M[a] := n`; `d := ` old `M[a]` | `LOCK CMPXCHG` |
| 23 | `sys d a` | Linux system call: number in slot `a`, six arguments in `a+1 … a+6`, result in `d` | `SYSCALL` |
| 24 | `spawn a k` | a new OS thread (`clone`) whose first frame is at address `k`-slot `a` and which calls the function number stored there; the thread ends by `exit` | `SYSCALL` (clone) |

**Speed set (10 opcodes, planned, 2026-10-28).** Each replaces a frequent sequence of the base set by one handler and
uses only integer x86 instructions already in the subset, so it adds handler proofs, not model:

| # | Instruction | Replaces | x86-64 |
|---|---|---|---|
| 25 | `ldx d a i` | `d := M[a + 8·i]` (a table or aggregate element: `shl`, `add`, `ld`) | `MOV r, [a + i*8]` |
| 26 | `stx a i b` | `M[a + 8·i] := b` | `MOV [a + i*8], r` |
| 27 | `addi d a k` | `add` with an immediate (indices, counters, budgets) | `ADD`/`LEA` |
| 28-30 | `blt a b L`, `beq a b L`, `bne a b L` | compare and branch (every loop and condition) | `CMP; Jcc` |
| 31 | `ltu d a b` | unsigned compare (limbs, unsigned ranges) | `CMP; SETB; MOVZX` |
| 32 | `jtab a L0 n` | jump to `L0 + a` through a table of `n` entries (`onTag`, `onWhy`, a compiler's `match` over tags; `a < n` by `ir_typed`) | `JMP [table + a*8]` |
| 33 | `copy d a n` | `n` words from `a` to `d`, non-overlapping (aggregates and strings by value) | `REP MOVSQ` |
| 34 | `mulhi d a b` | the high word of the unsigned 128-bit product (wide ranges, hashing) | `MUL` |

The base set is complete without them: the lowering uses a speed instruction where present and the base sequence
otherwise, and `ir_sim` covers both.

The runner checks nothing
at run time: the image is the lowering of an accepted program, and the typing invariant `ir_typed` (every slot holds
a value of its static type, every address computed for a load or store lies in its carrier) is a theorem, not a
check. The x86-64 subset the runner needs is therefore about 20 instructions.

#### 2.1.4 What is lowered instead of built in

**Measured float fragment (2026-10-29):** binary64 literals, comparisons and narrowing are lowered.
`floatOf (.lit n)` reuses literal materialisation, with a generic proof for every `Int` (including rounding
and overflow) and the same range stop as G. `floatRoundL` is an integer-only nearest-even fragment, proved
against `rundeInt` when `remainder < denominator < 2^63`; it avoids doubling the remainder and supports an
arbitrary unsigned quotient, with a modular word result. This is not yet a complete soft-float operation.
`floatMagnitudeL` now extracts the unsigned magnitude with generic IR simulation, including `-2^63`.
Pure input-code composition is shared with rounding. `floatRoundShiftL` rounds an unsigned magnitude after
a right shift of 0–62 bits, with generic IR simulation against `rundeInt` and G's normal-path `normQ`.
It retains the full remainder and allows a carry out of the significand. Dynamic `floatOf` still needs
exponent discovery, left scaling, packing and block simulation. `floatShiftJamL` aligns an unsigned word with
generic IR simulation: discarded bits become a sticky low bit, exactly the nonzero remainder modulo
the alignment power. Counts at least 64 saturate, including counts with the sign bit set, despite the
IR's masked shifts. `add/sub` still need the full guard/sticky alignment argument against G, cancellation,
normalisation, all signed-zero/infinity/NaN rules (including G's payload choice), and the final range test.
`mul/div` remain refused: multiplication needs a proved wide significand product and exponent combination;
division needs a proved quotient/remainder algorithm with sufficient precision for final nearest-even
rounding. Both additionally need special cases, normal/subnormal packing, range checks and block simulation.
No arithmetic operation is accepted on the strength of the rounding fragment alone.

* **Expressions:** every G operation becomes the instructions above in G's evaluation order; `neg` is `sub 0`, `not`
  is `xor 1`, `le` is `lt` swapped and negated, `ne` is `eq` and `xor 1`; unsigned compare by flipping the sign bit;
  wide ranges by limb sequences (carry = unsigned `sum < a`, 64×64→128 by 32-bit halves); a slot access
  `T.slots[i].f` is `shl i 3`, `add base`, `ld`; `getBytes`/`putBytes` are `n` loads/stores with shifts
  (`bytesZuZahl`); `forallSlots`, `existsSlots`, `reaches` (the fuel of `kette`), string operations and aggregate
  copies are loops or unrolled `ld`/`st`; `wenn`/`eng` and the boolean connectives are branches; `old` (checked mode)
  is a value saved at entry; floats call soft-float routines (one IR function per operation, proved once).
* **Control:** `ite`, `onOption`, `onTag`, `onWhy`, `narrow`, `check`, `floatNarrow` and `switch` become `brz` chains;
  `traverse` an index loop, `retry` a counter loop, `forever` a counter set to the run's `passes`; `leave`/`next`
  jumps.
* **Calls and reasons:** a callee writes a status word (0 = value, `r+1` = reason `r`) beside its result;
  `bindCallElse` and the fallible gates branch on it. `callInd` is `call` on the slot holding the function number.
* **Budgets:** the remaining call depth is a hidden parameter: the caller passes `depth - 1`, the callee's entry tests
  it and at 0 stops in `abstieg f` exactly where `rufAt 0` does. The runner gives the first frame the run's depth and
  reserves stacks so that this depth of the largest frame fits: stack exhaustion cannot happen.
* **Cost proof status:** `ZeitAb` bounds G-machine own steps using `kostenTief`;
  `passes` bounds semantic loop attempts. Neither counts emitted S0IR instructions.
  `Schleifen/Counted.lean` counts canonical `Runner.IR.step` executions exactly,
  erases to `Star`, and composes segment counts, including callees and nested loops.
  `Schleifen/CountedLoop.lean` connects instruction counting to the real counter
  test, decrement and backedge, with a local counted body contract. Its inhabited
  `whole_loop_zeuge` instance uses the emitted `foreverCode` with a true invariant
  and empty body: arbitrary representable remaining fuel costs at most `6 * fuel + 1`
  instructions from the live header to the budget-stop entry. Initialization and
  the terminal stop are outside this bound. No unrolling or CPU latency claim is
  involved. General declaration-derived callee bounds, hardware assumptions and
  propagation through all accepted statement families remain OPEN.
  `CalleeCostCertificate.call` now connects the checked expression-body
  instruction declaration to the actual call opcode, entry-memory ABI writes,
  source-derived execution and return. Its bound is `declared f + 1`, retaining
  the callee frame agreement and encoded result; a loaded nonempty witness
  jointly satisfies these premises under canonical `Runner.IR.Kern`. This is
  not yet the full `callC` argument/depth/status protocol or a `BlockCost` call
  constructor. Source-certificate-derived nested/whole-forever bounds remain OPEN.
  `Schleifen/StatementCost.lean` derives normal assignment-block costs recursively
  from accepted `lowS`/`lowB` results and expression certificates, including lexical
  binding, environment updates, world preservation and protected slots. Its loaded
  nonempty body witness discharges all simulation premises jointly. The terminal
  `lowEnd .cons` composition also retains counts through a returning/stopping child.
  Global stores now compose value-expression cost, the actual address constant and
  the actual store opcode; the recursive tail receives the updated world. A loaded
  three-instruction witness changes a global function pointer. Other world-store
  forms, calls, branch outcomes and nested loops still require recursive cost rules.
  `EndCost.sound` now integrates normal returns into the recursive terminal
  certificate, alongside reason returns, assignment and binding. Original
  parameter environments and the saved snapshot survive recursive prefixes;
  normal returns derive their count from the result expression and actual
  `lowEns` certificate, including result and status ABI writes. A loaded
  nine-instruction witness combines binding, assignment and normal return.
  `lowFun_counted` now composes the full successful emitted function from the
  depth guard, recursively certified requires plus its guard, actual snapshot,
  parameter relocation and `EndCost.sound` body (including actual ensures and
  return ABI). The sum is checked against the declared instruction bound;
  neither whole-body execution nor whole-body cost is assumed. Its loaded
  twelve-instruction witness relocates one parameter before normal return.
  `ArgsCost.fullCall` composes actual argument certificates and the four
  call-entry instructions with that full function contract. Its loaded
  seventeen-instruction witness executes a real argument, callee parameter
  relocation and normal return. Both generic contracts apply to the recursive
  certificate fragment, not all accepted source forms.
  `normalRet_counted` now retains the exact same counted endpoint for the
  encoded result, successful status slot, frame agreement from ABI slot 2,
  writable frame and preservation of every initially represented world under
  the existing layout separation. `retC_counted` carries its frame agreement
  through ensures and the actual return tail; the source result prefix composes
  that agreement. No determinism premise is needed: `Kern.ans` remains an
  arbitrary relation, and both properties follow from one constructed execution.
  The loaded normal-return witnesses now check result/status and agreement on
  that same returned memory. `EndCost.Post` now computes the result/status
  obligation from the recursive source certificate. `EndCost.sound` carries
  that obligation, writable frame, saved caller PC/frame and represented world
  through assignment and binding on its single counted execution. Reason
  returns retain their zero status at that endpoint too. The loaded recursive
  nine-instruction witness jointly checks result, status, frame, caller header
  and world. `lowFun_counted` and `ArgsCost.fullCall` retain the same source
  certificate postcondition through the full function and actual call entry,
  together with frame/world agreement, the callee frame, caller header and
  world. The call contract also retains the writable caller frame; its
  agreement permits changes only above the caller's free slot or in the world.
  No independent
  semantic endpoint or complete execution premise is introduced.
  Still OPEN: `EndCost` branching and call constructors; propagation of the
  encoded return value/status and frame/world agreement for the same returned
  memory into `BlockCost.call`; source-certificate-derived nested-forever
  instantiation. The bounded returning execution alone does not discharge those
  continuation premises.
  `RecursiveEndCost.sound` now proves execution of the actual recursive terminal
  certificate by induction on its source tree: `call` and `bindCall` descend into
  `P.rumpf`, with decreasing call depth and the same returned-value index.
  Guard/requires, snapshot and parameter relocation are counted before applying
  the genuine child induction hypothesis; the continuation uses the identical
  returned memory. Assignment, binding and branch prefixes transport the frame,
  world, entry parameters, saved caller header and `Umf`.
  `RecursiveTerminalProbe.sound_zeuge` jointly instantiates these premises with
  argument/result 37, distinct caller addresses and a bound of 23 S0IR steps.
  This does not yet replace the `EndCost` premises in `recursiveBlockCost`:
  its call/bindCall integration, a nested-forever cost constructor and the
  whole-source bound remain OPEN.
  These instruction counts use the existing canonical `Kern` semantics; source
  passes and G steps remain separate units, with no hardware-latency conversion.
  The generic instruction bound for arbitrary actual `foreverCode` is still OPEN: invariant,
  body/callee, header, backedge and exit bounds must be connected to the lowering
  simulation and then related to the source budget. `forever_runtime` alone proves
  uncounted simulation. A finite count or a fixture's result is not that bound.
* **Stops:** a G stop (`logik …`, `hardware …`) is `sys exit_group(code)`, the code naming the constructor and its
  argument. What was observed up to then is a prefix of a run of the thread machine, which is a run.
* **Locks:** a lock word in memory. `locks L` = a `cas` 0→1 loop with `sys futex(WAIT)` on contention, the body, and on
  EVERY exit edge of the body (normal end, `leave`, `next`, `ret`, a reason, a stop) the release: `cas` to 0 and `sys
  futex(WAKE)` when a waiter is marked. The rank order (`H006`) excludes wait cycles. Checked mode adds the lock
  invariant checks G makes at a lock move.
* **Atomics:** on x86-TSO a plain `ld` is an acquire load and a plain `st` a release store; a sequentially consistent
  store and `exchange` are `cas` loops (a failed `cas` is zero G steps, the successful one is G's step); `publish` is
  the payload stores then the release store; `awaits` an acquire load. `runner_tso` maps them to GX.
* **Gates:** a `syscall` item lowers to: pack its buffer words into bytes in the staging area (`shl`/`or`, eight
  bytes a word, little-endian), `sys`, unpack the bytes the call wrote into the declared field only, hold the result
  against its type (outside it: the stop `hardware (annahme a)`, as G's `einpassen`).
* **Open tables:** each open table is a reserved address range (the runner's start maps it with `MAP_NORESERVE`); a
  `ref` is an address in it; the provider (a `syscall` item whose contract says fresh) is a bump pointer in that
  range, lowered: fresh by construction, and the end of the range is the provider's "no memory" reason (OOM stays
  user logic).
* **Threads:** the roots (`main`, `entry`, `concurrent`, `start { .. }`; G spawns nothing at run time) are started by
  `spawn` at the beginning of `main`'s lowered prologue.
* **Refused by name** (a Linux user process): device registers (`regRead regReadElse regWrite transition`), interrupt
  handlers (`via idt`), a `fnptr` answered by a gate (`Orakel.zeiger`), and any form the model does not yet carry.

**Implemented aggregate fragment (2026-10-29).** `Stage0/Senke/Ausdruck/Aggregat/` extends `Enc` and
`lowE_ok` without changing G, frame slots or the one-word call convention. Empty arrays use zero; singleton
arrays recursively reuse their element word, including signed integers, function pointers and nested singleton
arrays. All four array expression forms are proved. Strings with a static maximum of zero or one byte use zero
for empty and `256 + byte` for nonempty, so a zero byte remains distinct from empty. Literal, length,
concatenation, byte indexing (zero outside the actual length, including negative indices), equality,
lexicographic order and `strWeit` truncation are proved. Constructors and reads refuse larger aggregates,
including unsupported element aggregates inside singleton arrays. Concatenation requires the sum of the static
maxima to be at most one; string indices must fit the existing signed-word fragment. The surface front end still
refuses mutable aggregate locals; G fixtures cover replacement and truncation directly. These are representation
limits of this lowering, not restrictions of G. Packing several small elements would extend the fragment while
preserving the ABI; unrestricted aggregates need multiword frames/calls or a proved allocation and lifetime
discipline for indirect immutable values. `AggregateProbe.simulation_zeuge` supplies concrete nonempty code,
code memory and a writable disjoint frame jointly; surface probes and the exported G fixture exercise the runner.

#### 2.1.5 The runner's part, in full

Load the image (`open`, `read`/`mmap` at its fixed address, the reserved ranges), set up the first frame, then the
dispatch loop: fetch 16 bytes at `pc`, jump through a table indexed by the opcode, run the handler, continue. That,
the 24 handlers and `spawn`'s thread entry are all the machine code there is.

#### 2.1.6 Semantics and theorems

* In Lean: `S0IR` syntax, the image format, a small-step semantics (a thread machine over the flat memory, the same
  oracle questions as G: the `sys` answers).
* `ir_lower_ok`: lowering is total on accepted programs, or refuses by name; `ir_typed`: the typing invariant;
  `ir_decode`: decoding the image gives the lowered program; `ir_sim`: one `S0IR` step is zero or more fast-machine
  steps (`Schnell/`), related states agree on memory, held locks and answers; `ir_budget`; `ir_erase`; `ir_softfloat`:
  each soft-float routine computes the kernel IEEE model; `ir_parallel`: a parallel run equals an interleaving of the
  thread machine (from `RennfreiBis` and the lock discipline).
* **The lowering's output is checked, not trusted.** Stage 0 runs as compiled Lean (Lean compiler, runtime, the
  toolchain's C compiler); the image carries a hash, and either the kernel evaluates `lower P = image` on the pinned
  program or an `S0IR` checker written in Gabbro does it on the runner. Measured before chosen.
* Witnesses: the probes of `stage0/proben/`, a program with every former, a multithreaded probe with locks and
  atomics; planted mis-lowerings (a wrong slot, a missing release on a `leave` edge, a dropped check in checked mode)
  must fail.

**`ir_parallel`, the route (2026-10-29).** Built on `ir_sim` (one thread against `rufAt`, done for the sequential
forms and the gates) and on `AgreeW` (a statement of a thread changes its own stack and the world, nothing else; the
world lies above every stack):
1. *Threads in the image*: `main` and every root (`concurrent`, `entry`, the roots of `start`) on a stack of its own;
   the start code spawns the roots (`spawn`, frames below the world), a root thread ends with `exit`.
2. *Locks as mutexes*: a lock word per lock above the world; `locks L { .. }` takes it by `cas` (wait: `futex`) and
   gives it back on every way out (`leave`, `next`, `return`); G's `nimmt`/`gibt` steps match.
   Design (2026-10-29): three words per lock in a sync region above the world -- owner, count, waiters. The owner is
   the holding thread's number + 1 (computed from `fp`: `(fp - sb) / st + 1`, `sb` the first stack, `st` a stack's
   size), so a lock is re-entrant, as G's `offen` is a multiset (`rufAt` lets a thread take a lock it holds). Take:
   the owner is me -- count + 1; else `cas owner 0 -> me` (count := 1), on failure waiters + 1, `futex_wait` on the
   owner word with the seen owner, waiters - 1, again. Give: count - 1; at 0 `cas owner me -> 0` (a locked operation:
   the store of the release cannot pass the read of the waiters under TSO), and `futex_wake` only when waiters is
   not 0. One thread alone never waits and never wakes. A statement keeps the sync words (`AgreeW` exempts only the
   world); `leave`/`next` out of `locks` give the locks taken inside the loop before the jump, so their targets allow
   exactly those words to change; `ret` inside `locks` cannot be typed (`Λ ~ ende`). The precondition `SyncAt` --
   the exact state of every lock word for the locks the thread holds -- holds where a `locks` starts.
3. *Atomics* (`publish`, `awaits`, `exchange`) as `cas`/loads on their cells, against GX.
   Done for one thread (2026-10-29): `publish` is the store of an assignment to a global (a release under TSO);
   `awaits` a load (acquire under TSO), with the named assumption `SichtOK` (A10: the oracle never answers G's
   `sichtbarkeit` stop); `exchange` a `cas` loop (`exC`: the old word into the variable's slot, the new value,
   `cas` from old to new, again when the word read back differs), proved where one thread alone finds the old
   word still there (`exch_ok`, `awaits_ok`, also at a function's end). Probe `proben-ir/atomar`.
4. *The structural half*: a thread state of the runner's machine at a statement boundary corresponds to a thread state
   of `RufSchrittG` (the residue `.ende`/`.dann`, the call stack as the chain of frames).
5. *The reduction*: in a run of the runner's machine every thread's code since its last boundary ran on its own stack
   and on world cells no other in-flight statement writes -- if one did, the two statements would be a race of G from
   a reachable machine, against `RennfreiBis` (carrier-level, lock-ordered; atomics apart). So a run is a run with
   whole statements, each one `ir_sim`'s forward step, made unique by the determinism of a thread's run.
6. *The statement*: every observation of the runner's process (under SC, then TSO by `runner_tso`) is a run of the
   thread machine from the start machine, or ends in a stop of a check (101-105, 110+) after a prefix that is one;
   premises: the goal theorem's (a)-(d), `TorOK`.

#### 2.1.7 Size

Lean: syntax, semantics, image 2 000 - 4 000 lines; lowering with `ir_lower_ok`/`ir_typed` 5 000 - 10 000 (it now
carries locks, reasons, wide integers and gates); soft-float with `ir_softfloat` 2 000 - 5 000; `ir_sim`, `ir_budget`,
`ir_erase` 5 000 - 12 000; `ir_parallel` 3 000 - 8 000.

#### 2.1.8 Speed

Base set: a G step becomes about 2-10 IR instructions (a slot read alone is three); a handler is 2-5 machine
instructions plus the dispatch (one load, one indirect jump); about 10^8 - 2 * 10^8 IR instructions a second per core.
With the speed set: about 1.5-4 IR instructions per G step, about 2 * 10^8 - 3 * 10^8 a second per core. Times about
20 for the threads of a parallel `gkomp`, `gkomp -O3` (about 10^11 - 1.5 * 10^12 G steps) takes about 5 min - 1.5 h
on the base set and about 30 s - 25 min with the speed set. Estimates, to be measured on the first runner.

**Further, only if a measurement demands it:** a copy-and-patch translator in the runner (each IR instruction copied
as a fixed machine-code template with its operands patched in, no dispatch at run time; about 3-5 times faster). Its
proof reuses the handler lemmas as template lemmas but adds the translation loop and instruction fetch from memory
the runner wrote; estimated +20 000 - 35 000 lines, so it fits under the hard limit only if the rest stays low.

### 2.2 The verified x86-64 runner (Simon, 2026-10-28)

**What it is.** A program of x86-64 machine code (no C, no compiler, no Lean runtime) that loads an `S0IR` image and
runs it (§2.1.5): a loader, a dispatch loop through an indirect jump table, and 24 handlers (§2.1.3); everything
else -- locks, budgets, gates, floats -- is IR code lowered in Lean (§2.1.4). Its bytes are written down in Lean and proved there.

**What is proved.** `runner_ok`: for every image that is the lowering of an accepted program (checked by its hash, §2.1.6) and every
run of the runner on the x86-64 model, the sequence of
machine states refines a run of the `S0IR` machine of §2.1 (per handler: its instructions from dispatch to dispatch
refine its `S0IR` rule; the loader refines `ir_decode`). Concurrency: the x86-TSO memory model, with the mapping of
the runner's atomics and locks to GX proved (`runner_tso`). Together with §2.1: every output of the runner is an output
of a run of the thread machine, so the goal theorem applies to it. The precedent for the method is seL4's binary
verification (machine code against a formal ISA model, refinement of a proved specification).

**The model: written anew, tested against the CPU** (2026-10-28). The archived x86-64 model (branch `archive`,
`7c693cb7`) was written by hand in lanes and never tested against hardware; it is not the base (at most a quarry for
the decoder). seL4 did the same as planned here: its binary verification (Sewell, Myreen, Klein, PLDI 2013) ran
against Anthony Fox's ARMv7 model (HOL4, later L3), which is not proved but VALIDATED -- instructions executed at
random on real processors and compared with the model; that the CPU follows the model stays a named assumption.
For the runner:
1. **Only the instructions the runner uses** (23 mnemonics in about 40 encodings, §2.1.3: `MOV MOVSXD MOVZX LEA ADD SUB IMUL
   MUL CQO IDIV AND OR XOR SHL SHR CMP TEST SETcc JMP Jcc REP MOVSQ LOCK CMPXCHG SYSCALL`, no floating point; the model
   decodes only these encodings), their semantics in Lean written after the most
   validated x86-64 definitions -- ACL2 `x86isa` (Goel, co-simulated against real CPUs) and Fox's L3 x64 model
   (CakeML's x64 back end) -- with the Intel and AMD manuals as the cross-check; what a vendor leaves undefined (some
   flags) stays FREE.
2. **Differential tests on the CPU:** random register and memory states plus the edge cases (overflow, sign, shift
   counts, alignment), each instruction executed on Simon's x86-64 machine and compared with the Lean evaluation of the
   model. A stage of `pruefe-lean.py` (no fifth guardian); the machine is named in `AGENTS.md` §4.
3. **x86-TSO** (Sewell, Owens et al.) for several cores, with its litmus tests run on the same machine.
4. **Named assumption:** the CPU implements this model for these instructions -- the trust base seL4 has.

* **Why x86-64:** the AArch64 machine at hand is 5-10 times slower, and `arm/` is far from complete (Simon, 2026-10-28).
  The compiler's own targets (`gkomp`: x86-64 and AArch64, `ARM-PLAN.md`) are not affected.
* **Why not C:** a verified C runner needs a verified C compiler; CompCert is Coq and not freely licensed, and gcc/clang
  bring LLVM back. Handwritten C is also against `AGENTS.md` §3.
* **Speed:** §2.1.8.
* **Size and risk:** the runner, counted handler by handler (2026-10-28): the 24 base handlers about 250 machine
  instructions, the speed set about 100, loader and argument parsing about 100 - 150, `spawn`'s thread entry about 25:
  about 450 - 650 in all (the dispatch table is data); the proofs 8 000 - 20 000 lines of Lean with the base set, 15 000 - 30 000 with the speed set (budget 60 000,
  hard limit 80 000): the x86-64 subset with its CPU tests, an instruction layer that makes symbolic execution of a
  handler cheap, the handlers, the loader, `spawn`, `runner_tso` over x86-TSO for `MOV` and `LOCK CMPXCHG`. The least charted part is
  `ir_parallel` with `runner_tso`.

**State (2026-10-28, package `runner/`).** Built and proved, with threads, on the standard axioms:
* `IR/Step.lean`: `S0IR` with 24 opcodes. Deviations from §2.1.3, decided for the smallest runner: the opcode is
  byte 0; `jmp`/`brz` take a byte offset relative to the instruction; `call a k` jumps to the code ADDRESS in slot
  `a`; `cas d a e` takes the new word from slot `e+1`; `spawn d a` starts a thread at the code address in slot `a`
  with the frame in slot `a+1` by `clone` with fixed thread flags; the image header is one word (the first frame),
  the code starts at byte 16. A step is a TREE OF REQUESTS (read, write, `cas`, system call) in a fixed order;
  the memory and the kernel answer them, so every image has a defined run under every memory model.
* `sys d a` executes every Linux system call (number and six arguments from slots, pointers are plain words);
  the machine itself interprets only `exit`, `exit_group` and the thread `clone`.
* `X86/`: the 22 instruction forms, the decoder, `decode_enc`; the step fetches from the runner's fixed code and
  makes the same requests. `Test/Diff.lean` with `instrumente/teile/runner-cpu.py`: random cases of every form
  against this processor, fault programs, and litmus tests of x86-TSO run by the runner on real threads.
* `Prog/`: the runner (loader, threaded dispatch through a 256-entry table, 24 handlers; a 4288-byte ELF), its
  listing `runner/runner.s`, probe images with fixed outputs (`runner/proben/`; no Lean program runs the IR).
* `Mach/`: one machine for both sides over a memory model (`MemSys`): SC with the kernel, and x86-TSO with a
  store buffer per thread.
* `Beweis/`: `step_ok` (every handler makes the requests of its IR instruction, all 256 opcode bytes),
  `runner_mt` (every observation of the runner's threads -- system calls of all threads with their answers, in
  order, and the end -- is one of the IR's threads, never an undescribed step; for every program, also with data
  races, under every memory model that reads the table right), `runner_tso` and `runner_sc` on the real file,
  `runner_zeuge`; `loader_ok` (from the ELF entry the loader makes exactly the requests `argv[1]`, `open`,
  `lseek`, `mmap`, the first frame, and every failure ends in its own `ud2`), so `runner_entry_tso` and
  `runner_entry_sc` hold from the process's first instruction (`entry_is_loader`).
* Named assumptions: the CPU implements the model for these forms (differential tests) and x86-TSO for `mov` and
  `lock cmpxchg` (litmus tests); the ELF loader maps the file (`FileInv`); the kernel keeps the runner's code and
  table and the registers but `rax`, `rcx`, `r11` across `syscall`; `clone` behaves as Linux documents for the
  fixed thread flags; the program makes no other process- or thread-creating call and installs no signal handler.
* Open: `ir_sim` (S0IR against machine G) and the lowering of stage 0, the speed set.

**Order.** `S0IR` (syntax, semantics, image) and `ir_sim` first; beside it the x86-64 subset written anew with its
differential tests on the CPU and the instruction layer; then the runner with `runner_ok`, first on one thread as a
step; then threads, `ir_parallel`, x86-TSO and `runner_tso` -- the target. The Lean-run stage 0 stays the reference until the runner runs the probes and `gkomp`, then its run
path is deleted.

## 3. What is proved, for each tool

For a tool `T`, `run_T x` is the output of its G program on input `x` (machine G, any oracle that meets the gates'
contracts).

### 3.1 Termination

∀ `x`, `run_T x` returns (never by budget exhaustion) within `passes ≤ c · |x|^k`. Every loop and recursion carries a
measure (`Logik/Terminierung/Mass`, `Klasse`); the bound is a theorem.

### 3.2 Determinism

* The output is a function of the input bytes: two oracles that agree at the input gates give the same output; output
  and exit gates return nothing the program branches on.
* **Address neutrality:** the provider may answer any fresh cell; the output is invariant under every renaming of
  region cells (no reference is ordered, hashed by address or printed) -- a noninterference statement over reference
  values (`Nichtinterferenz/`).
* The first versions are single-threaded (no `concurrent`). A parallel version later owes schedule independence: race
  freedom from `gabbro_ziel` plus deterministic joins.

### 3.3 Neutrality: H1-H7 of `CHECKER.md` §16.1 as theorems

Today H1-H8 are ASSUMPTIONS about the Rust code, checked by audit and metamorphic tests. For `gpruef` and `gkomp` they
are proved:

* **H1, syntax-directed with finite state:** the core of the tool is a fold `node : Ctor → List St → St` over the
  elaborated tree with a FINITE state type `St`. Theorem: an `Automat` (`Adaequanz/Baum.lean`) with `m = |St|` states
  computes the same as the tool on every tree; at the fine level, the tool is an instance of `NeutralF`
  (`Gen/Fein/Neutral.lean`: `pruefer_fein`, `compiler_fein`).
* **H2, names:** renaming identifiers renames the output's symbols and changes nothing else.
* **H3, data:** constants reach the control only through their range class, otherwise they are copied
  (noninterference with the class as the public part).
* **H4, order:** reordering independent items permutes the output's items.
* **H5** is §3.2. **H6** (bounded mark multiplicity) and **H7** (whole-program conditions are bounded patterns: a
  function's verdict and code depend on its body and the signatures it uses, `WRAP`) are theorems about the fold.
* **H8** (LLVM's passes, `llc`, `ld.lld`) stays outside: translation validation, `PLAN-TRANSLATION-VALIDATION.md` §9c.

### 3.4 Logic proofs where the test route does not reach

* **The checker, `gpruef`:** besides §3.1-§3.3, GabbroV proves the parts the test sets do not decide: the lexer and the
  parser against `lex`/`parseTopTief` (text-level behaviour, R), the elaborator against `elabU`, and the refusal
  REPORT (`NurAn c` of the refused cell). The ten components are written as the fold of §3.3, so their correctness
  comes from the test route, not from ten functional proofs.
* **The compiler, `gkomp`:** the IR printer and the symbol handling (outside the fold) are proved against their Lean
  counterparts.
* **The helpers:** `ggen` against the Lean generator (it emits exactly M, N, R with the right labels: soundness and
  completeness by exact size), `gabdeck` against the cell functions, `gvalid` against the `Code/Refine` decision, `glauf`
  against the comparison predicates. These are functional GabbroV proofs; the helpers are small and loop over data, so
  the proofs are simulations, one per function.

## 4. Correct on every program: M, N and the adequacy theorem

* **Coverage first:** M ∪ N must cover every cell (`deckung`): today 459 component cells and 4267 fine cells, 876 fine
  cells open since the search of 2026-10-23 (`CHECKER.md` §16.8). `gabdeck` closes them by witnesses, or a Lean theorem
  proves a cell unreachable.
* **The campaign:** `glauf` runs `gpruef` on every program of M ∪ N (label: accept, or refuse by exactly `c`) and of R
  (refuse at the text level), and `gkomp` on every program of M with `gvalid` on the result; it writes a ledger.
* **The theorems:**
  * `gpruef_korrekt`: ∀ `src`, `run_gpruef src = pruefSpec src` -- from §3.1-§3.4 and `hinlaenglich` (`CHECKER.md` §16.2)
    over the agreement on M ∪ N, plus the GabbroV proofs for R.
  * `gkomp_korrekt`: ∀ `p` with `AkzeptiertX p`, `run_gkomp (print p)` refines `kompSpec p` -- from §3.1-§3.4 and
    `hinlaenglich` over the agreement on M; with H8, the binary refines the model.
* **Where the computation enters the proof.** The agreement on M ∪ N is a COMPUTED fact: the verified `glauf` ran on a
  native binary. It enters the theorems as the named premise *campaign*, with the ledger as its record. It is not
  circular in the dangerous way: the campaign's binaries are produced by the fixpoint compiler, and the diverse double
  compilation of §2 re-runs a sample on machine G in Lean. Where a kernel-sized certificate exists for a test (the
  verdict of a small program), the premise is replaced by a kernel check. `native_decide` stays forbidden in
  `grammatik/`.

## 5. What the language needs first (Lean model first)

The tools read inputs of unbounded size; each need is modelled in Lean before it is used (CLAUDE.md):

| Need | State |
|---|---|
| storage without a ceiling: `table T from p`, `alloc T`, references, their ownership rule, the refinement to `ArenaStorage.Heap` | done in the Lean model and its Lean front end (`PLAN-DYNAMIC.md` §14) |
| release of region cells (a provider-side `free`, grants for references) | open |
| bounded strings `string max N` and byte buffers in G | strings exist outside G |
| file IO as declared `syscall` gates with contracts (open, read, write, exit) | gates exist; contracts to write |
| loops and recursion over input-sized data with a measure accepted by the checker | model exists; checker side to extend |
| containers as Gabbro libraries over the open region (vector, hash map, tree), with GabbroV contracts | open |
| no generics: one container instance per element type, produced by a Gabbro generator (not a macro in the language) | by design |

## 6. What is deleted

* At parity of `gpruef`/`gkomp` with the Rust checker and compiler on M ∪ N ∪ R and the corpus: the Rust checker, the
  Rust compiler and their tests. The guardians `pruefe-pruefer.py` and `pruefe-llvm.py` then measure the Gabbro tools.
* At parity of `ggen`/`gabdeck`/`gvalid` with the Lean drivers: the Lean drivers (`gen-abdeckung`, `gen-zellen`,
  `gen-fein`, the executable pipeline and validator). The Lean DEFINITIONS stay: they are the specifications.

## 7. Targets: a new ISA is a profile, not a port (Simon, 2026-10-25)

**Requirement:** moving the tools and their output to another 64-bit ISA is easy: a target is a checked profile plus a
binding library, never a change of the front end, the checker or the compiler's core. **Built:** x86-64 and AArch64
(AArch64 hardware is available, Simon 2026-10-25). **Kept easy, not built:** RISC-V -- the design must make it items 1-4
below and nothing else; no RISC-V profile, binding, proof or measurement belongs to this plan's deliverables.

* **One target-independent core.** `gpruef` knows no ISA at all. `gkomp` lowers to target-independent LLVM IR; the ISA
  enters only through the **target profile** `Ziel`, a Gabbro data item: triple, data layout, calling convention and
  aggregate ABI, the register and stack conventions of `entry`/`asm` stubs, the width classes of atomics, and the
  mapping of `acquire`/`release`/`seq`/fences to the target's memory model.
* **What is per target, and only that:**
  1. the profile `Ziel` (data);
  2. the binding library of the environment (syscall numbers, entry stubs) -- Gabbro code with user-logic contracts,
     never in the compiler (AGENTS.md §3: the OS is user logic);
  3. the memory-model mapping of the profile, proved in Lean against the target's model (AArch64: `ARM-PLAN.md`;
     x86-64 TSO is frozen; a later RISC-V owes RVWMO modelled the same way);
  4. a QEMU stage in `pruefe-llvm.py` and, for performance (§8), real hardware.
* **Theorem `ziel_neutral`:** `run_gkomp (p, z)` = `abi z (kern p)`: the output is the target-independent core `kern p`
  followed by a function of the profile alone; the core never reads the profile. So the proofs of §3 and §4 are made
  ONCE and hold for every profile; a new target owes only items 1-4.
* **Measure of "easy":** a new 64-bit target with an existing LLVM back end is items 1-4; the gate is the four guardians
  plus the QEMU stage on the new target. Estimate (a guess): days for 1, 2 and 4; the memory-model proof (3) is the
  long item, and it is shared by every program.
* **Hardware model and translation validation** (H8, `PLAN-TRANSLATION-VALIDATION.md` §9c) stay per ISA; `Code` is
  ISA-neutral by design (§9a there), so a new ISA adds its CPU model, not a new IR.

## 8. Performance: at least `gcc -O3` and `clang -O3` (Simon, 2026-10-25)

**Requirement:** the code `gkomp` produces is at least as fast as equivalent C compiled with `gcc -O3` or `clang -O3`,
on x86-64 and AArch64 (both measured on real hardware). This raises the minimum of AGENTS.md §11 (80 %) to 100 %. A
later RISC-V target owes the same minimum when it is built.

* **Score:** per workload `100 · t_C / t_Gabbro` (fixed work) or `100 · throughput_Gabbro / throughput_C`, against the
  FASTER of `gcc -O3` and `clang -O3` (same machine, same ISA extensions, `-march`/`-mcpu` matched, same semantics,
  no `-ffast-math` on either side). **Minimum 100 % on every workload class; ambitious above 110 %.**
* **Why it is reachable:** `gkomp` hands LLVM's `-O3` pipeline IR that carries what the proofs know and C cannot say:
  * no bounds checks, no overflow checks where M1 proves the range (they are not emitted, not optimised away);
  * `!range` from every integer type's bounds, `nsw`/`nuw` where the range proves no wrap, `inbounds` GEPs;
  * `noalias` from ownership (`own`, the ledger) and from distinct carriers, `!tbaa`-style disjointness per table and
    field, `nonnull`/`dereferenceable` for references into regions;
  * loop trip counts from the loop bounds, `llvm.assume` from narrowed facts;
  * the open region's allocator: a bump/free-list fast path inline, the provider called per chunk, not per cell (OOM is
    user logic, so no refusal path on the fast path);
  * whole-program optimisation across units (LTO) where linking allows (`GabbroZielVerbund`).
  Every such fact is justified by a proof and checked by translation validation (`PLAN-TRANSLATION-VALIDATION.md` §8,
  §8.6): a validated optimised image or a refusal, never "optimised but unchecked".
* **Measurement:** a benchmark suite of workload classes (compute kernels, pointer-chasing over regions, parsing and
  string work, the tools themselves as a workload); each Gabbro program beside a C version written to the same
  algorithm; a performance stage in `pruefe-llvm.py` (no fifth guardian) that records the scores per ISA and fails below
  100 %. x86-64 runs here, AArch64 on the available AArch64 machine (QEMU timings are no measurement).
* **The compiler itself** is a Gabbro program compiled by itself at `-O3`, so its own speed follows the same requirement;
  compile latency (checking, optimisation, validation) is measured beside it.

## 9. Order of work, estimates, critical path

| | Step | Gate |
|---|---|---|
| S1 | the language needs of §5 in the Lean model | full Lean build, `gabbro_ziel` on the standard axioms |
| S2 | stage 0 (`stage0/`: machine G in Lean with the IO oracle; `GutO` of the oracle proved) | a probe program's run equals its Lean semantics |
| S3 | libraries in Gabbro (bytes, strings, vector, hash map over the open region), GabbroV contracts | GabbroV GREEN |
| S4 | the shared front end in Gabbro, proved against `lex`/`parseTopTief`/`elabU` | kernel |
| S5 | `ggen` and `gabdeck` in Gabbro, proved against the Lean generator and cells; the open cells closed | kernel; coverage complete |
| S6 | `gpruef` (the fold) with §3.1-§3.3, the campaign on M ∪ N ∪ R, `gpruef_korrekt` | kernel + ledger |
| S7 | `gkomp` and `gvalid` with §3.1-§3.4, bootstrap stage 0 → stage 1, fixpoint, double compilation, `gkomp_korrekt` | kernel + fixpoint + ledger |
| S8 | deletions of §6 | the four guardians on the Gabbro tools |
| S9 | targets (§7): the profile `Ziel` and `ziel_neutral`; the x86-64 and AArch64 profiles, bindings, memory-model proofs; the RISC-V path checked as "profile only" by a design review, not built | QEMU and hardware stage on AArch64 |
| S10 | performance (§8): the proof-derived IR facts, the benchmark suite, the performance stage | 100 % of the faster of `gcc -O3`/`clang -O3` per workload class, on x86-64 and AArch64 |

**New lines of code (ranges, a guess; measured bases 2026-10-25 in brackets).** Gabbro is denser in ceremony than Rust
(contracts, effects, costs, no generics: one instance per element type), so a Gabbro tool is costed at 1.5-2.5x its
Rust counterpart and 2-3x its Lean definition.

| Part | Base today | New lines |
|---|---|---|
| **Gabbro, written by hand** | | |
| libraries: bytes, strings, vector, hash map, tree, file IO, formatting | -- | 8 000-15 000 |
| shared front end: lexer, parser | Rust syntax 11 200; Lean parser without proofs ≈ 8 100 | 15 000-30 000 |
| shared front end: elaborator to G | Lean `Elab` 10 200 | 15 000-35 000 |
| `gpruef`: the ten components of `AkzeptiertX` as a fold, refusal reports | Rust checker 110 900 (with diagnostics, passes, tools) | 20 000-45 000 |
| `gkomp`: lowering, IR facts of §8, IR printer, profile handling | Rust LLVM 12 900; Lean `Code` 17 900 | 20 000-45 000 |
| `ggen`, `gabdeck`, `glauf`, `gvalid` | Lean `Gen` 22 000 (with proofs) | 24 000-48 000 |
| target profiles and bindings: x86-64, AArch64 | -- | 2 500-6 000 |
| benchmark suite: Gabbro side | -- | 8 000-20 000 |
| **Gabbro total** | | **112 000-244 000** |
| generated container instances (not written by hand) | -- | 10 000-30 000 |
| **Lean, specification and proof** | | |
| language needs of §5 (region release, strings in G, file-gate contracts, measure-based loops) | region in G ≈ 5 000 | 8 000-20 000 |
| stage 0 (`stage0/`) as the translator into `S0IR` over the whole language: semantics, image, lowering, soft-float, `ir_typed`, `ir_sim`, `ir_budget`, `ir_erase`, `ir_parallel`, `ir_decode` (§2.1.7) | stage 0 ≈ 6 900 | 17 000-39 000 |
| the verified x86-64 runner of `S0IR` (§2.2): 500-1 000 machine instructions (base and speed set), the x86-64 subset (about 22 instructions) written anew with its CPU tests, x86-TSO, `runner_ok`, `runner_tso`; budget 60 000, hard limit 80 000 | -- | 15 000-30 000 |
| GabbroV: libraries' contracts | GabbroV today 115 000 | 8 000-20 000 |
| GabbroV: front end against `lex`/`parseTopTief`/`elabU` | | 30 000-70 000 |
| GabbroV: helpers, IR printer, refusal reports | | 15 000-35 000 |
| §3.1-§3.3: termination, determinism (address neutrality), neutrality H1-H7, the fold as `Automat` | Nichtinterferenz 4 300, Terminierung 2 400, Adaequanz 1 600 | 15 000-40 000 |
| §7: `ziel_neutral`, profile semantics, AArch64 memory-model mapping | `ARM-PLAN.md` parts | 7 000-20 000 |
| §8: soundness of the IR facts (ranges, `nsw`/`nuw`, `noalias`, disjointness) in translation validation | | 8 000-20 000 |
| closing the open cells (witness support, unreachability proofs) | 876 fine cells open | 3 000-10 000 |
| **Lean total** | | **96 000-239 000** |
| **Other:** C side of the benchmark suite | -- | 5 000-12 000 |
| guardian stages (performance, AArch64 hardware), scripts | -- | 500-1 500 |
| **All new lines** | | **≈ 210 000-490 000** |
| **Deleted at parity (§6)** | Rust checker, compiler, syntax ≈ 122 000 plus their tests; Lean drivers 3 000-6 000 | |

The ranges are wide because the two largest items -- the front end's GabbroV proof and the neutrality theorems -- have
no precedent in the tree; the low ends assume the fold structure of §3.3 removes most of the per-component proofs.

**Critical path:** S1 → S3 → S4 → S6. The least charted parts are §3.3 (neutrality as theorems), above all H1 for a
real implementation, and the AArch64 memory-model mapping of §7. The performance minimum (§8) is decided by the IR facts:
they must be designed into `gkomp` from S7 on, not added afterwards.

## 10. Decisions (Simon, 2026-10-25; 2026-10-26)

0. (2026-10-26, changed 2026-10-28) The bootstrap (§2): stage 0 in Lean (`stage0/`) only translates Gabbro into the IR
   `S0IR`; a formally verified x86-64 machine-code runner runs it (not AArch64: the machine is 5-10 times slower and
   `arm/` is far from complete). No interpreter in a Gabbro subset, no LLVM and no C on the bootstrap path.

All decided:
1. The premise *campaign* (§4) is accepted: the agreement on M ∪ N, computed by the verified `glauf` on the native
   binary, enters the correctness theorems as a named premise; where a kernel certificate fits, it replaces the premise.
2. The first `gpruef`/`gkomp` are single-threaded.
3. The Rust tools and the Lean drivers are deleted at parity (§6).
4. AArch64 hardware is available: x86-64 and AArch64 are built and measured; RISC-V only stays easy to add (§7).

First step (Simon, 2026-10-25): complete GabbroV so that full logic proofs of Gabbro programs are possible -- it is what
§3.4 and §4 rest on.
