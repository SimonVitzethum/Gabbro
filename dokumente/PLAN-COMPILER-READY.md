# PLAN-COMPILER-READY — from today's tree to a kernel written in Gabbro

*Written 2026-11-12 at the owner's request, revised the same day for the owner's end goal: **a kernel written
entirely in Gabbro, with no assembly anywhere, that boots on x86-64, with as little architecture-specific code as
possible, with raw addresses handled safely, where only the kernel's logic and its environment (hardware, CPU, or
an operating system below a hosted program) are left to the user.** It merges and reviews: the lead's scratch plan
`.scratch-dev/COMPILER-READY.md`, the gaps of the goal theorem agreed between the Stage-0 session and the
goal-theorem review (2026-11-12), [LOW-LEVEL-SYNTAX-PLAN.md](LOW-LEVEL-SYNTAX-PLAN.md) with the owner orders of
2026-11-03, [MACHINE-IR-PLAN.md](MACHINE-IR-PLAN.md), [PLAN-SELF-HOSTING.md](PLAN-SELF-HOSTING.md),
[IR-COMPILATION-LANES.md](IR-COMPILATION-LANES.md), [GABBROV.md](GABBROV.md) and [PLAN-LONG-RANGE.md](PLAN-LONG-RANGE.md).*

*This is a plan, not a findings log: open findings stay in gitignored scratch (AGENTS.md, owner 2026-11-11).
The staffing and build order of AGENTS.md "Current work" stays the one valid order until the owner adopts this
plan into it. Every number marked **measured** was measured on the date given; every range is an estimate.
"LOC" means new or changed lines including witnesses; "full builds" means full `grammatik/` builds.
Where this plan changes a standing owner rule it says so and lists the change in §8; nothing is changed silently.*

---

## 0. The end state

Five gates. Nothing of a later gate starts its trust-path work before the earlier gate is green; preparatory
Lean work may run in parallel where §6 says so.

| Gate | Condition | Meaning |
|---|---|---|
| **R1 Stage 0 complete** | every form that the sources of GabbroV and of the compiler need compiles through Stage 0 with a connected generic theorem; the IR corpus is green; `accepts` is proved equal to the goal theorem's checker on the unit it builds | the compiler can be written and run |
| **R2 GabbroV ready** | the duty files are generated in Lean from the elaborated unit for every Stage-0 form; the bridge derives premise (b) from the user's proved duty statements for every such unit | a user (and the compiler's own sources) can discharge (b) |
| **R3 Trusted output** | the image theorem: the goal theorem holds on every image Stage 0 emits (owner, 2026-11-12: "stage0 braucht einen Beweis, dass sie korrekt ist, der Zielsatz auf allem gilt, was sie erzeugt") | what Stage 0 emits carries memory safety, race freedom, contracts and time |
| **R4 Low-level model** | addresses, contexts, bounded views, device registers, privileged operations, entry frames, address translation, nested interrupts, user-mode guests and the kernel as its own runtime are in the Lean model, with `gabbro_ziel` extended and still on the standard axioms | a kernel is a program of the language, not a foreign body |
| **R5 Kernel ready** | the compiler on GIR emits freestanding images with privileged and entry cells; a witness kernel written in Gabbro boots on x86-64 (firmware emulator and one real machine), its unit meets (a) by computation, (b) through GabbroV, (d) by proof, and (c) is exactly the named environment list of §4.4 | a kernel can be written, and what is left to its author is logic and environment |

After R1+R2 the compiler on GIR starts (owner, 2026-11-11: "GabbroV zuerst", the compiler "von Anfang an auf
GIR"). R3 and R4 run beside it. R5 needs all of them.

**What "no assembly anywhere" means in this plan** (details in §4.1): no instruction text in any source, binding
or library; no assembly file in a kernel, a runtime or a compiled binary. Machine instructions exist in exactly
one place, as rows of a target table (data: a cell and its encoding template), checked by `TargetOk` and measured
by M. One handwritten assembly file exists in the repository today, the Stage-0 runner (`runner/runner.s`); it is
a bootstrap tool, verified against an x86-TSO model (`runner_tso`), it is in no kernel and no compiled binary, and
it is deleted when the compiler compiles itself (K7).

---

## 1. Where the tree stands (2026-11-12)

| Fact | State |
|---|---|
| `master` = `origin/master` | `d9019873f` |
| on `dev`, not pushed | `e7bafb9c0`, `65cc01677` (AGENTS: build rules), `0675bb884` (tagged static read), this plan; `1fafd3622` (Spec header names Stage 0) is pushed |
| branch `float-entkopplung` (`../gabbro-float-entkopplung`) | contracts over `Ops`, `hardware_satisfiable` and `GleitHw` decoupling: full grammatik build green (3943 jobs, **measured**), `gabbro_ziel` and the float-free witness `n1E_gabbro` on the standard axioms; stage0 and bridge builds pending |
| lock stage 1 (`AgreeW` keeps lock classes) | working change in the main tree, being built; first builds failed at two overlooked sites, both repaired |
| builds on `d9019873f` (**measured**) | grammatik 3940 jobs, stage0 5629, bridge 1614; `gabbro_ziel` on the standard axioms; GabbroV guardian green; Lean guardian green except `7 ir` |
| IR corpus (**measured**, `0675bb884`) | 325 of 333; the eight red probes are `c11-scoped-*` (`return` inside `locks`) |
| Stage-0 speed (**measured**) | 16 000 functions / 96k lines in 12.7 s; tempo work closed by the owner |
| full grammatik build (**measured**) | about 30 min with `LEAN_NUM_THREADS=3`, 13G scope; stalls without the variable |
| low-level forms in the tree | syntax only: `SItemTief.asmT` (a signature and a string), `bootT`, `trustT`, `entry` declarations, `reg`/`bank`/`transition`, `walk`; no instruction semantics, no authority model, no privilege model |

**The goal theorem today** (`Spec.lean`): over the model G/GX, for every accepted unit, under user logic (b), named
hardware and foreign code (c) and runtime (d), every reachable thread machine satisfies `ZielFX`. The only
connected bridge to an image is sequential (`irBild_correct` over `bild_ok_u`); no concurrent leg reaches the
image. Stage 0 targets a hosted Linux process through the runner; it cannot emit a kernel.

---

## 2. Review: what the existing plans get wrong or leave inconsistent

Found while merging; each item says how this plan resolves it. The documents themselves are corrected in the
first documentation pass of Phase 0 (§4), as pure edits.

| # | Document | Problem | Resolution |
|---|---|---|---|
| D1 | PLAN-SELF-HOSTING §0, §2, §9 | still says "LLVM stays the back end", gkomp emits LLVM IR, `gvalid` validates per program, stage 0 is "machine G in Lean with the IO oracle", bases count the deleted Rust tools | superseded by MACHINE-IR-PLAN (owner 2026-11-10: GIR, no refinement, no translation validation, every pass proved with GabbroV) and by the translator-only Stage 0 (2026-10-31). Rewrite §0/§1/§9 against GIR; drop `gvalid`. |
| D2 | LOW-LEVEL-SYNTAX-PLAN, header | "Device-register forms remain excluded" | owner 2026-11-03 put device-register reads, writes, fallible reads and register transitions in scope (AGENTS.md). Phase 6 includes them. |
| D3 | LOW-LEVEL-SYNTAX-PLAN, evidence; IR-COMPILATION-LANES low-level design | name the Rust front end and `crates/` as targets | Rust was deleted on 2026-11-10; the targets are the Lean model, parser/exporter and checker only. |
| D4 | LOW-LEVEL-SYNTAX-PLAN decision 3 | first target AArch64 EL1 only | superseded by O13: the first boot boundary is firmware entry in 64-bit mode on x86-64 (§4.2); AArch64 follows as the second binding (K6) through the same boundary. The `boot16to64` item is gone (D13); further cores use the generated start item (K4). |
| D5 | LOW-LEVEL-SYNTAX-PLAN decision 2 vs goal-theorem gap A1 | the same change twice: software foreign assumptions into user obligations | one work item (A1, §3); its `Spec.lean` diff goes to the owner before merge (owner rule 2026-11-03). |
| D6 | LOW-LEVEL device registers vs goal gap A2 (`RegLokal`) | device reads need register answers that depend on history; `RegLokal` forbids that | A2 is the model foundation of the device forms; it is scheduled before them. |
| D7 | GABBROV.md | describes components in `crates/` (manifest, harness, `lean.rs`) and translation validation | the duty generator must be rebuilt in Lean (R2); update the component table when it exists. |
| D8 | COMPILER-READY §2.2 | the bridge was taken to carry most forms and V2 was sized at 2 000–10 000 lines | measured by V0: it carries 4 of 34 statement forms. V2 is resized (§3 V2), and with it the path to the compiler start. |
| D9 | Stage 0 `accepts` | is `AkzeptiertX … [] [] [] guests` without `besitzB`/`akkuStartB`, while Stage 0 compiles arenas (**probed**) | (a) of the goal theorem does not hold for Stage-0 units with arenas, accumulators or checks; item S6 (§3) closes it. |
| D10 | Stage-0 lock | DONE 2026-11-13: Stage 0 emits the ticket lock (`locksCodeT`), the old owner-word lock with its hold count is deleted. Before: owner word, `cas`, hold count, futex; not the model's FIFO ticket lock; for `return` inside `locks` the design note `Faelle/RueckgabeScoped.lean` would emit no release (the release would be ghost); the form is refused today, so nothing wrong is emitted | the model refuses re-taking a lock (`Stmt.locks` carries the rank proof, callers' locks lie below the floor), so the hold count is dead behaviour; Stage 0 emits the ticket lock (owner: yes). |
| D11 | Spec header | 5.2 (claim (1) of termination is no statement about the program) and 5.10 (source rewrites before the elaborator are trusted) missing | written in `float-entkopplung`; merged with Phase 0. |
| D12 | LOW-LEVEL-SYNTAX-PLAN, "Alternatives" and "Canonical typing" | privileged instructions "stay inside contracted ASM functions"; an ASM body is a string of instructions with a per-body certificate | owner 2026-11-12: no assembly anywhere. Privileged operations become typed operations of the target binding (§4.1); there is no source ASM body, no per-body certificate, and the existing `asmT` string form is refused and then removed. This replaces step 3 of that plan (L4, L5). |
| D13 | AGENTS.md "Scope" (owner 2026-11-03) | the one exception: a bundled, once-proved x86-64 boot-stub ASM item (16→32→64-bit switch) the user includes by name; "source ASM bodies" are in scope | superseded if the owner confirms O12/O13: the first boot boundary is firmware entry in 64-bit mode, so no mode switch is needed; where one is needed (second cores, K4) it is a generated binding item made of table rows, never assembly text. AGENTS.md is corrected in the Phase-0 documentation pass. |
| D14 | AGENTS.md §3 "The operating system is user logic, never an assumption" vs the owner's sentence of 2026-11-12 ("nur Logik und Environment, also Hardware, CPU oder OS") | the two read differently for a hosted program on an operating system nobody verified | resolution proposed in §4.4 (O14): software INSIDE the verified image is user logic; software OUTSIDE it (an operating system below a hosted program, firmware before the entry) is a named environment assumption with a declared contract, listed per unit like hardware. A1 keeps this class apart from hardware. |
| D15 | MACHINE-IR-PLAN §1.9, §12.9 | privileged and boot cells "later", after further tables | they become part of the first x86-64 table that the kernel gate needs (K2), with M measured on a bare-metal harness, because user-mode M cannot run privileged rows. |
| D16 | Stage 0 and the image theorem B6 | Stage 0 emits hosted Linux images for the runner; B6 is stated over runner states | a kernel image comes from the compiler, not from Stage 0. B6 is built so that its G side (thread-machine simulation, lock refinement, stop mapping) is reused by the compiler's own image theorem (C9). |
| D17 | the Stage-0 lock design (futex) | parking in the lock needs an operating system | the wait strategy of the lock is a profile binding: spin in a freestanding image, futex on Linux (S7); the FIFO ticket order is the same in both. |

---

## 3. All work items

Grouped by stream. IDs are used in §5–§7. Estimates: LOC / full grammatik builds / other builds.

### S — Stage 0 complete (R1)

| ID | Item | Estimate |
|---|---|---|
| S1 | rest of the language forms: `spec fn` with typed parameters, nested records in table slots, substring (needs the owner's language decision) | 300–800 / 1–2 / 8–15 |
| S0m | measurement before S2: DONE (2026-11-12, agent W1-M6, run by the lead). A compiler front end written in Gabbro (source buffer, lexer, recursive-descent parser with precedence, AST in tables, symbol table with scopes, one checking pass; 1 267 lines in four files, `stage0/proben-compiler/`) compiles through Stage 0 as one unit and runs: exit 87 = 52 tokens + 35 nodes. Thirteen wanted forms were refused, each with a workaround (FINDINGS.txt there): cross-module calls that write (`use`/`pub`: "public interface is not closed"); `while`; `return f(..)` inside a branch; narrowing a value by the condition that guards it (about 60 explicit `narrow` instead); `narrow` on a record field; character literals; a wildcard `match` arm; tuples; a `bool` record field as a condition; a constructor or a computed index written straight into a table slot; a `const` string; `==` on tagged values; `next` in a `traverse` after a call-derived narrowed value. Not tried: substrings, function pointers, locks, separate compilation | done |
| S2 | the forms S0m measured, in the order of what a compiler writer hits most: narrowing by the guarding condition and cross-module writes are the two large ones (a typing rule of the model; the closed-interface rule of modules); the others are sugar or small elaborator cases (`return f(..)` in a branch, character literals, wildcard arm, tuples over records, `bool` field conditions, slot writes of constructors, `const` strings, tagged equality, the `traverse` gate case, `narrow` on a field). `while` is a language decision (O18). Scoped returns (C11) hang on S3 stage 3. Shared locks (C10), invariant groups (C05) and statement-else (C07/C08) were NOT needed by the front end and leave the critical path until a later slice needs them | 3 000–10 000 / 2–4 / 25–60 |
| S2 state | 2026-11-13, built and probed (corpus 362 of 370, the eight red are the scoped returns): narrowing by the guard (immutable number locals against a literal, a constant or another local's range; the `else` block; the code after a then block that always ends) and the difference of two locals under a guard (`if a >= b { return a - b; }`), both in the total `eng` form with nothing new in machine G and behind a switch of the elaborator context that only the compiler turns on, so the read-back theorems keep their text; qualified effect places (`writes b::T.slots`); `return f(..)` in a branch; character literals; the wildcard arm; `bool` record fields; equality of tagged values; named string constants; a computed read or a bare case stored into a slot; a tagged slot field read into a local; calls in a `traverse` body (the header check discharges the callees' declared effects); one-field records; option payloads in match arms; the statement's line in diagnostics; a function declared twice, or named like a case, is refused. Added the same day after a measurement on the Gabbro front end (rewritten with the new forms: four modules with qualified write effects, 56 character literals, `bool` fields; but 0 of about 115 `narrow` sites could go, because real parser code guards with equality): equality and inequality at an end of the range narrow (`if k == 0 { return ..; }` leaves `k ≥ 1`), record-field arguments of a call returned from a branch, a computed slot index, string escapes (`\n`, `\t`, `\r`, `\0`, `\\`, `\"`; the lexer's round trip now holds for every string value). OPEN of S2: tuples, a wildcard arm over numbers, `narrow` on a field, `while` (O18), named effect groups (O19), the relation when the read is the enclosing block's ending (`if a < b { return 0; } return a - b;` at the end of a function), u64 differences under a guard, the bool argument of a `spec fn` (import cycle) | — |
| S3 | ticket lock (lock stage 1–3): `AgreeW` keeps lock classes (stage 1), ticket code and `locks` theorem (stage 2), held set tied to G's trace and a real release on every exit including `return` inside `locks` (stage 3; only this stage turns the eight red probes green) | 1 500–3 000 / 0–1 / 15–30 |
| S3 state | 2026-11-13: stages 1 and 2 DONE and measured. Stage 0 emits the model's ticket lock (`nimmT ++ body ++ gibT` with a release on the normal end and on `leave`/`next`; body + 86 instructions); the old lock is deleted (13 modules). The simulation carries the held set `H`: `TicketOK` says a lock is mine iff it is in `H`, `HeldIn H Λ floor` ties `H` to the static held list and the caller's floor, and `HeldIn.frei` gives "not held at `locks L`" from the rank premise of `Stmt.locks` and a new lowering condition `ueberBodenB` (the floor rule for one lock) — the old theorem had ASSUMED free-or-mine and survived through the hold count. `locks_okT` is the lock theorem on the ticket code; `FunSpec.run` takes `TicketSync … H` and `HeldIn`; `bild_ok_u` and `irBild_correct` keep their statements. Measured: stage0 5 668 jobs, corpus 362 of 370, and 200 runs each of the two-thread probes `lock-wait-wake` and `sperre` without a deviation. OWED (named in `Sperre/Ticket/Offen.lean`): the contended paths have no theorem — the take when the ticket is not served (wait block), the `cas` retry, the give with waiters (wake-all on the serving word), and a cross-thread invariant; the theorems about the OLD wait/retry/wake code went with that code. Stage 3 (a release on `return` inside `locks`: the eight red probes) is open. To decide: wake-all (as emitted) or wake-one, with the profile binding (D17/S7) | — |
| S4 | link step (separate compilation, verified link) — not needed for the start | 2 000–5 000 / 0–1 / 10–20 |
| S5 | stack depth for finite call trees: `b.depth ≥ rufTief`, `abstieg` unreachable (B9, first half) | 500–1 500 / 0–1 / 3–6 |
| S6 | `accepts` = `akzeptiertX_pruefer.akzeptiert` as a Lean equation on the unit the goal theorem uses (ws, `E.akku`, `E.pruefungen`, `besitzB`, `akkuStartB`); until proved, Stage 0 refuses units with arenas, accumulators or checks for the certified path | 800–2 500 / 0–1 / 5–10 |
| S6 state | 2026-11-13: `accepts` judges the compiled entry `main` as a start (before, a plain `main` was judged with NO start, and the separation of `main` from `concurrent` workers was never checked); the bridge `accepts_gibt_pruefer` is on the judged `Einheit` (`einheitDer`, with the unit's real checks), its hypothesis `zertifizierbar` is used, and `Compiled.goal_checker_main` / `Emitted.goal_checker_main` state premise (a) for a plain `main` with the image's own start environment, with a joint witness. Still premises: arenas and accumulators (no exporter from the elaborated unit into the goal theorem's interfaces; `zertifizierbar` excludes them), the start lists in the general case with `concurrent`, and all of (d): the memory of the `Einheit` against the image's initial world, the thread assignment | — |
| S7 | the lock's wait strategy as a profile binding (D17): spin for freestanding images, futex for Linux, one ticket order | 300–1 000 / 0 / 3–6 |

### V — GabbroV (R2)

| ID | Item | Estimate |
|---|---|---|
| V0 | measurement of what the bridge carries: DONE by reading (2026-11-12, spot-checked by the lead). `stmtBody` (bruecke/Bruecke/Pflichten.lean) has three arms: store through a pointer, store to a table, call; with the trailing `return` that is 4 of 34 statement forms of machine G, none of the 22 block binders, and about 15 of 64 expression forms. `Stimmig` (Lauf.lean) further demands no `requires` beside `Held`, no reason channel, no invariant, no static. The `Body` model has forms for about 12 more statements but no values for bytes, floats, references, records or linear marks | done |
| V1 | the duties as a Lean TERM computed from the source, no printed duty file (design W3-M1, checked by the lead): `Pflichten src` (bruecke/Bruecke/Quelle.lean) already states the duties of a source text over `zuBody`/`meetsU`, `nutzer_aus_quelle` already derives premise (b) from it for every source text, and `vorlage` (Vorlage.lean) already prints the goal stub a user fills. V1 is what is left: a term-level stub in place of the printed one, the workflow written down, one witness. A printer of duty files (the deleted Rust tool's job) is NOT rebuilt: it would be a second register beside the computed statement | 400–900 / 0–1 / 3–8 |
| V2 | bridge extended to every Stage-0 form: about 30 statement forms, the binders, the remaining expression forms, and the `Body` values they need; the three costliest are loops with exits, locks with atomics, and foreign/fallible/indirect calls with reason channels. Calibration: the existing bridge has about 7 000 lines for the 4 forms it carries  Order by what makes the 61 functions of `stage0/proben-compiler` provable first (W3-M1): local bindings and assignment, statics, `if`/`else`, value calls, `narrow`, a call returned from a branch, `bool` values, `match` on option and tagged; these eight with their shared scaffolding are about 10 000–20 000 lines. `Stimmig` is violated by that source at once in three conditions (statics, a `bool` result, record parameters); loops with exits, locks and fallible calls are not used by it | 12 000–40 000 / 3–6 / 40–120 |
| V3 | GabbroV written in Gabbro with its initial Lean proof (MACHINE-IR-PLAN step 2) | see C1; after R2 |

### A — goal theorem: fewer assumptions

| ID | Item | Estimate |
|---|---|---|
| A1 | foreign software in conditional form: the binding proves `pre → post` (`ForeignPflicht`), the user proves `pre` at every call (`AxVor` in `LogikPflichtA`), `hlink` through the replay over G/GX/spawn/link; (c) narrowed to named hardware in `GabbroZiel` itself; also LOW-LEVEL decision 2 | 2 500–6 000 / 2–4 / — |
| A2 | lift `RegLokal`: record register answers in the local replay like foreign answers (63 of 70 readable example registers have no carriers, **measured**; refusing them is no option) | 3 000–8 000 / 2–4 / — |
| A3 | float premise conditional (`GleitHw`) and satisfiable (`hardware_satisfiable`); Stage-0 `Runner.IR.Kern` without `extends Hardware` | 100–400 left / 1–2 / 1–3 |
| A4 | `ImBereichO` and `KernPlan` into the named list (c) or derived from `GutO` | 300–1 500 / 1–2 / — |
| A5 | (d) proved for Stage-0 images: start, clone, spawn success at the checked places (today `Senke.CloneOK` is a premise) | 1 500–4 000 / 0–1 / 10–20 |

### B — goal theorem: more conclusions

| ID | Item | Estimate |
|---|---|---|
| B6 | **image theorem** (R3): every runner state of an image under x86-TSO is the image of a reachable GX thread machine of the elaborated unit, and the legs of `ZielFX` carry over. Pieces: (i)=S6, (ii) thread-machine simulation, (iii)=S3, (iv)=A5, (v) IR process under TSO (`runner_tso` exists) refines W/GX — first a named premise, (vi) `layU` is `LayoutOk`, (vii) every image stop is a named stop of `FortschrittFX`, (viii)=A3. Stages: lock words as state (after S3), rely/guarantee simulation of one thread, process simulation and leg transfer | 30 000–80 000 / 3–7 / 150–400 |
| B7 | liveness over GX with spawned threads and the ticket lock (after B6) | 3 000–8 000 / 1–3 / — |
| B8 | time without exceptions: declared costs and hold bounds in `Einheit` and (a) (K001/K002 into the model), hold-time theorem from `held`, per-pass bound for `forever` (`ForeverBinding` soundness), recursion by the measure | 4 000–10 000 / 2–4 / 5–15 |
| B9 | stack depth: S5, plus a NAMED stop instead of the logic code `abstieg` for recursion beyond the bound (Spec change, owner) | 1 000–3 000 / 2–3 / 3–6 |
| B10 | missing legs: accumulator fold (C15, run-level history), owner marks (C09, needs A1), arenas across the link, `Q` equal only on shared axioms in `GabbroZielVerbund` | 10 000–25 000 / 4–8 / — |

### C11 — non-emptiness in the statement

| ID | Item | Estimate |
|---|---|---|
| C11 | part of `Spec.lean`: a non-degenerate unit meets all premises jointly and has a non-trivial run (possible without a float instance through `GleitHw` and `n1E_gabbro`) | 200–800 / 1 / — |


### L — the low-level model (R4; LOW-LEVEL-SYNTAX-PLAN revised by D12–D14)

Lean model, parser/exporter and checker only; never Stage 0 or the runner. Starts after the C packages and their
userspace integration are green (owner 2026-11-03). No `unsafe` anywhere; no instruction text anywhere; boot code
is user code. The designs behind the items are in §4.

| ID | Item | Estimate |
|---|---|---|
| L0 | owner decisions of §8 that change rules or the goal statement (O12–O16, decisions 1–4 of the low-level plan), each with its explicit `Spec.lean` diff | — |
| L1 | canonical model of authority: `address<S>` as inert data, the linear `context<P>` with its ledger (live spans, space, permissions, class, owner, epoch, privilege and interrupt state), `ram_view` as the one producer of a bounded view from an address, the boot transition relation, generic preservation, joint witnesses with a real write and a privilege handoff | 8 000–20 000 / 3–5 / — |
| L2 | device memory: register reads, writes, fallible reads and register transitions over the lifted `RegLokal` (A2); device views as a memory class of their own that `ram_view` refuses; buffers lent to a device and taken back under quiescence | 4 000–10 000 / 1–3 / — |
| L3 | raw byte access below the type level, in hosted programs and in the kernel: byte capabilities with value flow (C01), grant generations (C08) and loans (C09); typed views over bytes need representation, endianness and layout proofs; uninitialised bytes are written before they are read | 6 000–15 000 / 2–4 / — |
| L4 | the architectural state as a neutral interface (privilege level, translation root, interrupt mask, vector base, per-core identity) and the privileged operations as calls of binding functions over `context<P>` with contracts; no source body, no certificate per body (D12) | 5 000–12 000 / 1–3 / — |
| L5 | entry and exit frames: interrupt and exception entry and return, system-call entry and return, thread switch and first entry of a thread, generated from the `entry` declaration (register maps, preserved set, stack) with ONE generic theorem per frame kind | 6 000–15 000 / 1–3 / — |
| L6 | address translation: a neutral model of a translation regime over the existing `walk` form, mapping, unmapping and protection as contracted operations on the tables, two aliases sharing one physical identity, reuse and revocation under quiescence of all cores with a proved translation-cache flush; what the translation unit does with installed tables is the named assumption `Mmu` | 6 000–15 000 / 2–3 / — |
| L7 | interrupts beyond `KernPlan`: re-entry, nesting with priority levels, masking as a per-core state of the context, the handler tables the kernel installs as proved statements about its own tables (was X3) | 5 000–12 000 / 2–3 / — |
| L8 | user-mode guests: the isolation boundary of an unverified or separately verified guest (C12), system-call contracts PROVED by the kernel in the conditional form of A1, no guest contract, cost or termination claimed for an unverified guest | 8 000–20 000 / 2–4 / — |
| L9 | the kernel as its own runtime: premise (d) (`Laufzeit.lader/start/einmal`, spawn) derived from the kernel's proved start, core bring-up and scheduler instead of assumed; stacks sized by B9. Shape: in the first kernel the threads of the goal theorem are the per-core roots (one root declared once per core, a pool in the sense of `Mehrfach`, so `einmal` holds unchanged) and the declared interrupt handlers; the kernel spawns no Gabbro thread (`start`/`child`), because (d) assumes every spawn succeeds on an unbounded `Faden` and a kernel has finitely many cores. User processes are guests (L8), not Gabbro threads. Spawning kernel threads later needs a refinement theorem "the kernel's scheduler implements the thread machine's spawn and switch steps" | 6 000–15 000 / 1–3 / — |
| L10 | parser, exporter, checker, obligations; refusals by name for everything unmodelled; `asmT` strings and software `assume` on `entrust` become refusals and are then removed | 3 000–8 000 / 1–2 / — |
| L11 | positive and negative validation set of the low-level plan (RAM write/read, context transition, boot-to-root handoff, interrupt entry/return; forged authority, wraparound, stale epoch, alias, bad stack, undeclared clobber, missing barrier, hidden shared write, wrong privilege, device view through `ram_view`) | 1 500–4 000 / 1 / — |

### C — the compiler on GIR (MACHINE-IR-PLAN §12, PLAN-SELF-HOSTING revised)

| ID | Item | Estimate |
|---|---|---|
| C1 | GabbroV in Gabbro (V3) with its initial Lean proof | 30 000–70 000 Lean, plus Gabbro sources |
| C2 | `gir_sem`, base cells, `tile_ok`, `encode_inj` (Lean, may start after R1) | 8 000–20 000 |
| C3 | `lower_ok` for the Stage-0 fragment, then form by form | 15 000–40 000 |
| C4 | one small target table, `TargetOk`, emitter shape contract, M for the base cells, first measured CPU run | 8 000–20 000 |
| C5 | one medium pass proved with GabbroV (GVN with per-region memory) — the measurement that sizes all other passes | 3 000–10 000 |
| C6 | location assignment, scheduling, idiom cells, optimisation passes, further tables (AArch64 first), vector cells; privileged and boot cells after L | sized after C5 |
| C7 | the compiler's own Gabbro sources (front end, checker fold, lowering, passes, emitter), ≥ 500 000 lines (owner 2026-11-11) | 112 000–244 000 Gabbro (PLAN-SELF-HOSTING §9 base, before GIR) |
| C8 | performance: ≥ 100 % of the faster of `gcc -O3`/`clang -O3` per workload class and ISA (owner 2026-10-25) | benchmark suite 13 000–32 000 |
| C9 | the image theorem for the compiler's own images: concurrent `lower_ok`/`emit_ok` (thread machine over GX, lock refinement, stop mapping, layout, start), reusing the G side of B6 (D16), with privileged and entry cells | 20 000–50 000 |

### K — kernel ready (R5)

| ID | Item | Estimate |
|---|---|---|
| K1 | freestanding profile and image profiles: no host runtime, no implicit loader; first image format the firmware-loadable one (§4.2), with the loader statement `Laufzeit.lader` proved from the image layout and `LayoutOk` | 4 000–10 000 Lean |
| K2 | privileged and entry cells in GIR; their x86-64 rows; `TargetOk`; M for these rows on a bare-metal measurement image (user-mode M cannot run them) | 5 000–12 000 Lean; harness 2 000–5 000 Gabbro |
| K3 | the x86-64 binding library, written in Gabbro: descriptor and interrupt tables, the paging format behind L6, interrupt controller and timer, the firmware handoff (memory map, exit of boot services) | 5 000–15 000 Gabbro; its proofs 5 000–15 000 Lean |
| K4 | start of further cores: on x86-64 a core starts in 16-bit mode, so the binding supplies a generated start item made of mode-transition rows with one proved contract ("the core arrives in 64-bit mode with this stack and context"); no assembly text, not written by the user | 3 000–8 000 Lean |
| K5 | the witness kernel, written in Gabbro: boot, memory authority, translation, interrupts with a timer, two cores, one user-mode guest, one system call; proofs of its duties through GabbroV | 3 000–8 000 Gabbro; proofs 5 000–15 000 Lean |
| K6 | a second binding (AArch64, the target direction of AGENTS.md) running the SAME kernel sources: the measure of how little is architecture-specific | 4 000–12 000 Gabbro; 4 000–12 000 Lean |
| K7 | the compiler compiles itself natively; the runner and its proofs leave the trust path and the tree (history in git) | after C7 |

### X — later, not on the critical path

| ID | Item | Note |
|---|---|---|
| X1 | `async fn` (design A, PLAN-LONG-RANGE §2) | 4 000–8 000; drop/cancellation is an owner decision |
| X2 | one-off corpus of all generated programs (PLAN-LONG-RANGE §1) | storage outside the repo |
| X3 | (moved: interrupts beyond `KernPlan` are L7, required for the kernel) | — |
| X4 | counting `bild_ok_u` for instruction bounds per form | blocked by AGENTS.md (no timing projects) until the owner lifts it |
| X5 | `bedingt` → `endet` through a user measure | language decision |

---

## 4. The kernel design this plan commits to

Proposed here; each point that changes an owner rule is an owner decision in §8. The aim is the owner's sentence:
logic and environment are left to the user, nothing else.

### 4.1 No assembly: where machine instructions live

- **Sources hold no instruction.** A privileged operation is a call of a function of the target binding with a
  contract over the linear `context<P>`: read or install a translation root, set the interrupt mask, load a table
  register, flush a translation cache, read or write a model-specific register or an I/O port, halt. The kernel
  calls `cpu::install_root(c, root)`; it never writes `mov cr3`.
- **A binding function has no body in text.** Its meaning is a GIR cell over the neutral architectural state of
  L4; the target table assigns the cell its bytes (MACHINE-IR-PLAN §6–§7). The row is data. `TargetOk` checks
  its shape, M measures it on silicon, and that every row computes its cell is the one hardware assumption
  `Hardware T`. Privileged rows are measured on a bare-metal image (K2).
- **Entry and exit code is generated.** Interrupt entry and return, system-call entry and return, thread switch:
  the compiler emits them from the `entry` declaration, and one generic theorem per frame kind (L5) covers every
  program. No handwritten stub exists.
- **What is refused.** The `asmT` string form, `prim fn … = asm { … }`, an `entrust` under a software `assume`,
  an external symbol without a proved contract. They are refusals first and are deleted when L10 lands.
- **What stays architecture-specific, and where.** The target table rows, the binding library (K3: descriptor
  tables, paging format, interrupt controller, timer, firmware handoff), the image profile (K1) and the start of
  further cores (K4). The kernel proper uses the neutral interface; K6 measures it by running the same sources
  on a second binding.

### 4.2 Booting on x86-64 without a mode switch

The first boot boundary is **entry from firmware in 64-bit mode** (UEFI): the processor is already in long mode
with paging on, the image is a firmware-loadable file the compiler writes (headers are data), and the kernel
takes over memory by the firmware's memory map and leaves the boot services. The same boundary exists on AArch64,
so the boot path of the kernel proper is architecture-neutral.

- The firmware is software outside the image. Its handoff state (mode, mappings, stack, the truth of the memory
  map, what stays reserved) is the named environment assumption `FirmwareHandoff` of §4.4, stated in the profile.
- A boundary further back (reset in 16-bit mode, a 32-bit loader protocol) needs mode-transition rows; it is
  possible with the mechanism of K4 and is not part of the first gate. Moving the boundary back means proving
  more software, never relabelling it as hardware (LOW-LEVEL-SYNTAX-PLAN).
- Further cores cannot be avoided this way on x86-64: a started core begins in 16-bit mode. K4 supplies the
  generated start item. The witness kernel boots on one core first and adds the second with K4.

### 4.3 Raw addresses, safely

- A number never grants memory or code. An `address<S>` is inert data with a space and a width; arithmetic needs
  non-wrapping bounds or a failure channel; equal numbers do not imply authority; a physical and a virtual
  address are different types; no address becomes a function pointer.
- The only way from an address to memory is `ram_view(c, a, n)`: it checks the whole half-open span, alignment,
  class, mapping, permissions, liveness and initialisation against the ledger of the context `c` and yields an
  ordinary bounded region borrowed from `c`. From there the existing region and reference rules, effects, race
  freedom and extent checks apply unchanged. What can be checked at run time fails into an `else`; what cannot
  be proved statically is refused.
- Authority starts in the initial machine state (the firmware handoff) and moves only by proved acquisition,
  split and merge; a software allocator proves partition and freshness (the provider model). Reuse and revocation
  need quiescence and an epoch change (L1, L6).
- Below the type level the same discipline holds for bytes (L3); device memory and buffers lent to devices have
  their own class and rules (L2). Ordinary integer-to-pointer casts stay refused (`M140`).

### 4.4 What is left to the user

**Logic (b):** the contracts and invariants of the kernel's own functions, discharged through GabbroV. This
includes everything the kernel does as software: its allocator, its scheduler, its page-table updates, its
system-call implementations.

**Environment (c), named per unit, each with a declared contract:**

| Assumption | Says | Evidence beside the theorem |
|---|---|---|
| `Hardware T` | every table row computes its cell, privileged rows and the float rows included (today's separate component `RootNativeFloat.Hardware`, assumed only where `GleitHw` asks for it) | M on silicon; the bare-metal harness for privileged rows; `hardware_satisfiable` for the float contracts |
| hardware frame (today `GutO`, restricted to hardware items after A1) | a hardware item writes only its declared carriers, keeps the held locks and leaves its accesses in the trace | manual; tests |
| `Mmu` | the translation unit translates by the installed tables and caches as the architecture manual says | manual; differential tests |
| `IrqDelivery` (replaces the premise `KernPlan`) | an interrupt is delivered at an instruction boundary, to the installed handler, under the mask and priority the kernel set | manual; tests |
| the memory-model reading (Spec header, five points) | the weak-memory machine W over-approximates the target for the emitted instructions | published models |
| device contracts | the declared answers of each device register and port (after A2 they may depend on the history; today `RegLokal` and the hardware part of `AxVertragO`), and where a device writes memory (DMA): only into the carriers and extents its contract names (today `ImBereichO`, which then leaves the leg) | data sheets |
| `FirmwareHandoff` | the state at entry, the truth of the memory map, and that the image and its initial memory are loaded as declared (for the kernel this replaces `Laufzeit.lader`) | firmware specification |
| for a hosted program only: the contract of the operating system behind each system call, in the conditional form of A1 (assumed `pre → post`, the caller proves `pre`) | declared in the binding, visible per call | — |
| for a hosted program only: the operating system's loader and thread creation (today `Laufzeit.lader`, `Senke.CloneOK`, the runner kernel class `Runner.IR.Kern`) and, where liveness or waiting bounds are claimed, its scheduler's fairness (today `Fair`, `FairF` of `GabbroZielLeben`/`GabbroZielWarten`) | declared in the profile | — |

Nothing else may remain: no loader assumption beyond `FirmwareHandoff` (K1, L9), no runtime assumption (L9), no
foreign-code assumption for software inside the image (A1), no unnamed stop (B6 piece vii, B9), no `ImBereichO` or
`KernPlan` hidden inside a leg (A4, L7). For the kernel, fairness and hold times are not assumed either: they are
properties of its own scheduler and lock code, proved as logic (b) where liveness or waiting bounds are claimed.

Checked against today's ONE ASSUMPTION LIST of `Spec.lean` (2026-11-12): every entry has its place above
(`GutO` → hardware frame and A1; `RegLokal`, `AxVertragO` → device contracts and A1; `RootNativeFloat.Hardware` →
`Hardware T` via `GleitHw`; `Laufzeit.lader` → `FirmwareHandoff` or the OS loader; `Laufzeit.start/einmal` → L9
or the OS; `KernPlan` → `IrqDelivery`; `ImBereichO` → device contracts; `Fair` → the kernel's own scheduler or the
OS; the five weak-memory points → the memory-model reading).

### 4.5 Three targets and performance (owner, 2026-11-12)

- **x86-64, AArch64 and RISC-V 64 from the start.** Source semantics, the model, GIR, every pass and every proof
  are target-neutral; a target is a table (rows for the base, privileged and entry cells), a binding library and
  an image profile. Adding the second and third target must change none of the neutral parts; K6 measures that
  for AArch64, and RISC-V 64 follows by the same three pieces.
- **Cross compilation is the normal case.** One source compiles to every target whose table and binding exist; a
  program names an architecture only inside a binding. Length-parametric vectors and the idiom cells keep sources
  free of per-target intrinsics (MACHINE-IR-PLAN §1.8, §6).
- **Performance is not traded for neutrality.** The goal stays more than optimised C on every workload class and
  ISA (AGENTS.md §11): the neutral program is tiled into the widest cells a target's table offers, so special
  instructions are used without appearing in a source. What a target lacks is ordinary GIR that tiles into
  smaller cells, never a refusal.
- **What this forbids now.** No form, model rule, Stage-0 lowering or binding interface may fix a word size,
  an endianness, a calling convention, a page size, an interrupt-controller shape or a register name outside a
  target's table, binding or profile. A neutral interface that only one target can implement is a finding.

---

## 5. Phases and order

```
Phase 0  float decoupling merged, documentation pass (D1–D17), S3 lock stage 1 built
   │
Phase 1  R1: S0m S1 S2 S3 S5 S6 S7 (S4 optional)   ──┐
   │                                                  │ parallel, Lean only:
Phase 2  R2: V0 → V1 → V2                            │ A3 A4 C11 B8 B9 A2 A1
   │                                                  │
Phase 3  compiler start on GIR: C2 C3 C4 → C5 → C6 … │ (C1 after R2)
   │                                                  │
Phase 4  R3: B6 (pieces i–viii, stages) → B7 ────────┘
   │
Phase 5  B10 (after A1 and the C rounds)
   │
Phase 6  R4: L0 → L1 → L3 → L2 → L4 → L5 → L6 → L7 → L8 → L9 → L10 → L11   (after all C packages)
   │
Phase 7  R5: K1 K2 (after C4 and L4/L5) → K3 → K5 on one core → K4 → K5 on two cores → C9 → K6
   │
Phase 8  K7: the compiler compiles itself; the runner leaves the tree
Later    X1, X2, X4, X5
```

**Rounds of full builds.** Every change of `Spec`, `Einheit`, `LogikPflicht`, the replay of `ZielOrt` or
`HaltArt` forces an almost complete grammatik build. They are batched into rounds (one full build each, plus at
most one repair run), as for the C packages:

| Round | Content | Phase |
|---|---|---|
| G1 | A3 + C11 + D11 | 0 |
| G2 | A1 + A4 (all changes of premise (c), with the environment class of §4.4) | 1–2, parallel |
| G3 | A2 (replay) | 1–2, parallel |
| G4 | B8 + B9 (`Einheit`, `HaltArt`) | 2 |
| G5–G7 | B10 by sub-package | 5 |
| G8–G12 | B6/B7 interfaces in `Zielsatz` and `Code/Conc` | 4 |
| G13–G23 | L1–L11, one round per item | 6 |

That is **about 23 full grammatik builds** for the goal theorem and the low-level model (30 min each with
`LEAN_NUM_THREADS=3`), plus the Stage-0 builds of S, V and B6 (compiler build 4–10 min, full stage0 after a deep
`Senke` change 20–40 min). The compiler and kernel streams (C, K) build in packages of their own, not sized here.

---

## 6. Critical path and parallelism

1. **To the compiler start:** S0m → S2 → S6 → V0 → V1 → V2. With S1, S2, S6 and V this is about 16 500–54 200
   lines. No day count exists for it: the earlier figure "10–28 working days" (COMPILER-READY §2.3) covered S1 and a
   bridge that was assumed to carry most forms; V0 measured that it carries 4 of 34 statement forms, and S2 is
   not sized until S0m has measured it. GabbroV, and inside it the bridge (V2), is the longest single chain.
2. **To trusted output:** S3 → B6 (stage "lock words as state" → "rely/guarantee simulation of one thread" →
   "process simulation and leg transfer") → B7. B6's second stage is the largest single uncertainty of the whole
   plan, and C9 repeats its shape for the compiler.
3. **To the kernel:** two chains meet in K5. The model chain is A1, A2 → L1 → L4 → L5 → L6 → L7 → L8 → L9 (R4);
   the compiler chain is C2 → C3 → C4 → K1, K2 → K3. Neither can be shortened by the other. The kernel gate
   cannot be reached with Stage 0: Stage 0 emits hosted images for the runner only (D16).
4. **In parallel with all of it, Lean only, no Stage-0 or runner change:** A1, A2, A3, A4, B8, B9, C11. They
   change the goal statement and need the owner's approval of each `Spec.lean` diff before merge. For the kernel
   A1, A2, B6/C9 and L7 are required, not optional.
5. **Gated by the owner:** every Spec change, the rule changes of §8, X1, X4, X5.

---

## 7. Size of everything

| Stream | Lean LOC (estimate) | Gabbro LOC (estimate) |
|---|---|---|
| S Stage 0 complete | 8 400–23 800 | — |
| V GabbroV to R2 | 12 400–40 900 | — |
| A fewer assumptions | 7 400–19 900 | — |
| B more conclusions (B6 alone 30 000–80 000) | 48 000–126 000 | — |
| C11 non-emptiness | 200–800 | — |
| L low-level model (L1–L11) | 58 500–146 000 | — |
| C compiler on GIR, Lean side (C1–C5, C9) | 84 000–210 000 | — |
| K kernel ready (K1–K6) | 26 000–72 000 | 14 000–40 000 |
| C compiler sources and benchmarks (C7, C8) | — | 125 000–276 000 |
| **sum** | **≈ 244 900–639 400** | **≈ 139 000–316 000** |

**Everything together: about 385 000 to 955 000 new lines**, of which roughly two thirds Lean. Not included: C6
(location assignment, scheduling, idiom cells, optimisation passes, further tables), which is sized only after C5
has measured what one proved pass costs.

Parts of the sum by gate (each includes what the earlier gates need):

| Up to | Lean LOC | Gabbro LOC |
|---|---|---|
| the compiler start (S1, S2, S6, V) | 16 500–54 200 | — |
| R3 trusted Stage-0 output (adds the rest of S, A, B, C11) | 76 400–211 400 | — |
| R4 low-level model (adds L) | 134 900–357 400 | — |
| R5 kernel ready (adds C1–C5, C9, K, C7, C8) | 244 900–639 400 | 139 000–316 000 |

Calibration (**measured**): seven Stage-0 forms took about 490 lines and 16 builds (2026-11-12); the float
satisfiability proof about 2 100 lines; the sequential `Senke` 62 700 lines; the goal-theorem proof `ZielOrt`
72 800 lines; the C08 foundation `FremdRuf` 2 400 lines; the deleted Rust duty generator 9 800 lines. The low
ends assume the existing infrastructure carries (replay, `runner_tso`, `Sperre/Interference`, the provider
model, the `walk` and `entry` syntax); the high ends assume per-form case work as in `Senke`. The L and K rows
have no measured calibration at all: no privileged operation, entry frame or translation regime exists in the
model today, so their ranges are the least certain of the table.

---

## 8. Owner decisions to take (consolidated)

| # | Decision | Recommendation |
|---|---|---|
| O1 | adopt this plan into AGENTS.md "Current work" (staffing, order) | yes, with the phases of §5 |
| O2 | A1 Spec diff: foreign software as user obligation in conditional form (= LOW-LEVEL decision 2) | yes; show the diff first |
| O3 | A2: lift `RegLokal` (not refuse carrier-less registers) | yes |
| O4 | A4, B8, B9, C11 Spec diffs | yes, batched in rounds G2/G4/G1 |
| O5 | named stop for stack depth instead of `abstieg` | yes, where the derived bound does not fit |
| O6 | substring as a language form (S1) | decide before S1 closes |
| O7 | record fields in table slots start at zero (`d9019873f`) | confirm |
| O8 | LOW-LEVEL decisions 1, 3, 4 (types and region-producer rule; first boundary and architecture; added goal coverage) | 1 and 4 as recommended there; 3 is replaced by O13 |
| O9 | counting simulation for instruction bounds (X4) | not now |
| O10 | `bedingt` → `endet` through a measure (X5); async drop/cancellation (X1) | later |
| O11 | staffing: delegates (AGENTS.md) or the lead alone. Owner, verbatim: to the goal-theorem session "mach alles selbst ohne agents"; to the Stage-0 session "agents bringen nicht viel, 95% deiner zeit wartest du auf Builds" (an observation about waiting, from which the writing-tree rule of `65cc01677` follows) | decide per phase; B6, L and C need several parallel workers, each in its own writing tree |
| O12 | **no assembly anywhere** (owner 2026-11-12) read as §4.1: no instruction text in sources, bindings or libraries; instructions only as target-table rows. This REPLACES the source ASM bodies of the low-level plan and the bundled `boot16to64` ASM item of 2026-11-03 (D12, D13) | confirm the reading; then correct AGENTS.md and the low-level plan |
| O13 | first boot boundary: firmware entry in 64-bit mode (§4.2), with `FirmwareHandoff` as a named environment assumption; reset in 16-bit mode later, if at all | yes |
| O14 | the environment class (§4.4, D14): software outside the verified image (an operating system below a hosted program, firmware before the entry) is a named assumption with a declared contract; software inside the image is always user logic. This changes the wording of AGENTS.md §3 | confirm; A1 is built with this class: the provenance `AxOrigin` gets a third value beside hardware and software (environment); for both software classes the caller proves the contract's `pre` at every call (`AxVor`, `CallSitePflichtFremd`); the image's own software proves `pre → post` (`ForeignPflicht`), environment software has `pre → post` named in (c); hardware keeps its unconditional contract |
| O15 | interrupts with re-entry and nesting (L7) and user-mode guests (L8) are in scope, as the kernel needs them | yes |
| O16 | a second binding (K6, AArch64) as the measure of architecture neutrality, before the kernel gate is called reached | yes |
| O17 | further cores on x86-64 through a generated start item of the binding (K4), accepted as the one place where 16-bit and 32-bit rows exist | yes; the alternative is a single-core kernel |
| O18 | a `while` loop (S0m: the form a compiler writer reaches for first; today recursion with a measure or `retry until … bounded` stand in) | decide: sugar over an existing loop with a user measure, or stay without |
| O19 | named effect groups: a module declares a name for a set of its places, and other modules write `effects b::group` instead of each table (S0m: cross-module writes need every slot table of the other module in the effect clause; the qualified place `b::T.slots` is a parser case and is done without a decision) | decide: a language addition with a model rule (the group unfolds to its places before `Akzeptiert`), or stay with the listed places |

O12–O17 were put to the owner on 2026-11-12 with this plan and answered "passt alles": they are confirmed. AGENTS.md
and LOW-LEVEL-SYNTAX-PLAN.md are corrected to them in the Phase-0 documentation pass (D12–D14).

---

## 9. Standing rules this plan relies on

- Lean model first; guarantees only from generic theorems; never weaken a check to make a case green.
- `gabbro_ziel` stays on exactly `propext`, `Classical.choice`, `Quot.sound` after every round.
- At most two Lean runs globally, slot locks, memory scopes without swap; **every `lake build` sets
  `LEAN_NUM_THREADS`** (full grammatik: 3, 13G); a job counter that stands still for 10 minutes means stop and
  restart with the table's values (AGENTS.md, 2026-11-12).
- Write in a writing tree beside the building tree (AGENTS.md, `65cc01677`). Between two pushes the compiler
  build (`lake build` of `stage0/`) and single-module checks are the test; the full `grammatik/` build runs once on
  the state that is pushed, batched into the rounds of §5.
- Every file below 500 lines, module system, English in the repository.
- Each Spec change is described in its commit and shown to the owner before merge.
- No instruction text in the repository outside the runner, and none at all after K7; a new handwritten assembly
  or C file is a finding (AGENTS.md §3, owner 2026-11-10 and 2026-11-12).
