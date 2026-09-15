# What cannot be written in Gabbro today

*Opus lane `schreibbar`, 2026-09-15, on master `f470f344`. Method: lane 201's — **write it,
run the tool, record what happens.** Twenty-one probe files under `messung/schreibprobe/`, run
with `gabbro pruefe`, `gabbro emit`, `gabbro lean-g`, `cc -std=c11 -Wall -Wextra -Werror` and,
where it links, the program itself. **No checker, emitter, grammar or rule was changed.**
Nothing was added to `beispiele/`; `MARKE_EMIT` untouched.*

---

## 1. The table

**Classes.** **(A)** no form at all · **(B)** the form exists, the checker refuses every shape
tried · **(C)** the checker accepts, the emitter has no arm · **(D)** writable, but only by
giving something up.

### 1.1 The runtime — the owner's top priority

| # | What a writer cannot write | Class | Probe | What the tool said, verbatim |
|---|---|---|---|---|
| **1** | **Start a thread on a declared root.** `concurrent { hauptA, hauptB };` declares that two bodies run at once; nothing starts them, and the emitted unit has no caller for either. This is `pthread_create` in `laufzeit/start.c`:158-167. | **A** | `S01-faden-start.gab` | 6 shapes. `concurrent {…};` in a body → `[P017] assignment or call expected, `{` found` + `[P033]`; `spawn f;`, `start f;`, `concurrent f;` → `[P017]`; `threads {…};` → `[P017]`+`[P033]`; `let t = spawn(f);` → `[M119] `spawn` is declared nowhere` + `[H021]`. The seventh shape, `hauptA();`, parses — and is a sequential call, not a thread. |
| **2** | **An entry point and an exit code.** `main` in C. `entry`/`boot` exist and emit a prototype plus a `#define`, never a body (see #12). An `impl fn` lowers to `static`, so nothing in an emitted unit can be C's `main`. | **D** | `S05-treiber-in-gabbro.gab` | Accepted (0 errors). The exit code travels as an ordinary return value nobody reads; the driver that reads it is C. |
| **3** | **A message.** No string type, no string in an expression, no varargs. `printf("konto=%u…", …)` in `start.c`:195. | **A** | `S05-treiber-in-gabbro.gab` | `melde_text("INVARIANT BROKEN");` → `[P011] expression expected, string found`. `melde_stand(a, b)` on a 1-parameter callee → `[M143] declares 1 parameter(s), this call passes 2`. Strings exist only as the text of `assume`/`claim`. |
| **4** | **A boolean flag at module scope.** `static mut bereit : bool = false;` — a stop flag, a ready bit, an initialised latch. | **C** | `S16-bool-statik.gab` | `gabbro pruefe`: **0 errors, 0 hints.** `gabbro emit`: `error: [C001] …:12: no lowering: `static` with a non-constant initialiser`. 4 shapes: `= false`, `= true`, without `mut` — all three `C001`; the same line at `u32` emits. `emit.rs`:2258 evaluates the initialiser to an integer and refuses when it gets none. **No corpus program carries a `bool` static**, so no guardian sees it. |
| **5** | **`atomic_fetch_add`.** `SPRACHE.md` promises a primitive `exchange update` body lowers to `atomic_fetch_*`; `CTicket.lean`'s `zieht` is one wait-free step. | **C** | `S06-fetch-add.gab` | Accepted, 0 errors, C written — and the C is a bounded `atomic_compare_exchange_weak_explicit` loop with a writer-chosen bound and a `_Noreturn` exit at overrun. **Measured over the whole corpus: 0 of 113 emitted units contain an `atomic_fetch_*`; the string occurs once in `emit.rs`, inside a comment (line 9263).** `accumulates … merge max/add` also lowers to load/store on per-cpu cells, not to a fetch op. |
| **6** | **Wrapping arithmetic over a local.** `n +% 1` where `n` is a `let` local or an `exchange` binder. | **C** | `S07-wrap-ueber-lokaler.gab` | `gabbro pruefe`: 0 errors. `gabbro emit`: `error: [C001] …:12: no lowering: wrapping `+%` over operands whose exact ranges cannot be read off their declarations -- both sides need an exact unsigned range `0 .. 2^N - 1` on one storage width`. The same line over a **parameter** and over a **static** emits. Lane 201 routed around it with a helper whose parameter is readable. |
| **7** | **The idle root.** `for (;;) pause();` / `wfi` — what every thread that is not a declared start runs (`start.c`:128-146, `E.P.mitRuhe`'s `none`). | **D** | `S04-ruhewurzel.gab` | Accepted, and the C is `for (;;) { warten(); }`. **The price:** `forever` demands `progress <ident>` (compulsory, «SG-11») and `[S003] `progress …` names no declared assumption` refuses a bare name — *"otherwise it is a hope with a keyword in front"*. An idle root is a loop **nobody** ends, and that is the one thing the clause cannot say; the file declares an assumption that states the opposite of what is meant, with a falsifier that can never fire. Also: `[K003] `ruhe` promises costs, but a `forever` loop has no total cost` — an idle root cannot carry the unit's cost register at all. |
| **8** | **Define the lock primitive the emitter calls, in the same unit as the lock.** | **B** | `S02-sperre-selbst-definiert.gab` | 2 shapes. `impl fn L_nimm()` beside `lock L` → `[N042] `L_nimm` is the C name of two different declarations` … *"the generator forms `L_nimm` here as `{fn}` … and it forms the same name as `{Lock}_nimm` -- the acquire primitive … rename one of the two"*. `pub impl fn L_nimm()` adds `[N038]` (exported and names non-exported atomics). |

### 1.2 The Caprock areas

| # | What a writer cannot write | Class | Probe | What the tool said, verbatim |
|---|---|---|---|---|
| **9** | **Move a `state` field.** `transition T.slots[i].s : A -> B;` — `stateassign`, «SG-19», `SYNTAX.md`:866, in §8's table with `Stmt.uebergang` and the theorem `uebergang_erklaert`. **The Rust statement parser has no `Kw::Transition` arm** (`crates/gabbro-syntax/src/parse.rs`:3467-3630), so a `state` declaration is unusable: the only statement that could use it does not parse. F3's reply obligation. | **A** | `S08-zwei-orte-ein-uebergang.gab` | 5 shapes, all `[P017] assignment or call expected, identifier `Endpunkte` found`: `: A -> B;`, `: 0 -> 1;`, `transition oeffnen;`, `transition S.oeffnen;`; plus `S.oeffnen();` → `[M129] is not a function pointer` and `oeffnen();` → `[H021] unknown to the graph`. |
| **10** | **Advance a phase mark.** `advances a -> b;` — `advstmt`, «SG-14», `SYNTAX.md`:847, with its own resource rule in §8 (`Λ after … = Λ − marke(m,a) + marke(m,b)`). **Same hole:** no `Kw::Advances` arm in the statement dispatch. The *signature* clause parses. F7's boot ladder, F4's `QueueSetup`. | **A** | `S09-advances-anweisung.gab` | `[P017] assignment or call expected, identifier `roh` found`. **And the promise is vacuous:** delete the line and the file is **0 errors** — `stufe_eins` then promises `advances roh -> mmu` with a body that advances nothing. Today every advancing step in the corpus is an `extern fn` (`beispiele/22`), i.e. a named assumption. |
| **11** | **Stop a table walk at the first hit.** `traverse` takes **no label**, and `leave` must name one. F3's fastpath, F1's `peak_revoke_ops`. | **B** | `S13-erster-treffer.gab` | 2 shapes. `leave i;` → `[S001] `leave i` targets no enclosing loop label` … *"there is no unnamed `break`/`continue` -- with nested loops the target would be convention … `retry`/`forever` take one"*. `traverse runde i over …` → `[P001] `over` expected, identifier `i` found` — the `ident` after `traverse` is the binder. **What is left:** walk all 64 slots and guard every later pass, or write it as a `retry` and hand-thread the index with its range re-proved. |
| **12** | **A function pointer to something that takes a lock.** F3's `&mut dyn SchedOps`; `SCHEDS` is a lock in every Caprock fragment. | **B** | `S19-zeiger-der-sperrt.gab` | 5 shapes. `locks SCHEDS` at the `fn(…)` type → `[N036] `locks` cannot be promised at a function pointer type` … *"the pass that reads this effect resolves the callee by NAME, and an indirect call has none … this is a refusal and not an omission"*. Same for `masks` and `publishes`. And from the other side, with the clause dropped or replaced by `requires Held(SCHEDS)`: `[M128] `fn() -> u32` does not fit `fn() -> u32`: it declares `locks SCHEDS`, which the slot does not allow`. **What is left:** the lock is taken outside the indirect call, and the discipline moves from the vector to every call site. |
| **13** | **Type application.** `Queue(T)`, `Outcome(T,E)`. `TODO.md` §0 defers the standard library for want of *content* — "no ring buffer, no queue"; without this it is one queue per element type. | **C**, and an **UNCOVERED** clause beside it | `S20-typanwendung.gab` | `type Queue(T) = { kopf : u32, ende : u32, };` → **0 errors, emit rc=0**, and `gabbro emit` of it against `type Queue = {…}` is **byte-identical C with an unchanged obligation register**. The list parses because `typedecl` carries `[ "(" typelist ")" ]` for `linear ghost type Held(Lock)`; on an ordinary `type` nothing reads it. Using the parameter: `w : T` → `gabbro pruefe` 0 errors, `gabbro emit` `[C001] …:43: no lowering: field type`. `type Queue<T>` → `[P001] `;` expected, `<` found`; `table Queue(T) count N` → `[P001] `{` expected, `(` found`. |
| **14** | **Aggregation in a predicate.** `count k in slots of T : p` inside an `invariant` or a `spec fn`. F1's `refcount_matches` — the capability system's bookkeeping. | **B** | `S11-zaehlung-im-praedikat.gab` | In an `invariant` → `[D021] `k` in an `invariant` is not declared here`; in a `spec fn` body → `[D021] `k` in the body of a `spec fn` is not declared here`. The binder is not bound in either. **Four further spellings** of the cross-table form → `[P012] predicate expected, identifier `Objekte` found` (×2) and `[P001]`. **The same expression IS accepted in an `ensures` and in a body** (`beispiele/71`:33) — so the aggregation exists as a computation and not as a statement. The cross-table half is refused **by decision** (`SYNTAX.md`:554: *"over ONE table only … A cross-table count is a `group` invariant"*). |
| **15** | **`refcount -= 1` under a relational `requires`.** «B29», *"the contested case of the dividing line, on a real case"*. | **D** | `S10-refcount-minus-eins.gab` | Under `requires Objekte.slots[o].refs >= 1`: `[M104] `Objekte.slots[…].refs` -= leaves the range: `u32 in 0 .. 64` against `u8 in 1 .. 1`` and `[M101] the assignment requires `u32 in 0 .. 64`, the value has `u32 in -1 .. 63``. **The `requires` is not read by the range pass.** Two shapes pass, and both cost the same: `if refs >= 1 { refs -= 1; }` and `narrow refs to 1 .. 64 else { return; }` — the precondition written twice, once as a promise the caller owes and once as a branch the callee runs. `M104`'s own note draws the line: *"a relation between two places carries too (V2)"* — between a place and a constant, in the `requires`, it does not. |
| **16** | **`option` of an ordinary type.** F5's `let mut capacity : option Sectors = none;`, F6's `frei_min : option Bytes`. | **A** | `S12-option-als-typ.gab` | `-> option Sektoren` → `[P001] `index` expected, identifier `Sektoren` found`. `option` takes **only** a table index. |
| **17** | **A record as a value that reaches the proof.** | **B at the third tool** | `S18-verbund-als-wert.gab` | `gabbro pruefe` **0 errors**, `gabbro emit` rc=0 with `return (Completion){ .id = k, .len = n };`, `gabbro lean-g` → `[LG002] the result of fertig is the record Completion, and a record has NO `Ty` … it does NOT travel as a value, so a result, a parameter or a `let` of record type has no form at all`. The braced spelling is refused and names the working one: `[P037] Gabbro has no braced record literal … one writes `P(a: 1, b: 2)``. **Already priced and refused** as `OFFEN.md` O15/O16 (zero of 113 corpus programs gained). |
| **18** | **A multi-line assumption text.** All three `claim` texts and two `assume` texts of F2/F6 are multi-line. | **A** | `S21-mehrzeilige-zusicherung.gab` | `[L001] string literal with no closing quote` (×2) and `[P029] `falsifier` or `unfalsifiable` expected`. No concatenation, no newline escape. What is written instead is one 300-character line — this probe's own `assume` is one. |
| **19** | **The kernel-side entry stub.** `entry syscall vector 0x80 … regs in { nr : rax, … }` parses and checks; the emitted C is a `#define` for the vector, a prototype and a comment. | **D**, and it says so | `S14-syscall-und-asm.gab`, `beispiele/07` | `gabbro emit beispiele/07`: `#define gabbro_eintritt_syscall_VEKTOR 128u` / `void gabbro_eintritt_syscall(void);` / a dispatch pointer — plus *"THE STUB IS NOT A C FUNCTION. It is entered by hardware, it keeps the register footprint above and it leaves with `iretq` -- none of which C can write. What stands here is the PROMISE."* The register map travels as a comment. `boot` the same, nine steps as nine comment lines. |
| **20** | **A register wider than `u64`** — VT-d's 128-bit context entry, «B24». | a **decision**, not a gap | `S17-vtd-gemischtes-register.gab` | `DID @[66:64]` → `[N007] bit 66 of `DID` lies outside its own word (u64 has bits 0..63)` … *"«B24», decided 2026-08-18: a position lies inside the field's OWN word … A 128-bit entry is TWO words, and saying so is cheaper than a rule about crossing"*. Listed so it is not counted twice: the refusal names its own decision. |

### 1.3 Writable, and this tree says it is not — four findings the other way

| # | Finding | Proof |
|---|---|---|
| **P1** | **The runtime's lock primitive can be written in Gabbro, linked and RUN.** `laufzeit/start.c` says *"a lock is a runtime object (futex, ticket lock, interrupt mask), **never program text**"* and defines `L_nimm`/`L_gib` as a POSIX mutex. Measured otherwise: `pub impl fn L_nimm()` in a unit of its own emits **`void L_nimm(void) { … }`** — non-static, the exact symbol `beispiele/124`'s emitted C declares. | `S03-sperre-eigene-einheit.gab` (0 errors, emit rc=0) + `S03-treiber.c` (= `start.c` with the mutex half cut out). `cc -std=c11 -O0 -Wall -Wextra -Werror -pthread` clean; **10 runs, all exit 0**, `konto=30 konto=30` once and `konto=70 konto=70` nine times — both schedules, the lock invariant holds in every run, no lost private write. **The ticket lock of `laufzeit/sperre.gab`, in Gabbro, serving a real two-thread program.** |
| **P2** | **«B17» first half is closed:** a `transition` takes SEVERAL places in one move (`transset = placeshift { "," placeshift }`), and the two-place `state` block of `S08` checks. F3's *"`caller` and `reply_owner` never half set"* is declarable — it is only unusable, for the different reason in row 9. | `S08` (7 items, the ONLY error is the statement) |
| **P3** | **«B23» is closed:** a register FIELD carries its own class (`regfeld = ident "@" bitpos [ "class" regklasse ]`), so VT-d's `FSTS` writes `PPF @1 class w1c` beside `FRI @[15:8] class r`. F2's last standing finding. | `S17` (the only error is the 128-bit line) |
| **P4** | **«B27» is closed on the user side, artefact and all.** *"The place at which 168 `asm!` sites were meant to converge has no content"* — `syscalldecl` («SS-1») emits real inline assembly: `register uint64_t _sys_rdi __asm__("rdi") = (uint64_t)fd; … __asm__ __volatile__("syscall\n" : "+a"(_sys_rax) : "r"(_sys_rdi), … : "rcx", "r11", "memory");` generated from one declaration. | `S14` (0 errors, emit rc=0) |

**Further «Bnn» measured closed on the way, each with the file that shows it:** «B2» (atomics and locks are reachable — every probe here declares one) · «B6» (`result` in an `ensures` — `S14`, `beispiele/124`) · «B7» record constructor and array literal (`S18`, `beispiele/123`) · «B8»/«B9» call through a place and a contract at the pointer type (`beispiele/49`, 2026-08-21; the residue is row 12) · «B11» `forever` has a named exit (`S15-dienstschleife-mit-ausgang.gab` — **F5's lethal finding is gone**) · «B12» second half (`slots of` binds an INDEX, and `D022` says so) · «B14» first half (`option index into T` works as a parameter and as a local — `S12`) · «B21» `accumulates max/min/add` (`beispiele/05`, and it emits) · «B31» `old()` inside an arithmetic expression (`S10`, `beispiele/104`).

---

## 2. Where this leaves the runtime

`laufzeit/start.c` does five things. **One of them is no longer C:**

| what `start.c` does | can it be Gabbro today |
|---|---|
| defines `L_nimm`/`L_gib` (POSIX mutex) | **YES — measured, linked, run.** Row P1. The lock stops being a runtime assumption and becomes a program. |
| starts one thread per declared root (`pthread_create`) | **No form at all.** Row 1. |
| joins them (`pthread_join`) | **No form at all.** Not separately probed — the same absence as row 1. |
| parks every other thread in the idle root | **Yes, at a price.** Row 7: the body and the C are right; `progress` forces an assumption that says the opposite of what is meant. |
| `main`, the printed line, the exit code | **`main` no; the line no; the code only as a value nobody reads.** Rows 2 and 3. |

**So the honest shape of the runtime today is: the lock is Gabbro, the thread start is not.** The
remaining C is small and it is exactly the part the goal theorem books as assumption (d)
`Laufzeit` — and rows 1 and 2 say that assumption cannot currently be discharged by a program,
because the act of starting a body has no syntax. That is one word (`concurrent` already names
the set) and one statement form away, and it is the single highest-leverage absence in this
report.

## 3. The pattern that runs through rows 9, 10 and 13

**Three forms stand in `SYNTAX.md`, two of them with a Lean constructor and a theorem, and no
program can use them.**

- `stateassign` (row 9) — EBNF, §8's statement table, `Stmt.uebergang`, `uebergang_erklaert`.
  No parser arm.
- `advstmt` (row 10) — EBNF, §8's resource table. No parser arm. **And the signature clause
  that promises the advance is accepted with a body that does not advance** — a promise nobody
  keeps that looks kept.
- the `typelist` on an ordinary `type` (row 13) — parses, and its presence leaves the emitted C
  byte-identical.

`pruefe-syntax.sh` measures EBNF **closure** and **reachability from `program`** — 177 rules,
0 open, 0 unreachable — and both are true of all three. Neither question is "does the parser
have an arm for it". The `UNCOVERED` cell of `instrumente/miss-grammatikdeckung.py` is built
for exactly this class and its population is the *derived* grammar (the decision points of
`parse.rs`), so a form the parser never reaches is not in its denominator either. **A form in
the document with no arm in the parser is measured by nothing today.**

*The cheap instrument, if one is wanted: every `Kw::` in the statement and item EBNF held
against the `match` arms of `parse.rs`. That is a text comparison, not a build.*

## 4. What was NOT measured, and is therefore not claimed

- **`./instrumente/miss-grammatikdeckung.py` was not run.** The 23 UNCOVERED forms named in the
  task are taken from the instrument's own description and from `SYNTAX.md`; this report adds
  one measured instance of the class (row 13) and one argument about the denominator (§3). The
  census itself rebuilds per form and belongs on `fisch` with time for it.
- **No proof, no Lean.** Nothing in `grammatik/` was touched or read for a theorem. Row 17's
  `LG002` is the exporter's refusal, not a statement about the model.
- **The `pthread_join` absence** (§2) was inferred from row 1, not probed on its own.
- **Only `x86_64`, gcc 13.3.0, `-O0`.** The P1 run is 10 executions on one machine under no
  contention; the ticket lock's bounds (64 CAS passes, 1431655765 spin passes) were never
  reached and are therefore untested, exactly as lane 201 recorded.
- **Of the 38 «Bnn» findings in `FRAGMENTE.md`, this lane re-measured 15 and read the rest.**
  The unmeasured ones are named so nobody reads a silence as a verdict: «B1» «B3» «B4» «B5»
  «B16» «B18» «B19» «B20» «B22»-adjacent `claim` positions, «B25» «B26» «B28» «B30» «B32»-«B40».
- **`cargo test --no-fail-fast`** was started on `fisch` in `gabbro-opus-schr` after the probes
  were in place. The diff adds no Rust and no corpus file; `beispiele.rs`/`korpus.rs` walk
  `beispiele/` and `dokumente/FRAGMENTE.md` only, neither of which this lane touches.

## 5. Files

```
messung/schreibprobe/S01-faden-start.gab                start a thread on a declared root
messung/schreibprobe/S02-sperre-selbst-definiert.gab    L_nimm beside its own lock          N042
messung/schreibprobe/S03-sperre-eigene-einheit.gab      the lock as its own unit            ACCEPTED
messung/schreibprobe/S03-treiber.c                      start.c minus the C mutex           RUNS
messung/schreibprobe/S04-ruhewurzel.gab                 the idle root, with a body          ACCEPTED (D)
messung/schreibprobe/S05-treiber-in-gabbro.gab          main, the message, the exit code
messung/schreibprobe/S06-fetch-add.gab                  atomic_fetch_add                    (C)
messung/schreibprobe/S07-wrap-ueber-lokaler.gab         +% over a local                     C001
messung/schreibprobe/S08-zwei-orte-ein-uebergang.gab    two places, one transition          P017
messung/schreibprobe/S09-advances-anweisung.gab         advances as a statement             P017
messung/schreibprobe/S10-refcount-minus-eins.gab        refcount -= 1                       M104/M101
messung/schreibprobe/S11-zaehlung-im-praedikat.gab      count in a predicate                D021
messung/schreibprobe/S12-option-als-typ.gab             option of an ordinary type          P001
messung/schreibprobe/S13-erster-treffer.gab             first hit over a table walk         S001
messung/schreibprobe/S14-syscall-und-asm.gab            the syscall ABI                     ACCEPTED
messung/schreibprobe/S15-dienstschleife-mit-ausgang.gab F5's service loop with an exit      ACCEPTED
messung/schreibprobe/S16-bool-statik.gab                a bool static                       C001
messung/schreibprobe/S17-vtd-gemischtes-register.gab    mixed register, 128-bit entry       N007
messung/schreibprobe/S18-verbund-als-wert.gab           a record as a value                 LG002
messung/schreibprobe/S19-zeiger-der-sperrt.gab          a fn pointer that locks             N036/M128
messung/schreibprobe/S20-typanwendung.gab               Queue(T)                            C001
messung/schreibprobe/S21-mehrzeilige-zusicherung.gab    a multi-line assumption text        L001
```

**Reproducing P1** (the one measurement with a running program):

```bash
K=$(mktemp -d)
target/debug/gabbro emit beispiele/124-two-threads-private.gab            > $K/einheit124.c
target/debug/gabbro emit messung/schreibprobe/S03-sperre-eigene-einheit.gab > $K/sperre.c
printf '#include <stdlib.h>\n_Noreturn void warte_aufgegeben(void);\n_Noreturn void warte_aufgegeben(void){ abort(); }\n' > $K/stop.c
cc -std=c11 -O0 -Wall -Wextra -Werror -pthread -I $K \
   -DEINHEIT_INCLUDE='"einheit124.c"' -o $K/lauf \
   messung/schreibprobe/S03-treiber.c $K/sperre.c $K/stop.c
$K/lauf    # konto=<n> konto=<n> privA=7 privA=7 privB=5 ; exit 0
```
