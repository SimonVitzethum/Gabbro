# Gabbro — open items

*Rewritten from scratch on 2026-09-15, after the goal theorem was confirmed. The previous file
(5,441 lines, stages 0–9 from August) is in the git history at commit `1434efba`. Everything it
listed is one of four things:*

- *done;*
- *superseded by the goal-theorem track;*
- *recorded as a known absence in `dokumente/OFFEN.md`;*
- *deferred (last section).*

*Its guardian-booked figures moved verbatim to `messung/KENNZAHLEN.md`. How the work is run —
machines, lanes, merge scripts, number ranges — is in `AGENTS.md`.*

**Where we are.** `gabbro_ziel : GabbroZiel` is proved over the Lean model and was confirmed by
two independent reviews in round 6 (tag `milestone-2026-09-15-zielsatz-bestaetigt`). Following
Simon's end sequence, the work now is:

1. transfer into the checker and the emitter (§1);
2. translation validation (§2): **direct x86-64 output validated through final machine bytes**
   (Simon's decision, 2026-10-01). The backend and validator are planned. The existing
   `instrumente/zaehle-kette.py` counts C-model chains; its results remain historical C evidence,
   not a measurement of machine-code validation.

Each item names its owner (lane or agent) where one is running.

---

# -1. Verdict walls: the not-going code (first)  ⟨A⟩

*14 walls from the firewall-in-Gabbro tree (`Verdict/messung/BEFUNDE-bm*.md`,
measured against Gabbro master `71c5eaea`); 3 cost nothing — N042/N323 and
atomic arrays are built, sigaction stays out by design (threshold counters
are free). The remaining 11 were cut into 26 lanes in 3 waves below: 24 Muse
lanes (workers 221–248, 230 unused) + 2 Opus lanes (O-1, C-2, sequential —
both touch the model core). Waves A–E ran 2026-09-17 to 2026-09-26; lanes
249–258 were added later (waves C–E and §0). O-1 landed via fix lanes F3/F9,
C-2 via the syscall lanes. Review loop (`bin/review-wache.sh`, max 3
rounds, builds re-run by the reviewer) covered workers 221–248 with
reviewers from 321; the dispatcher worker list was extended on
2026-09-19. The
number ledger is `AGENTS.md` §7. What is still open from these waves stands
in the wave sections below; the rest is history.*

**Binding constraint (Simon): no language feature hard-depends on an OS.**
Syscalls are always user-made — declared in-program (`extern`/`syscall`
items carrying ABI numbers, registers, costs), never baked into the tree
as OS tables. This shapes lane 226 (fd + open/read declarations, no
number table in `crates/`), O-1 (handoff shape OS-agnostic, clone numbers
stay in user code) and C-2 (address + timespec carrier, no `CLOCK_*` in
the tree). A lane that smuggles an OS constant into `crates/` or
`grammatik/` fails review.

**Safety is never traded for features** (Simon): no lane weakens a
guarantee — memory safety, race freedom, contracts, costs, lock
discipline — to make a wall go green. A wall that only yields by
weakening is recorded as a finding (like 208's vacuity pins or 203's
recorded blockage), never bypassed. A bypass fails review, no matter how
green its build is.

**Decision gate RESOLVED 2026-09-17 (Simon): LIFT.** Criterion was the
project goal — a `folge()` wrapper around a proved bound is user ceremony
for language plumbing, and plumbing belongs to the language, not to the
proof. Lane 221 launched on that basis (`OPUS-BERICHT-FETCHADD.md` §2.3
patch shape + surviving test).

**Wave A (ran 2026-09-17 to 2026-09-26):**

| lane | wall | files owned (exclusive) | size | reserves N / gift / ex |
|---|---|---|---|---|
| 221 | `+%` fetch_add (bm4-F5) | `emit.rs` fetch arm, `tests/holform.rs` | S | N391–395 / 1052–1056 / — |
| 222 | syntax: int-match arms + traverse domain | `parse.rs`, `lex.rs`, `kw.rs`, `ast.rs` | M | snippets only (no corpus files) |
| 223 | costs on extern, trusted (K003) | `kosten.rs` | S | N396–400 / 1057–1061 / — |
| 224 | m1 bound shapes (`k-1` class, first shapes) | `m1.rs` | M | none (existing M101) / — / — |
| 225 | never-bodies accept (asm/forever) | `namen.rs` (`asm_never` region) | M | N401–405 / 1062–1066 / — |
| 226 | fd + open/read decls (L-2, OS-agnostic) — **fixed by fix lane F5 (2026-09-22, review G04 F2–F6):** 149's register map is Linux `open(path, flags, mode)` (measured on the emitted C), the NUL-terminated path is a named caller obligation (`spec fn path_nul_terminated`, counted `V`), open/read carry their own assumptions and probes (`sonde_open`, `sonde_read`), the frame length is decided (`N463`/`N464`, `requires len <= lenof(buf)`). **Open:** `OFFEN.md` O23 | `syscall.rs`, decl shape | M | N406–410 / 1067–1071 / 149–150; F5 took N463–N464, gifts 1155–1158 |
| 236 | ALG sketch FTP (Obergrenze): 1024 control table, 512 B bounded buffer + refuse, hash match, fenster-expiry, VOLL-refuse, packet-tick — **fix lane F7 (review G05 F1):** the word-wise hash now folds `h ^ (h >> 22)` before `% 1024`, so every input bit reaches the bucket (the G05 collision pairs split; emitted C = Python model); `fnv` costs 95 → 101 | new `beispiele/` only | M | no new codes / — / 147–148 |
| 237 | layout-factor muster: word tables + index arithmetic (`i>>2`, `(i&3)*8`), static-link budget measured | new `beispiele/` + report only, NO `m1.rs` (lane 224 owns it) | S | no new codes / — / 151–152 |
| O-1 | clone handoff (K-1) | new syntax + new Lean files, `Spec` diff | XL | SPLIT 2026-09-18: checker + emitter TRANSFERRED (N446–N450, C185 refusal, LG004 exporter refusal; no Linux constants, verified by grep); Lean model + Spec (d2) under REVIEW (lane 372, O-1 branch; the branch is an ANCESTOR of master since merge `a4461b6b`, so `git merge` is a no-op -- take `cde18e25` by checkout/cherry-pick; review G11: under (d) `CloneAssume` is vacuous, no child thread exists in the model). Fix lane F3 (2026-09-21): the child is a thread in the checker (`N456` no child under a held context, `N457` race rule over the region and its callees, held-set walkers reset at `child`), `N450` per region (one dominating gate call), spill read set exhaustive; the lowering must enter the child BY JUMP at the region (PLAN-SYSCALL, pinned by `tests/klon_faden.rs`). Fix lane F9 (2026-09-22): the Lean half is in, REWORKED -- `CloneHandoff.lean` models the child as a spawned thread of machine G (dormant slot + spawn rule, `klonErreichbar_G`, `klon_kind_haelt_nichts` ~ N456, `klon_ziel` ~ N457, witnesses on 124 and a stepping child run); the vacuous (d)/(d2) Spec diff of `cde18e25` was NOT taken, `GabbroZiel` unchanged. Open: Teil 3 (inline-trap lowering + correspondence), `child` in the exporter (LG004), a child in `GabbroZiel` itself (spawn-time data, repeated spawns), N457 => Lean acceptance of the child as a start. |

**Wave B (after A: emit.rs free from 221, AST known from 222, K003 from 223):**

| lane | wall | files owned (exclusive) | size | after |
|---|---|---|---|---|
| 227 | switch lowering (int-match) | `emit.rs` | M | 221 |
| 228 | match semantics (Lean) | new `CFormMatch`-family file | M | 222 |
| 229 | subrange traverse checker: effects + early exit (S001) — MERGED `e2184405` as the traverse-OBJECT read rule only (E010/E011, gifts 1077/1078); window bounds and labelled exit NOT built (no AST home) | `wirkungen.rs`, `absenkung.rs` | L | 222 |
| 231 | divergence lemmas (Lean) — merged (`fa68bbb2`); **fix lane F8 (2026-09-22, review G10 F3):** the `KeinLogikHaltG` "bridge" was one step and vacuous; now `spin_prueft` (every `PrueftG` clause at every head of the empty `forever … invariant true` spin) with a REACHED G-machine witness `ewig_spin_zeuge` (`KeinLogikHaltG` for the whole machine), per head only; `nieZurueck_blatt_frei` renamed `bindAxiom_kein_blatt` (discrimination only). SATZKARTE §46 | new file | M | 225 design |
| 232 | hold chunking (K002) — MERGED `f8a946cd` as advisory `N421` beside `K002` (gift 1082); no chunking mechanism, the windowed scan needs the window syntax | `kosten.rs` | M | 223 |
| 233 | syscall/fd model (Lean) — merged; **fix lane F5 (2026-09-22, review G10 F5):** `FremdRuf.lean` §9 splits the gate contract (caller precondition `AufruferPflicht` vs hardware `AxVertragOP`) with a bridge to `HardwareAnnahmen`; `fdQ` admits fd 0; `Spec.lean` unchanged (`OFFEN.md` O23, SATZKARTE §42) | new file, no OS constants | M | 226 |
| 234 | traverse lowering | SUPERSEDED by 252 below (234's tree predated 222/229; pins archived as `archive/234` on origin) | — | — |
| 252 | traverse lowering, fresh tree — MERGED `d8792871` as exit PINS only (`tests/traverse_exit.rs`, doc comment in `emit.rs`); nothing salvaged from `archive/234` (unreachable), no window lowering | `emit.rs` | M | 222, 229 merged |

*Wave-B reserves: 227: N411–415 / 1072–1076; 229: N416–420 / 1077–1081 /
151; 232: N421–425 / 1082–1086. Lean lanes (228, 231, 233) need no codes —
witnesses instead of poison probes.*

*Wave-B traverse walls still OPEN after 229/232/252 (review G09, 2026-09-21;
the three merge messages describe the lane TASKS, not what landed -- the
lane reports `messung/muse/MUSE-REPORT-229.md`, `-232.md`, `-252.md` are
the accurate record):*

- *window `traverse … from <start> count <len>`: parses to `P001` and
  builds no AST node; bounds against effects/`touches`, lowering and the
  real hold chunking all wait for a syntax lane (252 F1 gives the spec);*
- *traverse-labelled exit: needs a label slot in the grammar (252 F2);
  exits to an outer `retry`/`forever` label already lower and are pinned;*
- *`retry` whose body holds a `traverse` passes the checker and falls at
  emit with `C001` (per-pass cost not fixed) -- pre-existing (252 F3);*
- *~~`E011` holds only the body's direct deeds: a call inside a `traverse`
  body is never held against `touches`.~~ **Closed by fix lane F7
  (2026-09-22):** every call in the body and in the object is held against
  `touches` through its callee's hull (gift 1169), and `E011` runs under a
  derived clause too (gift 1170). Corpus: `beispiele/09` named a callee read
  in its `touches` line (C byte-identical).*

**Wave C:**

| lane | wall | files owned (exclusive) | size | after |
|---|---|---|---|---|
| 235 | never/never-asm lowering | `emit.rs` | M | 252 |
| 249 | spill-read rule: child vs caller-frame (Teil 3 gate) | `clone.rs` | S | — |
| 250 | `D.klon` exporter fill (O-1 remainder) | `lean_g.rs` | M | — |
| 251 | inline-trap lowering, FIRST attempt (FINAL-ROT after 5 rounds — core deliverable never landed; salvageable parts feed 258) | `emit.rs` | M | superseded by 258 |
| 258 | Teil-3 trap lowering, second attempt (GRANT: zeugnis `child` booking + marker rebook; D.klon present via 250) | `emit.rs` + `CFormTrap` + tests | M | 249, 250 merged; salvages 251 (CFormTrap skeleton, gifts, harness) |
| C-2 | address-of + timespec (L-1/bm8-F3) | model core, `Spec` diff | XL | landed via the syscall lanes (Opus L, N562–N567) |

*Launched 2026-09-18 as lanes 242 (+248, emitter arm queued post-235):
**mmap-backed tables** (Obergrenze #2). `table … storage mmap`: same
checker rules (240's `max` cap), runtime reserves virtual + commits on
demand (`laufzeit/`, A4-style assumption — OS rule holds: no ABI constant
in the tree), Lean region (241's `ArenaDyn`) + mmap-contract assumption
as ONE-list entry. The 40 GB number itself is irrelevant — what counts is
statically linkable, bucket-bounded, refuse-on-full (lanes 236/237 prove
the discipline without it).*

**Wave D — bounded dynamic memory: 300 MiB working set, 30 GB ceiling,
near-Rust efficiency (Simon).** Reservation vs commit split: the program
declares the ceiling statically, the runtime (A4-style assumption, NOT a
language feature — the OS rule holds: no ABI constant in the tree)
reserves virtual and commits on demand; faults cost as a named hardware
assumption. Efficiency is measured first (census vs handwritten Rust
`repr(C)`), then enforced: Gabbro owes at most the proved plumbing over
Rust, never a header per object.

| lane | what | files owned (exclusive) | size | after |
|---|---|---|---|---|
| 238 | efficiency census: emitted layouts vs Rust | new `messung/` report only, NOTHING else | S | — |
| 239 | dynamic-table design (`PLAN-DYNAMISCH.md`): `max` cap clause, fault-vs-explicit growth, free discipline, fault-latency assumption text, Lean sketch, efficiency budget | new doc only | M | 238 consults |
| 240 | checker: `max` cap, growth points, cap refusal | `arena.rs` + new module, NOT `kosten.rs` (223/232) | M | 239 |
| 241 | Lean: virtual region + commit subset + refinement | new files | M–L | 239 |
| 242 | runtime: reserve/commit, mmap backing, OOM fail-stop + emitter-arm SPEC (no `emit.rs` — owned by 234→235) | `laufzeit/` + new module, examples 153–154 | M | 239, 240, 241 |
| 243 | free discipline (arena-reset proof or linear free-list) | new files + 240's region | M | 240 |
| 244 | efficiency fixes: kill census overhead | measured sites only | S–M | 238 |
| 248 | emitter arm for reserve/commit — merged as gate-doc (max/grow syntax missing, arm queued) | report only | S | 235, 242 |
| 257 | max/grow syntax (unblocks the arm) | `parse.rs`, `ast.rs` | M | — |

*Review G08 fix lane F2 (2026-09-21, `messung/review-2026-09-21/FIX-F2.md`):
`N426` now holds every `grow` against the UPPER bound of the whole run's
commit (max at joins, saturated in loops without a constant pass bound,
callee bounds at calls, summed over call-graph roots; `entry` dispatch targets
unbounded), and `grow`'s `else` walks from the unbumped state; `N211` crosses
calls (may-reset summaries), parameters and untracked carriers (gifts
1132–1138, no new code). The runtime commit is lazy (no `memset`).
**Still owed before lane 248's emitter arm lands:** nothing on the ceiling;
`R-commit` (alloc past the committed LOWER bound) and `R-max` stay unwired;
the PLAN §9 Lean work (`DynForm`, the four Block-form theorems, the
simulation) and the two `Spec.lean` (d) assumption texts are unassigned
(review G08 F5; lane 244 did efficiency instead). Open: `OFFEN.md` O20.*

*Reserves: 240: N426–430 / 1087–1091; 242: N431–435 / 1092–1096 (only if a
new refusal is measured — over-cap growth already refuses via 240). 248
takes no new codes (lowering lane). Example
pool extended 147–160 (153–154 for the dynamic demo). Wave D ran with lane
242 alongside waves A/B.*

**Wave E — bounded strings (owner): general strings are planned, max length
known like integer ranges.** Lane 256 MERGED 2026-09-19 (`afb286ee`):
`string max N` in `TypExpr`, `zeichenfolge.rs` length discipline
(`N453`–`N455`, gifts 1118–1127), Lean value model
`ZeichenfolgeGebunden.lean`; the emitter stops every string program with
`C001`. **Not delivered:** string literals (`"hi"` stays `P011`, needs an
`ExprArt` arm in `m1.rs`). **Review G12 findings closed by fix lane F6
(2026-09-22):** an index is proven against the LENGTH by a flow fact
(`if lenof(s) > k`, `if i < lenof(s)`, `requires`, early exit), never by
`k < max` (`gift/1125` now `N454`; Lean `bindex_max_beweist_nichts`,
`bindex_geschuetzt`); strings stand only in parameters, results and `let`s
(`N465`, fields/consts/statics/table slots/nested types refused, gifts
1160-1163); contracts and `let … else` sources are walked (gifts 1164,
1165); the name table is scoped (gifts 1166/1167). **Owed by the lowering
lane:** the representation -- NUL termination (a NUL-terminated buffer
needs `max + 1` bytes) or a length word -- and an upper limit on `max`
(parsed as `u128`, no bound; the pass sums saturating and cannot accept
wrongly, but a lowering must refuse a max it cannot allocate); literals;
strings in aggregates and constants (refused by `N465` until a layout
exists). See `dokumente/OFFEN.md` O24. L4 library text (formatting/parsing/UTF) stays library work
(§0b), not language work.

*Not lanes: sigaction (out by design, not by backlog: an async handler is a
root that fires at an arbitrary program point, breaking the start/thread
model — reentrancy against lock invariants, contracts and costs cannot be
checked at the interruption site, so it would need a Spec diff for a
guarantee the language cannot hold; threshold counters + exit status cover
the firewall need fail-closed and free); M147 foreign taint (bm8-F2, helper
discipline, no build); TIEFE_MAX stays 32 (raise = constant + fuzz inside
lane 222 if measured); M101 further shapes are one small lane per shape,
priced per shape, never as "done". Example pool 147–155 shared in order;
`keine_zwei_korpusdateien_teilen_eine_nummer` catches collisions.*

# 0. The runtime — MAXIMUM PRIORITY (Simon, 2026-09-15)  ⟨A⟩

*Measured the same day, with `gabbro emit beispiele/124-two-threads-private.gab`: the emitted C
of a two-thread program declares `void L_nimm(void); void L_gib(void);` and defines neither;
`hauptA`/`hauptB` are `static` and **nobody calls them**; there is no `main`. **A program that
the checker accepts, the emitter emits and `cc` compiles still does not run.** The runtime is
assumption A4 of the goal theorem today — and an assumption is the right place for it only as
long as nobody has written it.*

- [ ] **The lock primitive, written in Gabbro.** `L_nimm`/`L_gib` are external symbols. The
  ticket lock is proved in Lean (`CTicket.lean`, SATZKARTE §32) as four instructions; the
  language has atomics with orderings and a compare-exchange that lowers to
  `atomic_compare_exchange_strong_explicit`. If the lock can be WRITTEN IN GABBRO and accepted
  by the checker, the runtime stops being an assumption and becomes a program the same chain
  covers. Where the checker refuses it, **the refusal is the finding** — it says what the
  language cannot yet express about its own runtime.
- [ ] **Thread start and the idle root.** Something must place the declared `concurrent`
  members on threads and leave every other thread in the idle root — that is exactly the shape
  A4 demands (`LaufzeitStart`). A hosted driver first (it can be run and measured), the
  bare-metal form after it.
- [x] **Bare-metal thread runtime** — Opus agent I (2026-09-26, OFFEN O32,
  `messung/OPUS-I-METALL.md`; DONE.md entry 2026-09-26). `laufzeit/metall/` boots 159, 124,
  157 on QEMU; stage 11 green.
- [x] **Every feature freestanding** — Opus agent J (2026-09-26, OFFEN O32/O33,
  `messung/OPUS-J-FREESTANDING.md`; DONE.md entry 2026-09-26). Stage 12: 311 units link
  `-nostdlib`; handlers, arenas, strings run in metal.
- [x] **System calls as named variables** — Opus agent L (2026-09-26, OFFEN O31,
  `messung/OPUS-L-ZIELBINDUNG.md`; DONE.md entry 2026-09-26). `N561`–`N568`, Linux AND
  metal bindings.
- [ ] **Runtime residue (O32/O33/O31/O19).** Real hardware; program-declared `via idt`
  handlers in the metal IDT; `-DMETALL_*` knobs as `gabbro build` link steps; Caprock
  integration (Caprock's own boot instead of the Multiboot stub); entry stacks/IST;
  error-code exception entries left from (7)–(12); a Caprock binding (needs its trap
  template); a metal kernel serving 155's thread-start number 1000.
- [ ] **One concurrent program that actually RUNS**, through the emission guardian's executed
  set, with its result compared against a handwritten version — the way 37 single-threaded
  units already are.
- [ ] **Then: A4 discharged, or narrowed.** With the driver written, the premise is either
  proved against it (as the ticket lock's premise was on 2026-09-15) or it stays and says
  precisely what about the driver is assumed.
- [ ] **`entry`/`boot`: the vector and the dispatch.** Today only the dispatch root travels;
  the vector, the registers and the steps have no form. After the hosted driver.

**The standard library is NO LONGER deferred** (Simon, 2026-09-16): it moved to §0b, and the
reason is the same measurement that set this section's priority — a firewall written entirely in
Gabbro ran, and what it kept hitting was the empty shelf. *The runtime is still first: it is the
smallest piece of that shelf and the one every other piece stands on.*

**Threading is a MUST (Simon, 2026-09-17): 3 Muse lanes now, Opus handoff later.**
O-1 (clone handoff) stays parked; these three feed it (sound pool semantics,
generated driver, lock through the chain). Reviewers from 321.

| lane | what | files owned (exclusive) | size | reserves N / gift / ex |
|---|---|---|---|---|
| 245 | symmetric pool: lift N304 with soundness + driver + Lean starts multiset | `fusswache2.rs`, `laufzeit/*`, starts-Lean | M–L | N436–440 / 1097–1101 / — |
| 246 | generated per-unit driver (ROOTS from `concurrent`) + P017 findings | `bau.rs`, new gen module | M | N441–445 / 1102–1106 / — |
| 247 | ticket lock through the chain (checks, emits, RUNS) | `laufzeit/sperre.gab` only | S | none |
| 253 | P017 thread-start statement (from 246's findings; hosted form only) — MERGED 2026-09-19 (`8de4fc1a`): parses, roots resolve (`W003`), emitter/exporter refuse by name. **Checker rules since fix lane F4 (2026-09-22, review G12 F2/F3):** roots are call-graph edges (`E008`), the statement costs the sum of the roots' costs plus 2 per root, `N458` root shape, `N459` duplicate root, `N460` one owner per thread (a `concurrent` member may not be started by `start`), `N461` no held context at `start`, `N462` started roots pool-safe. **Still open:** lowering (`C001`), export (`LG004`), no model of statement-level starts | `parse.rs`, `ast.rs` | M | no new P-codes planned |

# 0b. The standard library, native in Gabbro  ⟨A⟩

- [ ] **Handwritten C out of every Gabbro binary, as far as possible** (Simon, 2026-09-30).
  Measured 2026-09-30: `laufzeit/` + `bibliothek/` carry ~5,100 lines of handwritten C, asm and
  headers (largest: `metall/kern.c` 997, `bibliothek/linux/linux.c` 536, `metall/start.S` 427,
  `metall/metall.h` 372, `kmodul/kmodul.c` 267, `bibliothek/linux-kmod/linux-kmod.c` 265), and the
  hosted binaries link glibc. Target: runtimes and binding libraries in Gabbro, OS access by
  raw `syscall` items (no libc; a freestanding hosted Linux target), what remains in C/asm listed
  with its reason (a wall per piece). Instrument first: count handwritten C/asm linked into each
  built binary per target (from the build's file list), so every step is measured.
  - [x] C0, the instrument: `instrumente/zaehle-c.py` (with `--sprech`, `--baue`).
  - [x] A process without libc (`nolibc`, examples 172-174), gates in the model (`D.Ax`,
    `bindAxiom`, `bindAxiomElse`), templates `tor.nie`, `start.nolibc`, `tor.fehlbar` proved.
  - [x] Memory from outside as a REGION (Simon's decision 1): `tor.region`, example 183.
  - [x] The hosted arena runtime: `laufzeit/arena_dyn.c` gone, the generated driver writes it
    (template `arena.dyn`, proved), and the binding's storage and report calls are Gabbro
    (`linux.gab`). Hosted C0 1174 -> 818 lines, 7 -> 5 files (`zaehle-c.py`, 2026-09-30).
  - [x] Hosted locks without pthread: the ticket lock of `CTicket.lean` in the generated driver
    (template `sperre.ticket`), its yield a Gabbro gate; the hand drivers `laufzeit/start.c`,
    `start_pool.c` deleted. The page return in Gabbro (template `region.leeren`, the helper
    computes the pages, `madvise` is a gate). Hosted C0 818 -> 687 lines (`zaehle-c.py`).
  - [x] Threads without pthread: the C-only trampoline of the program's stack gate (template
    `tor.trampolin`) and the generated thread runtime (`faden.laufzeit`), both proved as
    abstract cores (`SchablonenFaden.lean`); `bibliothek/linux/linux.c`, `laufzeit/bindung.h`,
    `faden.c`, `faden.h` deleted -- the hosted binding is Gabbro only. On the way: `N572` (a
    stack-gate call with no `child` region checked clean), the clone trap's store (OFFEN O38).
    Hosted C0 687 -> 28 lines, 1 file (`zaehle-c.py`): the os-probe's own `melde.c`.
  - [x] The os-probe's own `melde.c`: its report is Gabbro over the binding's writers
    (`gabbro_os_schreibe`, `_schreibe_zahl`). **Hosted C0: 0 lines, 0 files**; hosted imports
    (`zaehle-c.py --baue`): 0 for 172, 173 and the os-probe; `putchar`/`write` for examples
    63/64, which bind the C library by their own `extern fn` (their libc-free twins are 172/173).
  - [ ] A hosted `nolibc` DRIVER (its `main` returns into the C runtime's start code:
    `__libc_start_main`, the toolchain's names only).
  - [x] C2, slice 1 -- the kernel-module RUNTIME generated: `laufzeit/kmodul/` (driver,
    `vzalloc` arena, lock macros, `bindung.h`, type shims) and the LKMM table
    `bibliothek/linux-kmod/stdatomic.h` deleted; `gabbro build` writes the module driver
    (templates `arena.modul`, `modul.lebenslauf`, proved, `SchablonenModul.lean`), the type
    headers and a C11-builtin `<stdatomic.h>` ((M11) revised, comment only); the loader's entry
    symbols, the licence and the arena `provision` are manifest words. kmod C0 (three probes)
    1659 -> 399 lines, runtime share 0 (`zaehle-c.py`); `pruefe-kernelmodul.sh` GREEN, 12 of 12
    gifts caught.
  - [x] C2, slice 2 -- the binding in Gabbro: `N573` (a variadic `extern fn` marker `...`; the
    emitter writes the C prototype `(fixed…, ...)` and casts every argument behind it; gifts
    1390, 1391; the Lean front end skips it, probe `tVar`), `_printk`/`panic`/`_raw_spin_*` as
    externs, the report, the load verdict and the lock operations as Gabbro functions; the
    probes `halde`/`atomar` report through `gabbro_kern_zeige`/`_halt` (`melde.c`, `atomar.c`
    deleted). kmod C0 399 -> 210 lines, 4 -> 2 files; `pruefe-kernelmodul.sh` GREEN, 12/12 gifts.
  - [x] C2, slice 3 -- the kernel thread start in Gabbro (OFFEN O39): `N575`-`N577`, the type
    `entry fn(…) -> R` (code a generated driver hands in; gifts 1394-1397, example 184);
    `gabbro_kern_faden_start` over `kthread_create_on_node`/`wake_up_process`, the join a word
    per root and `msleep` (template `faden.modul`, proved, `SchablonenModul.lean` §3); the core
    number and the holder record gone; `bibliothek/linux-kmod/linux-kmod.c` DELETED. kmod C0
    210 -> 95 lines, 2 -> 1 file; `pruefe-kernelmodul.sh` GREEN (`takt` 49 ticks), 12/12 gifts.
  - [ ] The `takt` probe's own hrtimer (`messung/proben/kmodul/takt.c`, 95 lines, the probe's
    HARNESS): on kernel 6.8 the callback is a field of `struct hrtimer`; a question for Simon
    whether a probe's harness counts for acceptance (STAND-C).
  - [ ] Bare metal (C3).

*Simon, 2026-09-16: **everything a standard library does — except networking, files, graphics
and windows — is to be written in Gabbro itself**, not as `extern` with a named assumption. The
plan is `dokumente/PLAN-STDLIB.md`; what stands here is the work.*

- [ ] **Composition across units comes FIRST, and nothing below is worth building without it.**
  Measured in the firewall on 2026-09-16: a module reading another module's table draws
  `[M119] … is declared nowhere`; `use` parses and reaches nothing; the honest workaround is an
  `extern fn` mirror **plus a named assumption per crossing**. A library whose guarantees enter
  the caller as assumptions is the opposite of a library. Decide and build: what a unit sees of
  another unit (functions with contracts — tables never?), who checks the crossing (the checker
  over both units, or the linking theorem over both certificates), and what the goal theorem
  says about two units. **This item and the linking theorem (§2) are one item seen from two
  sides.**
- [ ] **The generic question, measured before anything is written.** Tables are concrete, so a
  ring of `u32` and a ring of a record are two modules. Three routes — per-type by hand, a
  generator with a byte-identity guardian (`pruefe-genlean.py` is the precedent), or a type
  parameter in the language. **The last one touches `Ty`, which is deliberately non-recursive,
  and `OFFEN.md` O15's rule applies: it must pay for itself in programs.**
- [ ] **L1 primitives**: copy/set/compare over table slices, endianness, bit operations,
  saturating and wrapping helpers, `log2`/`sqrt`/division. Everything else stands on these, and
  they are where the bound checks live.
- [ ] **L5 concurrency, early and not late** — the ticket lock (written 2026-09-15, in
  `laufzeit/sperre.gab`), futex wait/wake, sequence lock, epoch reclamation. **The runtime (§0)
  needs these, and the runtime is the top priority.**
- [ ] **L2 containers**: ring buffer (SPSC and MPSC), timer wheel first — a firewall and every
  driver want those two before anything else — then stack, bitset, fixed hash map and set,
  sorted array, index-linked list.
- [ ] **L3 algorithms** (sort, binary search, hashing, CRC and Internet checksum), **L4 text**
  (byte strings, number formatting and parsing, no allocation), **L6 randomness** (counter-based
  PRNG plus kernel entropy through a system call).
- [ ] **Every item owes five things** (plan §3): a contract, its `ensures` **proved once** so the
  caller inherits it, a cost bound, a poison and a positive probe, and the named absence where a
  C library would allocate or grow.
- [ ] **It lives in `bibliothek/` in THIS tree**, under the same guardians as the corpus. A
  standard library measured by different instruments is a promise, not a library.

# 0c. What a real program hit — the walls, from the firewall  ⟨A⟩

*All measured 2026-09-16 while writing a Linux firewall entirely in Gabbro (7494 lines, eight
modules, netlink socket open and the worker parked in `recvfrom`). Twenty-three named findings
in `/home/ubuntu/brandmauer/messung/` (August server tree); these are the ones that belong to the language.*

- [x] **No atomic array** — 256 counters cost 5136 lines and 1797 ops per increment. Built
  2026-09-16; measured payoff 287 lines and 11 ops. *And the wall was hiding three silences: the
  index bound was never checked at two of three atomic access forms.*
- [x] **`Held(L[i])` evaporated silently** — a file whose only lock guard named a lock that does
  not exist passed with `0 errors, 0 hints`. Refused by name since 2026-09-16 (`N390`), and the
  answer to striping is **stripe the tables, not the locks**: 8× the concurrency for 4,9 % more
  ops (measured), because the permission predicate is conjunctive and `Held(L[i])` could only
  ever mean "hold all N".
- [ ] **Cross-unit table access does not exist** (`M119`) — see §0b, first item. **This is the
  one Simon named: it blocks the library and it blocked the firewall's own wiring.**
- [x] **No symmetric worker pool** — closed 2026-09-22 (fix lane F10): the goal theorem
  covers pools (`AkzeptiertSpec.einzeln := EinzelnPool`, `gabbro_ziel` re-proved, witness
  `pool_ziel_zeuge`, SATZKARTE §47, OFFEN O18 closed); the exporter's `LG001` for repeated
  starts is lifted (`beispiele/157` exports and agrees); `N315` retired.
- [ ] **No thread start at all** — every shape refused (`P017`, measured 2026-09-15). §0 owns it.
  *Status 2026-09-22: lane 246's generated driver starts the declared `concurrent` roots (one
  thread per occurrence since fix lane F4); lane 253's `start { … };` parses, carries checker
  rules since fix lane F4 (`N458`–`N462`, call-graph edges, costs), and is refused at emit
  (`C001`) and export (`LG004`).*
- [ ] **No early exit from a `traverse`** (`S001`, no label) — "find the first, then continue"
  is unwritable. *Status 2026-09-21: a `leave`/`next` naming an enclosing `retry`/`forever`
  label lowers and is pinned (lane 252, `tests/traverse_exit.rs`); the traverse itself still
  carries no label.*
- [ ] **`match` has no integer arms** and nesting is capped at 32 (`P038`), so a 256-way
  dispatch becomes a flat chain of comparisons, measured at 1797 ops. *Status 2026-09-21:
  integer arms parse (lane 222) and lower to a `switch` without `default` (lane 227). Fix lane
  F1 (2026-09-21) built the coverage refusal: `N411` (a value of M1's scrutinee range no arm
  names), `N412` (overlap / empty arm), `N413` (label outside the storage type), `N414`
  (non-integer scrutinee, mixed arms); gifts 1128-1131. The flow passes keep reading an integer
  match as possibly skipped (review G07) as a second line -- a precision cost only. Still open:
  the Lean correspondence lemma for `stmt:switch-int`/`stmt:case-int` (`CFormMatch.lean` §4b
  ties `fallListe` to a `CS.sw` built from it, not to what `emit.rs` writes), and a 256-way
  dense dispatch over a full `u32` cannot be written (ranges cap at 256 values per arm, so the
  scrutinee must be narrowed first).*
- [ ] **`accumulates` cannot be `pub`** (`P041` against `N038`).
- [ ] **A `bool` static checks clean and never becomes C** (`C001`).
- [ ] **`transition` and `advances` stand in `SYNTAX.md` §7 and parse** — one of them
  with a Lean constructor and a theorem. Two of sixteen statement head words, and **nothing in
  the tree measures this class**.
- [ ] **The emitter has no `atomic_fetch_add`**, and the measured reason is real: a checked
  `±1` cannot answer in its own type, and `+%` would wrap at a different width than C's
  fetch-add. Simon decides whether the binder-range refusal is lifted (`OPUS-BERICHT-FETCHADD.md`
  §2.3 has the patch shape and the test that must survive it). *Status 2026-09-21: decided LIFT
  (§-1); lane 221 lowers `+%`/`-%` to `atomic_fetch_add/sub` when the declared range is the full
  unsigned width.*

# 0d. The claims, as they stand — corrected against today's measurements  ⟨Q⟩

*Simon listed these on 2026-09-16 as the things that must be written down. Where a line was
stale, the measured number stands beside it: a status list nobody re-measures is the thing this
tree refuses everywhere else.*

| the claim | as measured (2026-09-16; re-measured 2026-09-27) |
|---|---|
| chain count 2 of 111 | **2 of 129** (`zaehle-kette.py --lean`, 2026-09-26); sieves (a) 2, (b) 15, (c) 15, (d) 55, (e) 2 (2026-09-16; sieve denominators move with the corpus) |
| T2, the re-checker: designed, not built | **built** — `korrOk` (`KorrespondenzAllg.lean`), 23 expression arms plus the block structure (`if`, `let` of a call, `traverse`), sound with a planted defect per arm |
| 11 of 23 templates are an abstract core | unchanged since 2026-09-16 (then counted 16; `gabbro schablonen` now reads 23 entries, 12 machine-checked -- the two added 2026-09-30 by the C-free lane are proved: `tor.nie` over the real block semantics, `start.nolibc` as an abstract core), and still the honest state of T5 |
| the concurrent half not begun | **begun and closed for ONE program**: `schlusssatz_124`, every SC run of the emitted C simulated in G, race freedom PROVED from the model's rather than assumed; the generic concurrent case is untouched |
| no pass proved individually | unchanged. 198 sentences, 190 measured, 0 proved — and that is the gap between "the checker is measured" and "the checker is proved" |
| Caprock: fragments only | unchanged. Six areas written out, 10 of 10 units error-free, nothing compiled into a kernel |
| the runtime | assumption A4; hosted driver plus bare-metal runtime since 2026-09-26 (agents I/J/L) — §0 owns what is left |
| the standard library | empty shelf; §0b is the plan since 2026-09-16 |

# 0e. General kernel modules/drivers + bounded heap (10 MiB fixed + 40 GiB ceiling)  ⟨A⟩

*Simon, 2026-09-27: API calls are always user-made (`extern`/`syscall` items carrying ABI
numbers, registers, costs in-program, never baked into the tree as OS tables — the §-1 binding
constraint). A heap is allowed but never unbounded: every region has a declared ceiling
(PLAN-ERWEITUNG rule, `SYNTAX.md` §9.1). The example shape is 10 MiB fixed (committed `lo`/`hi`)
plus 40 GiB ceiling (reserved `M`, refuse-on-full) — the 40 GiB number itself is irrelevant, what
counts is statically linkable, bucket-bounded, refuse-on-full.*

- [x] **Bounded heap `arena A capacity lo .. hi max M of T` (the 10 MiB + 40 GiB shape).**
  Stands: checker rules `N210` (0≤lo≤hi≤M), `N212` (static reservation), `N426` (every `grow`
  against the UPPER bound, fix lane F2), `N211` (generations); static Lean sugar
  (`ArenaZucker.lean`, covered by `gabbro_ziel` with no re-proof); static lowering sound where
  no `grow` stands. **The row above was stale on 2026-09-28 and is re-measured here:** the
  emitter arm LANDED (lane 259, `R-commit` = `N466`, `beispiele/158-arena-commit.gab` emits and
  runs), and so did the hosted runtime (lane 242, `laufzeit/arena_dyn.c`: `mmap(PROT_NONE)` +
  `mprotect`, lazy since fix lane F2, no `memset`, OOM fail-stop at load).
  **Measured by the server lane 2026-09-28** (`messung/SERVER-0E-REPORT.md` §2): *the ceiling
  costs nothing* — the same program at `max 1310720` (10 MiB) and at `max 4294967295` (32 GiB,
  the largest `M` the `uint32_t` counters admit; 40 GiB is not expressible in any element type)
  translates in 4 ms against 5 ms, emits 3168 against 3180 bytes of C over 70 lines each, and
  links to 16488 bytes with `.bss` and `.data` equal to the byte
  (`instrumente/miss-arena-decke.sh`, twins in `messung/proben/arena-h4/`, poison probe
  `--gift` catches a linked static array of the ceiling).
  **And a third runtime flavour stands** (server lane, `laufzeit/kmodul/`): the Linux kernel
  module, reserve = one `vzalloc` region per arena, commit = a budget over it — `vmalloc`-class
  calls are all the kernel EXPORTS, so the ceiling reads there as it does on metal
  (`Spec.lean` (M10)), and refuse-on-full is deterministic rather than practically unreachable.
  **The Lean half LANDED 2026-09-28** (server lane, session 3, `messung/SERVER-0E-REPORT.md`
  §9): `grammatik/Grammatik/ArenaDyn.lean` section `Form` carries `DynForm` (the table spans
  the ceiling, the committed prefix is a second `stand`-style word `komSt`), the four
  PLAN-DYNAMISCH §9 theorems in `Block` form — `dynGrow_commit` with its frame (the used
  counter and every slot stay put), `dynCommit_monoton`, `dynAlloc_unter_commit`,
  `dynAlloc_ueber_commit` — and the simulation `dynAlloc_simuliert`, each with a
  non-degenerate witness on a fixture whose committed prefix stands at 2 of 4: *an arena with
  room to the ceiling whose allocation is refused*, the one state the static form cannot name.
  The 40–80 lines of narrow-on-committed plumbing the file's tail comment estimated were NOT
  needed: the guard is `Block.pruefung` on `used < committed` with `Block.arenaAlloc` taken
  from `ArenaZucker.lean` unchanged underneath (`cd grammatik && lake build` 355 jobs,
  `#print axioms gabbro_ziel` standard).
  **And the two `Spec.lean` (d) assumption texts** (`Laufzeit.reserve`, `Laufzeit.commit`)
  stand in THE ONE LIST as a **comment-only** diff — 36 insertions, 1 deletion, no definition,
  no premise, no field. The review is `messung/SERVER-0E-SPEC-DIFF.md`: a new field of
  `Laufzeit` would be a new premise and therefore a weaker theorem, `Laufzeit.lader` already
  carries the reservation (an arena IS a table of `M` slots in `E.sp0`), and the commit text's
  first clause is now PROVED (`dynGrow_commit`) rather than assumed.
  Restriction (OFFEN O20) KEPT, and the Lean section says so in its cuts: no `reset`
  concurrent with a reader of `A`, no arena shared across threads without the strict option;
  no `Spec.lean` diff naming a weaker run model was made.
  Open, named in three places so it cannot be read past (`Spec.lean` NOT CLAIMED, the
  `ArenaDyn.lean` cuts, the diff review §5): **the exporter does not produce the dynamic
  shape** — `lean_g.rs` refuses `grow` (`LG005`) and builds the static `ArenaForm` over `hi`,
  not over `M`, so no dynamic-arena program is CERTIFIED. Exporter work, not model work.
- [ ] **General kernel modules/drivers with manual API.** Stands: syscall bindings as named
  in-program variables (Opus agent L, `N561`–`N568`, Linux AND metal, no OS constants in the
  tree); bare-metal base (agents I/J/L — QEMU boot, stage 11/12, 311 units `-nostdlib`).
  **Composition across units is DONE** (server lane 2026-09-28,
  `messung/SERVER-0E-REPORT.md` §1): `gabbro build a.gab b.gab` and a two-unit manifest already
  derived each unit's interface from the units named and linked+built them (Opus agent F);
  `gabbro link a.gab b.gab` now does the same, out of the SAME function
  (`vorspaenne_aus_einheiten`), so `use bib::setze;` reaches the body without a hand-written
  mirror. A STALE hand-written head still falls at `N502` — the derivation removes the manual
  step, not the check — and two units that share a module derive nothing from each other,
  because that is `N516` and the refusal has to reach the link (measured: probe `1248`
  reported `N001` twice before that rule).
  **K2 was re-measured 2026-09-28 (server lane, session 3) and the row above it was stale:
  both halves stand.** The emitter LOWERS a statement-level `start`
  (`gabbro emit beispiele/159-laufzeit-start.gab` → **0 `C001`**; the C calls
  `gabbro_faden_start` per root with its own stack and join word and traps loudly when the
  kernel refuses, lane 260), and it refuses only the shapes the checker already owns
  (`N459`–`N462`). The exporter does NOT refuse the statement either: the `StmtArt::Start`
  arm is `tr_rest`, and the roots travel as `gE.gestartet` (`check_gestartet`), i.e. as
  spawn and join steps of the THREAD machine (Opus agent A; the statement's own point among
  the lock-free ones is over-approximated — OFFEN O22).
  What is missing is **not a model and not a lowering: it is a program that survives the
  exporter's OTHER fragment limits.** Measured on the corpus's one `start` program: 159 is
  refused by `LG002` (a `wrapping` field, nothing to do with `start`), and with that repaired
  by `LG004` *function lauf falls off with a result* (its tail is a `locks` block whose
  `return` is inside). So no `start` program is CERTIFIED yet, and that is exporter-fragment
  work.
  **K3's C half LANDED 2026-09-28** (server lane, session 4,
  `messung/SERVER-0E-REPORT.md` §10), and the row above it was stale for the FOURTH time in
  this section: the C masks. On bare metal since Opus agent J (`METALL_SPERRE_MASKIERT`, IF
  cleared from before the ticket is drawn); in a Linux kernel module since this session
  (`laufzeit/kmodul/sperre.h`: `masks irqs` → `raw_spin_lock_irqsave`, PLAIN →
  `raw_spin_lock`), where before it a `module` unit with ONE `lock` **did not link at all**
  (`ERROR: modpost: "TAKT_nimm" … undefined!`) over a unit the checker had passed. The lock
  list comes from `gabbro build` (`sperren.h`, out of `TreiberPlan::sperren` — the same
  register the hosted and the bare-metal driver read) and NOT from the emitted C: it stood
  there first, and the translation-validation pin said no (`parseC` reads a closed directive
  grammar, so `a2_104 := rfl` broke; widening the parser to skip an unevaluated `#define`
  would let a macro rename anything below it). Measured in QEMU
  (`instrumente/pruefe-kernelmodul.sh` probe `takt`, 7 of 7 harness mutations caught -- they
  are `--gift` runs, not `beispiele/gift/` files): a masked
  lock held across a 4096-slot traversal, 64 rounds, while the program's own C runs a 50 µs
  hardirq timer taking the same lock — **`ticks=26 landed=0`**, and the unmasked mutation does
  not finish.
  **And `H102`'s trigger stopped being one word:** an entry is thrown if it carries a `via`
  path, any of them — before, a misspelt path and a host kernel's interrupt path (`via irq`, no
  vector the program could name) both turned the rule off in silence. Widened in the three
  places that must agree (`kontexte.rs`, `lean_g.rs`, and the K6 source pattern of
  `pruefe-akzeptiert-diff.py`) in one commit; 0 corpus diff (nine `via` words at an `entry`,
  all `idt`); witnesses `beispiele/gift/1364` and `beispiele/166` (which also exports —
  27 CERTIFIED of 208 accepted).
  Open, and this is the box: **the MODEL half** — `entry`/`boot` vector/registers/steps have no
  form in `Einheit` (only the dispatch root travels), and handler pinning/re-entry stay outside
  `KernPlan` (in G a handler thread runs once). Plus, for the module target only, the twin of
  the metal `N561`: nothing in the build checks that the program's own C hands the declared
  stub to the kernel (OFFEN O19).
  First acceptance, measured: two units (`bib` + `app`) link, check whole and build
  (`gabbro link`, `gabbro build a.gab b.gab`) — **done**; one concurrent driver RUNS through
  the executed set against a handwritten C version — **done 2026-09-28** (server lane,
  `messung/SERVER-0E-REPORT.md` §7): `messung/proben/nebenlaeufig/sperre-rueckgabe.gab`
  against a handwritten C twin written from the source, one driver over both,
  2 sides × 2 optimisation levels × 5 repetitions, contention measured beside the answer
  (`instrumente/pruefe-nebenlaeufig-zwilling.sh`, stage 22b of `pruefe-emission.sh`; 4 of 4
  poison probes caught). **It found a defect the whole tree was green over:** a `return
  <expr>` inside `locks` released the lock BEFORE evaluating the expression, so
  `beispiele/125-read-under-lock.gab` — the flagship of "guarded at the access" — read a
  guarded carrier unguarded, and `beispiele/31-rcu.gab` read the protected slot after leaving
  the RCU read section. The emitted C answered 0 where the twin answered 448. Repaired in
  `emit.rs` (the value is produced before the releases; literals keep the old text), 12 of 317
  emitting files change, new test `der_wert_wird_unter_der_sperre_gelesen` over all three
  return channels.
- [x] **The Linux kernel module target.** *Built and booted 2026-09-28 (server lane), but not
  yet by `gabbro build`.* Stands: `laufzeit/kmodul/` (the driver `kmodul.c` — NOT generated,
  everything unit-specific arrives as a `-D` macro; the bounded-heap `arena.c`; five header
  shims over the kernel's own types, because the kernel builds `-nostdinc` and every emitted
  prelude asks for them), the probe `messung/proben/kmodul/halde-treiber.gab` (ONE foreign
  function, declared by the program, body in the program's own C — no table of Linux kernel
  functions in the tree), and `instrumente/pruefe-kernelmodul.sh`: build against the host's
  6.8.0-139 headers, boot QEMU, `insmod`, read `dmesg`, `rmmod`. **Measured:** loads,
  allocates and reads back (`k=2 v=33`), hits refuse-on-full deliberately at the third `grow`
  below the ceiling (`k=3 v=3`), reports it, unloads with no oops/BUG/WARNING; 4 of 4 harness
  mutations caught (`--gift all`). In QEMU only — nothing is loaded into this host's kernel.
  **The manifest word LANDED 2026-09-28** (server lane, `messung/SERVER-0E-REPORT.md` §8):
  `kmod <runtime dir> <kernel build dir>` plus a third art `unit <name> module <init> <exit>`,
  so `gabbro build` writes the `Kbuild`, copies the runtime beside the emitted C and calls
  `make -C <kernel build dir> M=<dir> modules` -- the instrument builds through it now and the
  shell knows two paths and two names, nothing else. Beside it: `.c` paths in a module unit's
  file list are the unit's own foreign bodies (that is how a kernel call enters the artefact),
  the emitter writes `#define GABBRO_ARENEN` so no driver carries its own arena list (4 of 317
  emitting files gain the line), and seven refusals stand before any C is written (an init the
  unit does not declare, one with a parameter, one that answers nothing -- the load verdict --,
  one name for both calls, a module with `pub fn main`, a module without `kmod`, `kmod` without
  a module). 6 new CLI tests, `--dry-run`, so they need no kernel headers.
  **The `atomic` refusal was lifted 2026-09-28** (server lane, session 5, K6; Simon tasked it
  the same day, and session 3's refusal is its specification — OFFEN O34).
  `laufzeit/kmodul/include/stdatomic.h` is the LOWERING now, not a refusal: the emitter's nine
  C11 call forms and one qualifier — a CLOSED surface — onto `READ_ONCE`/`WRITE_ONCE`,
  `smp_load_acquire`/`smp_store_release`, `smp_store_mb` and the `try_cmpxchg` family, one row
  per ordering, each at least as strong as what it replaces. In the header and not in the
  emitter, because the emitted C is pinned byte for byte in the translation-validation chain;
  measured, `0` emitted bytes change anywhere. *The one row where the obvious mapping would be
  WEAKER is named and repaired: a failed `cmpxchg` implies no ordering in LKMM, not even in the
  fully ordered form, while C11 gives the exchange a failure ordering — so that path carries
  its own `smp_mb()`.* What stays refused: a floating-point `atomic` (`bau.rs::modulregel` and a
  `_Generic` in the header — the FPU is not usable in kernel context without
  `kernel_fpu_begin`), an unlisted (form, ordering) pair (an undefined name at the kernel
  build), and an RMW of a width the target's native `try_cmpxchg` does not cover
  (`_Static_assert`). The memory-model argument is a NAMED ASSUMPTION and not a proof —
  **(M11)** in `Zielsatz/Spec.lean`, a comment-only diff of 47 insertions and 0 deletions,
  reviewed in `messung/SERVER-0E-SPEC-DIFF.md` Part II. **Measured in QEMU**
  (`instrumente/pruefe-kernelmodul.sh` probe `atomar`, `messung/proben/kmodul/atomar-faeden.gab`):
  two DECLARED `concurrent` roots as kernel threads, a saturating counter bumped 256 times by
  each (`k=2 v=512`, exact — a lost update is a number below it), a release/acquire flag seen
  set 256 times over a payload never stale (`k=3 v=256`, `k=4 v=0`), two bits ORed through
  `atomic_fetch_or` (`k=5 v=3`); **10 of 10 harness mutations caught** (they are `--gift` runs,
  not `beispiele/gift/` files). And two STATIC checks, because a run on x86 cannot falsify a
  missing barrier: every access to an atomic goes through a call form, token level over the
  whole corpus (`instrumente/pruefe-atomar-zugriffe.py`, 276 files, 75 objects, 137 accesses,
  0 findings; stage 22c of `pruefe-emission.sh`), and each of the 13 mapping rows expanded by
  the preprocessor against the primitive it must select — **gift 8 is a deliberately too-weak
  mapping and is caught by that and by nothing else.**
  **And a module's `concurrent` roots became kernel threads in the same step** (K2's module
  half): `TreiberPlan` now knows the unit's art, `gabbro build` writes `wurzeln.h` out of the
  same walk the other two driver flavours read, and `kmodul.c` starts one `kthread` per root
  after the load function answers 0 and joins them all before the unload function runs. Before
  it, a `module` with a `concurrent` set had a HOSTED pthread driver written beside its `.ko`.
  **K7 LANDED 2026-09-28** (server lane, session 6, `messung/SERVER-0E-REPORT.md` §13;
  OFFEN **O35** closed for this target): *every kernel call of the module target is the
  program's now.* Session 5 had measured the twelve the RUNTIME chose — `vzalloc`, `vfree`,
  `param_ops_uint`, `_printk`, `_raw_spin_lock_irqsave`, `_raw_spin_unlock_irqrestore`,
  `pcpu_hot`, `kthread_create_on_node`, `wake_up_process`, `complete`, `wait_for_completion`,
  `__init_swait_queue_head` — and the stage `symbole_pruefe` reads **0 on all three probes**
  now (`halde`, `takt`, `atomar`), a WALL where it was a ratchet. `laufzeit/kmodul/bindung.h`
  is the interface (twelve declarations, no definition; the runtime owns the lock's and the
  thread's STORAGE as a blob of words, the program owns the operations, and the program's own
  `_Static_assert` holds its struct against that blob for the kernel it is built for);
  `bibliothek/linux-kmod/{linux-kmod.gab,linux-kmod.c}` is the binding a program takes off the
  shelf, ordinary user code in its manifest. **A `module` that binds nothing is refused before
  a byte of C**, per thing it uses and by SHAPE as well as by name (`bau.rs::bindungsregel`:
  the report channel always, the reservation trio for an `arena`, init + core number for any
  `lock`, the PLAIN and the MASKED pair separately, the thread pair for a `concurrent` set) --
  *the half no measurement over a `.ko` could give, because a unit with no binding has no
  `.ko`; what it would get is `modpost`'s "gabbro_kern_reserve undefined", about a name the
  user never wrote.* The atomic table moved too: `bibliothek/linux-kmod/stdatomic.h` is the
  program's, the runtime's `<stdatomic.h>` refuses `_Atomic` again, and a `.h` in a module
  unit's file list is copied into the module's include directory in place of the runtime's
  shim. **(M11) of `Zielsatz/Spec.lean` did not change in substance** — 5 insertions and 2
  deletions, comment only, and the 160 macro lines are byte-identical
  (`messung/SERVER-0E-SPEC-DIFF.md` Part III). **No `N` code, no gift, no example**: the rule
  is about a MANIFEST, which no pass ever sees, so it has no `Satz` — the reading
  `eintrittsregel` wrote down. Poison probes: harness gift **12** (the binding dropped from
  the manifest; the refusal's own sentence is demanded) and 3 CLI tests with their positive
  twins. **12 of 12 gifts caught**, `cargo test --no-fail-fast` 1427 passed 0 failed,
  `pruefe-emission.sh` ALL PASS 51 / 323 of 323.
  Open (Simon, 2026-09-28, `AUFTRAG-1.md` **K8**): the same rule for the HOSTED runtime
  (`pthread_*`, `mmap`, `mprotect`, the raw `clone`/`futex` through `syscall`, `exit`,
  `abort`, `printf` — about fourteen names, measured in §12.4 of the report) — bare metal
  keeps its hardware access, which is instructions and not API.
  **K8's MEASUREMENT stands since 2026-09-28** (server lane, sessions 7 and 10,
  `messung/SERVER-0E-REPORT.md` §14): `instrumente/pruefe-os-bindung.sh` is K7's criterion for
  the hosted side — `nm -u` over a BUILT probe intersected with the runtime objects', so the
  program's own `printf` does not count — and it reads **12** (`MARKE_OSSYM`, the list in
  §14.1) plus **3** raw `syscall` sites in `laufzeit/faden.c` that leave no symbol at all
  (`MARKE_ROHRUF`), both as ratchets to be pulled to 0, and **0 OS names in the 7 files of
  `laufzeit/metall/` beside 65 machine accesses** — the half K8 asks for explicitly. 5 of 5
  poison probes caught. **And the probe found a defect nobody was looking for:** neither
  GENERATED driver read `GABBRO_ARENEN`, so a hosted or bare-metal unit with a dynamic arena
  ran with `base == NULL` — every `grow` and every `alloc` took its `else`, the heap was dead,
  and fail-closed means it was silent (`treiber.rs::arenen_reservieren`, `GENERATOR_KENNUNG`
  → `treiber-gen-5`, gift 5 keeps it found).
  **K8's HOSTED RUNTIME is bound since 2026-09-28** (server lane, sessions 10 and 11,
  `messung/SERVER-0E-REPORT.md` §15 and §16), in two slices and both measured over a BUILT
  binary: `laufzeit/bindung.h` is the interface (eleven declarations, no definition),
  `bibliothek/linux/{linux.gab,linux.c}` is the binding a hosted program takes off the shelf,
  and `bau.rs::bindungsregel_gehostet` refuses a unit that binds none — sharing ONE shape
  check with the module rule (`bindung_pruefe`, `W7`). Slice 2 moved the bounded heap's six
  (`mmap`, `mprotect`, `sysconf`, `fprintf`, `exit`, `abort`, all of `arena_dyn.c`) and
  lifted the build's refusal to compile a non-module unit's own `.c` bodies; slice 3 moved the
  GENERATED DRIVER's seven (`pthread_create`, `pthread_join`, the two mutex calls, `pause`,
  `fprintf`, `abort`) and with them the root adapters and the never-spawned idle root.
  **`MARKE_OSSYM` 12 → 7 → 0**, `7 of 7` poison probes, `MARK_AUSSEN` → 27,
  `GENERATOR_KENNUNG` → `treiber-gen-6`. **The corpus needed nothing** — the rule fires over a
  MANIFEST and the corpus is checked and emitted, not built (`pruefe-akzeptiert-diff.py` rc 0,
  ten pins true on 29 of 29). Slice 4 closed the rest
  (`messung/SERVER-0E-REPORT.md` §17): the raw `clone`/`futex`/`exit` of `laufzeit/faden.c`
  became `gabbro_os_klon`/`gabbro_os_wort_warte` (the runtime keeps what a join word MEANS,
  the alignment a stack top needs, and the acquire loop that never trusts a wake;
  **`MARKE_ROHRUF` 3 → 0**), and a THIRD stage was added that reads the SOURCE of every file
  in `laufzeit/` — because `nm` can only see what a binary LINKS, and the hand drivers
  `start.c`/`start_pool.c` are linked by nothing. Its first run found **31 OS calls** in those
  two, all bound now.
  **K8 is CLOSED, and it is measured three ways over one probe**: 0 by symbol over a built
  binary, 0 raw `syscall` sites (which no `nm` sees), 0 OS names in the 7 files of `laufzeit/`
  — and the other half of Simon's sentence confirmed rather than merely not-denied: the
  bare-metal runtime names 0 OS calls in 7 files beside **65 machine accesses**. 8 of 8 poison
  probes. What is NOT claimed is that a program cannot reach the OS: it declares what it
  reaches, with an ABI, a cost and a named assumption.
  **The measurement stands** (server lane, session 5, `messung/SERVER-0E-REPORT.md` §12): the
  stage `symbole_pruefe` of `instrumente/pruefe-kernelmodul.sh` intersects `nm -u` on the `.ko`
  with `nm -u` over the RUNTIME objects only, so a symbol the program's own C pulls does not
  count — **halde 4, takt 7, atomar 9, twelve distinct names**, as a ratchet whose poison probe
  is one kernel call added to the runtime. The atomic rows contribute none of them: macros and
  inline assembly leave no symbol. Recorded as OFFEN **O35**.

# 0f. GabbroV — the user's logic proofs, end to end  ⟨A⟩

Lane `gabbrov` (2026-09-29; `messung/GABBROV-SERVER-REPORT.md`). State: `gabbro prove` over the
corpus is 192 GREEN / 13 OWED (12 real) / 0 RED; 188 units need no proof, 4 carry one (0.42 proof
lines per code line, `messung/GABBROV-PROOF-RATIO.md`). What is open, in the order it blocks:

- [ ] **V5 — the bridge to premise (b): closed for the parser's fragment** (2 of 146; report `messung/GABBROV-BRUECKE-REPORT.md`). Open: units the Lean parser does not elaborate; the shared-atomic rely. Original wording:
  **the bridge to premise (b).** The duty files (`programmlogik/`, `exec`) and
  `NutzerPflicht` (`grammatik/`, `execEndH`) are two models with two exporters and no relation.
  Needs translation validation of the fragment the duties cover; and the rows the duties do not
  cover: shared-atomic rely, `StartPflicht` (the initial memory is an assumption `Initially`).
- [ ] **A traversal's index is a member of its domain, in the state of the pass** (`beispiele/57`,
  `09`, `01`, `messung/caprock/kapraum`): `RunsLoopN` bounds the range and the count, not the
  membership, nor that a `by unvisited` traversal without `leave` covers the domain. A premise in
  the `RunsLoop*` family (`Body.lean`) and the exporter; a language-surface decision for the
  visited-set.
- [ ] **Does `tree { parent … child … sibling … }` imply parent consistency?** (`beispiele/09`,
  `messung/caprock/kapraum`: `blatt_loeschen(opfer)` needs `benutzt(opfer)` for every descendant.)
- [ ] **Disjunctive callee posts multiply the pipeline's splits** (`beispiele/126`, 94 goals).
- [ ] **A chain of 64 calls** (`beispiele/147`/`148` `tick_runde`) is not instantiated by twelve
  rounds of `gabbro_calls`, nor by three passes.
- [ ] The person's linked-structure arguments: `01`, `55`, `F01`, `kapraum` (PLAN.md §5.1).

# 1. Transfer into the checker and the emitter  ⟨A⟩

- [x] **The exporter produces a full `Einheit`** — lanes 198 (fields) and 207
  (verification + widening), reviewed (reviewer 215) and merged (`9586c8c6`,
  2026-09-17). The five width items (real `requires`, starts with arguments,
  `sp0`, lock family `S`, `def gE : Einheit gD`) were complete from 198;
  207 verified them against the tree and added the `traverse`-over-pointer
  widening (`lean_g.rs::tr_traverse`, with one positive and two LG006
  poison tests in `tests/lean_g.rs`).
- [ ] **Corpus width of the exporter (the residue of the bullet above).**
  Census 2026-09-17 over `beispiele/*.gab` (117 files): 15 export, before and
  after 207 — the identical 15 (104, 108, 109, 118, 119, 120, 121, 124, 130,
  15, 16, 34, 62, 69, 73). First refusals: LG001 x71, LG002 x19, LG003 x1,
  LG004 x5, LG005 x4, LG006 x2. The widening moved 19/46 from LG006 to LG005
  with zero corpus gain, honestly reported. **Width lane 254 merged
  2026-09-19, same honest result: corpus since grown 117→127 files,
  exports still the identical 15; LG001 now x74, surveyed by subclass
  (each needs model narrowing). Next: LG002 x21, or per-subclass lanes
  with model-side work. Concurrent lane 255 merged 2026-09-19
  (`ba9b6c07`).**
- [x] **Every accepted program certified in Lean or named** — Opus agent C,
  2026-09-26 (`messung/OPUS-C-TRAGWEITE.md`, SATZKARTE §51). Each exported,
  accepted program under `beispiele/` has its generated certificate in the
  build (`Grammatik/Zertifikat/`, `gCheck` by `decide`, `gP_gabbro_f` =
  `GabbroZiel` on it); every other accepted program stands in
  `Zertifikat/REGISTER.txt` with its first exporter refusal, cited by
  `Spec.lean` ("WHAT A GREEN BUILD COVERS"); the cargo test `zertifikate`
  fails on any program outside both. Measured: 199 accepted, 23 CERTIFIED
  (was 2 from the exporter's output), 176 UNCERTIFIED. Constants now travel
  folded (93 certified).
- [ ] **Shrink the register (the residue of the bullet above).** The measured
  shape of the 176 (all refusals per program, not the first, via a throwaway
  continue-on-refusal build of the exporter, 2026-09-26): 62 programs have ONE
  refusal shape at item/function level, 57 two, 31 three, 26 four or more.
  Most frequent shapes: `function X is not impl` 37 programs (7 alone —
  `extern`/`library`/`raw`), `assume` 24, a pointer naming no table 20,
  `device` 19, address spaces 19, `atomic` 17 (Opus B's area), non-scalar
  `static` 15. Lifting `extern fn` alone (axioms) was measured: 0 programs
  gained. `return` under `locks` (125) and a tail `let` of a call (110) need
  an `Endblock` form G has no constructor for — a model decision, not an
  exporter rule.
- [x] **The Rust checker against the Lean checker Bool `Akzeptiert`** — lane
  208 (relaunch of 202), reviewed (reviewer 218, r2) and merged (`c8b9c1a4`,
  2026-09-17). Closed by finding, not by construction: five of nine
  components are decided by existing Rust rules with zero disagreements;
  four (`abg`, `stufen`, `sperrOrte`, `antworten`) are vacuous on every
  exported program by exporter construction, so no Rust rules were built
  for them. Delivered instead: `pruefe-akzeptiert-diff.py` with honest
  denominator (compared=19, skip=182, partial=1, findings=0) and
  machine-checkable vacuity pins K1–K4 (exit 2 on drift, negative-tested),
  two agreement probes
  (`messung/proben/probe-akzeptiert-diff-guarded.gab`,
  `probe-akzeptiert-diff-deepchain.gab`), the corrected `stufen` row
  (`N294` decides the take rule, not `stufenB`), and `N317`–`N319`
  identified as phantom codes. No N codes consumed. Side effect, booked by
  the merger: `MARKE_EMIT_M` 141 → 143 (the two probes emit).
- [x] **Hand models for the concurrent programs** — lane 203, reviewed
  (reviewer 217, r2) and merged (`2c53e282`, 2026-09-17). `Korpus07.lean`,
  `Korpus59.lean`, `Korpus109.lean`, `Korpus125.lean` after the `Korpus124`
  template: 5 of 6 with full models (108, 124, 109, 59, 125). 125 was first
  reshaped (constant `return 0`); review G02 found a value-faithful term
  and fix lane F8 (2026-09-22) built it: `let r = 0; locks WACHE { let v = z;
  z = v; r = z; } return r;`, premise groups and goal theorem re-proved as
  `korpus125_nutzer`/`korpus125_ziel`, witness returns the value read (5).
  The exporter still refuses the source shape (LG004, no rule for a return
  under a lock). 07 with no
  G program at all (no table, no `impl` body in the source; the blockage is
  a reading of the source, the Lean lemmas restate the empty declaration).
- [ ] **Exporter-side concurrent coverage (the residue).** `lean-g` still
  refuses locks, `held` sections and multiple starts (LG001/LG004); only
  108 of the six exports. The hand models above are the bridge, not the
  widening. Measured by how many of 07, 59, 108, 109, 124 and 125 export.
  **Lane 255 merged 2026-09-19 (`ba9b6c07`): `masks irqs` travels as
  `D.maskiert`, `deadline` drops as NO-FORM (named in the header); 59 now
  exports (15 -> 16). Caveat (review G12): `Ziel` never reads `D.maskiert`
  and entry dispatch roots travel as ordinary starts, so 59's exported
  deadlock freedom does not cover same-core interrupt preemption, and the
  emitter lowers no `cli`/`sti` -- that belongs in the `Spec.lean`
  NOT-CLAIMED list.** **Fix lane F11 (2026-09-22) answered the caveat with
  coverage, not a line:** `Ziel` gained the leg `keinKernHalt`
  (`KernHaltG`, `Spec.lean`; proofs `Zielsatz/Masken.lean`, witnesses
  `Zielsatz/MaskenZeuge.lean`, SATZKARTE §48) -- under a core schedule a
  handler never stands at a lock a thread of its core holds, and the
  `gift/460` shape is refused by the discipline Bool that mirrors `H102`.
  What stays open is in OFFEN O19 (narrowed): handlers and cores are
  hypotheses of the leg, not fields of the unit, and the C still masks
  nothing. **Opus agent H (2026-09-26) put the handlers into the unit:**
  `Programm.unterbricht` (exported from `via idt`), the (a) component
  `masken` (`maskenB` = `H102`), and the leg `KernHaltE`, discharged from
  (a) and false on the refused shape (SATZKARTE §57,
  `messung/OPUS-H-KERNE.md`). Left in O19: no `cli`/`sti` in the C, no
  pinning (the leg holds for every core assignment), no handler re-entry.
- [x] **`beispiele/124`'s `setze` promises both slots** (`dokumente/OFFEN.md`
  O12) — lane 204, reviewed (reviewer 219, r2) and merged (`5ececd63`,
  2026-09-17). `ensures konto.slots[0].stand == konto.slots[1].stand &&
  konto.slots[0].stand == x`, so the locked section re-establishes the lock
  invariant from the callee's promise. `gabbro obligations` and
  `gabbro counterexample` display a failing user obligation
  (`obligations_g.rs`, `gegenbeispiel.rs` + tests); no new refusal, the
  checker still accepts. The release rule (demand the invariant from callee
  promises at every locked-section exit) stays a proposal in
  `MUSE-REPORT-204.md`, not built. **Fix lane F7 (2026-09-22, review G02
  F3):** the `RELEASE` rows are one shared analysis (`freigabe.rs`), order-
  aware (a write or callee write after the last promise breaks the hold),
  walk every block (`observes`, `child`), check early exits and name cells
  binder-aware; before, `setze(30); konto.slots[1].stand = 5;` read HOLDS.
  Corpus rows unchanged (124: 2 HOLDS, 119: 1 UNPROVED). The rule half of
  O12 is still open.
- [x] **The O12 release refusal `N511`** (`dokumente/OFFEN.md` O12 half (2)) —
  lane 263, `messung/muse/MUSE-REPORT-263.md`. At every locked-section exit
  (`release`, early `return`, `leave`, `next`) the invariant must follow from
  the acquire frame, the section's direct writes and the callees' `ensures`
  equalities, decided over cells and constants with `ptr`-parameter carriers
  (`freigabe::beurteile`, shared with the `RELEASE HOLDS` rows, agreement
  pinned inline). 119 stays silent (direct write `40 <= GRENZE` through `k`);
  124/157 hold from the promise; poison probes `beispiele/gift/1261`-`1264`.
  Corpus verdict diff: no clean file falls; 119's row moves UNPROVED→HOLDS.
  Certificates regenerated (release header text changed).
- [x] **The C read correspondence for nested arrays** — lane 205, reviewed
  (reviewer 212, r1) and merged (`1198a0b9`, 2026-09-17).
  `grammatik/Grammatik/CFormNested.lean`: `cform_nested_read` for the
  emitted reads of `[[T; n]; m]` plus `cform_nested_read_zeuge`, standard
  three axioms, planted-defect check (a swapped stride fails red). **Fix
  lane F8 (2026-09-22, review G01 F1):** the witness was degenerate (no
  block, both sides `none`); it now uses a live `uint32_t M[3][4]` block and
  both reads load the value at byte offset 24 (the transposed `M[2][1]`
  loads 36). SATZKARTE §44. The
  `Grammatik.lean` import was added by the merger. The reviewer verified
  that `pruefe-cformen.py` carries no nested-array row to flip (only
  `expr:array-read`).
- [x] **The simulation-certificate printer for stage (b)** — lane 206,
  reviewed (reviewer 220, r1) and merged (`71c5eaea`, 2026-09-17).
  `corrcert.rs::SimCert124` prints the four R124 position tables as JSON
  (`.simcert`) and as the Lean literal `cert124_printed`, with unit tests
  (every forged table fails, both spellings pinned);
  `grammatik/Grammatik/SimPruef.lean` checks the printed certificate into
  a simulation (`simpruef_liefert`, `simpruef_124_zeuge`). **Fix lane F8
  (2026-09-22, review G01 F2/F3 + integration):** `pruefeSim` compares with
  `gOfA`/`heldGA`/`gOfB`/`heldGB` themselves; the simulation's relation is
  READ FROM the certificate (`R124c c`), and the check is what makes it
  `R124` (`r124c_eq`); the integration's wrong `gB[7] = 3` is refused
  (`pruefeSim_falsch`). The segments and step cases stay hand-proved for
  `R124`, so nothing carries over to program #2 but the shape: program #2
  needs a checker establishing `SegPasst` per step from the certificate.
  The Rust round trip now reads `SimPruef.lean` itself (`include_str!`).
  SATZKARTE §45.

# 2. Translation validation  ⟨D⟩

**Active target, 2026-10-01: direct x86-64 bytes.** This replaces C11 validation as the
work order. See `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0–5 and
`dokumente/AUFTRAG-UEBERSETZUNGSVALIDIERUNG.md`. The existing C backend stays in use until
its replacement is implemented and checked; no new binary guarantee is claimed.

**Wave A started:** at most 20 Opencode Go Muse Spark 1.3 Contributor agents, local-only.
The first ten lanes (269–278) own isolated foundation/inventory files; see
`dokumente/x86/WELLE-A.md`. **User priority: Lean first** (`dokumente/x86/LEAN-ZUERST.md`); Rust codec 280 is stopped with its draft preserved. Lean owners 272/279/282–288 model execution, byte decoding, integer/image/TSO/flags/IEEE/IR/invariant optimisation. Foundation lanes 270/271/273 are reviewed and merged locally; execution lane 272 and byte-codec/review lanes 279–281 form the next wave. No source-to-final-image chain is closed. Shared x86 syntax is `X86/Typen.lean`; no native backend or
final-byte chain is claimed. The starter optimisation scope is recorded in that wave contract.

- [ ] **Scope from implementation:** inventory all source operations, emitter/runtime paths,
  widths, atomic orders, hardware forms and entry sequences; examples are witnesses only.
- [ ] **Machine profile and relation:** fixed encodings/decoder, byte-addressed memory,
  per-access x86-TSO, layout/ownership, stack/ABI, flags/traps, MMIO/DMA distinction, W / GX
  refinement. Review the definitions before widening instruction coverage.
- [ ] **Source-side reuse:** extend the Lean parser/elaborator, source-computed model
  certificates and GabbroV duties generically. Derive layout and `Einheit` from source;
  retain the open arena, recursion-depth and shared-atomic/payload duties recorded below.
- [ ] **Generic final-byte pilot:** integer data, memory, control and calls, with validated
  relocations/entries and non-degenerate witnesses; reject planted byte/layout defects.
- [ ] **Concurrent correspondence:** reuse W / GX and `gabbro_ziel`; prove every permitted
  x86-TSO execution is model-covered. Ordinary-access footprints, widths/alignment, atomics,
  CAS, locks and start/join need correspondence, not `DRFSC` or runtime assumptions.
- [ ] **Optimisation and execution preservation:** validate register allocation, private
  spills, flags and calls; preserve infinite executions/progress and declared costs with
  named hardware timing bounds. No implicit atomicity of emitted instruction sequences.
- [ ] **Generic extensions:** floating point, regions, runtime/entries, linking and
  optional ISA profiles, each modelled/proved before admission. OS/binding code remains
  user logic with contracts and implementation proofs.
- [ ] **Closing theorem and measurement:** all final executable bytes and mappings bound
  to the source/model; finite and infinite concurrent runs; generic witness and negative
  probes. Add an x86-specific measured status without relabelling the C-chain counter.

**Historical C-backend work and reusable source-model record.** The stage-(a)/(b), C-parser,
C-form and C-linking checklists below are retained for audit, not scheduled as the selected
validation route. Source/model gaps still apply and are included in the active work above.
Earlier weak-memory estimates are superseded by their dated updates; no x86 bridge is proved
by those updates.

**Stage (a) — single-threaded, generic** (`Schlusssatz.lean`, `KorrespondenzAllg.lean`; plan §6).

- [ ] **Sieve (a), the elaborator and the Lean parser** -- re-measured 2026-09-30 (parser lane,
  `messung/PARSER-LANE-REPORT.md`, `python3 instrumente/zaehle-kette.py --lean`): **passes 10 of 148**
  (104, 108, 130, 69, 73, 16, 15, 62, 93, 109); the others stop at `elab` 99 (81 an item kind without a G form -- `static`
  42 programs, `proto` 20, `atomic` 19, `assume` 11, `device` 10 --, 10 `Typ unbekannt: bool`, ...) and
  `parse` 40 (`wanted (` 11, `reserved head forall` 10, `wanted ;` 5 -- lock invariants --, ...).
  Walls done: 1 (units without tables, `+ - *`, built-in widths, omitted `effects`), 2 (conversions
  `T(e)`, `T::max`, named consts, `& | ^`), 3 (`bool`), 4 (`own`, `~p` over declared widths) and 5
  (compile-time constants), 6 (`locks` blocks) and 7 (`entry` roots as declared starts). **Next:** `let` (the parser drops the annotation: keep it), `if`, `locks`,
  `requires`, lock invariants (119, 124, 157), `static`/`atomic`.
- [x] **Chains and bridges for the sieve-(a) units (P4)**: chain count 2 -> **5**, closed bridge 2 -> **5**,
  end to end 2 -> **5** (`beispiele/130`, `69`, `73` through the generic `ketteAllg` and
  `nutzer_aus_quelle`, `bruecke/Bruecke/Quelle.lean`). The chain of a unit WITH tables still needs a
  per-program `EmitLay`: derive it generically from `UTab` (open).
- [ ] **P6, the generic C-chain side**: `Kette` for units with tables from the source alone (`EmitLay`, the
  certificate from `corr-lean` as data), and the fragment premises of `nutzer_aus_quelle` (lock
  invariants, axiom ensures, declared starts, atomics, `requires`, arithmetic inside `ensures`), each
  removed construct by construct.
- [ ] **`korrOk` arms** for `if`, `traverse`, compound assignment, globals, `let` of a call, and
  arithmetic. Each is one arm over an existing lemma. Measure each by the chain count it moves.
- [ ] **Discharge the "no model error" condition** of part 4 from the model judgement, instead
  of carrying it. *Down to ONE residue since 2026-09-15: the hardware half is 4b, six of the
  seven `logik` kinds fall to the user's own duty (4e(ii), now unconditional --
  `SATZKARTE.md` §§36-37), and what is left is the `abstieg` DEPTH, which 4e(i) turns into a
  computation at one depth. To finish it, the depth has to come from the program (a measure
  the checker reads) rather than from the chain author.*
- [ ] **Re-instantiate the link between the single-thread machine and `rufAt`** inside the
  closing theorem. Today it is the adequacy chain, outside it.
- [ ] **Take the `Einheit` of a chain from the exporter** (depends on lane 198) instead of the
  chain author writing it.
- [ ] **Export the arena** (`OFFEN.md` O14, `SATZKARTE.md` §32). The specification carries
  `alloc`/`reset` since 2026-09-15 (`Grammatik/ArenaZucker.lean`: a table of `count = hi` slots
  beside a `used` global); `lean_g.rs` refuses the DECLARATION by name instead of building that
  pair, so `beispiele/98` and `99` stop at sieve (b). Read an `ArenaDecl` into a `TableModel` +
  `GlobModel` and lower the two statements. *The reservation `lo` does not travel — it is the
  checker's static count (`N212`), and the model-side consequence is already proved.*
- [ ] **T3 round trip for statements** (`SAnw`), and for full `gutPlatz` index payloads. Lane 195
  closed the expressions through level 6 (`Parser/Rundlauf4.lean`).
- [ ] **A2: a Lean C parser for the emitter's subset** (`parseC text = some prog` by `decide`).
  It replaces the hand transcription of the emitted C by "the compiler's front end reads the
  subset as `parseC`", which is part of A1.
- [ ] **A3: the missing lemma** that the C semantics reads a `RecLay` only through the pinned
  numbers.
- [ ] **T4/T5 coverage.** Every form `pruefe-cformen.py` lists as uncovered gets a lemma or
  becomes a named assumption. The remaining T5 templates.

**Stage (b) — concurrent** (`CNebenlaeufig.lean`, `Schlusssatz124.lean`; plan §7). It is closed
for 124 with `DRFSC` and `LaufzeitC` as named premises. Open, by plan §7.6:

- [ ] **Region serialisability inside DRF-SC.** It needs a C semantics with one step per memory
  access.
- [ ] **General footprint soundness.** It needs an access-instrumented `Exec`; the key lemma
  `ev_zform_blk` is proved.
- [ ] **The runtime's ticket lock behaves as `sperrAbstrakt`** (a proof, not a premise).
- [ ] **A simulation-certificate checker** (see §1, printer).
- [ ] **Exporter support and parse fidelity for 124** (§1, and sieve (a)).
- [ ] **Semantic extensions:**
  - lock calls inside loops, branches and callees (today only at the top level of a root
    function);
  - atomics as a source of ordering and as exempt from race freedom;
  - volatile and foreign calls inside blocks.

**Beyond the single unit** (PLAN-ZIELSATZ §10):

- [ ] **The linking theorem.** If each unit's certificate checks and the units' ABI interfaces
  match (decidable from the `_Static_assert` pins), the linked C refines the composition of the
  programs.
  *(2026-09-26, Opus agent E: the MODEL half is proved -- `gabbro_ziel_verbund`; what remains
  here is the C half: the linked C refines the linked G program, OFFEN O28.)*
- [ ] **Inline assembly: a small ISA semantics** for exactly the stub patterns the emitter
  writes, so each stub gets a correspondence lemma instead of `AxCorr`.

**Beyond DRF-SC: full weak-memory coverage (priced, deferred — Simon, 2026-09-18).**
Today G is sequentially consistent and data-race freedom buys SC behavior
(`DRFSC` premise in stage (b)); atomics/pairing are ordered by axiom A10
and exempt from `rennfrei` (`Spec.lean` NOT-CLAIMED: weak memory beyond
DRF-SC). Full coverage means: rebuild G on an RC11/IMM-class model
(memory as history/graph, visibility instead of interleavings), re-prove
`gabbro_ziel` + one review round, give every ordering its own meaning in
model + checker (today A10 covers them wholesale), per-architecture
fence mappings (x86-TSO vs ARM/POWER) with a per-access C semantics, and
re-do stage (b) with DRF-SC proved instead of assumed (region
serialisability + footprint soundness become mandatory). Price: ~6–10
lanes + 2 Opus tracks + 1–2 goal-theorem review rounds, roughly 1–3
months review-bound — and it invalidates stage-(b) work in flight.
Gate: starts only after stage (b) is closed generically; until then
DRF-SC is the honest contract for the non-atomic accesses (no races ⇒ SC
for them). It does not cover relaxed atomics (the per-core accumulators and
the ticket lock's draw use relaxed orderings, and A10 orders them wholesale)
nor device or DMA memory.

**Update 2026-09-26 (Opus agent B, SATZKARTE §50, `messung/OPUS-B-SPEICHERMODELL.md`).** The
model half is done differently and cheaper than priced above: G is NOT rebuilt. Machine W
(`grammatik/Grammatik/Speichermodell/`) is G over a view-based weak memory (the promise-free
timestamp machine of RC11 for the emitted orders; `seq_cst` as release/acquire), and the DRF
theorem (`schwach_ist_g`) proves that on an accepted program W takes only G's steps, for every
order assignment -- so `Ziel` gained the leg `schwach` (a reviewed `Spec.lean` diff, no premise
moved) and `gabbro_ziel_schwach` gives every leg at every machine W reaches. Litmus facts (MP,
SB, CoRR) are Lean theorems. What is still open from the list above:
- [ ] **A rely for unguarded atomic reads** (`OFFEN.md` O25): programs that COMMUNICATE through an
  atomic without a lock are refused by `fuss`, so W's non-SC outcomes occur on no accepted
  program. Closing it: a havoc at shared atomic reads in `execEndH`, `fuss` exempting atomics,
  the replay carrying it. Opus-sized. **Narrowed 2026-09-26 (Opus lane O25, SATZKARTE §52,
  `messung/OPUS-O25-ATOMICS.md`):** the memory half and the language-carried legs are proved
  standalone -- with `fuss` exempting atomics (`AkzeptiertA`, embedding of `Akzeptiert`) every
  W step is a GA step (plain carriers SC, atomics per W, `schwach_ist_gA`), and trace invariant,
  lock exclusivity, no deadlock, no wait cycle, time and plain race freedom hold over W
  (`w_sprache_akzeptiertA`). Still open, in this order: (1) the rely in `execEndH`/`KoerperGutS`
  and the replay family carrying it (the contract legs); (2) then ONE reviewed `Spec.lean` diff:
  `akzeptiert` over `AkzeptiertA`, the leg `schwach` in GA form (`SchwachSC` is false on
  accepted flag programs, `n1_schwachSC_falsch`); (3) RMW atomicity in `SchrittW`
  (`zaehler_verloren`: W loses a `fetch_add` update RC11 keeps); (4) a footprint rule for a
  PLAIN payload read after an `awaits` (the view transfer `hb_uebergabe` is proved); (5) the
  exporter for `atomic` items (`LG001`). **Narrowed again 2026-09-26 (Opus lane O25b, SATZKARTE
  §55, `messung/OPUS-O25B-ATOMICS.md`):** (1) is DONE standalone -- the rely (`execEndHA`,
  `KoerperGutSA`), the replay over machine GX through all 70 rules, and `gabbro_ziel_atomar`:
  `AkzeptiertX`/`AkzeptiertSpecX` (shared atomics admitted when in no contract),
  `NutzerPflichtA`, `HardwareAnnahmen`, `Laufzeit` give every leg of `Ziel` with shared atomics
  (`ZielAtomar`) at every machine W reaches; embedding `gabbro_ziel_atomar_vor`; Rust `N484`
  (a contract over a shared atomic) makes the Rust footprint legs decide `fussWXB`. (3) exists
  as a sub-machine (`RufSchrittWR`, `wr_kein_verlust`). Still open before the ONE Spec diff (2):
  the thread machine over GX (`ZielF`: spawn, join, `spawnSicht`), `GabbroZielVerbund` with the
  rely, and (5) for a differential measurement; then (3) into `SchrittW` and (4).
  **Narrowed to (4) 2026-09-26 (Opus lane O25c, SATZKARTE §58, `messung/OPUS-O25C-ATOMICS.md`):**
  (2) DONE -- `GabbroZiel` is the rely version (`PrueferX`, `NutzerPflichtA`, `ZielFX` over the
  thread machine over GX), the statement of before `GabbroZielSC` derived
  (`gabbro_ziel_sc_aus`), linked units likewise; (3) DONE -- `SchrittW.rmw`, `w_kein_verlust`,
  `w_zaehler`; (5) PARTLY -- payload-free atomics export, 116 and 162 certified. Still open:
  (4) the plain-payload rule (`N485`, gifts 1205-1210 reserved), the exporter for payloads,
  `awaits`, `exchange` and atomic arrays, and a concrete term discharging `ZaehltHoch`.
- [ ] **Stage (b) keeps `DRFSC` as a premise** (`CNebenlaeufig.lean`): the C side is still
  SC-by-assumption; W is on G's side. Connecting them needs a per-access C semantics (§2 above).
- [ ] **Hardware fence mappings:** not started. W is a source-side weak-memory abstraction;
  its correspondence to x86-TSO is now an active target above. ARM/POWER are outside the selected
  backend profile.
- [x] **`N323` must demand memory orders** (`OFFEN.md` O26, Spec-diff verdict of Opus agent B,
  F2): an own lock primitive's take must be an acquire and its give a release; today `N323`
  checks atomicity and hold time only, and `Spec.lean` names the orders as assumption (3) of the
  reading. Rust lane: tighten `N323`, poison probe (relaxed spinlock), positive probe. **Done
  2026-09-26 (Opus lane O25):** `N481` (take without an ordered read), `N482` (give without an
  ordered write), `N483` (take and give meeting on no ordered atomic), sentence
  `namen.sperrprimitiv_ordnung`, gifts 1201-1203, snippet tests (an acquire spinlock and the
  ticket lock shape pass); corpus diff: only the gifts. Measured: `N042` refuses every own or
  foreign `L_nimm`/`L_gib` beside `lock L`, so no accepted program has one today. Foreign
  primitives stay assumed.

# 3. The goal statement — follow-ups  ⟨D⟩

- [ ] **The liveness assumptions go into the ONE list in `Spec.lean`'s header**: `LaufzeitAnnahme`
  (FIFO lock and fairness window `F`) and `HardwareImAbschnitt`. Today they sit in
  `Lebendigkeit.lean`.
- [ ] **The external human review** of the review package (PLAN-ZIELSATZ §5): the definitions
  the kernel cannot judge. That is the machine G, the good-run predicates, `KoerperGutS`, the
  goal predicates, and the selected x86 semantics/decoder. The C semantics remains a review
  subject for the current backend.
- [ ] **The final double verdict over the whole chain.** One Muse lane and one Opus agent,
  independent, once the generic final-byte chain covers the supported language: "is the goal
  reached for the product, not only the model?"
- [ ] **Keep README §5 true** after every merge that moves the chain count or a stage.

# 4. Extensions and named gaps  ⟨D⟩

*Rules for every extension: PLAN-ZIELSATZ §8. The criterion is counted per obligation, there is
one assumption list, and the number is booked before and after.*

- [ ] **Opt-in unbounded heap region (planned, not required; Simon, 2026-09-29).** The default
  stays a region with a declared ceiling (§0e: fixed commit + ceiling, refuse-on-full). Beside it,
  an EXPLICITLY declared region with no ceiling -- spoken out like `divergent fn` -- in which
  every allocation may fail and the program must handle the failure; exhaustion becomes a named
  hardware assumption instead of a static number. With it the language is Turing-complete in
  the model (an unbounded tape plus `forever`); without it every program is finite-state, like
  any program on real hardware. What such a program gives up, and must be refused where it is
  promised: the static whole-program memory bound (a program that declares one may not use an
  unbounded region). Needs a reviewed `Spec.lean` diff (the allocation-failure assumption), the
  model of an unbounded heap, checker rules with poison probes, and a runtime without a
  reservation ceiling. Memory safety, race freedom, contracts and termination checking are
  unaffected.

- [ ] **Linearizability** of lock-free structures. SPSC ring first, then the Treiber stack and the
  sequence counter, then RCU. External and helping linearization points are a separate, later
  extension. Opus-sized, more than a week.
- [ ] **WCET as a named interface with proven inputs.** Export the flow facts (loop bounds, paths,
  call graph, `deadline`) as a certificate; the processor timing model is a named assumption.
  About 8–10 working days.
- [ ] **Noninterference: declassification** (delimited release). It decides whether the flow rule
  is usable. The customer sentence stands in NICHTINTERFERENZ.md.
- [ ] **Timing channels.** A constant-time discipline as an extension of the flow rule. After
  declassification.
- [ ] **Waiting bounds that fit a data sheet.** Use dominance, per-lock contenders from the call
  graphs, and computed block costs instead of the declared `held`
  (`messung/WARTESCHRANKEN-2026-09-15.md`: nested bounds are astronomical from three levels).
- [ ] **`bv_decide` axioms.** Each per-computation axiom goes into the ONE assumption list by name,
  with an independent re-check as the ratchet (lane 181 measured the mechanism).
- [ ] **Checker robustness.** One register sentence per pass: it terminates on every input, with
  the measure. Where no proof exists, a fuzz run as evidence.
- [ ] **Float accuracy (error bounds)** stays named, not claimed. Pick it up only if a kernel
  needs it.
- [ ] **The people gap.** A tutorial path from a first program to a proved `ensures`, with
  `gabbro obligations --g` and `gabbro counterexample` (lane 180) as the everyday interface.
- [ ] **Tool maturity** (LSP, localisation, profiling). After the goal.

**NOT-CLAIMED items that earn a place here, ranked (Simon triage 2026-09-18).
P0 ships product value, P3 is recorded honesty. Rule §8 applies to each.**

- [x] **Linking separately compiled units (P0 — NOT-CLAIMED #10).** Done in the model
  and at the source level 2026-09-26 (Opus agent E, `messung/OPUS-E-LINKEN.md`, SATZKARTE §54):
  `GabbroZielVerbund` (Spec.lean, second statement, purely additive) proved as
  `gabbro_ziel_verbund` -- two units over one link declaration, each accepted alone, the link
  check over composed hulls (`schnittstelleB`), each user's duty over the bodies it owns, the
  SAME hardware assumptions -> `ZielF` on the linked program. Rust: `gabbro link`,
  `N501`-`N505`. **Opus agent F (2026-09-26, `messung/OPUS-F-VERBUND-RENNEN.md`) closed
  review E F1 and the Rust residue:** an imported head's declared reads join the importer's
  footprint (the F1 reproduction falls in `check --with` with the one-file `N291`/`N301`);
  `gabbro link` checks the LINKED program whole (threads on both sides judged, not refused;
  `N516` for a module split over units); contracts compared as trees; `gabbro build` links
  two or more units (manifest, or `gabbro build a.gab b.gab` as a link check). What stays
  open is OFFEN O28: the review round of the Spec diff and of Opus F, no certificate for a
  linked program, the C-level link step (the §2 item below).
- [x] **Symmetric starts in the model (P0 — NOT-CLAIMED #9, O17, O18).** The
  checker accepts pools since lane 245; the goal theorem does not cover
  them at all (`Akzeptiert` still demands `ws.Nodup`, and (d) excludes a
  busy start on several threads). `PoolSym.lean` adds definitions and a
  separation lemma, not the `Ziel` legs, and per-core locality is
  unproved. Either prove `RennfreiBis` and the other legs over start
  multisets and swap `einzeln` for `EinzelnPool` (a `Spec.lean` diff), or
  gate the exemption until then. No lane is tasked with it (wave B has no
  such row, contrary to what this item said until 2026-09-21). Medium to
  large, not small: review G06 F1/F4. (The generated driver's one-thread
  pool was fixed in fix lane F4; the exporter now refuses repeated starts,
  `LG001`, until this item lands -- fix lane F10.) **Done 2026-09-22 (fix lane
  F10, O18 closed):** `Spec.lean` diff (`einzeln := EinzelnPool`, occurrence
  `Getrennt`, `Laufzeit.einmal` with `Mehrfach`), every leg re-proved in
  `gabbro_ziel`, witnesses in `Zielsatz/PoolZeuge.lean`, `LG001` lifted,
  `N315` retired. **Still open: the per-core half (O17)** -- the Rust pool
  rule exempts `per cpu` cells, the model has no notion of them. **Narrowed
  2026-09-26 (Opus agent B):** read as relaxed atomics the pool rules agree
  (`poolSicherRust_iff`) and writes are covered; the read half is O25.
  **Narrowed again 2026-09-26 (Opus lane O25):** the fold is accepted by
  `AkzeptiertA` (`faltung_akzeptiertA`) and its memory side is proved
  (`schwach_ist_gA`); the contract side is O25's rely. **And again (Opus lane
  O25b):** the fold is accepted by `AkzeptiertX` (`faltung_akzeptiertX`), and
  `gabbro_ziel_atomar` covers it under the rely (standalone; the Spec diff is O25's).
  **And again (Opus lane O25c):** the rely is the goal statement; `gabbro_ziel` covers the fold.
- [x] **Threads created at run time in the goal (O21, O22).** Done 2026-09-26 (Opus agent A,
  SATZKARTE §49, `messung/OPUS-A-LAUFZEITFAEDEN.md`): `GabbroZiel` runs over the thread
  machine (`start` spawns and joins, `kind` spawns a child), run-time roots are
  `Einheit.gestartet` judged as pool routines, every leg of `ZielF` proved, the old statement a
  corollary (`gabbro_ziel_vor`); the exporter carries `start` roots. **Still open:** per-spawn
  arguments (a `child` reading its handed values), a root `requires` at the spawn world, the
  `child` export (its stack gate is a foreign body), and the lowering (lane 260).
- [ ] **Stack budget as a measured bound (P1 — NOT-CLAIMED #2).** No
  full proof: a `costs`-like static budget over call depth with the
  2MiB-thread test as evidence (the `TIEFE_MAX` doctrine). Overflow stays
  impossible by construction of the bound. Small to medium.
- [ ] **Weak memory beyond DRF-SC (P1 — NOT-CLAIMED #4, gated).** Priced
  under §2; starts only after stage (b) closes generically. Lock-free
  programmers need it, and linearizability above builds on it. **Model half
  done 2026-09-26 (Opus agent B):** machine W, the DRF theorem, the leg
  `schwach` (§2 update). Open: the rely for atomic reads (O25; its memory
  half is proved since 2026-09-26, Opus lane O25), stage (b).
- [ ] **Termination and waiting bounds (P2 — NOT-CLAIMED #1).**
  `forever` budgets plus `Fortschritt` cover the practical shape; the
  data-sheet variant above comes first. Full termination stays per-program
  user logic, never a language claim.
- [ ] **Starvation freedom (P2 — NOT-CLAIMED #7).** After the data-sheet
  waiting bounds; FIFO lock and fairness window `F` move from
  `Lebendigkeit.lean` into the ONE list first (§3).
- [x] **Invariants at entry and while locks are held (P3 — NOT-CLAIMED #8)** —
  Opus agent D, 2026-09-26 (`messung/OPUS-D-INVARIANTEN.md`, SATZKARTE §53).
  Four new legs of `Ziel` (`invRuhe`, `invSicht`, `sperrWechsel`,
  `sperrSicht`) and `ZielF.spawnSicht`, proved, no premise moved; the NOT
  CLAIMED line is replaced by what is claimed. OFFEN O11 closed by `N496`
  (every writer of an invariant carrier maintains it) and
  `inv_ohne_schreiber`. Witnesses on `mP` (Zielsatz/InvariantenZeuge.lean).
- [ ] **Table invariants in the exporter (residue of the bullet above).** The
  exporter writes `Inv := Empty`, so for every certified program the legs
  `invRuhe`/`invSicht` are vacuous; exporting `table … invariant` (and the
  `maintains` it now requires, `LG001` today) makes them bite. The start
  memory stays the legs' hypothesis; for an exported unit it is decidable, so
  a certificate could discharge it by `decide`.
- [ ] **`N496` and `table … ops` (OFFEN O11, the `ops` condition).** A
  hand-written body writing a carrier of a table with `ops` is not asked;
  decide whether it must `maintain` the invariant too, and measure.

# 5. Simplicity without losing a guarantee  ⟨E⟩

*Measure (PLAN-EINFACHHEIT §0): `gabbro zeremonie` goes down AND the pass register stays
constant.*

- [ ] **Lever 3: `gabbro fmt --explicit` / `--elide`** — lane 197 ran 2026-09-17; check what
  landed and what is still open. Pure views: same diagnostics, same register, byte-identical
  C, round-trip idempotent.
- [ ] **Lever 2: defaults with a named escape.** Design the rule set first (rank order, phase,
  `pure` on spec functions), with one register sentence per rule, then build.
- [ ] **Lever 6: tactics** (`gabbro_simp`, `gabbro_wf`, normalisation) and better handed-over
  goals. Measure by lines per obligation.

Levers 1, 4 and 5 are done: derivation (lane 191, demanded effects 616 → 277), fix-its (lane 187)
and contextual keywords (lane 188, the residue is irreducible).

# 6. The measurement layer  ⟨Q⟩

- [ ] **Pre-existing red guardians.**
  - `pruefe-todo.py` and `pruefe-zahlen.py` carried findings before this rewrite; the lane
    reports list them as pre-existing.
  - `zaehle-gifttreffer.py` exits 1 with a stable finding set.

  Re-measure each locally with `./instrumente/abnahme.py --voll`, and rebook or repair them, one
  guardian at a time.
- [ ] **`messung/KENNZAHLEN.md` is German where the old TODO was.** Give each pattern in
  `pruefe-zahlen.py` / `pruefe-todo.py` its English alternative, then translate the ledger
  lines (patterns first, document second).
- [ ] **The README headline numbers** (diagnostics, sentences, mutations) move with every merge.
  Rebook them in one pass after the transfer lanes land.
- [ ] **Re-measure the time of the mutation run.** CLAUDE.md quotes the time for 377 mutations;
  the catalogue is past 400.

# 7. Deferred, with reason  ⟨Z⟩

- **`aarch64`** is second-rate and later. When it starts, the "sealed" note in CLAUDE.md changes
  first.
- **GPU** support belongs in the standard library (SPIR-V payloads, the GPU driver as a named
  assumption), after the chain.
- **Probabilistic statements and dynamic unbounded data structures** are out of scope (Simon,
  2026-09-14). They are not claimed and not worked on.
- **Nonlinear arithmetic over unbounded integers** stays user logic with hand lemmas. It is the
  one place the oracle-plus-certificate pattern does not reach.
- **The bootstrap chain** (Gabbro written in Gabbro) is deferred, with the measured reason in the
  old TODO (commit `1434efba`, "DIE BOOTSTRAP-KETTE").
- **Known absences** O1–O14 are recorded, with what would close each, in `dokumente/OFFEN.md`.
