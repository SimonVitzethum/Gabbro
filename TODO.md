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
the owner's end sequence, the work now is:

1. transfer into the checker and the emitter (§1);
2. translation validation (§2), whose one headline metric is the **chain count**, from
   `instrumente/zaehle-kette.py`. It stood at 1 of 101 on 2026-09-14 and at 2 of 111 after
   stage (a) (programs 104 and 108).

Each item names its owner (lane or agent) where one is running.

---

# -1. Verdict walls: the not-going code (first)  ⟨A⟩

*14 walls from the firewall-in-Gabbro tree (`Verdict/messung/BEFUNDE-bm*.md`,
measured against Gabbro master `71c5eaea`); 3 cost nothing — N042/N323 and
atomic arrays are built, sigaction stays out by design (threshold counters
are free). The remaining 11 are cut into 26 lanes in 3 waves below: 24 Muse
lanes (workers 221–248, 230 unused) + 2 Opus lanes (O-1, C-2, sequential —
both touch the model core; PARKED 2026-09-17, no Opus capacity — wave A
runs without them). Review loop (`bin/review-wache.sh`, max 3
rounds, builds re-run by the reviewer) covers workers 221–248 with
reviewers from 321; the dispatcher worker list needs the extension
(orchestrator step). Max parallel: 8 at start (221–226 + 236–237; O-1 parked), up to 8
in wave B.*

**Binding constraint (owner): no language feature hard-depends on an OS.**
Syscalls are always user-made — declared in-program (`extern`/`syscall`
items carrying ABI numbers, registers, costs), never baked into the tree
as OS tables. This shapes lane 226 (fd + open/read declarations, no
number table in `crates/`), O-1 (handoff shape OS-agnostic, clone numbers
stay in user code) and C-2 (address + timespec carrier, no `CLOCK_*` in
the tree). A lane that smuggles an OS constant into `crates/` or
`grammatik/` fails review.

**Safety is never traded for features** (owner): no lane weakens a
guarantee — memory safety, race freedom, contracts, costs, lock
discipline — to make a wall go green. A wall that only yields by
weakening is recorded as a finding (like 208's vacuity pins or 203's
proved blockage), never bypassed. A bypass fails review, no matter how
green its build is.

**Decision gate RESOLVED 2026-09-17 (owner): LIFT.** Criterion was the
project goal — a `folge()` wrapper around a proved bound is user ceremony
for language plumbing, and plumbing belongs to the language, not to the
proof. Lane 221 launched on that basis (`OPUS-BERICHT-FETCHADD.md` §2.3
patch shape + surviving test).

**Wave A (parallel now):**

| lane | wall | files owned (exclusive) | size | reserves N / gift / ex |
|---|---|---|---|---|
| 221 | `+%` fetch_add (bm4-F5) | `emit.rs` fetch arm, `tests/holform.rs` | S | N391–395 / 1052–1056 / — |
| 222 | syntax: int-match arms + traverse domain | `parse.rs`, `lex.rs`, `kw.rs`, `ast.rs` | M | snippets only (no corpus files) |
| 223 | costs on extern, trusted (K003) | `kosten.rs` | S | N396–400 / 1057–1061 / — |
| 224 | m1 bound shapes (`k-1` class, first shapes) | `m1.rs` | M | none (existing M101) / — / — |
| 225 | never-bodies accept (asm/forever) | `namen.rs` (`asm_never` region) | M | N401–405 / 1062–1066 / — |
| 226 | fd + open/read decls (L-2, OS-agnostic) | `syscall.rs`, decl shape | M | N406–410 / 1067–1071 / 149–150 |
| 236 | ALG sketch FTP (Obergrenze): 1024 control table, 512 B bounded buffer + refuse, hash match, fenster-expiry, VOLL-refuse, packet-tick | new `beispiele/` only | M | no new codes / — / 147–148 |
| 237 | layout-factor muster: word tables + index arithmetic (`i>>2`, `(i&3)*8`), static-link budget measured | new `beispiele/` + report only, NO `m1.rs` (lane 224 owns it) | S | no new codes / — / 151–152 |
| O-1 | clone handoff (K-1) | new syntax + new Lean files, `Spec` diff | XL | SPLIT 2026-09-18: checker + emitter TRANSFERRED (N446–N450, C185 refusal, LG004 exporter refusal; no Linux constants, verified by grep); Lean model + Spec (d2) stay on `opus/clone-handoff` for the review round. Open: Teil 3 (inline-trap lowering + correspondence), spill-read rule, `D.klon` exporter fill, `Ziel` leg. |

**Wave B (after A: emit.rs free from 221, AST known from 222, K003 from 223):**

| lane | wall | files owned (exclusive) | size | after |
|---|---|---|---|---|
| 227 | switch lowering (int-match) | `emit.rs` | M | 221 |
| 228 | match semantics (Lean) | new `CFormMatch`-family file | M | 222 |
| 229 | subrange traverse checker: effects + early exit (S001) | `wirkungen.rs`, `absenkung.rs` | L | 222 |
| 231 | divergence lemmas (Lean) | new file | M | 225 design |
| 232 | hold chunking (K002) | `kosten.rs` | M | 223 |
| 233 | syscall/fd model (Lean) | new file, no OS constants | M | 226 |
| 234 | traverse lowering | `emit.rs` | M | 227 |

*Wave-B reserves: 227: N411–415 / 1072–1076; 229: N416–420 / 1077–1081 /
151; 232: N421–425 / 1082–1086. Lean lanes (228, 231, 233) need no codes —
witnesses instead of poison probes.*

**Wave C:**

| lane | wall | files owned (exclusive) | size | after |
|---|---|---|---|---|
| 235 | never/never-asm lowering | `emit.rs` | M | 234 |
| C-2 | address-of + timespec (L-1/bm8-F3) | model core, `Spec` diff | XL | PARKED (Opus, after O-1) |

*Launched 2026-09-18 as lanes 242 (+248, emitter arm queued post-235):
**mmap-backed tables** (Obergrenze #2). `table … storage mmap`: same
checker rules (240's `max` cap), runtime reserves virtual + commits on
demand (`laufzeit/`, A4-style assumption — OS rule holds: no ABI constant
in the tree), Lean region (241's `ArenaDyn`) + mmap-contract assumption
as ONE-list entry. The 40 GB number itself is irrelevant — what counts is
statically linkable, bucket-bounded, refuse-on-full (lanes 236/237 prove
the discipline without it).*

**Wave D — bounded dynamic memory: 300 MiB working set, 30 GB ceiling,
near-Rust efficiency (owner).** Reservation vs commit split: the program
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
| 248 | emitter arm for reserve/commit (QUEUED, starts after 235 merges) | `emit.rs` | S–M | 235, 242 |

*Reserves: 240: N426–430 / 1087–1091; 242: N431–435 / 1092–1096 (only if a
new refusal is measured — over-cap growth already refuses via 240). 248
takes no new codes (lowering lane). Example
pool extended 147–160 (153–154 for the dynamic demo). Max parallel now:
242 alongside waves A/B (11 total on fisch).*

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

# 0. The runtime — MAXIMUM PRIORITY (owner, 2026-09-15)  ⟨A⟩

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
- [ ] **One concurrent program that actually RUNS**, through the emission guardian's executed
  set, with its result compared against a handwritten version — the way 37 single-threaded
  units already are.
- [ ] **Then: A4 discharged, or narrowed.** With the driver written, the premise is either
  proved against it (as the ticket lock's premise was on 2026-09-15) or it stays and says
  precisely what about the driver is assumed.
- [ ] **`entry`/`boot`: the vector and the dispatch.** Today only the dispatch root travels;
  the vector, the registers and the steps have no form. After the hosted driver.

**The standard library is NO LONGER deferred** (owner, 2026-09-16): it moved to §0b, and the
reason is the same measurement that set this section's priority — a firewall written entirely in
Gabbro ran, and what it kept hitting was the empty shelf. *The runtime is still first: it is the
smallest piece of that shelf and the one every other piece stands on.*

**Threading is a MUST (owner, 2026-09-17): 3 Muse lanes now, Opus handoff later.**
O-1 (clone handoff) stays parked; these three feed it (sound pool semantics,
generated driver, lock through the chain). Reviewers from 321.

| lane | what | files owned (exclusive) | size | reserves N / gift / ex |
|---|---|---|---|---|
| 245 | symmetric pool: lift N304 with soundness + driver + Lean starts multiset | `fusswache2.rs`, `laufzeit/*`, starts-Lean | M–L | N436–440 / 1097–1101 / — |
| 246 | generated per-unit driver (ROOTS from `concurrent`) + P017 findings | `bau.rs`, new gen module | M | N441–445 / 1102–1106 / — |
| 247 | ticket lock through the chain (checks, emits, RUNS) | `laufzeit/sperre.gab` only | S | none |

# 0b. The standard library, native in Gabbro  ⟨A⟩

*Owner, 2026-09-16: **everything a standard library does — except networking, files, graphics
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
in `/home/ubuntu/brandmauer/messung/`; these are the ones that belong to the language.*

- [x] **No atomic array** — 256 counters cost 5136 lines and 1797 ops per increment. Built
  2026-09-16; measured payoff 287 lines and 11 ops. *And the wall was hiding three silences: the
  index bound was never checked at two of three atomic access forms.*
- [x] **`Held(L[i])` evaporated silently** — a file whose only lock guard named a lock that does
  not exist passed with `0 errors, 0 hints`. Refused by name since 2026-09-16 (`N390`), and the
  answer to striping is **stripe the tables, not the locks**: 8× the concurrency for 4,9 % more
  ops (measured), because the permission predicate is conjunctive and `Held(L[i])` could only
  ever mean "hold all N".
- [ ] **Cross-unit table access does not exist** (`M119`) — see §0b, first item. **This is the
  one the owner named: it blocks the library and it blocked the firewall's own wiring.**
- [ ] **No symmetric worker pool**: `concurrent { f, f }` is refused (`N304`), so N workers on
  one routine must be spelled as N distinct roots. **For a firewall that is a bigger ceiling
  than the lock was**, and it needs its own lane.
- [ ] **No thread start at all** — every shape refused (`P017`, measured 2026-09-15). §0 owns it.
- [ ] **No early exit from a `traverse`** (`S001`, no label) — "find the first, then continue"
  is unwritable.
- [ ] **`match` has no integer arms** and nesting is capped at 32 (`P038`), so a 256-way
  dispatch becomes a flat chain of comparisons, measured at 1797 ops.
- [ ] **`accumulates` cannot be `pub`** (`P041` against `N038`).
- [ ] **A `bool` static checks clean and never becomes C** (`C001`).
- [ ] **`transition` and `advances` stand in `SYNTAX.md` §8 with no parser arm** — one of them
  with a Lean constructor and a theorem. Two of sixteen statement head words, and **nothing in
  the tree measures this class**.
- [ ] **The emitter has no `atomic_fetch_add`**, and the measured reason is real: a checked
  `±1` cannot answer in its own type, and `+%` would wrap at a different width than C's
  fetch-add. The owner decides whether the binder-range refusal is lifted (`OPUS-BERICHT-FETCHADD.md`
  §2.3 has the patch shape and the test that must survive it).

# 0d. The claims, as they stand — corrected against today's measurements  ⟨Q⟩

*The owner listed these on 2026-09-16 as the things that must be written down. Where a line was
stale, the measured number stands beside it: a status list nobody re-measures is the thing this
tree refuses everywhere else.*

| the claim | as measured 2026-09-16 |
|---|---|
| chain count 2 of 111 | **2 of 113** (`zaehle-kette.py --lean`); sieves (a) 2, (b) 15, (c) 15, (d) 55, (e) 2 |
| T2, the re-checker: designed, not built | **built** — `korrOk` (`KorrespondenzAllg.lean`), 23 expression arms plus the block structure (`if`, `let` of a call, `traverse`), sound with a planted defect per arm |
| 16 of 21 templates are an abstract core | unchanged, and still the honest state of T5 |
| the concurrent half not begun | **begun and closed for ONE program**: `schlusssatz_124`, every SC run of the emitted C simulated in G, race freedom PROVED from the model's rather than assumed; the generic concurrent case is untouched |
| no pass proved individually | unchanged. 163 sentences, 155 measured, 0 proved — and that is the gap between "the checker is measured" and "the checker is proved" |
| Caprock: fragments only | unchanged. Six areas written out, 10 of 10 units error-free, nothing compiled into a kernel |
| the runtime | assumption A4, and the two-thread program still does not run: no `main`, the lock primitives declared and undefined, no thread start (§0) |
| the standard library | empty shelf; §0b is the plan since today |

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
  with zero corpus gain, honestly reported. Next: the sieve classes one by
  one, measured by the export count.
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
  template: 4 of 6 with full models (108, 124, 109, 59), 125
  reshaped-with-proved-blockage, 07 with proved impossibility of a
  non-degenerate witness.
- [ ] **Exporter-side concurrent coverage (the residue).** `lean-g` still
  refuses locks, `held` sections and multiple starts (LG001/LG004); only
  108 of the six exports. The hand models above are the bridge, not the
  widening. Measured by how many of 07, 59, 108, 109, 124 and 125 export.
- [x] **`beispiele/124`'s `setze` promises both slots** (`dokumente/OFFEN.md`
  O12) — lane 204, reviewed (reviewer 219, r2) and merged (`5ececd63`,
  2026-09-17). `ensures konto.slots[0].stand == konto.slots[1].stand &&
  konto.slots[0].stand == x`, so the locked section re-establishes the lock
  invariant from the callee's promise. `gabbro obligations` and
  `gabbro counterexample` display a failing user obligation
  (`obligations_g.rs`, `gegenbeispiel.rs` + tests); no new refusal, the
  checker still accepts. The release rule (demand the invariant from callee
  promises at every locked-section exit) stays a proposal in
  `MUSE-REPORT-204.md`, not built.
- [x] **The C read correspondence for nested arrays** — lane 205, reviewed
  (reviewer 212, r1) and merged (`1198a0b9`, 2026-09-17).
  `grammatik/Grammatik/CFormNested.lean`: `cform_nested_read` for the
  emitted reads of `[[T; n]; m]` plus `cform_nested_read_zeuge`, standard
  three axioms, planted-defect check (a swapped stride fails red). The
  `Grammatik.lean` import was added by the merger. The reviewer verified
  that `pruefe-cformen.py` carries no nested-array row to flip (only
  `expr:array-read`).
- [x] **The simulation-certificate printer for stage (b)** — lane 206,
  reviewed (reviewer 220, r1) and merged (`71c5eaea`, 2026-09-17).
  `corrcert.rs::SimCert124` prints the four R124 position tables as JSON
  (`.simcert`) and as the Lean literal `cert124_printed`, with unit tests
  (every forged table fails, both spellings pinned);
  `grammatik/Grammatik/SimPruef.lean` checks the printed certificate into
  the `sim124` conclusion (`simpruef_liefert`, `simpruef_124_zeuge`).
  Round trip measured on 124; program #2 is §2 stage-(b) work.

# 2. Translation validation  ⟨D⟩

**Stage (a) — single-threaded, generic** (`Schlusssatz.lean`, `KorrespondenzAllg.lean`; plan §6).

- [ ] **Sieve (a), the elaborator** — lane 199 (running). 89 of 111 programs stop there: 69 have
  an item without a G form, 12 a unit without a table, 7 use `bool`, 1 uses `requires`.
- [ ] **Sieve (a), the Lean parser** — lane 200 (running). 20 programs stop there, 10 of them at
  `reserved head forall`.
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
- [ ] **Inline assembly: a small ISA semantics** for exactly the stub patterns the emitter
  writes, so each stub gets a correspondence lemma instead of `AxCorr`.

**Beyond DRF-SC: full weak-memory coverage (priced, deferred — owner, 2026-09-18).**
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
DRF-SC is the honest contract (no races ⇒ SC covers every real
firewall/driver case).

# 3. The goal statement — follow-ups  ⟨D⟩

- [ ] **The liveness assumptions go into the ONE list in `Spec.lean`'s header**: `LaufzeitAnnahme`
  (FIFO lock and fairness window `F`) and `HardwareImAbschnitt`. Today they sit in
  `Lebendigkeit.lean`.
- [ ] **The external human review** of the review package (PLAN-ZIELSATZ §5): the definitions
  the kernel cannot judge. That is the machine G, the good-run predicates, `KoerperGutS`, the
  goal predicates, and the C semantics core.
- [ ] **The final double verdict over the whole chain.** One Muse lane and one Opus agent,
  independent, once stage (a) covers the corpus: "is the goal reached for the product, not only
  the model?"
- [ ] **Keep README §6 true** after every merge that moves the chain count or a stage.

# 4. Extensions and named gaps  ⟨D⟩

*Rules for every extension: PLAN-ZIELSATZ §8. The criterion is counted per obligation, there is
one assumption list, and the number is booked before and after.*

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

# 5. Simplicity without losing a guarantee  ⟨E⟩

*Measure (PLAN-EINFACHHEIT §0): `gabbro zeremonie` goes down AND the pass register stays
constant.*

- [ ] **Lever 3: `gabbro fmt --explicit` / `--elide`** — lane 197 (running). Pure views: same
  diagnostics, same register, byte-identical C, round-trip idempotent.
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

  Re-measure each on fisch with `./instrumente/abnahme.py --voll`, and rebook or repair them, one
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
- **Probabilistic statements and dynamic unbounded data structures** are out of scope (owner,
  2026-09-14). They are not claimed and not worked on.
- **Nonlinear arithmetic over unbounded integers** stays user logic with hand lemmas. It is the
  one place the oracle-plus-certificate pattern does not reach.
- **The bootstrap chain** (Gabbro written in Gabbro) is deferred, with the measured reason in the
  old TODO (commit `1434efba`, "DIE BOOTSTRAP-KETTE").
- **Known absences** O1–O14 are recorded, with what would close each, in `dokumente/OFFEN.md`.
