# Declared concurrency with automatic non-interference — design

Status: DESIGN ONLY, no implementation. Main tree, 2026-09-10. Not committed.

Goal: interference checkable automatically, zero user proof, no Owicki–Gries by
hand. Missing piece per `ZIEL-BEWERTUNG-2026-09-10.md` §2: sequential
`requires`/`ensures` validity under interleaving needs a joint model, with
`exec_rahmen` (frame: a body writes only what its contract `V` names,
`Satz.lean:1323`, premise `GutO O` only) as the candidate premise.

## 1. Inventory (measured on this tree)

How concurrent bodies arise — there is NO thread-spawn syntax (not in
`SYNTAX.md` §§1–15, no `spawn`/`fork`/`clone` in the 222-word vocabulary):

| source of a second body | sites (corpus: 71 `beispiele/` + 141 `messung/` units) |
|---|---|
| `entry … dispatch f;` (vector/IPI/syscall/timer) | 9 decls in 5 files (`syscall`×3, `systemruf`×2, `nmi`, `zeitgeber`, `halt_ipi`, `leiser_eintritt`); 9 distinct dispatch roots |
| `boot … dispatch f;` | 1 (`multiboot1`) |
| `entrust … assume …` (guest room, content unknown) | 1 (`jitpuffer`) |
| scheduler "threads" | 0 syntax sites — threads are ROWS of tables (`Faden`/`Faeden`×4, `Threads`×1 decls), driven by entries/IPI and ordinary `fn`s (267 `fn` decls in `beispiele/`); `forall t in threads` names NO table (`57-faedenhalt.gab`, `D022`/`D023` guard the binder only) |
| `per cpu` cells/stacks | 21 lines in 11 files (stacks `kernstapel`/`nmi_stapel`/`halt_stapel`/`takt_stapel` + `accumulates … per cpu N`) — one cell per core, no sharing by shape |
| `static … shared` / `table … shared` carriers | 16 `shared` lines; `H013` reports 0 hits over `beispiele/*.gab` (all entry-written places declare sharing) |

Which pairs run concurrently — is it ANYWHERE in Gabbro? Half. `gabbro kontexte`
(`kontexte.rs`: each `entry` = one context with dispatch root + transitive
effect hull via `Graph::huelle`, minus `masks`/`nested`/`per cpu` exclusions
under `assume ein_kern`) knows which PLACES two contexts touch, but no
declaration names which BODIES may run at the same time. Interference between
two `fn`s is currently unnameable: `H013` approximates ("entry writes it ⇒
shared"), `W5` (`shared` ⇒ which carriers two threads reach) is discharged by
that same Rust pass, and `W4` (a mark in one thread) holds by construction (no
constructor moves a mark across threads). Caprock side (read-only
`../caprock-messbasis`): thread birth/death (`exit_current`,
`record_zombie`/`reap_core`) is a table-row state transition plus a `mov sp`
below every type system — no spawn primitive there either.

## 2. Rule sketch: `concurrent` declaration + automatic pairwise check

New declaration (spelling §4) naming the bodies that may run concurrently, e.g.
over dispatch roots / scheduler entry `fn`s:

```gabbro
concurrent { syscall_verteiler, zeitgeber_verteiler, halt_verteiler };
```

The checker verifies AUTOMATICALLY, per unordered pair, from the already
computed transitive hulls (`Graph::huelle`, `Huelle.wirkungen`,
`unvollstaendig` is fail-closed: incomplete hull ⇒ refuse):

- `writes(hull f) ∩ writes(hull g) = ∅` — set comparison over declared effects,
  no proof, no solver. Shared READS may overlap freely.
- Shared writes overlap only if some lock `L` is in BOTH hulls' `locks` effects
  (then HB comes from `gibt L → nimmt L`; exclusion itself stays assumption W3).
- `publishes`/`awaits` payload pairs are exempt (HB via pairing, `V001`–`V007`
  already checked); `atomic` globals are exempt (machine orders, A10).
- Unshared carriers/threads-table rows written from two declared-concurrent
  bodies ⇒ refuse (this makes W5 checkable instead of passed-over).

Checked: pairwise write-disjointness from transitive effect hulls. Assumptions
that stay assumptions: lock-primitive exclusion W3 (foreign body, `assume`),
memory-model visibility A10 (`hardware (sichtbarkeit)`), `ein_kern` for the
`masks`/`nested` exclusions, scheduler fairness/liveness D8 (`progress`+probe).

## 3. What it does NOT do (decided loudly)

- Scheduler fairness/starvation: no mechanism (D8, `SPRACHE.md`:341) — a
  `concurrent` set says "may run together", never "each gets a turn".
- Dynamic thread creation: REFUSED. The corpus needs no spawn (0 sites; threads
  are table rows, covered as named bodies). If a target needs spawn, that is a
  new proposal with sites, not an extension of this one.
- Interrupt arrival times and preemption points: a declared pair is checked for
  ALL interleavings of the two bodies (same quantifier as `kein_wettlauf`
  today); WHEN the timer fires stays `progress` + probe.

## 4. Sugar / exhaustiveness / Lean impact

- EBNF delta: one item, `concurrentdecl = "concurrent" "{" path { "," path } "}" ";"`
  — ONE new vocabulary word (`concurrent`, 222→223; lexer + `pruefe-wortschatz.py`
  cost). Zero-word alternative (reusing `group … over`) rejected: `group` is over
  carriers with invariants, and one word meaning two things is the `reserved`
  trap class. Non-declared pairs are NOT concurrent — closed world, so nothing
  is fail-open.
- Lean: the declaration becomes a premise `Nebeneinander : Faden → Faden → Prop`
  (which bodies share a run); `kein_wettlauf`/`kein_wettlauf_global` quantify
  over `IstVerschraenkung` RESTRICTED to declared pairs — strictly stronger than
  "every interleaving". W5-as-Rust-pass disappears (the declaration says which
  carriers are shared, `H013` checks the declaration instead of the world); W4
  stays by construction; W3 stays `assume`. The Owicki–Gries step becomes:
  `exec_rahmen` per body + pairwise disjoint frames ⇒ sequential contracts
  survive interleaving (joint model = the declared pair set).
- Relation to today: `kontexte.rs` already computes per-entry hulls — the new
  pass reuses `huelle()` and adds the pair comparison plus the closed-world
  refusal for undeclared overlap.

## 5. Falsifier pair (must-fail / must-pass, to be added as `gift/` probes)

```gabbro
// MUST FAIL: both bodies write T, declared concurrent
table T count 8 { slot { x : u32 } }
impl fn f_a() effects { writes T } { T.slots[0].x = 1; }
impl fn f_b() effects { writes T } { T.slots[1].x = 2; }
concurrent { f_a, f_b };   // expect: interference error naming T
// MUST PASS: disjoint write sets, shared read fine
impl fn g_a() effects { writes T } { T.slots[0].x = 1; }
table U count 8 { slot { y : u32 } }
impl fn g_b() effects { writes U, reads T } { U.slots[0].y = T.slots[0].x; }
concurrent { g_a, g_b };   // expect: clean
```

## 6. Open questions with owners

1. Lock-shared writes: is "common `locks L` in both hulls" checkable, or must
   shared-locked writes stay refused until a held-set analysis exists? (Owner:
   checker lane; needs `verlangt` + hull join.)
2. `entrust` bodies in a `concurrent` set: the guest's writes are unknown —
   refuse, or `assume` with falsifier? (Owner: proof-architecture lane.)
3. Per-CPU cells: exempt by shape (`per cpu` ⇒ disjoint) — checker rule or
   desugar to disjoint write sets? (Owner: checker lane.)
4. Threads-table rows: two bodies writing DIFFERENT rows of `Faden` share a
   carrier name but not a place — row-level disjointness needs index analysis
   the checker lacks; interim: same-table writes ⇒ refuse unless lock-shared?
   (Owner: design, needs corpus count of same-table/different-row sites.)
