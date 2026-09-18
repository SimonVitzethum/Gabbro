# MUSE-REPORT-243 — arena-reset reuse safety (TODO §-1 wave D)

Lane 243, 2026-09-18. Scope: the decided free discipline of
`dokumente/PLAN-DYNAMISCH.md` §6 (arena-reset picked; linear free-list
rejected) plus the cost/budget handoff of plan §§7–8.

## Verdict in one line

**The decided discipline (arena-reset) is built where it was missing --
as a proved Lean reuse-safety theorem -- and needs no new refusal code;
the `grow` cost arm of plan §§7–8 is unbuildable on the current tree
(no `StmtArt::Grow`, no `max` clause) and is handed off with exact
coordinates. `MARKE_EMIT` untouched, corpus verdict diff zero.**

## 1. What was built

New file `grammatik/Grammatik/ArenaReset.lean` (151 lines) over the sugar
of `ArenaZucker.lean` -- no new syntax, no new constructor, no new checker
rule -- plus the one import line in `grammatik/Grammatik.lean`
(the only existing-file touch, required by rule 5):

- `reset_alloc_laueft_rumpf`: after `reset A;` the counter stands at zero,
  strictly under the hard bound, so the next `alloc` runs its body (never
  its `else`) with a freshly issued index `k` with `k.n = 0`. Composition
  of `arenaReset_stand` and `arenaAlloc_unter_schranke`; the index is
  carried existentially so no dependent rewriting is needed. Every premise
  is used (`hwG`/`hLG` feed both the reset and the alloc); no conclusion
  conjunct repeats a premise; worlds come from `execStmt`/`execBlock`;
  no premise has type `Prop`; no premise quantifies over contracts.
- `reset_alloc_rumpf_zeuge`: JOINT instantiation of ALL premises on the
  `ArenaZeuge` fixture (`Log`: four byte slots, `0 .. 4` counter): arena
  `Log`, value `sieben`, concrete continuations `voll0`/`Block.nil`, the
  FULL world (`welt 4` -- the wholesale case: reset from full, then
  reissue), `.nil`, oracle `oz`, `keinRuf`. NON-DEGENERATE: the fixture's
  one table is written by the reissued body, and the proved reset outcome
  moves the counter (`4 -> 0`, a global store) while the proved body-run
  is the slot-store-plus-bump path, not the `else`. (Precision note: these
  are `execStmt`/`execBlock` outcomes, not `RufMaschine` runs -- there is
  no machine run to reach here; the memory move is the proved world
  equality plus the proved body-vs-else branch selection.)
- `alloc_voll_ohne_reset_nimmt_else`: the negative direction -- without a
  reset, `alloc` on the full arena takes its `else` (by application of
  `zeuge_alloc_voll`). The positive theorem is not vacuous.
- Helpers: `oz` (witness oracle: `False` visibility, empty axiom/register
  domains), `voll0` (`.ret .keine`, nothing left to hold).
- `CUTS` block plus `#print axioms` for all three theorems.

Verification:

- `./lean-probe grammatik/Grammatik/ArenaReset.lean`: exit 0, 0 errors;
  all three theorems depend on exactly
  `[propext, Classical.choice, Quot.sound]` (standard three).
- `./lean-bau`: `Build completed successfully (278 jobs).`
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (grepped).
- `./cargo-pruef`: `== exit 0; failing tests: 0` (no Rust file touched;
  the run is the machine check behind the zero-diff claim below).
- Corpus verdict diff: ZERO by construction (no checker/emitter file
  changed; `cargo-pruef` green over the identical tree, gifts included).
- `MARKE_EMIT*`: untouched (grepped: zero hits in both touched files).
- New codes/gifts/examples: NONE consumed. The reset discipline needs no
  new refusal: staleness is `N211` (exists), over-reservation is `N212`
  (exists), and lane 240's reserves (`N426`–`N430`, gifts `1088`–`1091`)
  go back unused from this lane.

## 2. The aliasing-freedom argument (deliverable 2), stated plainly

Use-after-free is inexpressible and double-free is a no-op, for three
separate reasons owned by three separate layers:

1. **No handle outlives a reset (syntax).** An `alloc` index is a binder
   introduced by `Block.narrow`, scoped to the continuation block. There
   is no stored reference type for a slot -- only the binder and the
   counter. A reset cannot strand what cannot be named past it. (Stated,
   not formalised -- see CUTS: formalising it means quantifying over all
   terms.)
2. **Stale binders are refused (checker).** `N211`: every index bound
   before a `reset` is stale afterwards. Pre-existing, with probes.
3. **The wholesale reissues from zero (run -- proved here).**
   `reset_alloc_laueft_rumpf`: post-reset the counter is `0 < hi`, so the
   next `alloc` runs its body with index value `0`. No slot is stranded,
   no generation check is owed to the run, and the full-without-reset
   case provably takes `else` instead.

Where it refuses: any use of a pre-reset index (`N211`); any `alloc`
whose static count may exceed the reservation without a branch (`N212`).

## 3. The cost side: blocked, with exact handoff (plan §§7–8)

The `grow` cost arm (`1 + n * declared-per-slot + else`, through `K003`;
`K002`-falls probe for `grow` inside `locks`; §8 static-vs-dynamic tally)
cannot be built on this tree:

- `StmtArt` (`crates/gabbro-syntax/src/ast.rs:1295`) has `Alloc` and
  `ResetArena` but **no `Grow` variant**; the arena declaration has **no
  `max` clause** (parser lane unowned -- lane 240 finding 2, confirmed).
  A cost arm with no AST to match on is not a cost arm.
- `kosten.rs` is lanes 223/232's file (TODO §-1 waves A/B); one lane, one
  file set -- I did not touch it.

Handoff coordinates for the lane that owns `StmtArt::Grow`:

- Cost arm site: `kosten.rs:1080` (`StmtArt::Alloc` arm,
  `1 + value + else`) -- the `Grow` arm is that shape with the declared
  per-slot commit cost times the constant `n` in place of the value cost.
  `ResetArena` (`kosten.rs:1087`) stays `Zahl(1)`: commit survives reset
  (monotone), so reset prices nothing new.
- `K002` walk: the existing `sperrbloecke` traversal already prices every
  `StmtArt` inside `locks` against `held` (lane 240's
  `arena_wachstum_in_sperre_k002` probe proves the mechanism for `alloc`);
  a `Grow` arm is priced there with zero new machinery -- the probe to
  add is the `grow`-overflows-`held` twin.
- Static baseline measured on this tree (`target/debug/gabbro kosten`,
  binary built by `./cargo-pruef`):
  `beispiele/98-arena-erklaert.gab`: `nutzen 11 / 16` (3 allocs, 1 reset);
  `beispiele/99-arena-grenze.gab`: `grenze 34 / 34` (5 allocs, 1 reset).
  The §8 tally method is ready: dynamic checked-`alloc` must cost static
  + one word load per checked access (X = 10% headroom); ghost bytes are
  2 words (`base`, `committed`) + 0 proof bytes. Nothing to tally against
  yet -- no dynamic lowering exists (lane 242 unbuilt).

## 4. Design gaps and conflicts (findings, not built)

1. **Parser lane still missing** (confirms lane 240 finding 2): `max M`
   clause shape, `grow A by n else B` statement shape, `SYNTAX.md` §9.1
   delta, `ArenaSig::max` field. Until it lands, `R-commit` coincides
   with `N212` and `R-grow-else/const/form` have no syntax to fire on.
2. **Lane 242 (emitter + runtime) unbuilt**: no descriptor, no
   `reserve.c`/`grow.c`, no OS-token guardian. The §8 tally and the
   executed grow probe wait on it.
3. **Assignment conflict for the record**: TODO §-1 says 243 = free
   discipline while PLAN-DYNAMISCH §10 says 243 = costs + budget; the
   lane prompt merges both. I built the overlap that is buildable
   without new syntax (the reset proof, TODO side) and handed off the
   rest (cost arm, PLAN side) with coordinates instead of inventing
   syntax to cost. The linear free-list stays a rejected alternative
   per plan §6 (no corpus program needs interleaved lifetimes; `98`/`99`
   are single-phase) -- nothing built for it.
4. **Preamble vs task**: the wave preamble ("independent reviewer: do
   not change any existing file") contradicts the lane task (new Lean
   file + probes + report, committed). I followed the specific task like
   lanes 240/241 did; the only existing-file change is the one import
   line rule 5 requires. No existing theorem touched.

## 5. Names added

- `grammatik/Grammatik/ArenaReset.lean`: `reset_alloc_laueft_rumpf`,
  `reset_alloc_rumpf_zeuge`, `alloc_voll_ohne_reset_nimmt_else`, `oz`,
  `voll0`.
- Last `./lean-bau` result line: `Build completed successfully (278 jobs).`
- Last `./cargo-pruef` result line: `== exit 0; failing tests: 0`.

Open: parser lane (finding 1); lane 242 build (finding 2); the §8 tally
once 242 lands (method + baseline in §3); `DynForm`-level simulation and
the two (d) assumption texts (lane 241 CUTS / lane 244 §6.1 --
reassignment needed, not this lane).
