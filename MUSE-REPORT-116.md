# MUSE-REPORT-116 — Arena in the checker (PLAN-ERWEITUNG.md §3, lane E4 checker half)

Branch: `muse/116`. Task: surface + checker + emitter + probes for the monotone arena.
The Lean model (`grammatik/Grammatik/Arena.lean`, lane E4 model half) pre-exists and is
untouched — no Lean file changed, no Lean theorem added, so rule 13 owes no witness.

## What was built

**Surface** (`dokumente/SYNTAX.md` §9.1, new; §7 `allocstmt`/`resetstmt`; §9 `arena`):
`arena A capacity lo .. hi of T;`, `let i = alloc A (v) [else block];`, `A[i]`,
`reset A;`. Four new words (`arena capacity alloc reset`, all `ctx`), three new EBNF
rules (167 → 170), vocabulary 228 → 232 table words.

**Parser** (`crates/gabbro-syntax`): `Kw::{Arena,Capacity,Alloc,Reset}` with reason
blocks (`kw.rs`); `ItemArt::Arena(ArenaDecl)`, `StmtArt::Alloc(AllocStmt)`,
`StmtArt::ResetArena(Ident)` (`ast.rs`); `arena()` + `item` arm + `pub` + `faengt_item_an`,
alloc branch in `letform` (lookahead-gated so a bare `alloc` stays an expression),
`reset` arm in `stmt` (`parse.rs`). `A[i]` is the existing place form, no parser change.

**Checker**: new pass `crates/gabbro-check/src/arena.rs` (`pub fn pass`), wired behind
`syscall::pass`, plus `N214` at the one place typing every `Ort` (`m1.rs::arena_ort`,
`arena_schreibziel`):

| code | rule | probe |
|---|---|---|
| `N210` | bounds are constants with `0 <= lo <= hi`, `hi` in `1 ..= u32::MAX` | gift 885 (inverted) |
| `N211` | no read of an index outside its generation (incl. reassigned names) | gift 886 (stale after `reset`) |
| `N212` | `else` owed iff the static count since the last reset is already `>= lo` | gift 887 (missing `else`) |
| `N213` | `alloc`/`reset` name a declared arena | gift 888 (unknown) |
| `N214` | an arena place is exactly `A[i]`, `i : index into A`, never written outside `alloc` | gift 889 (foreign index) |

Counting runs per function like `costs` (reset → 0, alloc → +1 saturating, branches join
with max, growing loop bodies saturate); generations are counters, reset takes a fresh
one, a one-sided reset invalidates at the join. `Umgebung` carries `arenen`
(`ArenaSig{lo,hi,element}`), `indextyp` reads arena bounds, `typ_von_ort` resolves the
well-shaped `A[i]` to the element type. One code lives in exactly one file
(`pruefe-kennungen.py` ALL PASS); `N214`'s three faces are one rule (`N065` precedent).

**Emitter** (`emit.rs`): `arena()` writes `typedef struct { T buf[hi]; uint32_t used; }
A_arena;` plus conditional `static A_arena A_arena_speicher;` (used-set, like tables);
`alloc` lowers to the checked bump (with `else`) or the counted bump (inside the
reservation); `reset` stores 0; `A[i]` reads `A_arena_speicher.buf[i]`. No heap.

**Probes/examples**: `beispiele/gift/885-889` (each fires exactly its code, verified with
`faellt_genau` in `paesse.rs::arena_*`), `beispiele/98-arena-erklaert.gab` (in-reserve
without `else`, past-reserve with `else`, reset, alloc again, read) and
`beispiele/99-arena-grenze.gab` (`lo == hi` boundary, empty reservation, two arenas) —
both fully clean and compiling at `-O0`/`-O2` under `-Werror`.

**Sentences/registers**: `arena.erklaerung` (`saetze.rs`, in `PHASEN`, claims N210–N214);
`N210`–`N214` in `korpus.rs::BENANNT`; `MARKE_WOERTER` 231→235; `MARKE_EMIT` 75→78
(decomposed: +2 mine, +1 E2 drift); `PASSREGISTER.md` recomputed (131 sentences, 123
measured, 331 codes, 276 claimed, `ohne Satz` unmoved at 55); `TODO.md` figures
(131/331, 26/26 item kinds); `pruefe-zahlen.py` Item-Arten pattern made total-flexible
(bilingually, before the document moved).

## Verification

- `./cargo-pruef`: **exit 0, 0 failing tests** (last full run).
- `./lean-bau`: **0 error lines** (no Lean changes; warnings pre-existing).
- `./emission-pruef`: **227 of 227 emitting files compile** (98/99 included); Stufe 9
  still exits 1 on count marks that are all drift (messung 132/73, gift decke 8/2, roots
  8/1, umgekehrt 2/4 — none involves a file of this lane; verified file by file).
- Guardians green: `pruefe-wortschatz` 232/232, `pruefe-syntax.sh` (170 rules, ALL PASS),
  `pruefe-grammatiktafel` (0/232 UNGEDECKT), `pruefe-saetze` (55 ohne Satz unmoved),
  `pruefe-kennungen` (ALL PASS), `pruefe-vergabe` (re-booked 25/81), `pruefe-sondendeckung`
  (ALL PASS), `zaehle-wortschatz` (235/212).
- Still red from the merged base (measured identical via `git stash` baselines, not mine):
  `pruefe-zahlen.py` (19 findings, all pre-existing drift), `pruefe-englisch.py`
  (7905/7881, 1085/1069, 1/0 — my delta is zero), emission Stufe-9 drift marks above.

## New definitions (Rust; no new Lean)

- `gabbro-syntax`: `Kw::Arena/Capacity/Alloc/Reset`, `ArenaDecl{name,oeffentlich,lo,hi,element,span}`,
  `AllocStmt{veraenderlich,name,typ,tisch,wert,sonst}`, `ItemArt::Arena`, `StmtArt::Alloc/ResetArena`.
- `gabbro-check`: `umgebung::{ArenaSig, Umgebung::arenen, nennt_arena}`, `arena::{pass, Stand, Laeufer}`
  (`N210`–`N213`), `m1::{arena_ort, arena_schreibziel}` (`N214`), `emit::{Namen::arenen/arenen_global, arena()}`,
  `saetze`: `arena.erklaerung`.

## What remains open (CUTS)

1. The count is per function: functions sharing an arena share the runtime counter unseen
   (same class as `costs` recursion). A cross-function reservation discipline is future work.
2. `let i: index into B = alloc A (…)` with equal bounds binds a cross-arena lie M1's
   `passt` cannot see; only one code per file is allowed, so no second verdict stands here.
3. Loop bounds saturate (`traverse`/`forever` with a growing body force `else`); `retry`
   uses its `bounded N`. A `domaene.rs`-read bound would narrow this.
4. `absenkung.rs::PRIMITIVES` still lists 17 statement kinds (hook unwired); arenas are not
   rows there. `&A` (pointer to arena) and `traverse … over` an arena are not built.
5. Stale-index-as-value (`alloc B (i)` with `i` of a consumed generation of `A`) is
   accepted: values are numbers, generations travel only with index positions.

## Task feedback

- "Implement with the existing linear-mark machinery (`eigner`, `consumes`, `allocs`)":
  that machinery is declaration-level only — `owner` parses and is refused (`D026`,
  no minter), `consumes`/`allocs` are effect words, and no per-statement linear value
  context exists. Generations are therefore tracked in the arena pass itself (counters
  shadowing the Lean type index), which is the honest reading of "an index obtained
  before a reset is a type error after it" at checker level.
- "New codes only 210-214": taken as `N210`–`N214` (the `N` family stands at `N069`;
  the 200s are collision-free). If numeric-only codes were meant, no such family exists.
- Gift 885–889 / examples 98–99 were free as assigned (`beispiele/98-99` did not exist;
  gift top was 854).
- Arithmetic on arena reads needs widening binds (`let x : u32 = A[i];`) — full-range
  elements overflow under `M104` otherwise; probes use comparisons, examples widen.
- `module m;` is not a form (braces required) — probes/examples wrap in modules.
