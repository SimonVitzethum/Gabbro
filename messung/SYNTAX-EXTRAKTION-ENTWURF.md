# Syntax-given extraction for shared footprints — design

Status: DESIGN ONLY, no implementation. Worktree lane-38, base 2657f77.
Not committed. `SYNTAX.md` itself is untouched; the paste-ready section
draft stands in §4 below.

Goal: turn `Geteilt.Bau`'s declared footprints into COMPUTED ones. Today
`Bau.schreibtFn` is declared per function and `Bau.neben` a declared pair
list (`Geteilt.lean` cuts C2/C3); the checker (`H013`) writes `shared` by
hand. The design computes all three from what the grammar already admits:
call-graph edges from bodies, per-body footprints from effects, the pair
list from the `concurrent` declaration — and states the linkage to the
`Geteilt` premise shapes as `Prop`-valued defs, not theorems.

New code (this lane, two files only): `grammatik/Grammatik/Extraktion.lean`
(standalone, no imports — the lane forbids the `Grammatik.lean` index edit,
so it mirrors instead of importing, same pattern as `Geteilt.lean`).

## 1. Inventory (measured on this tree)

What is declared where, and where its Lean home stands:

| spelling | declaration | Lean home (read-only) |
|---|---|---|
| `effects { writes T, … }` | per-signature write effects | `Signatur.schreibt/gschreibt` (`Syntax.lean:84-85`), per function via `D.schreibt/gschreibt` (`:195-196`), contract side `Vertrag` (`:234-240`) |
| `f(a, b);`, `let x = f(…);`, `… else …` | direct calls in bodies | `Stmt.call` (`:424`), `Block.bindCall` (`:475`), `Block.bindCallElse` (`:481`); bodies enter per function via `Programm.rumpf` (`:562`) |
| `p(a, b);` (fnptr), `extern`/`prim`/`asm` rumpfless | calls with NO static edge | `Stmt.callInd` (`:427`), `Block.bindCallInd` (`:478`), `axiomCall` (`:442`) |
| `shared` at `table`/`static` | the flag under test | `D.geteilt/ggeteilt` (`:128-129`), guarded-flag explanation `geteilt_bewacht` (`:178`) |
| `concurrent { f, g };` | declared-concurrent bodies | `Nebeneinander` premise (`Wettlauf.lean:523`), restricted interleaving `BeschraenkteVerschraenkung` (`:527-530`) |
| closed-world declaration | entries, edges, footprints, flags, pairs | `Geteilt.Bau` (`Geteilt.lean:69-81`), carrier computation `traegerBis` (`:157-160`), run form `BauLauf` (`:307-310`) |

What the corpus says about the call side: 267 `fn` decls in `beispiele/`
(per `NEBENLAEUFIGKEIT-ENTWURF.md` §1 inventory on this base); every one of
them already carries a mandatory `effects` clause (`SYNTAX.md`: a function
WITHOUT `effects` is a compile error, `effects { pure }` for the empty
case) — so the footprint source is total by construction, and the only
missing piece is the computation from source to `Bau`.

## 2. Extraction mapping (what `Extraktion.lean` computes)

Inputs are projections of the syntax (carried, not computed); every `def`
below them is computed. Output type is field-for-field `Geteilt.Bau`:

| syntax source | extraction input (carried) | computed `def` | `Bau` field | premise shape (`Prop`-valued `def`) |
|---|---|---|---|---|
| `Stmt.call`, `Block.bindCall`, `bindCallElse` over `Programm.rumpf` | `ruftDirekt : Fn → List Fn` | `ruftNorm` (domain filter), `kantenListe` | `ruft` | `kantenTreue`: no direct call falls out (over-approximation direction) |
| `effects { writes … }` via `Signatur.schreibt/gschreibt` | `effSchreibt : Fn → Carrier → Bool` | `fussAus` (filter over domain) | `schreibtFn` | `fussTreue`: no effect falls out |
| `shared` via `D.geteilt/ggeteilt` | `marken : List (Carrier × Bool)` (domain AND flag, one table) | `traegerAus`, `geteiltAus` (lookup, default `true`) | `traeger`, `geteilt` | — (fail-closed default is the shape: unknown means shared) |
| `entry`/`boot` dispatch roots | `eintritt : List Fn` | — (carried) | `eintritt` | `erreichtSpiegel` over `traegerBisSpiegel` (mirrors `ErreichtBau`/`traegerBis`) |
| `concurrent { … }` over thread numbers | `paare : List (Nat × Nat)` | `nebenAus` (entry-bounds filter) | `neben` | `paarTreue` (list into `Nb`), `paarVoll` (checker's converse duty) |
| — (assembly) | all of the above | `bauAus : BauSpiegel` | ALL SIX | `bauLaufSpiegel` (mirrors `BauLauf`: coverage AND pairs-only) |

Failure is LOUD and fail-closed throughout: dangling call edges, effects
outside the domain, and out-of-entry pairs are DROPPED by the computation,
and the fidelity shapes (`kantenTreue`, `fussTreue`, `paarVoll`) name the
checker's duty to REFUSE whatever was dropped. Indirect calls (`callInd`)
and foreign bodies (`axiomCall`) yield NO edge — the checker refuses them
instead of guessing (same direction as `W003`: incomplete hulls refuse).
`geteiltAus` answers `true` outside the table: unknown means shared, which
demands the guard instead of the uniqueness.

## 3. Cuts (booked, not hidden)

- C1 (carried over from `Geteilt.lean`): one `Carrier` for tables and
  globals; the `fnCode`/`tabCode`/`globCode` encodings arrive with the wiring.
- W-EXT (the traversal): `ruftDirekt` is the PROJECTION of the body, not the
  traversal itself — `Stmt`/`Block`/`Endblock` cannot be walked without the
  import, and the import needs the index edit this lane forbids. The
  traversal collects `call`/`bindCall`/`bindCallElse`; `callInd`/`axiomCall`
  contribute nothing (refuse, don't guess).
- Reads: `effects` declares writes only; an expression-read hull
  (`slot`/`glob` in `Expr`) is missing and needed only for the two-thread
  frame model (`Interferenz.lean`), not for (W5) — reaching means reaching
  to write.
- No theorems: every linkage item is a `Prop`-valued `def`. Proving
  `bauLaufSpiegel` from `bauAus`, and `geteilt_treu` over the extracted
  `Bau`, is the wiring lane's work.

## 4. Proposed `SYNTAX.md` section (paste-ready draft, NOT applied)

> ### `concurrent`, `effects`, `shared` — from declaration to computation
>
> The three declarations that feed the closed-world check arrive computed,
> not transcribed. `effects { writes T }` is the footprint source: per body,
> filtered over the declared carrier domain, it IS `Bau.schreibtFn` — a
> function without `effects` is already a compile error, so the source is
> total. Direct calls (`f(…)`, `let x = f(…)`, `… else …`) are the edge
> source: they ARE `Bau.ruft`, restricted to the declared function domain.
> `concurrent { … }` members resolve to thread numbers over the entries and
> ARE `Bau.neben`. What the computation drops (a call outside the domain, an
> effect outside the carriers, a pair outside the entries, any indirect or
> foreign call) the checker REFUSES — the fidelity shapes state exactly
> that. Unknown carriers count as `shared`: the loud direction, demanding
> the guard. Lean: `Grammatik/Extraktion.lean` (`bauAus`, `bauLaufSpiegel`,
> `kantenTreue`, `fussTreue`, `paarTreue`, `paarVoll`); premises consumed:
> `Geteilt.Bau`/`BauLauf`/`traegerBis`, `Nebeneinander` (`Wettlauf.lean` §6).

## 5. Wiring (what a later lane does, not this one)

1. Index edit (`Grammatik.lean`): register `Extraktion` — forbidden here.
2. Replace `BauSpiegel` by `Geteilt.Bau`, the `*Spiegel` fuel computation by
   `schrittBis`/`traegerBis`, `Nb : Nat → Nat → Prop` by `Nebeneinander`.
3. Write the body traversal (W-EXT) over `Programm.rumpf` and prove the
   fidelity shapes; feed the extracted `Bau` to `geteilt_treu` /
   `ungeteilt_aus_baulauf` so (W5) consumes computation instead of the pass.

## 6. Self-check evidence (this lane)

- `lake env lean Grammatik/Extraktion.lean` in `grammatik/`: clean, no
  output (no full build, no cargo).
- Hard rules, mechanically checked: no `theorem`/`lemma`/`example`, no
  `sorry`/`admit`/`axiom`, no `import`, no mathlib — only `def`/`abbrev`/
  `structure` (27 declarations); proof terms: none anywhere (the shapes are
  `Prop`-valued `def`s, no proofs taken or given).
- `SYNTAX.md` unedited; `Grammatik.lean` index unedited; only the two files
  of this lane are new.
