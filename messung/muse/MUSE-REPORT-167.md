# MUSE-REPORT-167: tagged-union construction in bodies

Lane 167. A `tagged` type could be matched but never built. This lane builds the
construction, in the smallest form consistent with the model's `fall`.

**How this lane was verified.** The first half of the lane ran without a Rust
toolchain (no `cargo` on the machine, server unreachable), so the design and
the code below were verified by reading, with the emitted C reconstructed by
hand and compiled under `cc`/`clang -Werror`. The toolchain came back for the
second half, and every gate below ran green on this tree: `./cargo-pruef`
(exit 0, 0 failing), `./emission-pruef` (ALL PASS, 247/247), `./lean-bau`
(exit 0, 0 errors, 154 jobs), `pruefe-kennungen.py` (ALL PASS),
`pruefe-saetze.py` (ohne-Satz 55, unmoved), `pruefe-englisch.py` (exit 0),
`pruefe-vergabe.py` (marks rebooked, see §4). What stays red is red at base
too, each item named in §5 with its decomposition -- nothing of it is this
lane's.

## 1. Measurement first

- **The document was ahead of the tree.** `dokumente/SYNTAX.md` §4 already
  carries the row `` `Variant(e)` (a `tagged` case) | the payload has the
  case's type; the case index is in range by shape | the sum type |
  `Expr.fall cs i nutz` `` -- the surface existed on paper, with no reader
  behind it anywhere.
- **No parser or AST change was needed (measured, not assumed).**
  `Variant(payload)` already parses as `ExprArt::Ruf` over a single-segment
  path (`parse.rs::primary`, the `Art::Ident` arm) and a bare `Variant` as
  `ExprArt::Ort`. Variant names are read with `erwarte_ident`
  (`verbund_oder_varianten`), so no keyword spelling -- `Some`/`None`, integer
  words, `old`/`result`, `Held` excepted (see below) -- can ever declare one.
  The grammar already had the shape; only the resolution was missing.
- **The checker's view:** `Typ::Summe { name, varianten }` (`typen.rs`), V3
  (`m1.rs`: the `match` binder carries its variant's payload), `D005`
  (`kbedingung.rs`: exhaustive, no catch-all). A case in a body fell through
  as an unknown call: M1 answered `Unbekannt`, the graph refused `H021`, costs
  answered unknown (`K003` where promised) -- refusal by accident, in nobody's
  rule. A bare nullary case fell at `M119`; a `static` initialiser fell at
  `C001` in the emitter (checker-green, M1 visits the initialiser but answers
  `Unbekannt` against the sum silently).
- **The emitter's representation** (`emit.rs::markiert`, «C2»): `typedef enum
  { T_V, … } T_marke; typedef struct { T_marke marke; union { <C> V; … } last;
  } T;` -- nullary cases have no union member. `match_markiert` reads
  `{scrutinee}.marke` and `{scrutinee}.last.{V}`. The construction must write
  exactly these two designators.
- **The model** (`grammatik/Grammatik/Syntax.lean:408,474`): `Expr.fall (cs :
  List (Option (Int × Int))) (i : Fin cs.length) (nutz : NutzlastExpr Γ Λ
  (cs.get i)) : Expr Γ Λ (.sum cs)`, eliminated by `Stmt.onTag`. No `.lean`
  file is touched by this lane. The Rust side of the Lean export
  (`lean.rs::expr_term`) **already carried the call form** (`(.tagOf "Kurz"
  (some …))` / `(.tagOf "Leer" none)`); only the bare nullary form had no
  term.
- **The open item this closes:** `dokumente/OFFEN.md` O8 (with
  `messung/FUENFTE-MARKE.md` §4 and `messung/proben/probe-tagged-wird-gebaut.gab`):
  four spellings, three refused. After this lane the bare `Keine`, `Keine()`
  and `let x : Aufsatz = Keine` build; only `Aufsatz::Keine` stays refused
  (`M126`, deliberately -- cases carry no type name).

## 2. Design: the smallest form consistent with `fall`

No new keyword, no new production, no new AST node. Two spellings, both
already parsing:

- `Case(payload)` / `Case()` -- the `Ruf` shape, positional payload like
  `Some(x)` (labels stay at record constructors);
- bare `Case` -- the `Ort` shape, nullary cases only.

Resolution (`Umgebung::variante`, the one predicate every pass asks instead of
re-resolving): the visible `tagged` declarations are searched for the bare
name (own module, enclosing, root, `use` -- the same candidate order as every
other lookup). Zero owners: `N280`, gated on `hat_markierte` so a unit without
`tagged` types keeps `H021`'s refusal alone. Several owners: `N280` -- the
model index is read off ONE case list, and last-wins would be the module bug
of 2026-08-19 one level down. One owner: the construction answers the owning
sum with the case index in declaration order.

The arity is the constructor's own: missing payload `N281`, payload on a
nullary case `N282`, bare name over a payload case `N283`, labels at a case
`N284`. The payload RANGE is `M101`'s and its SHAPE stays out of the
constructor rules -- a truth value against a number is `M135`'s crossing
(measured, not assumed: the first test run expected `M140` and got `M135`),
anything else misshapen is `M140`'s -- all through the ordinary `passt`, and
a wrong sum at the binding is `M140`'s nominal rule -- the same split the
record constructor draws with `M106`. Costs one op like `Some`; the graph
carries no edge; the bare nullary term joins the Lean export.

**The soundness gap found during the build (not in the task):** the emitter
reads callees unit-wide and bare-keyed (`Namen::funktionen`, last wins) while
the checker resolves module-aware. A function of the case's name in ANOTHER
module -- invisible at the use site -- would take the emitter's call lowering
while the checker typed a construction: checker-green, wrong C, silent (the C
function exists, so `cc` stays quiet where signatures line up). A function of
the same name therefore blocks the construction unit-wide (`N280`,
`funktionsname_belegt`), and a function visible at the site keeps the call on
both sides. Same-module shadowing at the bare form follows the value
namespace (locals, globals, functions, tables, arenas win); integer words and
their sugar never name a case (`return u13;` stays `M119`'s).

Lowering, to the SAME representation `onTag` reads: bodies get the compound
literal `(T){ .marke = T_V, .last.V = … }` (mark alone for nullary cases --
there is no union member and no writable empty initializer); file scope gets
the brace form `{ .marke = T_V, … }` (a compound literal is no constant
expression), with the payload gated to translation-time constants. Unannotated
`let`s read the sum through `wert_ctyp`.

## 3. What changed

- Codes: `N280` (unknown/ambiguous/shared-name construction, call and bare
  forms), `N281` (missing payload), `N282` (payload on nullary), `N283` (bare
  name over payload case), `N284` (labels at a case) -- all in `m1.rs` (one
  file, `pruefe-kennungen.py` holds).
- `Umgebung::{variante, hat_markierte, ist_variantenkonstruktor,
  funktionsname_belegt}` + `VariantenFund::{Keine, Eine, Mehrere}` (the index
  travels in the hit, so checker, emitter and model read one order).
- `m1.rs`: variant arm in `ruf_roh` (before `marken_pruefen` and the function
  lookup), bare-case arm in the `Ort` branch (before `name_aufloesen`, or the
  valid form would draw `M119` beside its own type),
  `variantenkonstruktor`, payload taint through construction
  (`traeger_im_ausdruck` descends into constructor arguments -- no clean
  program changes by it, none existed).
- `emit.rs`: `ruf` arm, `ort` arm, `wert_ctyp` arms, `varianten_statisch`
  (brace form), `fall_belegt` (one shadowing predicate for both expression
  arms), `schatten` per-function set via `gebundene_namen` (params, `let`s,
  `let … else` + error names, `match` binders, traverse variables, `alloc`,
  `awaits`, `exchange`; loop labels bind no value and stay out).
- `aufrufgraph.rs`: no edge for constructors (threaded `u`+`modul` through
  `nimm`/`nimm_ruf`/`sammle_*`, read the one predicate).
- `kosten.rs`: one op plus arguments, like `Some`.
- `lean.rs`: bare nullary term (`tagOf … none`) with the checker's shadowing
  guards read through this channel's maps.
- Sentence `m1.sum_constructor` over all five codes.
- Gifts: `944` unknown (`N280`, beside `H021`/`K003`), `945` out-of-range
  payload (`M101` alone), `946` payload on nullary (`N282`), `947` missing
  payload (`N281`); `938` rewritten (its old shape is legal now) to the
  ambiguous shape (`N280` over two sums sharing `Kurz`).
- Examples: `120` (call form + bare form constructed in `baue`, matched
  exhaustively in `nimm` -- all three arms answer), `121` (both spellings at
  file scope, matched over the stored value).
- Tests: `variant_konstruktor.rs`, 9 rows (`N283`, `N284`, both nullary
  lowerings, function-wins incl. emitter agreement, invisible-function refusal,
  local shadowing, `M140` shape half, bare `N280` beside `M119`).
  `bare_atomic.rs`' two variant rows flipped to the new behaviour (body builds
  and lowers; static lowers in braces) -- the old `H021`/`C001` pins are
  superseded, 938's successor carries the refusal.
- Docs: `SYNTAX.md` (§4 EBNF comment + two attribute rows), `OFFEN.md` O8
  closed, `messung/proben/README.md` tagged row answered,   `TODO.md`
  (151 sentences / 376 codes + lane trailer), `DONE.md` (99 / 648 / 782),
  `PASSREGISTER.md` lane entry (figures NOT recomputed -- see §5),
  `tests/korpus.rs` `BENANNT` +5.
## 4. Gates -- what ran and what it said

- `./cargo-pruef`: exit 0, 0 failing -- incl. the 9 new `variant_konstruktor`
  rows and the 2 flipped `bare_atomic` rows. Two rows failed on the first
  measured run, both expectation bugs of this lane, both instructive: a
  labelled call (`Kurz(x: x)`) reaches `marken_pruefen` as a record-shaped
  `Ruf` before any name is resolved, so it fell at `M107`, not `N284` -- the
  arm now resolves a KNOWN case before the `ist_verbundwert` gate (unknown
  labelled names stay `M107`'s: a label claims a record, and only a known case
  rebuts that reading). And `Kurz(true)` falls at `M135`, not `M140`:
  `gestalt_grund` punts bool/number crossings to `M135` explicitly, so the
  shape half of a payload is `M135`-or-`M140`, never the constructor's.
- `./emission-pruef`: ALL PASS -- 35 durchgestochen, 247 von 247 uebersetzen
  (up from 240: the two examples join the denominator), clang accepts all 247,
  ASan clean. The single FUND on the way was the lane's own shadow:
  `messung/*/` emitting files went 132 -> 133, and the +1 is exactly
  `probe-tagged-wird-gebaut.gab`, which checked `M119` before this lane and
  checks clean since (`gabbro emit` writes 40 lines with `(Aufsatz){ .marke =
  Aufsatz_Keine }`, `cc -Werror` takes it). Mark rebooked with the file named.
- `./lean-bau`: exit 0, 0 errors, 154 jobs (no `.lean` touched). The changed
  Rust exporter exercised directly: `gabbro lean` on `120` emits
  `(.tagOf "Kurz" (some …))` for the call form and `(.tagOf "Leer" none)` for
  the bare form -- the new `place_term` arm fires; on `121` it exits 0 with no
  `tagOf` (file-scope state is no program term, correctly).
- Direct runs: `120`/`121` check clean (0 errors); `944` falls `N280` beside
  `H021`/`K003`; `945` falls `M101` alone; `946` falls `N282` alone; `947`
  falls `N281` alone; rewritten `938` falls `N280` (ambiguous) beside
  `H021`/`K003`. Cost budgets recomputed by hand against `kosten.rs` (`baue`
  = max(1,0) <= 8, matches = 0 <= 16) and confirmed by the clean runs.
- `pruefe-kennungen.py`: ALL PASS (383 vergeben, all five new codes in
  `m1.rs`). `pruefe-saetze.py`: ohne-Satz 55, unmoved by construction.
  `pruefe-englisch.py`: exit 0 -- with one repair on the way: splitting a
  brace join in `aufrufgraph.rs` surfaced a pre-existing German comment line
  (7949 -> 7950, ratchet broken); the whole block is now English, count 7941
  (the ratchet falls, which is allowed).
- `pruefe-vergabe.py`: marks rebooked 29 -> 32 / 84 -> 88, each with
  decomposition (base: 31/86 against 29/84 booked -- drift; mine: +1 candidate
  `N280` with six sites over three readings, +2 probes `938`/`944`, each face
  carrying its own probe beside it). `gabbro blindstellen`: `74 blind ·
  173 covered · 25 poison-only · 12 no cell`, decomposed cell by cell against
  base (75/171/26): `tagged × return (body)` poison-only -> covered (`120`),
  `tagged × static` BLIND -> covered (`121`). TODO rebooked to 173/25.
- Stay red, red at base too: `pruefe-todo.py` aborts in its own speech test
  (README patterns, byte-identical at base); `pruefe-zahlen.py` keeps
  `Absagekennungen` 376 vs 383 (base actual 378 vs 371 booked -- 7 codes other
  lanes added without booking; mine is exactly 371+5, all with sentences),
  plus the README/ZEREMONIE/RUECKLAUFWERTE drift the lane never touched.
  PASSREGISTER figures stand unrecomputed except the lane's own +1/+5 entry;
  the ohne-Satz ratchet (55) is green.

## 5. Open / cuts

- **A bare case bound in one `match` arm and read bare in another** is typed
  as the case by the checker while the emitter withholds the literal -- loud
  through `cc` (undeclared identifier), booked in the sentence, not closed
  (same class as the lane-152 `match`-binder atomic note).
- **`match` over a constructed, non-place scrutinee** (`match Kurz(x) {…}`)
  stays the emitter's `C001` (checker-green, `D005`-silent); `marken_quelle`
  already names the shape for declared-return calls.
- **What the C correspondence still needs** (the later task, concretely): the
  lemma `fall` ↔ compound-literal/brace-init over the SAME union discipline
  `D005` argues informally (write `.last.V`, read `.last.V` behind `.marke =
  T_V`); the payload width/range half (what `M101` holds vs. the C type); the
  `N283`/`N284`/ambiguous backstops (accepted trees never reach them -- the
  proof may assume the checker). No `.lean` work: `fall`/`onTag` already
  exist; only the Rust-side export grew (bare nullary).
- **Registers left red, all red at base:** `pruefe-todo.py` (speech-test
  abort over README patterns); `pruefe-zahlen.py` items this lane never
  touched (RUECKLAUFWERTE, README ceremony/instrument counts, PASSREGISTER
  sentence figures, the deutsch booking at 7892 vs 7941 actual); the
  `Absagekennungen` 376-vs-383 gap whose 7 are other lanes' unbooked codes
  (base actual 378 vs 371 booked -- verified by diffing the issued sets, the
  only delta of this lane is exactly its five); `beispiele/` 103 files vs 99
  booked and `gift/` 656 vs 648 (base gaps 101/97 and 652/644 -- other lanes'
  files, unbooked, not certified here).
- `pruefe-vergabe.py` will keep listing `N280` (six sites, three readings,
  similarity 0.25) -- one resolution rule with three ways of failing, like
  `R009`'s four; each face carries its own probe, so a broken face takes its
  own witness red.

## 6. Where the task (or the tree) is wrong

- **"Payload out of range" needs no new code, and that is the finding.** The
  arity is the constructor's (`N281`/`N282`), but an out-of-range payload is a
  range refusal at an ordinary binding -- `M101`, pinned by 945 with no
  constructor rule beside it. All five reserved codes are still spent
  (`N283`/`N284` by unit rows, which is where they belong: no corpus site
  writes those shapes yet).
- **The static initialiser was listed as a falling position but scoped out by
  "in bodies" -- it is built anyway.** The brace form is the same designators
  with different punctuation, and leaving checker-green/emitter-`C001` standing
  next to a lane that owns the representation would have been a second
  register over one thing. `121` pins it.
- **`H021` as the constructor refusal was load-bearing by accident** (lane 152
  §7 flagged exactly this): had the call graph ever learned variant edges,
  the refusal would have evaporated and generic call text would have escaped
  to `cc`. This lane builds the dedicated rule lane 152 asked for -- and
  keeps `H021` firing beside `N280` on the truly unknown, so no existing pin
  goes quiet.
