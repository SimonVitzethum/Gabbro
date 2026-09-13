# MUSE-REPORT-154 — T3 part 2: Lean statement/item parser + probes

Lane 154, branch `muse/154`. Task: statements/blocks (SYNTAX.md §7)
and items (§1) on top of lane 135's lexer/expression parser, with
probes on real corpus lines, every §7/`item` form parsed or CUTS-listed,
one complete small corpus function end to end.

## What was built

Three new files (imports appended at the end of
`grammatik/Grammatik.lean`):

- **`grammatik/Grammatik/Parser/Anweisung.lean`** (901 lines) —
  surface tree `SAnw` (27 constructors: `lass`, `lassElse`,
  `lassLib`, `zuweis`, `uebergang`, `ruf`, `libruf`, `wenn`,
  `sonstWenn`, `matchS`, `arm`, `traverseS`, `retryS`, `foreverS`,
  `bricht`, `narrowS`, `sperrt`, `beobachtet`, `verlasse`,
  `weiter`, `publiziert`, `erwartet`, `tauscht`, `schreitet`,
  `rueck`, `allocS`, `resetS`, `sonst`, `block`) plus plain
  `SEnde` (`ret`/`fort`/`naechst`); shape equality `beqSAnw`,
  `beqSAnwList`, `beqOptAnw`, `beqSEnde`, `beqOptEnde`,
  `beqOptExpr`, `beqOptWort`, `beqWorte`; token helpers
  (`nimmWort`, `fordereZeichen`, `nimmName`, `istWort`,
  `istOrtsFort`, `istKopfForm`, `zeigeTok`, `nimmBisWort`,
  `nimmBisZeichen`, `nimmBereich`, `nimmBereichWorte`,
  `schleifenKopf`, `schliesseBlock`); fuel-indexed readers
  `parseStmt`, `parseLet`, `parseLetLib`, `parseLetAlloc`,
  `parseLetExpr`, `parsePlatzStmt`, `parseKopfStmt`, `parseLibRuf`,
  `parseLibStmt`, `parseWenn`, `parseElseIfs`, `parseMatchS`,
  `parseArme`, `parseSchleife`, `parseBricht`, `nimmIdentList`,
  `parseNarrow`, `parseSperrt`, `parseBeobachtet`,
  `parseVerlasse`, `parseWeiter`, `parseRueck`, `parseReset`,
  `parseUebergang`, `parseSchreitet`, `parseBlock`, `parseStmts`,
  `parseTopStmt`, `parseTopBlock`, `beqTopStmt`, `beqTopBlock`.
- **`grammatik/Grammatik/Parser/Element.lean`** (377 lines) —
  surface type `SItem` (30 constructors covering all 31
  `ItemArt` arms: `Profil`/`ProfilBedarf` share `profilS`);
  `beqSItem`, `beqSItemList`; `nimmBisStop`, `istMod`,
  `ueberspringe`, `fnStart`; fuel-indexed `parseItems`,
  `parseItem`, `parseItemKopf`, `parseRoh`, `parseEinfach`,
  `parseProfil`, `parseModul`, `parseFnName`, `parseTranslator`,
  `parseFnMit`, `parseTopItems`, `beqTopItems`.
- **`grammatik/Grammatik/Parser/AnweisungProben.lean`** (986
  lines) — 67 probes, each split lex-pin/tree-pin as in part 1:
  `s01`–`s35` (every §7 statement form), `e01`–`e31` (every
  `item` form), `f01` (end-to-end `uebernehmen` from
  beispiele/15, 66 tokens: header stepped over, 1 assignment +
  `return` ender). Each probe cites its corpus site and its
  `ast.rs` counterpart; `{ }` bodies stand for the corpus block
  where noted.

Every §7 form and every `item` form is either parsed with a
probe or named: synthetic probes (zero corpus occurrences,
measured 2026-09-13) are `s12` (`else if`), `s24` (`next`),
`s30` (`stateassign`), `e12` (`state` item); `s31`
(`advances`) has no statement-level `parse.rs` counterpart
either. `Lexer.lean`/`Ausdruck.lean` were NOT edited.

## Verification

Last `./lean-bau` result line: `== 0 error line(s) in the
COMPLETE output` (exit 0). `./lean-probe` on each of the three
files: exit 0. `#print axioms` on the mains: only `[propext,
Classical.choice, Quot.sound]`. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`. No theorem quantifies over program
syntax — all 134 probe theorems are ground `decide`s — so rule
13 needs no witnesses (there is no ZEUGE target and no
universal-over-syntax premise anywhere in the new files).

## Findings (measure, don't guess)

1. **Kernel `decide` does not reduce recursive `Bool` equality
   over a MUTUAL inductive family.** Even `beqSBlock (mk []
   none) (mk [] none)` gets stuck — not slow (2M heartbeats
   still stuck). A 5-function mutual `def` block compiles to the
   irreducible `PSum` fixed point (`#print` shows
   `@[irreducible] … _mutual`); the 2-function shape compiles to
   `brecOn` and reduces (part 1's `beqSExpr` precedent). Hence
   statements AND blocks live in the ONE type `SAnw`, `else if`
   branches ride as `sonstWenn` nodes, `match` arms as `arm`
   nodes, and the equality block stays three functions. Any new
   tuple-list field on `SAnw` re-opens this trap (CUTS 11).
2. **Lexer traps confirmed by eval, not by reading:**
   `TESTBUILD` lexes as `ident` (the `when` gate first read it
   as `wort` and fell); `r`/`slots`/`x`/`mut`/`u32` lex as
   `wort`; `narrow` targets start with numbers (`0 .. GRENZE`),
   not words. All fixed and pinned.
3. **Loop/fn headers contain `effects {…}` braces:** the header
   skippers (`schleifenKopf`, `fnStart`) step over exactly that
   group and treat any other `word {` adjacency as the body
   start. An anonymous `structty` in a signature would fool
   them; no corpus signature carries one (CUTS).
4. **`ueberspringe` stops laxly** (at `;`, `}` or end of input):
   brace-bodied items take no `;`, so the skipper cannot demand
   one — a missing `;` before `}`/EOF reads clean here and falls
   in `parse.rs` (CUTS).
5. **No `cargo` on this box**: `pruefe-zahlen.py`/`pruefe-todo.py`
   abort with `FileNotFoundError: 'cargo'` (pre-existing
   environment limit, same as SYNTAX.md §open-items notes for
   `pruefe-syntax.sh`). Untouched Rust, so nothing to verify
   there; `pruefe-englisch.py`/`pruefe-kennungen.py` pass.

## What I believe is wrong in the task

Nothing load-bearing. Two notes: (a) "comparing shapes against
parse.rs and ast.rs by reading" is the right method here — the
three refusal codes the reader knowingly differs on are
`P016` (let-else source), `P033` (lone `;`), `P041` (`pub`
placement), all booked in CUTS; (b) the single probe file holds
67 probes without OOM (part 1's kill came from definitions +
probes in one file; probes alone are fine) — no reviewer-split
needed this time.

## Open

Pred/contract/type readers (SYNTAX.md §§2, 5, 6 headers ride
raw); statement printer + round trip; `beqSAnw` soundness;
`count … : …` (needs `pred`); refusal codes; spans.
