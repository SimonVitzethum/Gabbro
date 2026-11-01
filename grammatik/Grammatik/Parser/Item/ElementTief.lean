/-
  File:      Grammatik/Parser/ElementTief.lean
  Subject:   T3 PART 3: Gabbro items in depth (SYNTAX.md sections 1-2,
               6, 9-14) over the Lean statement reader.

  The surface types `STyp`/`SEffekt`/`SKlausel`/`FnSig`/`SItemTief`
  with fuel-indexed readers (`parseItemTief`, `parseTopTief`).
  Probes live in `Parser/Item/ElementTiefProben1..7.lean`.
-/
module
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Item.ElementTief.Defs7

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here, and every shape difference against
  `crates/gabbro-syntax` found by the probes.

  *Every difference below was found by reading `ast.rs`/`parse.rs`
  (`cargo` cannot run in this lane); each is a documented gap, not a
  silent one. Against `parse.rs`, this reader accepts a SUPERSET in
  the rows marked [SUPERSET]: a program it accepts and `parse.rs`
  refuses is a soundness-side gap of this reader, never of the
  checker.*

  1. No `pred` reader (SYNTAX.md section 5): contract and invariant
     bodies ride `SExpr`, so `forall`/`exists`, `e in domain`,
     `reaches … via …`, `=>` and `Held(L, shared)` have no shape
     and are refused. Every corpus invariant quantifies
     (beispiele/01 `wurzel_ohne_vorgaenger`, `baum_bleibt_baum`;
     beispiele/17 `wartende_haben_grund`;
     beispiele/07 `wx_getrennt`; beispiele/50 `boot_ende`
     ensures); the probes pin the member shapes with
     quantifier-free bodies (t30, t34). `Held(L)` rides
     `ruf "Held" [l]` (shape-compatible); a two-argument
     `Held(L, shared)` would ride the same call shape unchecked.
  2. `structty`, `variants` and `fnptr` ride `roh`: balanced but
     uninterpreted (t09). A misspelled field type inside reads
     clean here and falls in `parse.rs`.
  3. The `by`, `retires` and `deadline` tails ride printed/raw
     strings (`induktion`, `quits`, `frist`), not split
     (t54). A misspelled word inside reads clean here.
  4. [SUPERSET] Trailing commas are allowed in every comma list
     this reader takes (`effects`, predicate lists, name lists,
     field lists, carrier/binding/path lists, error maps,
     reason cases, edges) and empty `effects {}` is allowed;
     `parse.rs` (`efflist`, `placelist`, `identlist`, all without
     trailing commas) refuses them. Reason case numbers ride
     general expressions (`parseOr`); `parse.rs` takes a `Zahl`
     only (`erwarte_zahl`). A repeated `exhaustive` is refused
     here (the first one closes the list) and skipped there
     (`continue`).
  5. The `fn`/`type` modifiers ride one `art` (the last) and one
     flag list; `pub` is dropped, never recorded (the same `P041`
     cut as item 4 of `Element.lean`). Whether `payload` stands
     on a `library fn` (`P043`), whether `effects` is present
     (`pure` by default is a refusal, not a default), and every
     other clause-presence rule (`N200`-`N204`, `P044`) are NOT
     held -- shapes only, no checks.
  6. `= asm {…}` rides raw and balanced (t17); the `in`/`out`/
     `clobbers` maps inside are not split.
  7. A `bank` body rides raw and balanced; registers inside are
     not split (t45).
  8. `use` paths ride split (`List String`); `SItem.useS` keeps
     them raw.
  9. `cost O(e)` takes the name `O` in either token shape: `O`
     is an identifier in both lexers (`kw.rs` has no `O`
     keyword), not a keyword (t30).
  10. `regdecl` takes no trailing `;` (grammar and corpus agree);
     the first cut wrongly demanded one (t03/t46).
  11. `check` takes bare `measures`/`gates` lists (no braces),
     exactly as `parse.rs` `placelist`/`identlist` read them
     (t26); the first cut wrongly demanded braces.
  12. Reason cases are whitespace-separated (commas allowed);
     the first cut took only commas or the closing brace (t22).
  13. A transition step splits at the top-level `->`
     (`nimmBisPfeil`): the place rides the restricted
     `shiftplace` shape and the `from` side is parsed alone,
     because a bare `parseOr` eats `a -> b` as an arrow field
     (t23/t46).
  14. `beqSItemTief`/`beqTopTief` are not proved sound or
     complete (same cut as item 8 of `Anweisung.lean`).
  15. `parseTopTief` is total but not complete: fuel
     `length * 8 + 32` suffices for every probe (each `decide`
     checks its own fuel); a huge input may report out-of-fuel
     instead of parsing.
  16. No printer, no round trip: items have no `druck`, so there
     is no `print_parse` for this level.
  17. Supported but sight-unseen (no corpus occurrence, reader
     present): table `owner`/`shared` flags, entry `ist`/`bounded`
    /`via` tails, `uN` widths in signatures, float ranges with
     `rounded`.
  18. equally unprobed: a `translator` with contracts, an `axiom`
     with `requires` or a result type, `accumulates` without
     `per cpu`, `walk` with invariants, `atomic` with
     `publishes nothing`, `group … ;` without a body.
-/

#print axioms Gabbro.Grammatik.Parser.parseTopTief
