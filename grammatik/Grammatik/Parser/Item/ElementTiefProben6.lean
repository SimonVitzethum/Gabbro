/-
  File:      Grammatik/Parser/Item/ElementTiefProben6.lean
  Subject:   T3 PART 3: the `decide` probes for the deep item
               readers, part 6 of 7 (tt56..tt58).

  The probes are split over seven modules only so that each one
  builds under the 4 GiB memory ceiling; part 6 carries the CUTS
  block for all seven.

  Like `Parser/AnweisungProben.lean`: one kernel evaluation per
  theorem keeps every worker small. Each probe is split in two: a
  lex pin (`tNN_lex`: the source line lexes to this token list)
  and a tree pin (`tNN`: the reader maps the list to this
  shape). A mistranscribed list fails its lex pin loudly. Tree
  shapes were compared against `ast.rs`/`parse.rs` by reading (no
  cargo in this lane); all differences are booked in the CUTS
  block of `Parser/ElementTief.lean`.
  Corpus sites stand at each probe; probes with no corpus line say
  so. The end-to-end probe is `tEnd` (beispiele/112, the smallest
  whole file with a table, a lock and contracted functions).
-/
import Grammatik.Parser.Item.ElementTief

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

def tt56 : List Token :=
  [.wort "const", .ident "T", .zeichen ":", .zeichen "[",
   .wort "u32", .zeichen ";", .num 2, .zeichen "]",
   .zeichen "=", .zeichen "[", .num 1, .zeichen ",", .num 2,
   .zeichen "]", .zeichen ";", .ende]
theorem t56_lex :
    lex "const T : [u32; 2] = [1, 2];" = .ok tt56 := by
  decide
theorem t56 : beqTopTief (parseTopTief tt56)
    (.ok [.constT "T" (.array (.atom "u32") (.lit 2))
      (.rows [.one (.lit 1), .one (.lit 2)])]) = true := by
  decide
-- beispiele/92-const-squares.gab:13 (shortened from 64
-- elements; the lane-111 const-table literal). Rust: `Konst`
-- over an array type with an `arraylit` value -- same shape.
def tt57 : List Token :=
  [.wort "pub", .wort "module", .ident "a", .zeichen "::",
   .ident "b", .zeichen "{", .wort "use", .ident "c",
   .zeichen "::", .ident "d", .zeichen ";", .zeichen "}",
   .ende]
theorem t57_lex :
    lex "pub module a::b { use c::d; }" = .ok tt57 := by
  decide
theorem t57 : beqTopTief (parseTopTief tt57)
    (.ok [.modT "a::b" [.useT ["c", "d"]]]) = true := by
  decide
-- Synthetic (no `pub module` in the corpus, measured
-- 2026-09-13): the `pub` prefix and nested members. Rust:
-- `Modul` with a `Use` member.
def tt58 : List Token :=
  [.wort "device", .ident "Ring", .zeichen "(", .ident "basis",
   .zeichen ":", .wort "u64", .zeichen ")", .wort "at",
   .wort "mmio", .zeichen "{", .wort "reg", .ident "AVAIL_IDX",
   .zeichen ":", .wort "u16", .wort "wrapping", .zeichen "@",
   .num 258, .wort "class", .wort "rw", .wort "reg",
   .ident "RING_LEN", .zeichen ":", .wort "u16", .zeichen "@",
   .num 260, .wort "class", .wort "r", .zeichen "}", .ende]
theorem t58_lex :
    lex "device Ring(basis : u64) at mmio { reg AVAIL_IDX : u16 wrapping @0x102 class rw reg RING_LEN : u16 @0x104 class r }" =
      .ok tt58 := by
  decide
theorem t58 : beqTopTief (parseTopTief tt58)
    (.ok [.devT "Ring" [("basis", (.atom "u64"))] "mmio" [.reg { name := "AVAIL_IDX", rtyp := (.wrap (.atom "u16")), addr := (.lit 258), klasse := "rw", stage := [], felder := [], voraus := .none, elseF := .none, abhaengt := [] }, .reg { name := "RING_LEN", rtyp := (.atom "u16"), addr := (.lit 260), klasse := "r", stage := [], felder := [], voraus := .none, elseF := .none, abhaengt := [] }]]) = true := by
  decide
-- beispiele/12-umlaufendes-register.gab (the `Ring` device).
-- Rust: `Device` with a `wrapping` register -- the width rides
-- the type (`wrap`), not the register.

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here.

  * The tree shapes above are checked by kernel `Bool` evaluation
    (`beqTopTief … = true`), not by a soundness theorem for
    `beqSItemTief` -- the same cut as item 11 of the CUTS block in
    `Parser/Ausdruck.lean`.
  * Every shape difference against `crates/gabbro-syntax` found by
    these probes is booked in the CUTS block of
    `Parser/ElementTief.lean`; the probe comments name the Rust
    counterpart (`ast.rs`) of each form.
  * Corpus text is quoted comment-free (comments lex away); the
    five shortened probes (`t40` two of ten boot steps, `t56`
    two of 64 array elements, `t34`/`t30` simplified invariant
    bodies, `t37` dropped quantified walk invariants) pin the
    surrounding shape, not the dropped text -- each says so.
  * Synthetic probes (no corpus occurrence, measured 2026-09-13):
    `t14` (`static … shared`), `t18` (bare-proto `deadline`
    carrier), `t23` (`state` item), `t54` (the clause-comb
    carrier), `t57` (`pub module`). The `t30`/`t34` invariant
    bodies are synthetic and quantifier-free; every corpus
    invariant quantifies (see CUTS item 1 of
    `Parser/ElementTief.lean`).
  * Heartbeat budgets: `t26_lex` runs at 800000 (default 200000
    fails), `tEndL_lex` at 1600000 -- the price of whole-item
    lexing through `String ==` over byte arrays (the same
   finder as lane 135 finding 6: tree comparisons run on
    character lists, source text does not). Since the 4 GiB
    ceiling `tEnd_lex` pins the 112 text as short character pieces
    (`srcEndL`, part 7) and reaches `lex` through `lex_ofList`; the
    single long literal no longer fits.
  * New single-line proof terms (`t42`, `t50`, `t51`, `t30`,
    `t34`, `t38`, `t41`, `t58`): hand-nested `SExpr` terms are
    balanced mechanically (a paren counter over the line) before
    probing -- two committed probes carried a slip each.
-/
