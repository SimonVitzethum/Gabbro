module

public import Grammatik.Parser.Stmt.Anweisung
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Stmt.AnweisungProben.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

-- beispiele/02-geraet.gab:129. The phase step as a statement --
-- `parse.rs` has no statement-level counterpart either (it rides
-- in the checker); the shape is the SYNTAX.md `advstmt`
-- production.
def st32 : List Token :=
  [.wort "let", .ident "a", .zeichen "=", .wort "alloc",
   .ident "Log", .zeichen "(", .num 10, .zeichen ")",
   .zeichen ";", .ende]
theorem s32_lex :
    lex "let a = alloc Log (10);" = .ok st32 := by
  decide
theorem s32 : beqTopStmt (parseTopStmt st32)
    (.ok (.alloc false "a" .none "Log" (.lit 10) .none)) = true := by
  decide
-- beispiele/98-arena-erklaert.gab:11. Rust: `Alloc` with no
-- `else` -- same shape.
def st33 : List Token :=
  [.wort "let", .ident "c", .zeichen "=", .wort "alloc",
   .ident "Log", .zeichen "(", .ident "a", .zeichen "+",
   .ident "b", .zeichen ")", .wort "else", .zeichen "{",
   .wort "return", .num 0, .zeichen ";", .zeichen "}",
   .zeichen ";", .ende]
theorem s33_lex :
    lex "let c = alloc Log (a + b) else { return 0; };" =
      .ok st33 := by
  decide
theorem s33 : beqTopStmt (parseTopStmt st33)
    (.ok (.alloc false "c" .none "Log"
      (.bin "+" (.variable "a") (.variable "b"))
      (.some (.block [] (.some (.ret (.some (.lit 0)))))))) = true := by
  decide
-- beispiele/98-arena-erklaert.gab:13 (shortened). Rust: `Alloc`
-- with the full-arena continuation -- same shape (the `else`
-- takes a plain block here, unlike `let … else`).
def st34 : List Token :=
  [.wort "reset", .ident "Log", .zeichen ";", .ende]
theorem s34_lex :
    lex "reset Log;" = .ok st34 := by
  decide
theorem s34 : beqTopStmt (parseTopStmt st34)
    (.ok (.reset "Log" .none)) = true := by
  decide
-- beispiele/98-arena-erklaert.gab:16. Rust: `ResetArena` --
-- same shape.
def st35 : List Token :=
  [.zeichen "@", .ident "spirv", .zeichen "#", .wort "kernel",
   .zeichen "(", .ident "n", .zeichen ")", .zeichen "{",
   .wort "dispatch", .num 0, .zeichen "}", .zeichen ";",
   .ende]
theorem s35_lex :
    lex "@spirv#kernel(n) { dispatch 0 };" = .ok st35 := by
  decide
theorem s35 : beqTopStmt (parseTopStmt st35)
    (.ok (.lcall "spirv" "kernel" 1)) = true := by
  decide
-- SYNTAX.md §7 (the library-call example). Rust: `LibraryCall`
-- in statement position -- same shape (one argument, region
-- skipped balanced).

end Gabbro.Grammatik.Parser

/-
  CUTS: what is not proved here.

  * The tree shapes above are checked by kernel `Bool` evaluation
    (`beqTopStmt`/`beqTopItems … = true`), not by a soundness
    theorem for `beqSAnw` -- the same cut as item 11 of the CUTS
    block in `Parser/Ausdruck.lean`.
  * Every shape difference against `crates/gabbro-syntax` found by
    these probes is booked in the CUTS blocks of
    `Parser/Anweisung.lean` and `Parser/Element.lean`; the probe
    comments name the Rust counterpart (`ast.rs`) of each form.
  * `{ }` bodies stand for the corpus block at the cited site: the
    probe pins the head dispatch and the empty-body shape, not the
    full corpus block. The one full block is `f01`.
  * Synthetic probes (no corpus occurrence, measured 2026-09-13):
    `s12` (`else if`), `s24` (`next`), `s30` (`stateassign`),
    (the item probes live in `ElementTiefProben1..7`). The `s31` (`advances`) shape has no
    statement-level counterpart in `parse.rs` either (it rides in
    the checker); the probe pins the SYNTAX.md production.
-/

#print axioms Gabbro.Grammatik.Parser.s01
