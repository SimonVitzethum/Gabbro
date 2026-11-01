module

public import Grammatik.Parser.Round.RundlaufQuant.Teil2
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil4

@[expose] public section


/-
  CUTS: what the statement round trip does not cover, and why.

  * `.other` (the reader never builds it) and a bare block in statement position (the reader has no
    such statement: `parseStmt` on `{` reads a place and fails).
  * A call through a `::` path or through a place (`a::f(x);`, `p->f(x);`): the printer prints the
    callee as text (`rohToks f`, `druck callee`); only a single name-shaped word re-lexes
    to one name token (`NameGut`). Paths would need the lexer over `a::f` without spaces.
  * Raw texts with braces, `;` or the collector's stop word inside (`publishes { a { b } }`, a
    `retry` header with an `effects { .. }` group, a `narrow` range with braces): the collectors track
    braces, but the class here is flat (`RohText` with the stop tokens excluded).
  * A `retry`/`forever` header that starts with a place continuation mark (`=`, `.`, `[`, ...):
    the dispatch would read the head word as a place.
  * Types: see `RundlaufTyp` (no `embeds`, raw groups, `entry fn`, rights lists).
  * Names print as `nameTok` (the lexer's token), so the TEXT level (`rundlauf_block_text`) needs
    only name-shaped names (`TokGut`). A name spelled like a word that opens a form where the name
    stands is outside the class: a `let` binder `mut`; a place head `transition` or a primary word
    (`true`, `false`, `Some`, `None`, `result`, `old`, `count`, `alloc`, and the refused heads of
    `istKeinPlatz`); a call statement head that is a statement word (`istAnwWort`, with `else`);
    the place of a plain `locks` headed `shared`. A variable `count` is excluded although the
    reader takes it unless `<name> in` follows (the `count` quantifier arm).
-/
