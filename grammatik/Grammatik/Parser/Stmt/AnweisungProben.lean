/-
  File:      Grammatik/Parser/AnweisungProben.lean
  Subject:   T3 PART 2: the `decide` probes for the statement/item
              readers.

  Like `Parser/AusdruckProben.lean`: one kernel evaluation per
  theorem keeps every worker small. Each probe is split in two: a
  lex pin (`sNN_lex`/`eNN_lex`: the source line lexes to this token
  list) and a tree pin (`sNN`/`eNN`: the reader maps the list to
  this shape). A mistranscribed list fails its lex pin loudly. Tree
  shapes were compared against `ast.rs`/`parse.rs` by reading (no
  cargo in this lane); all differences are booked in the CUTS
  blocks of `Parser/Anweisung.lean` and `Parser/Element.lean`.
  Corpus sites stand at each probe; probes with no corpus line say
  so (`{ }` bodies stand for the corpus block at the cited site).
-/
module

public import Grammatik.Parser.Stmt.AnweisungProben.Teil1
public import Grammatik.Parser.Stmt.AnweisungProben.Teil2
