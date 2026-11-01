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
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
