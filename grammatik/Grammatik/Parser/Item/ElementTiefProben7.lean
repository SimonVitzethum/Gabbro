/-
  File:      Grammatik/Parser/Item/ElementTiefProben7.lean
  Subject:   T3 PART 3: the `decide` probes for the deep item
               readers, part 7 of 7 (the lex pin of ttEnd).

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
import Grammatik.Parser.Item.ElementTiefProben5

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-- The source of `beispiele/112` as short character pieces: one long
    literal costs the kernel its whole UTF-8 decode (see `lex_ofList`),
    which does not fit the 4 GiB ceiling; the pieces are the same text,
    character for character. -/
def srcEndL : List Char := List.flatten
  ["module beispiel112 { table Zustand count ".toList,
   "4 { slot { bereit : u32, } } lock Sperre ".toList,
   "protects { Zustand } rank 0; device ".toList,
   "Geraet(basis : u64) at mmio { reg ST : ".toList,
   "u32 @0x00 class r depends { Zustand } } ".toList,
   "impl fn lesen(d : Geraet) -> u32 ".toList,
   "requires Held(Sperre) effects { reads d ".toList,
   "} costs <= 8 ops { let stand = d.ST; ".toList,
   "return stand; } impl fn schreiben(i : ".toList,
   "index into Zustand, w : u32) -> u32 ".toList,
   "requires Held(Sperre) effects { writes ".toList,
   "Zustand } costs <= 8 ops { ".toList,
   "Zustand.slots[i].bereit = w; return 0; } ".toList,
   "}".toList]

set_option maxHeartbeats 1600000 in
theorem tEndL_lex : lexL srcEndL = .ok ttEnd := by
  decide +kernel

/-- The lex pin over the `String`: `lex_ofList` carries it across as a
    rewrite, so the decoder is never run. -/
theorem tEnd_lex : lex (String.ofList srcEndL) = .ok ttEnd := by
  rw [lex_ofList]
  exact tEndL_lex

end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.tEnd_lex
