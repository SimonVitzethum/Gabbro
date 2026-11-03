/-
  File:      Grammatik/Parser/Elab/Proben/Spaet/UebersetzeProben42.lean
  Subject:   Track P: Phase-1 desugaring (`ABSTRACTION-SYNTAX-PLAN.md` §4, steps 1a/1b).

  * `?` elaborates exactly like the explicit `else` form: `entzuckere` maps the
    `bindQ` node to the `bindElse` node with one re-raise arm per ground
    (`frage_ist_else`, definitional), the desugared unit elaborates
    (`frage_explizit_ok`), and the source with `?` runs the whole pipeline
    (`frage_ok_stufe`). A different channel keeps the written `else`: `?` is
    refused (`frage_falsch_kanal_stufe`).
  * An adapter `fn … from f` elaborates exactly like the ordinary function it
    expands to (`adapt_ist_funktion`, definitional); the short `;` body returns
    the source answer (`adapt_kurz_stufe`).
-/
module
public import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3
public import Grammatik.Parser.Elab.Uebersetze
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
@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeProben42

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeProben3 (stufe)

set_option maxRecDepth 100000

/-! ### `?` elaborates like the explicit `else` form -/

/-- The sugared unit: `h` shares the channel `R` of `g` and propagates with `?`. -/
def frageQuelle : String :=
  "module m { reason R { A = 1 \"a\" exhaustive } impl fn g() -> u32 or R { return 1; } impl fn h() -> u32 or R { let y = g() ?; return y; } }"

/-- The whole pipeline accepts the `?` source (lex, parse, desugar, elaborate, lower). -/
theorem frage_ok_stufe : stufe frageQuelle = "OK" := by
  decide +kernel

/-- The sugared items, built by hand. -/
def frageSugared : List SItemTief :=
  [.whyT "R" [("A", .lit 1, "a")] true,
    .fnT { art := "impl", name := "g", params := [], res := some (.atom "u32"),
           fehler := some "R", klauseln := [] }
      (.block [] (some (.ret (some (.lit 1))))),
    .fnT { art := "impl", name := "h", params := [], res := some (.atom "u32"),
           fehler := some "R", klauseln := [] }
      (.block [.bindQ false "y" none (.call "g" [])] (some (.ret (some (.variable "y")))))]

/-- The explicit `else` form the plan demands for `?`. -/
def frageExplizit : List SItemTief :=
  [.whyT "R" [("A", .lit 1, "a")] true,
    .fnT { art := "impl", name := "g", params := [], res := some (.atom "u32"),
           fehler := some "R", klauseln := [] }
      (.block [] (some (.ret (some (.lit 1))))),
    .fnT { art := "impl", name := "h", params := [], res := some (.atom "u32"),
           fehler := some "R", klauseln := [] }
      (.block [.bindElse "y" none (.call "g" []) "#frage"
        (.block [.cases (.variable "#frage")
          [.arm "A" none (.block [] (some (.ret (some (.why "R" "A")))))]]
          (some (.ret (some (.why "R" "A")))))]
        (some (.ret (some (.variable "y")))))]

/-- The desugarer maps `?` to exactly the explicit `else` form (definitional). -/
theorem frage_ist_else : entzuckere frageSugared = .ok frageExplizit := rfl

/-- The explicit form elaborates. -/
theorem frage_explizit_ok : (elabU frageExplizit).isOk = true := by
  decide +kernel

/-- The desugared unit elaborates exactly like the written one: same functions. -/
theorem frage_gleiches_programm :
    (elabU frageSugared).map (fun u => u.fns.map (fun f => f.name)) =
      (elabU frageExplizit).map (fun u => u.fns.map (fun f => f.name)) := rfl

/-- Refused: `?` with a different channel than the callee keeps the written `else`. -/
def frageFalschKanal : String :=
  "module m { reason R { A = 1 \"a\" exhaustive } impl fn g() -> u32 or R { return 1; } impl fn h() -> u32 { let y = g() ?; return y; } }"

theorem frage_falsch_kanal_stufe :
    stufe frageFalschKanal = "elab: ? needs the same reason channel; write else" := by
  decide +kernel

/-! ### Adapters elaborate like the ordinary function -/

/-- The adapter source: `g` takes over `c`, binds `s` in the prelude, adds `k`. -/
def adaptQuelle : String :=
  "module m { impl fn f(c : u32, s : u32) -> u32 { return c; } impl fn g(.., -s, k : u32) -> u32 from f => a [ let s = 2; ] { return a; } }"

theorem adapt_ok_stufe : stufe adaptQuelle = "OK" := by
  decide +kernel

/-- The short body returns the source answer as it is. -/
def adaptKurz : String :=
  "module m { impl fn f(c : u32, s : u32) -> u32 { return c; } impl fn g(.., -s) -> u32 from f [ let s = 2; ]; }"

theorem adapt_kurz_stufe : stufe adaptKurz = "OK" := by
  decide +kernel

/-- The adapter items, built by hand. -/
def adaptSugared : List SItemTief :=
  [.fnT { art := "", name := "f", params := [("c", .atom "u32")], res := some (.atom "u32"),
          fehler := none, klauseln := [] }
      (.block [] (some (.ret (some (.variable "c"))))),
    .adaptT { art := "impl", name := "h", params := [], res := some (.atom "u32"),
              fehler := none, klauseln := [] }
      [.alle] { quelle := "f", gebunden := some "a", sonst := none, vorspiel := [] }
      (some (.block [] (some (.ret (some (.variable "a"))))))]

/-- The ordinary function the adapter expands to. -/
def adaptExplizit : List SItemTief :=
  [.fnT { art := "", name := "f", params := [("c", .atom "u32")], res := some (.atom "u32"),
          fehler := none, klauseln := [] }
      (.block [] (some (.ret (some (.variable "c"))))),
    .fnT { art := "impl", name := "h", params := [("c", .atom "u32")], res := some (.atom "u32"),
           fehler := none, klauseln := [] }
      (.block [.bind false "a" none (.call "f" [.variable "c"])]
        (some (.ret (some (.variable "a")))))]

/-- The desugarer maps the adapter to exactly the ordinary function (definitional). -/
theorem adapt_ist_funktion : entzuckere adaptSugared = .ok adaptExplizit := rfl

/-- The expanded function elaborates. -/
theorem adapt_explizit_ok : (elabU adaptExplizit).isOk = true := by
  decide +kernel

end Gabbro.Grammatik.Parser.UebersetzeProben42
