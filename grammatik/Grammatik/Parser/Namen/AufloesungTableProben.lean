module
public import Grammatik.Parser.Elab.UebersetzeAllg3
import Grammatik.Parser.Elab.UebersetzePipeline
-- Kernel probes need the bodies of the phase's floor, check, wrapper and static gates.
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
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

/-! Qualified table effect places: parser shape, canonical names, elaboration and export hull.
    These probes use tokens and surface trees, without lexing source strings in the kernel. -/
namespace Gabbro.Grammatik.Parser.AufloesungTableProben

open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-- A table with four bounded integer slots, also used twice to require full carrier keys. -/
def tableSlots (name : String) : SItemTief :=
  .tableT name none (some (.lit 4)) none none false
    [.tSlot [{ fname := "v", ftyp := .range (.atom "u32") (.lit 0) (.lit 9) false,
               pos := none, bezug := none, wo := none, reserviert := false, byOps := false }]]

/-- Both effect arms name the same table place. -/
def tableEffects (path : String) : List SEffekt :=
  [.reads (.field (.variable path) "slots"), .writes (.field (.variable path) "slots")]

/-- An effect-list tail with the path still split into source tokens. -/
def tableEffectTokens (path : List Token) : List Token :=
  [.wort "reads"] ++ path ++ [.zeichen ".", .wort "slots", .zeichen ",", .wort "writes"] ++
    path ++ [.zeichen ".", .wort "slots", .zeichen "}"]

theorem qualified_table_effects_parsed :
    (match parseEffektListe 100 (tableEffectTokens [.ident "b", .zeichen "::", .ident "T"]) with
     | .ok (effects, [.zeichen "}"]) => beqSEffektList effects (tableEffects "b::T")
     | _ => false) = true := by decide +kernel

theorem deep_table_effects_parsed :
    (match parseEffektListe 100
        (tableEffectTokens [.wort "x", .zeichen "::", .ident "y", .zeichen "::", .ident "T"]) with
     | .ok (effects, [.zeichen "}"]) => beqSEffektList effects (tableEffects "x::y::T")
     | _ => false) = true := by decide +kernel

theorem unqualified_table_effects_parsed :
    (match parseEffektListe 100 (tableEffectTokens [.ident "T"]) with
     | .ok (effects, [.zeichen "}"]) => beqSEffektList effects (tableEffects "T")
     | _ => false) = true := by decide +kernel

/-- The writer's effects and assignment use its own module's unqualified table name. -/
def tableWriter (table : String) : SItemTief :=
  .fnT { art := "impl", name := "set", params := [], res := none, fehler := none,
         klauseln := [.effs (tableEffects table), .cost (.lit 20)] }
    (.block [.set (.field (.index (.field (.variable table) "slots") (.lit 2)) "v") "=" (.lit 9)] none)

/-- The foreign caller supplies its own write right, independently of the callee's right. -/
def tableCaller (table : String) (callee : String := "b::set") : SItemTief :=
  .fnT { art := "impl", name := "main", params := [], res := none, fehler := none,
         klauseln := [.effs (tableEffects table), .cost (.lit 40)] }
    (.block [.call callee []] none)

/-- Two modules both declare `T`; `a::main` calls `b::set` and claims the table in `b`. -/
def tableUnit (path : String) : List SItemTief :=
  [.modT "b" [tableSlots "T", tableWriter "T"],
   .modT "a" [tableSlots "T", tableCaller path]]

theorem qualified_table_resolved :
    beqTopTief (.ok (Aufloesung.loese (tableUnit "b::T")))
      (.ok [tableSlots "b::T", tableWriter "b::T", tableSlots "a::T", tableCaller "b::T" "set"]) =
        true := by decide +kernel

/-- The real table lookup and both function write sets use exactly `b::T`, not `a::T`. -/
theorem qualified_table_elaborated :
    (match elabU (pre108 (tableUnit "b::T")) with
     | .ok unit => (unit.tabs.map (·.name), unit.fns.map (·.puts))
     | .error _ => ([], [])) = (["b::T", "a::T"], [["b::T"], ["b::T"]]) := by cbv

theorem unknown_table_path_refused :
    beqElabU (elabU (pre108 (tableUnit "missing::T")))
      (.error "name unknown: ?missing::T") = true := by decide +kernel

/-- A single module retains the pre-existing short table key and unqualified effects. -/
theorem unqualified_table_elaborated :
    (match elabU (pre108 [.modT "b" [tableSlots "T", tableWriter "T"]]) with
     | .ok unit => (unit.tabs.map (·.name), unit.fns.map (·.puts))
     | .error _ => ([], [])) = (["T"], [["T"]]) := by cbv

theorem qualified_table_private_hull_refused :
    Oeffentlich.huelleZu
      [.modT "b" [tableSlots "T", tableWriter "T"], .modT "a" [.pubT (tableCaller "b::T")]] =
        false := by decide +kernel

theorem qualified_table_public_hull_closed :
    Oeffentlich.huelleZu
      [.modT "b" [.pubT (tableSlots "T"), tableWriter "T"], .modT "a" [.pubT (tableCaller "b::T")]] =
        true := by decide +kernel

end Gabbro.Grammatik.Parser.AufloesungTableProben
