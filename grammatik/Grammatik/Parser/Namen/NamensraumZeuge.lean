import Grammatik.Parser.Namen.Namensraum
import Grammatik.Parser.Item.ElementTief

/-!
  File:      Grammatik/Parser/Namen/NamensraumZeuge.lean
  Subject:   Witnesses of the name-space rule: a library `lager` (modules `bestand` and `util`,
             only `bestand` public) linked as the copy `lager@2` into a program with a module
             `util` of its own; the library checked alone; and the `use` line as the parser reads it.
-/

namespace Gabbro.Grammatik.Parser.Namensraum.Zeuge

open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Namensraum

/-- The library: `bestand::Regal`, `bestand::fuelle`, a private `util::f`, and `use util::f;`
    inside `bestand`. -/
def lager : Quelle where
  namen := [["bestand", "Regal"], ["bestand", "fuelle"], ["util", "f"]]
  verwendet := [(["bestand"], ["util", "f"])]

/-- The library's public names. -/
def lagerPub : List Pfad := [["bestand", "Regal"], ["bestand", "fuelle"]]

/-- The program: a module `util` of its own, and `use lager::bestand::Regal;` at its root. -/
def app : Quelle where
  namen := [["util", "f"], ["main"]]
  verwendet := [([], ["lager", "bestand", "Regal"])]

/-- The library checked alone, as a program of its own. -/
def lagerAllein : Platz := ⟨none, []⟩

/-- The library linked: the copy `lager@2`. -/
def lagerLinked : Platz := ⟨some "lager@2", []⟩

/-- The program: its local dependency name `lager` means the copy `lager@2`. -/
def appPlatz : Platz := ⟨none, [("lager", "lager@2", lagerPub)]⟩

theorem gut_allein : lagerAllein.Gut := by unfold Platz.Gut lagerAllein; simp
theorem gut_linked : lagerLinked.Gut := by unfold Platz.Gut lagerLinked; simp
theorem gut_app : appPlatz.Gut := by unfold Platz.Gut appPlatz; simp

/-- The program reaches the library's public name through its `use` line. -/
theorem app_regal : aufloese app appPlatz [] ["Regal"] = some (some "lager@2", ["bestand", "Regal"]) := by
  decide

/-- The program's own `util::f` is its own, though the library has a `util::f` too. -/
theorem app_util : aufloese app appPlatz [] ["util", "f"] = some (none, ["util", "f"]) := by
  decide

/-- The library's private `util::f` is not visible to the program. -/
theorem app_privat : aufloese app appPlatz [] ["lager", "util", "f"] = none := by
  decide

/-- Inside the library, `f` in `bestand` resolves through its `use` line, alone and linked. -/
theorem lager_allein : aufloese lager lagerAllein ["bestand"] ["f"] = some (none, ["util", "f"]) := by
  decide

theorem lager_linked :
    aufloese lager lagerLinked ["bestand"] ["f"] = some (some "lager@2", ["util", "f"]) := by
  decide

/-- **The witness of `aufloeseK_platz`**: alone and linked, every path of the library means the same
    candidate; the two places differ in the copy. -/
theorem namensraum_zeuge (von p : Pfad) :
    aufloeseK lager lagerAllein von p = aufloeseK lager lagerLinked von p ∧
      lagerAllein.ns ≠ lagerLinked.ns :=
  ⟨aufloeseK_platz lager gut_allein gut_linked rfl von p, by decide⟩

/-- The two `util::f` of the unit are two names. -/
theorem zwei_util : (none, ["util", "f"]) ≠ ((some "lager@2", ["util", "f"]) : Name) := by decide

/-- The `use` line as the parser reads it: a path whose first segment is the dependency's local
    name; no new form of the grammar. -/
theorem use_gelesen : beqTopTief (parseTopTief
    [.wort "use", .ident "lager", .zeichen "::", .ident "bestand", .zeichen "::", .ident "Regal",
      .zeichen ";", .ende])
    (.ok [.useT ["lager", "bestand", "Regal"]]) = true := by
  decide

#print axioms namensraum_zeuge

end Gabbro.Grammatik.Parser.Namensraum.Zeuge
