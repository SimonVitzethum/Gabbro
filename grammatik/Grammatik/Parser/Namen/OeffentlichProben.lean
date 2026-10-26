import Grammatik.Parser.Namen.AufloesungProben

/-!
  File:      Grammatik/Parser/Namen/OeffentlichProben.lean
  Subject:   Probes of `pub` (`Oeffentlich.lean`) through `pre108`, `elabU` and `lowerAllg`, on surface
             trees (no kernel lexing): a closed export hull passes, an exported function that writes a
             private carrier is refused, two carriers of one short name are told apart, a `pub` before a
             kind that cannot carry it is refused, and a unit without `pub` is unchanged.
-/

namespace Gabbro.Grammatik.Parser.OeffentlichProben

open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Oeffentlich Gabbro.Grammatik.Parser.Aufloesung
open Gabbro.Grammatik.Parser.AufloesungProben (stufe c schreib zwei)

set_option maxRecDepth 100000

/-- WITNESS: `module a { pub static mut C; pub fn f() effects { writes C } }` -- the hull is closed. -/
def zu : List SItemTief :=
  [.modT "a" [.pubT c, .pubT (schreib "f" [.variable "C"] [.variable "C"])]]
theorem zu_huelle : huelleZu zu = true := by decide +kernel
theorem zu_ok : stufe zu = "OK" := by decide +kernel

/-- PLANTED DEFECT: the exported `f` writes a carrier that does not cross. -/
def offen : List SItemTief :=
  [.modT "a" [c, .pubT (schreib "f" [.variable "C"] [.variable "C"])]]
theorem offen_huelle : huelleZu offen = false := by decide +kernel
theorem offen_refused : stufe offen = "elab: item without G form" := by decide +kernel

/-- PLANTED DEFECT: `a::C` crosses, `b::C` does not, and `b`'s exported `g` names its own `C`. The rule
    sees items, not texts: the public `a::C` of the same short name does not close `g`'s hull. -/
def namensgleich : List SItemTief :=
  [.modT "a" [.pubT c], .modT "b" [c, .pubT (schreib "g" [.variable "C"] [.variable "C"])]]
theorem namensgleich_huelle : huelleZu namensgleich = false := by decide +kernel

/-- PLANTED DEFECT: a `pub` before a `syscall` variable, a kind without visibility. -/
def falscheArt : List SItemTief := [.modT "a" [.pubT (.varT "V")]]
theorem falscheArt_huelle : huelleZu falscheArt = false := by decide +kernel

/-! ## Witnesses of the general theorems -/

theorem huelle_ohne_pub_zeuge : huelleZu zwei = true := huelle_ohne_pub (by decide +kernel)

/-- The second export of `zu` (the function `f`; the first is the carrier `C`). -/
theorem zwei_exporte : 1 < (exporteL [] zu).length := by decide +kernel

/-- `pub_sichtbar` on `zu`: the carrier `C` that the exported `f` writes is a public name. -/
theorem pub_sichtbar_zeuge : ["a", "C"] ∈ oeffentlich zu :=
  pub_sichtbar (e := (exporteL [] zu)[1]'zwei_exporte) zu_huelle (List.getElem_mem zwei_exporte)
    (n := "C") (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Gabbro.Grammatik.Parser.OeffentlichProben
