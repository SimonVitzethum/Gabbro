module
public import Grammatik.Parser.Namen.AufloesungProben
-- Reuse the existing dependent lowering assembly, including its private certificates.
import all Grammatik.Parser.Namen.AufloesungProben
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
open Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-- WITNESS: `module a { pub static mut C; pub fn f() effects { writes C } }` -- the hull is closed. -/
def zu : List SItemTief :=
  [.modT "a" [.pubT c, .pubT (schreib "f" [.variable "C"] [.variable "C"])]]
theorem zu_huelle : huelleZu zu = true := by decide +kernel

-- Bind the whole actual elaboration before introducing its dependent function
-- index. The fields are certificates of the real producer, not an output snapshot.
private theorem zu_phases : ∃ unit : UProg,
    elabU (pre108 zu) = .ok unit ∧ unit.invs = [] ∧ contractGate unit = true ∧
    ∀ f : Fin unit.fns.length,
      (lowerFnAt unit f).toOption.isSome = true ∧ (fnAt unit f).decreases = none := by
  refine ⟨?unit, ?elaborated, ?invariants, ?contracts, ?functions⟩
  case elaborated => cbv <;> exact Eq.refl _
  case invariants => cbv
  case contracts => cbv
  case functions =>
    intro f
    rcases f with ⟨index, bound⟩
    have small : index < 1 := bound
    have zero : index = 0 := by omega
    subst index
    constructor <;> cbv

theorem zu_ok : stufe zu = "OK" := by
  rcases zu_phases with ⟨unit, elaborated, invariants, contracts, functions⟩
  exact AufloesungProben.stufe_certified (items := zu) (u := unit)
    elaborated invariants (fun f => (functions f).1) contracts
    (fun f => (functions f).2)
    (AufloesungProben.absent_measures unit (fun f => (functions f).2))

/-- PLANTED DEFECT: the exported `f` writes a carrier that does not cross. -/
def offen : List SItemTief :=
  [.modT "a" [c, .pubT (schreib "f" [.variable "C"] [.variable "C"])]]
theorem offen_huelle : huelleZu offen = false := by decide +kernel

private theorem offen_preprocessed : pre108 offen = [.useT ["pub"]] := by
  have ordinary : Modules.syntaxList offen = false := by decide +kernel
  simp only [pre108, ordinary, offen_huelle, Bool.false_eq_true, reduceIte]

-- Preserve the canonical refusal of the preprocessing sentinel independently of
-- source hull computation and of the successful unit's dependent lowering.
private theorem pub_sentinel_refused :
    elabU [.useT ["pub"]] = .error "item without G form" := by cbv

theorem offen_refused : stufe offen = "elab: item without G form" := by
  unfold stufe
  rw [offen_preprocessed, pub_sentinel_refused]
  rfl

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
