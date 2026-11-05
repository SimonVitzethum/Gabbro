module
public import Grammatik.Parser.Elab.UebersetzeAllg3
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


/-!
  File:      Grammatik/Parser/Namen/AufloesungProben.lean
  Subject:   Probes of the qualified names (`Aufloesung.lean`) through `pre108`, `elabU` and `lowerAllg`:
             two modules declare a carrier of the same short name and stay two carriers; a place head may
             be a path of two or more segments; a name of an item that is not visible from the module is
             refused; an effect and a body that name two different carriers stay apart.

  The probes start from surface trees (and one token list for the parser), never from a source string:
  lexing a string in the kernel costs gigabytes (O13; measured 2026-10-25: 12.7 GB for four short
  sources).
-/

namespace Gabbro.Grammatik.Parser.AufloesungProben

open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-- The stage of the pipeline after the parser that stops a unit (`OK` when none does). -/
def stufe (items : List SItemTief) : String :=
  match elabU (pre108 items) with
  | .error e => "elab: " ++ e
  | .ok u =>
    match lowerAllg u with
    | .error e => "lower: " ++ e
    | .ok _ => "OK"

/-- Assemble the actual per-function successes through the existing list producer. -/
private theorem lowerEach_certified (u : Uebersetze.UProg) :
    ∀ fs : List (Fin u.fns.length),
      (∀ f ∈ fs, (lowerFnAt u f).toOption.isSome = true) → lowerEach u fs = .ok ()
  | [], _ => rfl
  | f :: fs, success => by
    rw [lowerEach, except_ok_get (success f (List.mem_cons_self ..))]
    exact lowerEach_certified u fs (fun g hg => success g (List.mem_cons_of_mem _ hg))

/-- Close the canonical assembler from its real phase certificates. Empty source measures
    have equal tuple lengths on every call edge, independently of the assembled program. -/
private theorem stufe_certified {items : List SItemTief} {u : Uebersetze.UProg}
    (elaborated : elabU (pre108 items) = .ok u) (noInvs : u.invs = [])
    (functions : ∀ f : Fin u.fns.length, (lowerFnAt u f).toOption.isSome = true)
    (contracts : contractGate u = true)
    (noMeasures : ∀ f : Fin u.fns.length, (fnAt u f).decreases = none)
    (measures : (Measures.lowerMeasures u).toOption.isSome = true) : stufe items = "OK" := by
  let exported : Measures.Export u := (Measures.lowerMeasures u).toOption.get measures
  have measured : Measures.lowerMeasures u = .ok exported := except_ok_get measures
  have empty : ∀ f, exported.mass f = [] :=
    fun f => Measures.lowerMeasures_absent u exported f (noMeasures f)
  have checked : ∀ P : Programm (declOf u),
      Measures.checkedProgram u P = .ok (P, List.finRange u.fns.length) := by
    intro P
    have lengths : Measures.cycleLengths u P exported.mass = true := by
      unfold Measures.cycleLengths
      apply List.all_eq_true.mpr
      intro f _
      apply List.all_eq_true.mpr
      intro g _
      rw [empty f, empty g]
      change (!zykS P (List.finRange u.fns.length) f g || true) = true
      exact Bool.or_true _
    unfold Measures.checkedProgram
    rw [measured, if_pos lengths]
  have invs : lowerInvs u (List.finRange u.invs.length) = .ok () := by
    cases enumeration : List.finRange u.invs.length with
    | nil => rfl
    | cons i rest =>
      have length : u.invs.length = 0 := congrArg List.length noInvs
      have bound := i.isLt
      omega
  have each := lowerEach_certified u (List.finRange u.fns.length) (fun f _ => functions f)
  unfold stufe
  rw [elaborated]
  unfold lowerAllg
  split
  · rename_i error failed
    rw [invs] at failed
    cases failed
  · split
    · rename_i error failed
      rw [each] at failed
      cases failed
    · split
      · rw [checked]
      · contradiction

/-- The carriers (`static` items) a unit elaborates to, by name. -/
def traeger (items : List SItemTief) : List String :=
  match elabU (pre108 items) with
  | .error _ => []
  | .ok u => u.globs.map (·.name)

/-- The written carriers of the effects and the assigned places of a function's body, per function. -/
def wirkungUndRumpf : List SItemTief → List (List String × List String)
  | [] => []
  | .fnT s (.block ss _) :: rest =>
    (s.klauseln.flatMap (fun
        | .effs es => es.filterMap (fun | .writes (.variable c) => some c | _ => none)
        | _ => []),
      ss.filterMap (fun | .set (.variable c) _ _ => some c | _ => none)) :: wirkungUndRumpf rest
  | _ :: rest => wirkungUndRumpf rest

/-- `static mut C : u8 = 0;` -/
def c : SItemTief := .globT true "C" (.atom "u8") (.one (.lit 0)) none none false

/-- A function without parameters that writes `w` (effects) and assigns `1` to each of `ziele`. -/
def schreib (n : String) (w : List SExpr) (ziele : List SExpr) (vorher : List SAnw := []) : SItemTief :=
  .fnT { art := "impl", name := n, params := [], res := none, fehler := none,
         klauseln := [.effs (w.map .writes), .cost (.lit 9)] }
    (.block (vorher ++ ziele.map fun z => .set z "=" (.lit 1)) none)

/-- WITNESS: two modules declare `C`; a third writes both, one through a `use`d function and one by its
    path (`module a { C; setze } module b { C } module p { use a::setze; haupt }`). -/
def zwei : List SItemTief :=
  [.modT "a" [c, schreib "setze" [.variable "C"] [.variable "C"]],
   .modT "b" [c],
   .modT "p" [.useT ["a", "setze"],
     schreib "haupt" [.why "a" "C", .why "b" "C"] [.why "b" "C"] [.call "setze" []]]]
private theorem zwei_elaborated : (elabU (pre108 zwei)).toOption.isSome = true := by cbv
private def zweiU : Uebersetze.UProg := (elabU (pre108 zwei)).toOption.get zwei_elaborated

private theorem zwei_functions (f : Fin zweiU.fns.length) :
    (lowerFnAt zweiU f).toOption.isSome = true ∧ (fnAt zweiU f).decreases = none := by
  have count : zweiU.fns.length = 2 := by cbv
  have bound : f.val < 2 := by rw [← count]; exact f.isLt
  rcases (by omega : f.val = 0 ∨ f.val = 1) with zero | one
  · have same : f = ⟨0, by omega⟩ := Fin.ext zero
    subst f
    constructor <;> cbv <;> rfl
  · have same : f = ⟨1, by omega⟩ := Fin.ext one
    subst f
    constructor <;> cbv <;> rfl

theorem zwei_ok : stufe zwei = "OK" :=
  stufe_certified (u := zweiU) (except_ok_get zwei_elaborated) (by cbv)
    (fun f => (zwei_functions f).1) (by cbv) (fun f => (zwei_functions f).2) (by cbv)
theorem zwei_traeger : traeger zwei = ["a::C", "b::C"] := by cbv
theorem zwei_wirkung :
    wirkungUndRumpf (pre108 zwei) = [(["a::C"], ["a::C"]), (["a::C", "b::C"], ["b::C"])] := by
  decide +kernel

/-- WITNESS: a path of three segments, as the parser reads it, is one place head. -/
def tiefToks : List Token :=
  [.wort "module", .ident "b", .zeichen "{", .wort "impl", .wort "fn", .ident "f", .zeichen "(",
   .zeichen ")", .wort "effects", .zeichen "{", .wort "writes", .wort "x", .zeichen "::", .ident "y",
   .zeichen "::", .ident "C", .zeichen "}", .wort "costs", .zeichen "<=", .num 9, .wort "ops",
   .zeichen "{", .wort "x", .zeichen "::", .ident "y", .zeichen "::", .ident "C", .zeichen "=", .num 1,
   .zeichen ";", .zeichen "}", .zeichen "}", .ende]
theorem tief_geparst :
    beqTopTief (parseTopTief tiefToks)
      (.ok [.modT "b" [schreib "f" [.variable "x::y::C"] [.variable "x::y::C"]]]) = true := by
  decide +kernel

/-- The unit around it: `module x { module y { C } } module b { C; f }`. -/
def tief : List SItemTief :=
  [.modT "x" [.modT "y" [c]],
   .modT "b" [c, schreib "f" [.variable "x::y::C"] [.variable "x::y::C"]]]
private theorem tief_elaborated : (elabU (pre108 tief)).toOption.isSome = true := by cbv
private def tiefU : Uebersetze.UProg := (elabU (pre108 tief)).toOption.get tief_elaborated

private theorem tief_functions (f : Fin tiefU.fns.length) :
    (lowerFnAt tiefU f).toOption.isSome = true ∧ (fnAt tiefU f).decreases = none := by
  have count : tiefU.fns.length = 1 := by cbv
  have bound : f.val < 1 := by rw [← count]; exact f.isLt
  have same : f = ⟨0, by omega⟩ := Fin.ext (by omega)
  subst f
  constructor <;> cbv <;> rfl

theorem tief_ok : stufe tief = "OK" :=
  stufe_certified (u := tiefU) (except_ok_get tief_elaborated) (by cbv)
    (fun f => (tief_functions f).1) (by cbv) (fun f => (tief_functions f).2) (by cbv)
theorem tief_traeger : traeger tief = ["x::y::C", "b::C"] := by cbv

/-- PLANTED DEFECT: a module that neither declares nor `use`s `C` names it bare. Two items carry the
    short name and neither is visible from `p`: the name is refused, not bound to either. -/
def unsichtbar : List SItemTief :=
  [.modT "a" [c], .modT "b" [c], .modT "p" [schreib "f" [.variable "C"] [.variable "C"]]]
theorem unsichtbar_refused : stufe unsichtbar = "elab: writes clause without G form" := by cbv

/-- PLANTED DEFECT: the effect names `a::C`, the body writes its own module's `C`. The two names stay two
    carriers, so the footprint rule sees a body writing a carrier its effects do not name. -/
def falsch : List SItemTief :=
  [.modT "a" [c], .modT "b" [c, schreib "f" [.why "a" "C"] [.variable "C"]]]
theorem falsch_getrennt : wirkungUndRumpf (pre108 falsch) = [(["a::C"], ["b::C"])] := by decide +kernel


/-! ## Witnesses of the general theorems (`Aufloesung.lean`), each on a context whose premises hold -/

open Gabbro.Grammatik.Parser.Aufloesung

/-- Two items of the short name `C`, in `a` and `b`; seen from module `a`. -/
def kA : Kontext := { q := ⟨[["a", "C"], ["b", "C"]], []⟩, von := ["a"], lok := [] }

/-- The same unit seen from a module `p` that declares and uses nothing. -/
def kP : Kontext := { q := ⟨[["a", "C"], ["b", "C"]], []⟩, von := ["p"], lok := [] }

theorem ref_lokal_zeuge : ({ kA with lok := ["C"] } : Kontext).ref "C" = "C" :=
  ref_lokal (by decide +kernel)

theorem ref_aufgeloest_zeuge : kA.ref "C" = "a::C" := by
  rw [ref_aufgeloest (c := ["a", "C"]) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem ref_unsichtbar_zeuge : kP.ref "C" = gift "C" :=
  ref_unsichtbar (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem schluessel_kurz_zeuge : schluessel [["a", "C"], ["b", "D"]] ["b", "D"] = "D" :=
  schluessel_kurz (by decide +kernel)

theorem loese_einfach_zeuge : loese [.modT "m" [c]] = Uebersetze.uMembers [.modT "m" [c]] :=
  loese_einfach (by decide +kernel)

theorem segmente_name_zeuge : segmente "C" = ["C"] := segmente_name (by decide +kernel)

theorem segmente_verbinde_zeuge : segmente ("::".intercalate ["a", "C"]) = ["a", "C"] :=
  segmente_verbinde (by decide) (by decide +kernel)

/-- The premises of `schluessel_injektiv` hold on two items of one short name, whose keys differ. -/
theorem schluessel_injektiv_zeuge :
    (∀ p ∈ [["a", "C"], ["b", "C"]], p ≠ [] ∧ ∀ s ∈ p, ':' ∉ s.toList) ∧
      schluessel [["a", "C"], ["b", "C"]] ["a", "C"] ≠ schluessel [["a", "C"], ["b", "C"]] ["b", "C"] := by
  decide +kernel

end Gabbro.Grammatik.Parser.AufloesungProben
