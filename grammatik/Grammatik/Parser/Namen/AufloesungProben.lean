import Grammatik.Parser.Elab.UebersetzeAllg3

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
theorem zwei_ok : stufe zwei = "OK" := by decide +kernel
theorem zwei_traeger : traeger zwei = ["a::C", "b::C"] := by decide +kernel
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
theorem tief_ok : stufe tief = "OK" := by decide +kernel
theorem tief_traeger : traeger tief = ["x::y::C", "b::C"] := by decide +kernel

/-- PLANTED DEFECT: a module that neither declares nor `use`s `C` names it bare. Two items carry the
    short name and neither is visible from `p`: the name is refused, not bound to either. -/
def unsichtbar : List SItemTief :=
  [.modT "a" [c], .modT "b" [c], .modT "p" [schreib "f" [.variable "C"] [.variable "C"]]]
theorem unsichtbar_refused : stufe unsichtbar = "elab: writes clause without G form" := by decide +kernel

/-- PLANTED DEFECT: the effect names `a::C`, the body writes its own module's `C`. The two names stay two
    carriers, so the footprint rule sees a body writing a carrier its effects do not name. -/
def falsch : List SItemTief :=
  [.modT "a" [c], .modT "b" [c, schreib "f" [.why "a" "C"] [.variable "C"]]]
theorem falsch_getrennt : wirkungUndRumpf (pre108 falsch) = [(["a::C"], ["b::C"])] := by decide +kernel


/-! ## Witnesses of the general theorems (`Aufloesung.lean`), each on a context whose premises hold -/

open Gabbro.Grammatik.Parser.Aufloesung

/-- Two items of the short name `C`, in `a` and `b`; seen from module `a`. -/
def kA : Kontext := ⟨⟨[["a", "C"], ["b", "C"]], []⟩, ["a"], []⟩

/-- The same unit seen from a module `p` that declares and uses nothing. -/
def kP : Kontext := ⟨⟨[["a", "C"], ["b", "C"]], []⟩, ["p"], []⟩

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
