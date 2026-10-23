/-
  File:      Grammatik/Parser/Elab/Proben/Spaet/UebersetzeProben39.lean
  Subject:   Track P, the option test `o.is_some()` (`Expr.istSome`): the parser reads it as a call through the place
             `o.is_some` with no argument, and the truth-value reader takes that call to `UEns.istSome` over an option
             parameter and refuses it over a number. The probes run the parser on tokens and the reader on the trees
             (a whole-unit elaboration does not fit the 4 GiB build limit).
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben39

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- `o.is_some()` parses to the call through the place `o.is_some`. -/
theorem ist_some_baum : (match parseUnary 10
    [.ident "o", .zeichen ".", .ident "is_some", .zeichen "(", .zeichen ")", .ende] with
    | .ok (.ext .call [] [.field (.variable "o") "is_some"], [.ende]) => true
    | _ => false) = true := by decide

/-- A context with the option parameter `o` over table 0 and the number `k`. -/
def ctx : UCtx :=
  { names := ["o", "k"], kinds := [.opt 0, .int], types := [.opt 2, .int 0 9], tabs := [], locks := [], held := [],
    res := none, fname := "f", alias := [], lits := [] }

/-- `o.is_some()` over the option parameter is the option test. -/
theorem ist_some_wert : (match uBool ctx (.ext .call [] [.field (.variable "o") "is_some"]) with
    | .ok v => v == .istSome (.var "o") 0
    | .error _ => false) = true := by decide

/-- Twin: `!o.is_some()` is its negation. -/
theorem ist_some_nicht : (match uBool ctx (.un "!" (.ext .call [] [.field (.variable "o") "is_some"])) with
    | .ok v => v == .not (.istSome (.var "o") 0)
    | .error _ => false) = true := by decide

/-- Refused: `.is_some()` over a number. -/
theorem ist_some_zahl : (match uBool ctx (.ext .call [] [.field (.variable "k") "is_some"]) with
    | .ok _ => false
    | .error _ => true) = true := by decide

end Gabbro.Grammatik.Parser.UebersetzeProben39
