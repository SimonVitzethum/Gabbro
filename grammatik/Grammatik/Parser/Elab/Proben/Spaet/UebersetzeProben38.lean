/-
  File:      Grammatik/Parser/Elab/Proben/Spaet/UebersetzeProben38.lean
  Subject:   Track P, every model form readable (Simon, 2026-10-21): `-3` is the literal `-3` (`USide.lit (-3)`),
             `-(3)` the negation of the literal `3` (`USide.neg`): one tree each. The probes run the parser on tokens
             and the value reader on the trees (a whole-unit elaboration does not fit the 4 GiB build limit).
-/
import Grammatik.Parser.Elab.Proben.Fruehe.UebersetzeProben3

namespace Gabbro.Grammatik.Parser.UebersetzeProben38

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- `-3` parses to the minus over the numeral. -/
theorem neg_literal_baum : (match parseUnary 10 [.zeichen "-", .num 3, .ende] with
    | .ok (.un "-" (.lit 3), [.ende]) => true
    | _ => false) = true := by decide

/-- Twin: `-(3)` parses to the negation of the numeral. -/
theorem neg_klammer_baum : (match parseUnary 10 [.zeichen "-", .zeichen "(", .num 3, .zeichen ")", .ende] with
    | .ok (.un "-()" (.lit 3), [.ende]) => true
    | _ => false) = true := by decide

/-- `-(a + b)` is a negation too (the operand is no numeral). -/
theorem neg_summe_baum : (match parseUnary 20
    [.zeichen "-", .zeichen "(", .num 1, .zeichen "+", .num 2, .zeichen ")", .ende] with
    | .ok (.un "-" (.bin "+" (.lit 1) (.lit 2)), [.ende]) => true
    | _ => false) = true := by decide

/-- A context without names. -/
def leer : UCtx := { names := [], kinds := [], types := [], tabs := [], locks := [], held := [], res := none, fname := "f", alias := [], lits := [] }

/-- `-3` reads as the literal `-3`. -/
theorem neg_literal_wert : (match uWertBody leer (.un "-" (.lit 3)) with
    | .ok v => v == .lit (-3)
    | .error _ => false) = true := by decide

/-- Twin: `-(3)` reads as the negation of `3`. -/
theorem neg_klammer_wert : (match uWertBody leer (.un "-()" (.lit 3)) with
    | .ok v => v == .neg (.lit 3)
    | .error _ => false) = true := by decide

end Gabbro.Grammatik.Parser.UebersetzeProben38
