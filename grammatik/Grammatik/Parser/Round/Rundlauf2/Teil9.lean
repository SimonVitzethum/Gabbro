module

public import Grammatik.Parser.Round.Rundlauf
public import Grammatik.Parser.Round.Rundlauf2.Teil8

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- Step B3 witnesses: a field chain and an index place.
theorem zeuge_kern_feld : parseOr (brennstoff (.field (.variable "x") "f"))
    (druckToks (.field (.variable "x") "f") ++ [.ende]) =
      .ok (.field (.variable "x") "f", [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_feld_rech : (match parseOr
    (brennstoff (.field (.variable "x") "f"))
    (druckToks (.field (.variable "x") "f") ++ [.ende]) with
    | .ok (.field (.variable "x") "f", [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_kern_index :
    parseOr (brennstoff (.index (.variable "x") (.lit 0)))
    (druckToks (.index (.variable "x") (.lit 0)) ++ [.ende]) =
      .ok (.index (.variable "x") (.lit 0), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_index_rech : (match parseOr
    (brennstoff (.index (.variable "x") (.lit 0)))
    (druckToks (.index (.variable "x") (.lit 0)) ++ [.ende]) with
    | .ok (.index (.variable "x") (.lit 0), [.ende]) => true
    | _ => false) = true := by
  decide

end Gabbro.Grammatik.Parser
