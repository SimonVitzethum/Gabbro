/- C16: probes for check elaboration -- every refusal and the retained record.

   The decider runs by kernel evaluation (`rfl`): a resolved measure, an unknown
   gate, a duplicate name, and the exact elaborated record of a well-formed check. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- The probe fixture: a check over one variable, one gate, one true floor. -/
def probenCheck : SCheck :=
  { cname := "p", claim := "c", misst := [.variable "x"], gates := ["g"],
    canFail := .ret (some .tru), boden := [.tru], sonde := none }

/-- A variable resolves to itself. -/
example : uMessOrt (.variable "x") = .ok (.variable "x") := rfl

/-- A literal is no measured place. -/
example : uMessOrt (.lit 3) = .error "measure without G form" := rfl

/-- A well-formed check elaborates to its exact record. -/
example : uCheck [] [] ["g"] ["p"] probenCheck =
    .ok { name := "p", claim := "c", misst := [.variable "x"], tore := ["g"],
          boeden := [.tru], sonde := none } := rfl

/-- A gate that names neither a function nor a sibling check is refused. -/
example : uCheck [] [] [] ["p"] { probenCheck with gates := ["h"] } =
    .error "unknown gate: h" := rfl

/-- A duplicate check name is refused, never merged. -/
def probenFn : SItemTief :=
  .fnT { art := "impl", name := "g", params := [], res := none, fehler := none,
    klauseln := [] } (.ret none)

example : uChecks [] [] [probenFn, .checkT probenCheck, .checkT probenCheck] =
    .error "duplicate check: p" := rfl

end Gabbro.Grammatik.Parser.Uebersetze
