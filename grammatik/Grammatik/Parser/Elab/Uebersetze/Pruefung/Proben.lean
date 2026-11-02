/- C16: probes for check elaboration -- every refusal and the retained record.

   The decider runs by kernel evaluation (`rfl`): a resolved measure, an unknown
   gate, a duplicate name, the exact elaborated record of a well-formed check with
   its generated producer name, and the elaborated unit carrying the probe. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
public import Grammatik.Parser.Elab.Uebersetze.Teil13

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- The probe fixture: a check over one variable, one gate, one true floor. -/
def probenCheck : SCheck :=
  { cname := "p", claim := "c", misst := [.variable "x"], gates := ["g"],
    canFail := .block [] (some (.ret (some .tru))), boden := [.tru], sonde := none }

/-- The generated producer is named after its check. -/
example : probeFnName "p" = "p#probe" := rfl

/-- A variable resolves to itself. -/
example : uMessOrt (.variable "x") = .ok (.variable "x") := rfl

/-- A literal is no measured place. -/
example : uMessOrt (.lit 3) = .error "measure without G form" := rfl

/-- A well-formed check elaborates to its exact record, naming its probe. -/
example : uCheck [] [] ["g"] ["p"] probenCheck =
    .ok { name := "p", claim := "c", misst := [.variable "x"], tore := ["g"],
          boeden := [.tru], sonde := none, probe := "p#probe" } := rfl

/-- A gate that names neither a function nor a sibling check is refused. -/
example : uCheck [] [] [] ["p"] { probenCheck with gates := ["h"] } =
    .error "unknown gate: h" := rfl

/-- A duplicate check name is refused, never merged. -/
def probenFn : SItemTief :=
  .fnT { art := "impl", name := "g", params := [], res := none, fehler := none,
    klauseln := [] } (.block [] none)

example : uChecks [] [] [probenFn, .checkT probenCheck, .checkT probenCheck] =
    .error "duplicate check: p" := rfl

/-- The probe elaborates to one function under the generated name. -/
example : (uProbeFns [] [] [] [] [] [] [] [] [] [] [] [] [] [] 0 ["g"] [probenCheck]).map (List.map (·.name)) =
    .ok ["p#probe"] := rfl

/-- A generated name that meets a written function is refused, never merged. -/
example : uProbeFns [] [] [] [] [] [] [] [] [] [] [] [] [] [] 0 ["p#probe"] [probenCheck] =
    .error "duplicate probe: p#probe" := rfl

/-- A non-block body has no probe form. -/
example : uProbeFn [] [] [] [] [] [] [] [] [] [] [] [] [] [] 0 { probenCheck with canFail := .ret (some .tru) } =
    .error "check body without G form" := rfl

/-- A unit with a check elaborates, carrying its generated probe. -/
example : (elabU [probenFn, .checkT probenCheck]).isOk = true := rfl

example : (elabU [probenFn, .checkT probenCheck]).map (fun u => u.fns.length) = .ok 2 := rfl

example : (elabU [probenFn, .checkT probenCheck]).map (fun u => u.checks.map (·.probe)) =
    .ok ["p#probe"] := rfl

end Gabbro.Grammatik.Parser.Uebersetze
