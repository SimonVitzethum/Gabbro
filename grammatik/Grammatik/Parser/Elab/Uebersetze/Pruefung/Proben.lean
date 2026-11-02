/- C16: probes for check elaboration -- every refusal and the retained record.

   The decider runs by kernel evaluation (`rfl`): a resolved measure, an unknown
   gate, a duplicate name, the exact elaborated record of a well-formed check with
   its generated producer name and Duty, the elaborated unit carrying the probe,
   its gate wrapper and its mark table. -/
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

/-- The Duty is named after its check. -/
example : dutyName "p" = "p#duty" := rfl

/-- The wrapper is named after its check and its gate. -/
example : torHuellenName "p" "g" = "p#tor#g" := rfl

/-- A variable resolves to itself. -/
example : uMessOrt (.variable "x") = .ok (.variable "x") := rfl

/-- A literal is no measured place. -/
example : uMessOrt (.lit 3) = .error "measure without G form" := rfl

/-- A well-formed check elaborates to its exact record, naming its probe and its Duty. -/
example : uCheck [] [] ["g"] ["p"] probenCheck =
    .ok { name := "p", claim := "c", misst := [.variable "x"], tore := ["g"], boeden := [.tru], sonde := none, probe := "p#probe", duty := "p#duty" } := rfl

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

example : (elabU [probenFn, .checkT probenCheck]).map (fun u => u.fns.length) = .ok 3 := rfl

example : (elabU [probenFn, .checkT probenCheck]).map (fun u => u.checks.map (·.probe)) =
    .ok ["p#probe"] := rfl

/-- The wrapper travels with the probe. -/
example : (elabU [probenFn, .checkT probenCheck]).map (fun u => u.fns.map (·.name)) =
    .ok ["g", "p#probe", "p#tor#g"] := rfl

/-- The mark table carries the check's Duty. -/
example : (elabU [probenFn, .checkT probenCheck]).map (fun u => u.marken) = .ok ["p#duty"] := rfl

/-! ## The mark table and the gate wrappers, decided -/

/-- A plain gate for the wrapper probes. -/
def torGate : UFn := { name := "g", params := [], kinds := [], res := none, held := [], puts := [], gives := [], needs := [], body := [], ret := .empty }

/-- The mark table: linear types first, then the checks' Duties. -/
example : uMarken [.typeT ["linear"] "M" [] [] none] [{ name := "p", claim := "c", misst := [], tore := ["g"], boeden := [], sonde := none, duty := "p#duty" }] = ["M", "p#duty"] := rfl

/-- A declared mark is accepted. -/
example : uMarkenPruef ["p#duty"] [torGate] = .ok () := rfl

/-- An undeclared mark is refused. -/
example : uMarkenPruef [] [{ torGate with nimmt := ["m"] }] = .error "mark unknown: m" := rfl

/-- One gate derives its Duty-consuming wrapper, forwarding the empty result. -/
example : uTorHuelle "p#duty" [torGate] "p" "g" =
    .ok { name := "p#tor#g", params := [], kinds := [], res := none, held := [], puts := [], gputs := [], nimmt := ["p#duty"], gives := [], needs := [], body := [.call "g" []], ret := .empty } := rfl

/-- A gate with parameters keeps its named refusal. -/
def torGateParam : UFn := { name := "h", params := [("x", .int 0 10)], kinds := [.int], res := none, held := [], puts := [], gives := [], needs := [], body := [], ret := .empty }

/-- A gate with parameters derives no wrapper. -/
example : uTorHuelle "p#duty" [torGateParam] "p" "h" =
    .error "gate with parameters without wrapper form: h" := rfl

/-- A gate that names a sibling check waits for the test driver (C14). -/
example : uTorHuellen [torGate] [{ name := "p", claim := "c", misst := [], tore := ["q"], boeden := [], sonde := none, duty := "p#duty" }, { name := "q", claim := "c", misst := [], tore := [], boeden := [], sonde := none, duty := "q#duty" }] =
    .error "gate naming a check without driver form: q" := rfl

/-- A duplicated gate is refused, never merged. -/
example : uTorHuellen [torGate] [{ name := "p", claim := "c", misst := [], tore := ["g", "g"], boeden := [], sonde := none, duty := "p#duty" }] =
    .error "duplicate gate: g" := rfl

end Gabbro.Grammatik.Parser.Uebersetze
