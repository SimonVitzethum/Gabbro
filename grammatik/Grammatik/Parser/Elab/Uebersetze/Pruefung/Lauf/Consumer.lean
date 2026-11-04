module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12

@[expose] public section

namespace Gabbro.Grammatik.Parser.Uebersetze

/-- A driver selects one gate of one check. This is image configuration, not
    an instruction to execute all gates listed in the source declaration. -/
structure CheckConsumerSelection where
  check : String
  gate : String
  deriving DecidableEq, Repr

def consumerFnName (cname gate : String) : String := cname ++ "#consume#" ++ gate

def driverFnName (cname gate : String) : String := cname ++ "#driver#" ++ gate

/-- Both returning channels of the consumer owe no Duty. A foreign error is
    rethrown with its exact reason, after explicit retirement; it is never
    converted into a successful gate result. -/
def consumerFehler (duty : String) (count : Nat) : List UStmt :=
  [.retireMark duty] ++ torFehler count

/-- The physical consumer: invoke the selected wrapper, then retire its one
    returning mark. The wrapper's argument/result/reason types are unchanged.
    `retireMark` lowers to the existing zero-effect `Stmt.retires` rule. -/
def uCheckConsumer (c : UCheck) (gate : String) (wrapper : UFn) : UFn :=
  let (invoke, answer) := torErgebnis wrapper.name wrapper
  { wrapper with
    name := consumerFnName c.name gate, nimmt := [c.duty], gibt := [],
    body := (if wrapper.gruende == 0 then invoke else
      [.bindOptElseBeg "ans" wrapper.name [] "e"] ++
        consumerFehler c.duty wrapper.gruende ++ [.blkEnd]) ++ [.retireMark c.duty],
    ret := answer, boden := none }

/-- One explicit invocation: observe the producer's Bool, transfer its Duty
    to the selected consumer, and return with no remaining mark. The initial
    mark is the existing non-forgeable invocation permit threaded by the
    producer; only its completed return gives the consumer a completed Duty.
    A second invocation requires a new permit. -/
def uCheckDriver (c : UCheck) (gate : String) (consumer : UFn) : UFn :=
  {
    name := driverFnName c.name gate, params := [], kinds := [], res := none,
    gruende := consumer.gruende, held := [], puts := consumer.puts,
    gputs := consumer.gputs, gives := [], nimmt := [c.duty], gibt := [],
    body := [.bindCall "verdict" c.probe []] ++
      (if consumer.gruende == 0 then [.call consumer.name []] else
        [.bindOptElseBeg "ans" consumer.name [] "e"] ++
          torFehler consumer.gruende ++ [.blkEnd]), ret := .empty }

/-- Derive a selected driver and its consumer only from this unit's actual
    check and wrapper. Unknown, unselected and duplicate consumers fail by
    name; source code cannot spell the generated private identities. -/
def uSelectCheckConsumer (u : UProg) (selection : CheckConsumerSelection) :
    Except String UProg := do
  let some c := u.checks.find? (fun c => strEq c.name selection.check)
    | .error ("selected check unknown: " ++ selection.check)
  if !c.tore.any (strEq selection.gate) then
    throw ("selected gate is not declared by check: " ++ selection.check ++ ":" ++ selection.gate)
  if u.fns.any (fun f => strEq f.name (driverFnName c.name selection.gate)) then
    throw ("check consumer selected twice: " ++ selection.check)
  let some wrapper := u.fns.find? (fun f =>
      strEq f.name (torHuellenName c.name selection.gate))
    | .error ("selected check wrapper unknown: " ++ selection.gate)
  let consumer := uCheckConsumer c selection.gate wrapper
  let driver := uCheckDriver c selection.gate consumer
  pure { u with fns := u.fns ++ [consumer, driver] }

/-- Configuration is a list of independent invocations, each with its own
    input permit. A selection never duplicates the token across gate names. -/
def uSelectCheckConsumers : UProg → List CheckConsumerSelection → Except String UProg
  | u, [] => .ok (uMitBoden u)
  | u, choice :: rest => do
    let u ← uSelectCheckConsumer u choice
    uSelectCheckConsumers u rest

/-- Exact resource interface: the consumer cannot return a second usable Duty. -/
theorem uCheckConsumer_ressourcen (c : UCheck) (gate : String) (wrapper : UFn) :
    (uCheckConsumer c gate wrapper).nimmt = [c.duty] ∧
      (uCheckConsumer c gate wrapper).gibt = [] := ⟨rfl, rfl⟩

/-- The driver returns no Duty on either verdict or reason channel. -/
theorem uCheckDriver_ressourcen (c : UCheck) (gate : String) (consumer : UFn) :
    (uCheckDriver c gate consumer).nimmt = [c.duty] ∧
      (uCheckDriver c gate consumer).gibt = [] := ⟨rfl, rfl⟩

/-- The selected infallible driver has one producer completion followed by
    one consumer call. It never fans one completed token out across gates. -/
theorem uCheckDriver_reihenfolge (c : UCheck) (gate : String) (consumer : UFn)
    (normal : consumer.gruende = 0) :
    (uCheckDriver c gate consumer).body =
      [.bindCall "verdict" c.probe [], .call consumer.name []] := by
  simp [uCheckDriver, normal]

end Gabbro.Grammatik.Parser.Uebersetze
