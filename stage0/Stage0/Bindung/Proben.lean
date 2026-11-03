/- Binding selection regressions use the actual textual source parser. -/
module
public import Stage0.Bindung
meta import Stage0.Bindung
@[expose] public section


namespace Gabbro.Stage0.BindingProbes
open Gabbro.Grammatik.Parser

def source := "target first abi linux arch x86_64 {\n sys_gate = number 39 regs in { } regs out { rax } clobbers { } errors { } assume contract falsifier probe;\n}\ntarget second abi metal arch x86_64 {\n sys_gate = number 110 regs in { } regs out { rax } clobbers { } errors { } assume contract falsifier probe;\n}\ntarget second;"

def numberFrom (src arch : String) (target : Option String) : Except String (Option Int) := do
  let toks ← (lex src).mapError fun _ => "lex"
  let items ← parseTopTief toks
  let binding ← viaBindungFor arch target items "sys_gate"
  pure (zahlAus binding.id)

def number := numberFrom source "x86_64"

#eval do
  let selected := match number none with
    | .error "gate variable sys_gate: selected binding ABI is not supported by the Linux runner" => true
    | _ => false
  let override := match number (some "first") with | .ok (some 39) => true | _ => false
  let missing := match number (some "missing") with | .error _ => true | _ => false
  let ambiguous := match numberFrom (source.replace "target second;" "") "x86_64" none with
    | .error _ => true | _ => false
  let explicitMetal := match number (some "second") with | .error _ => true | _ => false
  unless selected && override && missing && ambiguous && explicitMetal do
    throw (IO.userError "textual target binding regression")

def binding : SBind :=
  ⟨.lit 39, [.binds "rdi" "fd"], [.reg "rax"], [], ["rcx", "r11"],
    [("EBADF", some (.lit 9), "BadFd")]⟩

/-- A selected binding retains nonempty registers, clobbers and error channels jointly. -/
theorem uniqueBinding_ok_zeuge : uniqueBinding "sys_gate" "x86_64" [binding] = .ok binding := by rfl

def errorBinding : SBind :=
  ⟨.lit 1, [], [.reg "rax"], [], ["rcx", "r11"],
    [("EBADF", some (.lit 9), "BadFd"), ("EBADF", some (.lit 9), "Other")]⟩

def errorCall : SSyscall :=
  ⟨"probe", [], none, some "Error", .via "sys_gate", ⟨[], [], [], none⟩⟩

set_option maxRecDepth 2000 in
/-- An explicit foreign ABI cannot use the current Linux syscall envelope. -/
theorem literal_metal_refused_zeuge :
    torVonFor "x86_64" none []
      { errorCall with way := .lit "metal" "x86_64" errorBinding (.core []) } =
      .error "gate probe: ABI metal is not supported by the Linux runner" := by rfl

set_option maxRecDepth 2000 in
/-- Validation applies before emission even if no gate requests a binding. -/
theorem gate_free_metal_refused_zeuge :
    validateTargetFor "x86_64" (some "bare")
      [.goalT "bare" (some ("metal", "x86_64", []))] =
      .error "target bare: ABI metal is not supported by the Linux runner" := by rfl

set_option maxRecDepth 2000 in
/-- Unselected targets cannot make a supported selected profile fail validation. -/
theorem unselected_metal_preserved_zeuge :
    validateTargetFor "x86_64" (some "host")
      [.goalT "bare" (some ("metal", "x86_64", [])),
       .goalT "host" (some ("linux", "x86_64", []))] = .ok () := by rfl

def errorItems : List SItemTief :=
  [.goalT "selected" (some ("linux", "x86_64", [("sys_gate", errorBinding, .core [])])),
   .whyT "Error" [("BadFd", .lit 9, "bad descriptor"), ("Other", .lit 4, "other")] true]

/-- The generic construction theorem applies jointly to a selected fallible source binding. -/
theorem torVonFor_via_zeuge :
    torVonFor "x86_64" (some "selected") errorItems errorCall =
      torAusBindung "x86_64" errorItems errorCall.name errorCall.params errorCall.fail errorBinding :=
  torVonFor_via _ _ _ _ _ _ rfl rfl rfl

/-- Duplicate numeric entries retain source order, as the canonical first-entry decoder requires. -/
example : (torVonFor "x86_64" (some "selected") errorItems errorCall).toOption.map Tor.fehler =
    some [(-9, 0), (-9, 1)] := by rfl

def foreignSignature : FnSig :=
  ⟨"extern", "probe", [], some (.atom "bool"), some "Error", []⟩

def foreignItems : List SItemTief :=
  [.protoT foreignSignature,
   .goalT "selected" (some ("linux", "x86_64", [("probe", errorBinding, .core [])])),
   .whyT "Error" [("BadFd", .lit 9, "bad descriptor"), ("Other", .lit 4, "other")] true]

/-- The actual head list resolves the foreign symbol, with its complete errno map. -/
theorem foreign_binding_selected_zeuge :
    (toreVonFor "x86_64" (some "selected") foreignItems).toOption.map
      (fun gates => gates.map (fun gate => (gate.name, gate.nummer, gate.fehler))) =
      some [("probe", 1, [(-9, 0), (-9, 1)])] := by rfl

/-- Absence stays a named refusal, with no invented executable gate. -/
theorem unbound_foreign_named_zeuge :
    toreVonFor "x86_64" none [.protoT foreignSignature] =
      .error "gate variable probe: no binding for x86_64 in the selected target" := by rfl

/-- An axiom head follows the identical explicit profile mechanism. -/
theorem axiom_binding_selected_zeuge :
    (toreVonFor "x86_64" (some "selected")
      [.axiomT "probe" [] (some (.atom "bool")) none [] (.probe "falsifier"),
       .goalT "selected" (some ("linux", "x86_64", [("probe", { binding with ins := [], codes := [] }, .core [])]))]).toOption.map
      (fun gates => gates.map Tor.name) = some ["probe"] := by rfl

#print axioms uniqueBinding_ok
#print axioms torVonFor_via
end Gabbro.Stage0.BindingProbes
