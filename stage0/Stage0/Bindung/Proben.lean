/- Binding selection regressions use the actual textual source parser. -/
import Stage0.Bindung

namespace Gabbro.Stage0.BindingProbes
open Gabbro.Grammatik.Parser

private def source := "target first abi linux arch x86_64 {\n sys_gate = number 39 regs in { } regs out { rax } clobbers { } errors { } assume contract falsifier probe;\n}\ntarget second abi metal arch x86_64 {\n sys_gate = number 110 regs in { } regs out { rax } clobbers { } errors { } assume contract falsifier probe;\n}\ntarget second;"

private def numberFrom (src arch : String) (target : Option String) : Except String (Option Int) := do
  let toks ← (lex src).mapError fun _ => "lex"
  let items ← parseTopTief toks
  let binding ← viaBindungFor arch target items "sys_gate"
  pure (zahlAus binding.id)

private def number := numberFrom source "x86_64"

#eval do
  let selected := match number none with | .ok (some 110) => true | _ => false
  let override := match number (some "first") with | .ok (some 39) => true | _ => false
  let missing := match number (some "missing") with | .error _ => true | _ => false
  let ambiguous := match numberFrom (source.replace "target second;" "") "x86_64" none with
    | .error _ => true | _ => false
  unless selected && override && missing && ambiguous do
    throw (IO.userError "textual target binding regression")

private def binding : SBind :=
  ⟨.lit 39, [.binds "rdi" "fd"], [.reg "rax"], [], ["rcx", "r11"],
    [("EBADF", some (.lit 9), "BadFd")]⟩

/-- A selected binding retains nonempty registers, clobbers and error channels jointly. -/
theorem uniqueBinding_ok_zeuge : uniqueBinding "sys_gate" "x86_64" [binding] = .ok binding := rfl

private def errorBinding : SBind :=
  ⟨.lit 1, [], [.reg "rax"], [], ["rcx", "r11"],
    [("EBADF", some (.lit 9), "BadFd"), ("EBADF", some (.lit 9), "Other")]⟩

private def errorCall : SSyscall :=
  ⟨"probe", [], none, some "Error", .via "sys_gate", ⟨[], [], [], none⟩⟩

private def errorItems : List SItemTief :=
  [.goalT "selected" (some ("linux", "x86_64", [("sys_gate", errorBinding, .core [])])),
   .whyT "Error" [("BadFd", .lit 9, "bad descriptor"), ("Other", .lit 4, "other")] true]

/-- The generic construction theorem applies jointly to a selected fallible source binding. -/
theorem torVonFor_via_zeuge :
    torVonFor "x86_64" (some "selected") errorItems errorCall =
      torAusBindung "x86_64" errorItems errorCall errorBinding :=
  torVonFor_via _ _ _ _ _ _ rfl rfl rfl

/-- Duplicate numeric entries retain source order, as the canonical first-entry decoder requires. -/
example : (torVonFor "x86_64" (some "selected") errorItems errorCall).toOption.map Tor.fehler =
    some [(-9, 0), (-9, 1)] := rfl

#print axioms uniqueBinding_ok
#print axioms torVonFor_via
end Gabbro.Stage0.BindingProbes
