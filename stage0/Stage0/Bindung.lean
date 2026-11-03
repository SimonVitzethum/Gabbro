/-
  File:      stage0/Stage0/Bindung.lean
  Subject:   The binding of a `syscall` gate to the running machine, read from the program itself (SYNTAX.md 12.1,
             12.3): the system-call number, which parameter goes to which argument register, and the `errors` map
             (`-errno` to a case of the gate's reason; the errno of a case is its declared number, or the one written
             at the binding). Binding selection uses the execution architecture and the explicitly selected source target.
-/
module
public import Grammatik.Parser.Item.ElementTief
@[expose] public section


namespace Gabbro.Stage0

open Gabbro.Grammatik.Parser

/-- The six request argument registers in order, and the answer register. -/
def argRegs : String → List String
  | "x86_64" => ["rdi", "rsi", "rdx", "r10", "r8", "r9"]
  | "aarch64" => ["x0", "x1", "x2", "x3", "x4", "x5"]
  | _ => []

def antwortReg : String → String
  | "x86_64" => "rax"
  | "aarch64" => "x0"
  | _ => ""

/-- **A gate bound on this machine.** -/
structure Tor where
  name : String
  nummer : Nat
  /-- For argument register `i`, the parameter it carries (none: the register is left 0). -/
  regs : List (Option Nat)
  /-- `-errno` to the case of the gate's reason. -/
  fehler : List (Int × Nat)
  deriving Repr

/-- A literal number. -/
def zahlAus : SExpr → Option Int
  | .lit n => some n
  | .un "-" (.lit n) => some (-(n : Int))
  | _ => none

/-- The cases of a reason by name: each with its declared number. -/
def gruendeVon (items : List SItemTief) (r : String) : Option (List (String × Option Int)) :=
  items.findSome? fun it => match it with
    | .whyT n cs _ => if n == r then some (cs.map fun (c, e, _) => (c, zahlAus e)) else none
    | .pubT (.whyT n cs _) => if n == r then some (cs.map fun (c, e, _) => (c, zahlAus e)) else none
    | _ => none

/-- A binding is executable only when profile selection leaves exactly one candidate. -/
def uniqueBinding (v arch : String) : List SBind → Except String SBind
  | [b] => .ok b
  | [] => .error s!"gate variable {v}: no binding for {arch} in the selected target"
  | _ => .error s!"gate variable {v}: ambiguous binding for {arch}"

/-- Successful selection preserves the complete selected binding, including its error map. -/
theorem uniqueBinding_ok (v arch : String) (bs : List SBind) (b : SBind) :
    uniqueBinding v arch bs = .ok b ↔ bs = [b] := by
  cases bs with
  | nil => simp [uniqueBinding]
  | cons a rest =>
    cases rest with
    | nil => simp [uniqueBinding]
    | cons c rest => simp [uniqueBinding]

/-- Resolve one target and its declared ABI from the same canonically flattened source used by gates.
    With no target declarations the runner's default profile applies. -/
def selectedTargetFor (arch : String) (target : Option String) (items : List SItemTief) :
    Except String (Option (String × String)) := do
  let active := items.filterMap fun
    | .goalT n none => some n
    | _ => none
  let selected ← match target, active with
    | some n, _ => pure (some n)
    | none, [] => pure none
    | none, [n] => pure (some n)
    | none, _ => throw "multiple active targets"
  let available := items.filterMap fun it => match it with
    | .goalT n (some (abi, a, _)) =>
      if a == arch && (selected.isNone || selected == some n) then some (n, abi) else none
    | _ => none
  match available with
  | [profile] => pure (some profile)
  | [] => match selected with
    | none => pure none
    | some n => throw s!"target {n}: no declaration for {arch}"
  | _ => throw s!"ambiguous target for {arch}"

/-- The current image's syscall, exit and clone envelope implements Linux only. -/
def validateTargetFor (arch : String) (target : Option String) (items : List SItemTief) :
    Except String Unit := do
  match ← selectedTargetFor arch target items with
  | none => pure ()
  | some (name, abi) =>
    if abi == "linux" then pure ()
    else throw s!"target {name}: ABI {abi} is not supported by the Linux runner"

/-- Successful validation uses either the default envelope or an explicitly Linux target. -/
theorem validateTargetFor_supported (arch : String) (target : Option String)
    (items : List SItemTief) (h : validateTargetFor arch target items = .ok ()) :
    selectedTargetFor arch target items = .ok none ∨
    ∃ name, selectedTargetFor arch target items = .ok (some (name, "linux")) := by
  cases hs : selectedTargetFor arch target items with
  | error e =>
    simp only [validateTargetFor, hs] at h
    change Except.error e = Except.ok () at h
    contradiction
  | ok selected =>
    cases selected with
    | none => exact Or.inl rfl
    | some pair =>
      rcases pair with ⟨name, abi⟩
      by_cases ha : abi = "linux"
      · subst abi; exact Or.inr ⟨name, rfl⟩
      · simp only [validateTargetFor, hs] at h
        change (if abi == "linux" then Except.ok () else
          Except.error s!"target {name}: ABI {abi} is not supported by the Linux runner") = .ok () at h
        simp [ha] at h

/-- Select a gate in the unique execution target, preserving all binding fields. -/
def viaBindungFor (arch : String) (target : Option String) (items : List SItemTief)
    (v : String) : Except String SBind := do
  let selected ← selectedTargetFor arch target items
  let bindings := items.flatMap fun it => match it with
    | .goalT n (some (abi, a, bs)) =>
      if a == arch && (selected.isNone || selected.map (·.1) == some n) then
        bs.filterMap (fun (w, b, _) => if w == v then some (abi, b) else none)
      else []
    | _ => []
  let binding ← uniqueBinding v arch (bindings.map (·.2))
  if !(bindings.all fun candidate => candidate.1 == "linux") then
    throw s!"gate variable {v}: selected binding ABI is not supported by the Linux runner"
  pure binding

/-- Construct the executable gate from the complete selected source binding. -/
def torAusBindung (arch : String) (items : List SItemTief) (name : String)
    (params : List (String × STyp)) (fail : Option String) (b : SBind) : Except String Tor := do
  let nummer ← match zahlAus b.id with
    | some n => if 0 ≤ n then pure n.toNat else throw s!"gate {name}: negative number"
    | none => throw s!"gate {name}: the number is not a literal"
  let regs := (argRegs arch).map fun r =>
    b.ins.findSome? fun rb => match rb with
      | .binds r' p => if r' == r then params.findIdx? (fun q => q.1 == p) else none
      | .reg _ => none
  if b.ins.length != (regs.filterMap id).length then throw s!"gate {name}: a parameter in a register of no argument"
  if !(b.outs.all fun o => match o with | .reg r => r == antwortReg arch | _ => false) then
    throw s!"gate {name}: the answer is not in {antwortReg arch}"
  let fehler ← match fail with
    | none => if b.codes.isEmpty then pure [] else throw s!"gate {name}: errors without a reason"
    | some r =>
      match gruendeVon items r with
      | none => throw s!"gate {name}: reason {r} unknown"
      | some cs =>
        b.codes.mapM fun (_, n, fall) => do
          let i ← match cs.findIdx? (fun c => c.1 == fall) with
            | some i => pure i
            | none => throw s!"gate {name}: case {fall} unknown"
          let e ← match n with
            | some expr => match zahlAus expr with
              | some e => pure e
              | none => throw s!"gate {name}: explicit errno of {fall} is not a literal"
            | none => match cs[i]?.bind (·.2) with
              | some e => pure e
              | none => throw s!"gate {name}: case {fall} has no errno"
          pure (-e, i)
  pure ⟨name, nummer, regs, fehler⟩

/-- **The gate `sc` on this machine.** -/
def torVonFor (arch : String) (target : Option String) (items : List SItemTief) (sc : SSyscall) : Except String Tor := do
  if (argRegs arch).length != 6 then throw s!"unsupported gate architecture {arch}"
  let b ← match sc.way with
    | .lit abi a b _ =>
      if abi != "linux" then throw s!"gate {sc.name}: ABI {abi} is not supported by the Linux runner"
      else if a == arch then pure b else throw s!"gate {sc.name} has no binding for {arch}"
    | .via v => viaBindungFor arch target items v
  torAusBindung arch items sc.name sc.params sc.fail b

/-- Profile selection feeds the complete binding to gate construction; no error, register,
    number or result field is reconstructed from a name match. -/
theorem torVonFor_via (arch : String) (target : Option String) (items : List SItemTief)
    (sc : SSyscall) (v : String) (b : SBind)
    (supported : (argRegs arch).length = 6) (way : sc.way = .via v)
    (selected : viaBindungFor arch target items v = .ok b) :
    torVonFor arch target items sc = torAusBindung arch items sc.name sc.params sc.fail b := by
  simp [torVonFor, supported, way, selected]
  rfl

/-- Foreign heads use the same C14 binding selection as `syscall … via name`.
    Only transport metadata is read here; the canonical compiler has already
    elaborated the original effects, contracts and provenance of the head. -/
def foreignHead : SItemTief → Option (String × List (String × STyp) × Option String)
  | .protoT signature =>
    if signature.art == "extern" then some (signature.name, signature.params, signature.fehler) else none
  | .axiomT name params _ _ _ _ => some (name, params, none)
  | .pubT (.protoT signature) =>
    if signature.art == "extern" then some (signature.name, signature.params, signature.fehler) else none
  | .pubT (.axiomT name params _ _ _ _) => some (name, params, none)
  | _ => none

/-- Every foreign head needs an explicit selected binding. A missing binding is
    refused with its source name, before the generic function-lowering refusal. -/
def toreVonFor (arch : String) (target : Option String) (items : List SItemTief) : Except String (List Tor) := do
  let syscalls ← (items.filterMap fun it => match it with
    | .callT sc => some sc
    | .pubT (.callT sc) => some sc
    | _ => none).mapM (torVonFor arch target items)
  let foreign ← (items.filterMap foreignHead).mapM fun (name, params, fail) => do
    if (argRegs arch).length != 6 then throw s!"unsupported gate architecture {arch}"
    let binding ← viaBindungFor arch target items name
    torAusBindung arch items name params fail binding
  pure (syscalls ++ foreign)

/-- The selected complete profile is the sole source of foreign transport data. -/
theorem foreign_binding_selected (arch : String) (target : Option String)
    (items : List SItemTief) (name : String) (params : List (String × STyp))
    (fail : Option String) (binding : SBind)
    (selected : viaBindungFor arch target items name = .ok binding) :
    (do let chosen ← viaBindungFor arch target items name
        torAusBindung arch items name params fail chosen) =
      torAusBindung arch items name params fail binding := by
  rw [selected]
  rfl

end Gabbro.Stage0
