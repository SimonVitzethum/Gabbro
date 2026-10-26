/-
  File:      stage0/Stage0/Tor/Bindung.lean
  Subject:   The binding of a `syscall` gate to the running machine, read from the program itself (SYNTAX.md 12.1,
             12.3): the system-call number, which parameter goes to which argument register, and the `errors` map
             (`-errno` to a case of the gate's reason; the errno of a case is its declared number, or the one written
             at the binding). Only the binding for the architecture stage 0 runs on is read (x86_64 or aarch64).
-/
import Grammatik.Parser.Item.ElementTief

namespace Gabbro.Stage0

open Gabbro.Grammatik.Parser

/-- The architecture stage 0 runs on, as the bindings name it. -/
def archHier : String :=
  if System.Platform.target.startsWith "x86_64" then "x86_64"
  else if System.Platform.target.startsWith "aarch64" then "aarch64" else "?"

/-- The Linux argument registers in order, and the answer register. -/
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

/-- The binding of a variable gate `via V` on this machine (`target T abi A arch X { V = … }`). -/
def viaBindung (items : List SItemTief) (v : String) : Option SBind :=
  items.findSome? fun it => match it with
    | .goalT _ (some (_, arch, bs)) =>
      if arch == archHier then bs.findSome? (fun (w, b, _) => if w == v then some b else none) else none
    | _ => none

/-- **The gate `sc` on this machine.** -/
def torVon (items : List SItemTief) (sc : SSyscall) : Except String Tor := do
  let b ← match sc.way with
    | .lit _ arch b _ => if arch == archHier then pure b else throw s!"gate {sc.name} has no binding for {archHier}"
    | .via v => match viaBindung items v with
      | some b => pure b
      | none => throw s!"gate {sc.name}: no binding of {v} for {archHier}"
  let nummer ← match zahlAus b.id with
    | some n => if 0 ≤ n then pure n.toNat else throw s!"gate {sc.name}: negative number"
    | none => throw s!"gate {sc.name}: the number is not a literal"
  let regs := (argRegs archHier).map fun r =>
    b.ins.findSome? fun rb => match rb with
      | .binds r' p => if r' == r then sc.params.findIdx? (fun q => q.1 == p) else none
      | .reg _ => none
  if b.ins.length != (regs.filterMap id).length then throw s!"gate {sc.name}: a parameter in a register of no argument"
  if !(b.outs.all fun o => match o with | .reg r => r == antwortReg archHier | _ => false) then
    throw s!"gate {sc.name}: the answer is not in {antwortReg archHier}"
  let fehler ← match sc.fail with
    | none => if b.codes.isEmpty then pure [] else throw s!"gate {sc.name}: errors without a reason"
    | some r =>
      match gruendeVon items r with
      | none => throw s!"gate {sc.name}: reason {r} unknown"
      | some cs =>
        b.codes.mapM fun (_, n, fall) => do
          let i ← match cs.findIdx? (fun c => c.1 == fall) with
            | some i => pure i
            | none => throw s!"gate {sc.name}: case {fall} unknown"
          let e ← match n.bind zahlAus, cs[i]?.bind (·.2) with
            | some e, _ => pure e
            | none, some e => pure e
            | none, none => throw s!"gate {sc.name}: case {fall} has no errno"
          pure (-e, i)
  pure ⟨sc.name, nummer, regs, fehler⟩

/-- The gates of a program by name. -/
def toreVon (items : List SItemTief) : Except String (List Tor) :=
  (items.filterMap fun it => match it with
    | .callT sc => some sc
    | .pubT (.callT sc) => some sc
    | _ => none).mapM (torVon items)

end Gabbro.Stage0
