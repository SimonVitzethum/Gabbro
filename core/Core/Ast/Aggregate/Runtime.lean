module

public import Core.Ast.Semantik.Arithmetik

@[expose] public section

namespace Gabbro.Core.Ast

abbrev Dynamisch := (type : Ty .value) × Wert type

end Gabbro.Core.Ast

namespace Gabbro.Core.Ast.Semantik

def wertAls : (type : Ty .value) → Dynamisch → Option (Wert type)
  | .int lo hi, ⟨.int _ _, number⟩ =>
    if bounds : lo ≤ number.wert ∧ number.wert ≤ hi then
      some ⟨number.wert, bounds.1, bounds.2⟩
    else none
  | .array _ 0, ⟨.array _ 0, _⟩ => some #v[]
  | target, ⟨source, value⟩ =>
    if same : source = target then some (same ▸ value) else none

def wertIn (type : Ty .value) (value : Dynamisch) : Option Dynamisch :=
  (wertAls type value).map fun checked => ⟨type, checked⟩

def liesTupel (temp : Nat → Option Dynamisch) (slot : Nat) :
    (types : List (Ty .value)) → Option (Wert (tupleType types))
  | [] => some PUnit.unit
  | head :: tail => do
    let value ← (temp slot).bind (wertAls head)
    let more ← liesTupel temp (slot + 1) tail
    pure (value, more)

def liesRecord (temp : Nat → Option Dynamisch) :
    (types : List (Ty .value)) → List Nat → Option (Wert (tupleType types))
  | [], [] => some PUnit.unit
  | head :: tail, slot :: sources => do
    let value ← (temp slot).bind (wertAls head)
    let more ← liesRecord temp tail sources
    pure (value, more)
  | _, _ => none

def tupleLocals : (types : List (Ty .value)) → Wert (tupleType types) → List Bool → List (Option Dynamisch)
  | head :: tail, values, keep :: more =>
    let rest := tupleLocals tail values.2 more
    if keep then some ⟨head, values.1⟩ :: rest else rest
  | _, _, _ => []

end Gabbro.Core.Ast.Semantik
