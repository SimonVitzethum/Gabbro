module

public import Init
import all Init.Data.String.Basic
import all Init.Data.String.Defs

@[expose] public section

namespace Gabbro.Grammatik

/-- Data access flags and a resolved exclusive owner identity. Ownership is never a write bit. -/
structure DataRights where
  read : Bool := false
  write : Bool := false
  owner : Option Nat := none
  deriving DecidableEq, Repr

namespace DataRights

/-- Union preserves a resolved owner; two different owners cannot describe one capability. -/
def join (a b : DataRights) : Option DataRights :=
  let owner : Option (Option Nat) := match a.owner, b.owner with
    | none, n | n, none => some n
    | some m, some n => if m = n then some (some m) else none
  owner.map fun n => ⟨a.read || b.read, a.write || b.write, n⟩

def splitParts : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | '+' :: rest, acc => acc.reverse :: splitParts rest []
  | c :: rest, acc => splitParts rest (c :: acc)

def part (resolveOwner : String → Option Nat) : List Char → Option DataRights
  | ['r'] => some ⟨true, false, none⟩
  | ['w'] => some ⟨false, true, none⟩
  | ['r', 'w'] => some ⟨true, true, none⟩
  | ['o', 'w', 'n'] => (resolveOwner "").map fun n => ⟨true, true, some n⟩
  | 'o' :: 'w' :: 'n' :: '@' :: name =>
    if name = [] then none
    else (resolveOwner (String.ofList name)).map fun n => ⟨true, true, some n⟩
  | _ => none

def parts (resolveOwner : String → Option Nat) : List (List Char) → Option DataRights
  | [] => some {}
  | p :: ps => do
    let a ← part resolveOwner p
    let b ← parts resolveOwner ps
    a.join b

/-- Normalize the complete `+` union. `own` resolves the table's implicit owner through `""`.
    Unknown components, unresolved/conflicting owners and execute rights fail closed. -/
def decode (resolveOwner : String → Option Nat) (text : String) : Option DataRights :=
  parts resolveOwner (splitParts text.toList [])

/-- A repeated matching owner survives the entire rights union. -/
theorem owner_union_zeuge :
    decode (fun n => if n = "lease" then some 7 else none) "r+own@lease+w+own@lease" =
      some ⟨true, true, some 7⟩ := by rfl

theorem conflicting_owners_refused :
    decode (fun n => if n = "left" then some 1 else if n = "right" then some 2 else none)
      "own@left+own@right" = none := by rfl

theorem unresolved_owner_refused : decode (fun _ => none) "rw+own@lease" = none := by rfl

theorem write_only_not_readable : (⟨false, true, none⟩ : DataRights).read = false := by rfl

theorem owned_not_plain : (⟨true, true, some 7⟩ : DataRights).owner ≠ none := by decide

theorem data_execute_refused : decode (fun _ => none) "rw+x" = none := by rfl

end DataRights
end Gabbro.Grammatik
