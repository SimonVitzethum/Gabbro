/-
  File:      stage0/Stage0/Tor/Worte.lean
  Subject:   The argument words of a question to a system-call gate: numbers, and tables handed by pointer; the
             argument key `kfVon` the oracle files an answer under.
-/
import Stage0.Laufzeit

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze Gabbro.Grammatik.Parser.UebersetzeAllg

/-- An argument as the machine sees it: a number, or a table handed by pointer. -/
inductive ArgWort (u : UProg)
  | zahl (z : Int)
  | puffer (t : (declOf u).Tab) (rw : Bool)

/-- The argument words of an argument list. -/
def argWorte (u : UProg) : (Γ : List Ty) → Env (declOf u) Γ → Except String (List (ArgWort u))
  | [], .nil => .ok []
  | .int _ _ :: Γ, .cons v ρ => return .zahl v.n :: (← argWorte u Γ ρ)
  | .bool :: Γ, .cons v ρ => return .zahl (cond (show Bool from v) 1 0) :: (← argWorte u Γ ρ)
  | .ptr n rw :: Γ, .cons _ ρ =>
    match (declOf u).tabNr n with
    | some t => return .puffer t rw :: (← argWorte u Γ ρ)
    | none => .error "a pointer to no table"
  | _ :: _, .cons _ _ => .error "an argument of a type a system call does not take"

/-- An argument word as a number of the key: a table by `-1 - t`. -/
def ArgWort.zahlVon {u : UProg} : ArgWort u → Int
  | .zahl z => z
  | .puffer t _ => -1 - (t.val : Int)

/-- **The argument key of a question**: the gate and the argument words (`orakelZ` adds the number of questions
    the asking thread asked before). -/
def kfVon (u : UProg) (a : (declOf u).Ax) (ρ : Env (declOf u) ((declOf u).aparams a)) : List Int :=
  (a.val : Int) :: ((argWorte u _ ρ).toOption.getD []).map ArgWort.zahlVon

end Gabbro.Stage0
