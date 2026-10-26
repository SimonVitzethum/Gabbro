/-
  File:      stage0/Stage0/Tor/Ausfuehren.lean
  Subject:   A question of the program answered by the real system call (`roherSyscall`): the argument values become
             machine words in the registers the gate's binding names; a pointer to a table becomes the address of
             a buffer holding the table's byte field (copied in before, copied back after the call); the kernel's
             word becomes the raw answer the model decodes (`sonstPasst`: a value `v` is `v * (n + 1)`, a listed
             `-errno` the reason case `i + 1`, anything else a word that decodes to no answer).
-/
import Stage0.Laufzeit
import Stage0.Tor.Roh
import Stage0.Tor.Bindung
import Stage0.Tor.Orakel
import Stage0.Tor.Frage

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

/-- The byte field of a table: its first field typed `0 .. 255`. -/
def bytFeld (u : UProg) (t : (declOf u).Tab) : Option ((declOf u).Feld t) :=
  (List.finRange (fieldCount u t)).find? (fun f => decide ((declOf u).typ t f = .int 0 255))

/-- The bytes of a table's byte field in a world. -/
def leseBytes (u : UProg) (σ : World (declOf u)) (t : (declOf u).Tab) (f : (declOf u).Feld t) : ByteArray :=
  let n := ((declOf u).count t).toNat
  ⟨(List.range n).toArray.map fun (k : Nat) =>
    match alsZahl _ (σ.slots t (k : Int) f) with
    | some z => z.toNat.toUInt8
    | none => 0⟩

/-- The slots after the call wrote the buffer back into the byte field. -/
def mitBytes (u : UProg) (t : (declOf u).Tab) (f : (declOf u).Feld t) (b : ByteArray)
    (sl : ∀ t : (declOf u).Tab, Int → ∀ f : (declOf u).Feld t, Wert (declOf u) ((declOf u).typ t f)) :
    ∀ t : (declOf u).Tab, Int → ∀ f : (declOf u).Feld t, Wert (declOf u) ((declOf u).typ t f) :=
  fun t' k f' =>
    if h : t' = t then
      if (h ▸ f') = f ∧ 0 ≤ k ∧ k < b.size then
        match ausZahl ((declOf u).typ t' f') (b.get! k.toNat).toNat with
        | some v => v
        | none => sl t' k f'
      else sl t' k f'
    else sl t' k f'

/-- The kernel's word as the raw answer of the model, for a gate with `n` reasons. -/
def rohVon (tor : Tor) (n : Nat) (rax : Int) : Int :=
  if n = 0 then rax
  else if -4095 ≤ rax ∧ rax ≤ -1 then
    match tor.fehler.find? (fun e => e.1 == rax) with
    | some (_, i) => (i : Int) + 1
    | none => -((n : Int) + 1)
  else rax * ((n : Int) + 1)

/-- The signed value of a kernel word. -/
def vorzeichen (w : UInt64) : Int := if w < 0x8000000000000000 then w.toNat else (w.toNat : Int) - 18446744073709551616

/-- **Answer the question `q` by the real system call** of its gate. -/
def ausfuehren (u : UProg) (tore : List Tor) (q : Σ a : (declOf u).Ax, World (declOf u) × Env (declOf u) ((declOf u).aparams a)) :
    IO (Antwort (declOf u)) := do
  let ⟨a, σq, ρa⟩ := q
  let name := (uaxAt u a).name
  let tor ← match tore.find? (·.name == name) with
    | some t => pure t
    | none => throw (IO.userError s!"stage0: the foreign body {name} is no system-call gate of this machine")
  let ws : List (ArgWort u) ← match argWorte u _ ρa with
    | .ok ws => pure ws
    | .error e => throw (IO.userError ("stage0: " ++ e))
  let puffer : List ((declOf u).Tab × Bool) :=
    ws.filterMap fun w => match w with | .puffer t rw => some (t, rw) | _ => none
  if puffer.length > 1 then throw (IO.userError s!"stage0: {name} takes more than one buffer")
  let (buf, feld) ← (match puffer with
    | [(t, rw)] => match bytFeld u t with
      | some f => pure (leseBytes u σq t f, some ⟨t, f, rw⟩)
      | none => throw (IO.userError s!"stage0: the table handed to {name} has no byte field")
    | _ => pure (ByteArray.empty, none) :
      IO (ByteArray × Option (Σ t : (declOf u).Tab, (declOf u).Feld t × Bool)))
  let regs : List (UInt64 × Bool) := tor.regs.map fun j? => match j? with
    | some j => match ws[j]? with
      | some (ArgWort.zahl z) => (UInt64.ofInt z, false)
      | some (ArgWort.puffer _ _) => (0, true)
      | none => (0, false)
    | none => (0, false)
  let which : UInt8 := match regs.findIdx? (·.2) with | some i => i.toUInt8 | none => 255
  let w : Nat → UInt64 := fun i => (regs.getD i (0, false)).1
  let (rax, buf') ← roherSyscall tor.nummer.toUInt64 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) buf which
  let slots := match feld with
    | some ⟨t, f, true⟩ => mitBytes u t f buf'
    | _ => id
  let worte : List Int := ws.map fun w => match w with
    | ArgWort.zahl z => z
    | ArgWort.puffer t _ => -1 - (t.val : Int)
  pure ⟨σq.spur.length, rohVon tor ((declOf u).agruende a) (vorzeichen rax), slots, worte⟩

end Gabbro.Stage0
