/-
  File:      stage0/Stage0/Senke/Bild.lean
  Subject:   The `S0IR` image of a whole program: header, start code, every function, the stack.

  Layout at `IMG` (the runner's loader maps the file there): word 0 the first frame's address, word 1 zero, the code
  from byte 16 (the loader's first `pc`), then the stack of `K` slots. The code is the start code (`startC`) and
  then every function of the program in the order of `fs`, at the addresses `A`.

  The addresses enter the code only as call targets (`const`), so a function's code length does not depend on
  them: `bild` lowers once with the address 0 for every function, lays the functions out by those lengths, lowers
  again with the real addresses and refuses unless every length came out the same (checked, not assumed).

  `bild` then checks the finished layout as one decidable proposition (`BildGut`): `main` without parameters,
  the lengths unmoved, the image below `2^31`, room for one call, every opcode a byte.

  The start code sets the depth to `n + 1` (G's `fuel`: `main` runs as `rufAt n`), calls `main` with its frame at
  slot `FB` and ends with `exit_group` of `main`'s result (`0` for a `main` without one). `n` is as large as the
  stack allows: every call needs at most `L` slots (the largest `top`), so `main` at depth `n` needs `(n + 1) * L`.
-/
import Stage0.Senke.Rekursion
import Runner.Prog.IRAsm

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-- The first `pc`: the loader starts the IR thread at `IMG + 16`. -/
def codeBase : Nat := Runner.Prog.IMG + 16

/-- The scratch slot of the start code's `exit_group`: above `main`'s frame header and the call's temporary. -/
def exitSlot : Nat := 2 * FB + 2

def startC (A : D.Fn → Nat) (main : D.Fn) (n : Nat) : List II :=
  [ci 1 2 ((n + 1 : Nat) : Int) 0] ++ callTail A main FB ++
    [ci 1 exitSlot 231 0,
     if (D.erg main).isSome then ci 2 ((exitSlot + 1 : Nat) : Int) ((FB + 2 : Nat) : Int) 0
     else ci 1 ((exitSlot + 1 : Nat) : Int) 0 0,
     ci 23 ((exitSlot + 7 : Nat) : Int) exitSlot 0]

def startLen : Nat := 8

theorem startC_len (A : D.Fn → Nat) (main : D.Fn) (n : Nat) : (startC A main n).length = startLen := rfl

/-- The start address of every piece, from `b` on. -/
def addrs : Nat → List Nat → List Nat
  | _, [] => []
  | b, l :: ls => b :: addrs (b + 16 * l) ls

structure Bild (D : Deklaration) where
  code : List II
  A : D.Fn → Nat
  /-- the first frame, an address -/
  fp0 : Nat
  /-- the stack, in slots -/
  K : Nat
  /-- `main` runs at this depth -/
  depth : Nat

def lowFunE (P : Programm D) (name : D.Fn → String) (A : D.Fn → Nat) (g : D.Fn) : Except String (List II × Nat) :=
  match lowFun P A g with
  | some ct => .ok ct
  | none => .error ("ir: the function " ++ name g ++ " uses a form outside the IR fragment")

/-- Every function of `fs`, lowered with the addresses `A`. -/
def lowAll (P : Programm D) (name : D.Fn → String) (A : D.Fn → Nat) : List D.Fn → Except String (List (List II × Nat))
  | [] => .ok []
  | g :: gs => do
    let c ← lowFunE P name A g
    let r ← lowAll P name A gs
    pure (c :: r)

/-- The largest stack need of the functions (at least 1). -/
def maxTop (cs : List (List II × Nat)) : Nat := cs.foldl (fun a c => max a c.2) 1

def depthOf (K L : Nat) : Nat := (K - FB) / L - 1

/-- What `bild` checks of the finished layout. -/
def BildGut (D : Deklaration) (main : D.Fn) (lens : List Nat) (cs : List (List II × Nat)) (fp0 K : Nat)
    (code : List II) : Prop :=
  (D.params main).isEmpty = true ∧ cs.map (·.1.length) = lens ∧ fp0 + 8 * K < 2 ^ 31 ∧
    FB + 2 * maxTop cs ≤ K ∧ exitSlot + 8 ≤ K ∧ code.all (fun i => decide (i.o < 256)) = true

instance (D : Deklaration) (main : D.Fn) (lens : List Nat) (cs : List (List II × Nat)) (fp0 K : Nat)
    (code : List II) : Decidable (BildGut D main lens cs fp0 K code) := by
  unfold BildGut; infer_instance

/-- The image of a program, or why not. -/
def bild (P : Programm D) (fs : List D.Fn) (pos : D.Fn → Nat) (name : D.Fn → String) (main : D.Fn) (K : Nat) :
    Except String (Bild D) :=
  match lowAll P name (fun _ => 0) fs with
  | .error e => .error e
  | .ok cs0 =>
    let lens := cs0.map (·.1.length)
    let A : D.Fn → Nat := fun g => (addrs (codeBase + 16 * startLen) lens).getD (pos g) 0
    match lowAll P name A fs with
    | .error e => .error e
    | .ok cs =>
      let body := cs.flatMap (·.1)
      let fp0 := codeBase + 16 * (startLen + body.length)
      let n := depthOf K (maxTop cs)
      let code := startC A main n ++ body
      if BildGut D main lens cs fp0 K code then .ok ⟨code, A, fp0, K, n⟩
      else if (D.params main).isEmpty = false then .error "ir: main takes parameters"
      else if cs.map (·.1.length) != lens then .error "ir: a code length moved with the addresses"
      else if fp0 + 8 * K ≥ 2 ^ 31 then .error "ir: the image does not fit below 2^31"
      else if K < FB + 2 * maxTop cs ∨ K < exitSlot + 8 then .error "ir: the stack is too small for one call"
      else .error "ir: an opcode above 255"

def encII (i : II) : List Runner.B := Runner.Prog.insB i.o i.a i.b i.c

/-- The file the runner loads. -/
def Bild.bytes (b : Bild D) : List Runner.B :=
  Runner.Prog.leN 8 b.fp0 ++ Runner.Prog.leN 8 0 ++ b.code.flatMap encII ++ List.replicate (8 * b.K) (0 : Runner.B)

end Gabbro.Stage0.Senke
