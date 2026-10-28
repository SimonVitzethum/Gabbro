/-
  File:      stage0/Stage0/Senke/Bild.lean
  Subject:   The `S0IR` image of a whole program: header, start code, every function, the stack.

  Layout at `IMG` (the runner's loader maps the file there): word 0 the first frame's address, word 1 zero, the code
  from byte 16 (the loader's first `pc`), then the stack of `K` slots. The code is the start code (`startC`) and
  then every function of the program in the order of `fs`, at the addresses `A`.

  The addresses enter the code only as call targets (`const`), so a function's code length does not depend on
  them: `bild` lowers once with the address 0 for every function, lays the functions out by those lengths, lowers
  again with the real addresses and refuses unless every length came out the same (checked, not assumed).

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

/-- The image of a program, or why not. -/
def bild (P : Programm D) (fs : List D.Fn) (pos : D.Fn → Nat) (name : D.Fn → String) (main : D.Fn) (K : Nat) :
    Except String (Bild D) := do
  if (D.params main).isEmpty = false then throw "ir: main takes parameters"
  let lens ← fs.mapM fun g => do pure (← lowFunE P name (fun _ => 0) g).1.length
  let as := addrs (codeBase + 16 * startLen) lens
  let A : D.Fn → Nat := fun g => as.getD (pos g) 0
  let cs ← fs.mapM (lowFunE P name A)
  if cs.map (·.1.length) != lens then throw "ir: a code length moved with the addresses"
  let L := cs.foldl (fun a c => max a c.2) 1
  let body := cs.flatMap (·.1)
  let fp0 := codeBase + 16 * (startLen + body.length)
  if fp0 + 8 * K ≥ 2 ^ 31 then throw "ir: the image does not fit below 2^31"
  if K < FB + 2 * L ∨ K < exitSlot + 8 then throw "ir: the stack is too small for one call"
  let n := (K - FB) / L - 1
  pure ⟨startC A main n ++ body, A, fp0, K, n⟩

/-- The file the runner loads. -/
def Bild.bytes (b : Bild D) : List Runner.B :=
  Runner.Prog.leN 8 b.fp0 ++ Runner.Prog.leN 8 0 ++ b.code.flatMap (fun i => Runner.Prog.insB i.o i.a i.b i.c) ++
    List.replicate (8 * b.K) (0 : Runner.B)

end Gabbro.Stage0.Senke
