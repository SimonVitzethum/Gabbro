/-
  File:      stage0/Stage0/Senke/Bild.lean
  Subject:   The `S0IR` image of a whole program: header, start code, every function, the stack.

  Layout at `IMG` (the runner's loader maps the file there): word 0 the first frame's address, word 1 zero, the code
  from byte 16 (the loader's first `pc`), then the stack of `Ks` slots, then the world (`Y b` with `b` its first
  byte, `Senke/Welt/Lay.lean`); the first frame's `K` slots reach over both, so every frame ends where the world
  ends (`WIn`). The world starts as the image's zero bytes. The code is the start code (`startC`) and
  then every function of the program in the order of `fs`, at the addresses `A`.

  The addresses enter the code only as call targets, function references and world addresses (`const`), so a function's code length
  does not depend on them: `bild` lowers once with the address 0 for every function and the world at 0, lays the
  functions out by those lengths, lowers again with the real addresses and refuses unless every length came out
  the same (checked, not assumed).

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

/-- The code a thread starts with, in its frame: the depth `n + 1`, the call of its root `f`, then the system call `e`
    (`exit_group` 231 for `main`, with `main`'s result; `exit` 60 for a root, with 0). -/
def startC (A : D.Fn → Nat) (f : D.Fn) (n e : Nat) (keep : Bool) : List II :=
  [ci 1 2 ((n + 1 : Nat) : Int) 0] ++ callTail A f FB ++
    [ci 1 exitSlot e 0,
     if keep && (D.erg f).isSome then ci 2 ((exitSlot + 1 : Nat) : Int) ((FB + 2 : Nat) : Int) 0
     else ci 1 ((exitSlot + 1 : Nat) : Int) 0 0,
     ci 23 ((exitSlot + 7 : Nat) : Int) exitSlot 0]

def startLen : Nat := 8

theorem startC_len (A : D.Fn → Nat) (f : D.Fn) (n e : Nat) (keep : Bool) : (startC A f n e keep).length = startLen := rfl

/-- `main`'s first code: for every root, its start code's address and its frame's address into `exitSlot`,
    `exitSlot + 1`, then `spawn` (the thread id into `exitSlot + 2`). -/
def spawnC : List (Nat × Nat) → List II
  | [] => []
  | (a, f) :: r => [ci 1 exitSlot a 0, ci 1 ((exitSlot + 1 : Nat) : Int) f 0,
      ci 24 ((exitSlot + 2 : Nat) : Int) exitSlot 0] ++ spawnC r

theorem spawnC_len : (l : List (Nat × Nat)) → (spawnC l).length = 3 * l.length
  | [] => rfl
  | _ :: r => by simp only [spawnC, List.length_append, List.length_cons, List.length_nil, spawnC_len r]; omega

/-- The start codes of the roots, one after the other. -/
def rootsC (A : D.Fn → Nat) (n : Nat) : List D.Fn → List II
  | [] => []
  | f :: r => startC A f n 60 false ++ rootsC A n r

theorem rootsC_len (A : D.Fn → Nat) (n : Nat) : (r : List D.Fn) → (rootsC A n r).length = startLen * r.length
  | [] => rfl
  | f :: r => by simp only [rootsC, List.length_append, startC_len, rootsC_len A n r, List.length_cons]; rw [Nat.mul_succ]; omega

/-- The code before the functions, for `k` roots: the spawns, `main`'s start, the roots' starts. -/
def headLen (k : Nat) : Nat := 3 * k + startLen + startLen * k

/-- The start address of every piece, from `b` on. -/
def addrs : Nat → List Nat → List Nat
  | _, [] => []
  | b, l :: ls => b :: addrs (b + 16 * l) ls

structure Bild (D : Deklaration) where
  code : List II
  A : D.Fn → Nat
  /-- the first frame, an address -/
  fp0 : Nat
  /-- the stack and the world, in slots -/
  K : Nat
  /-- the stack, in slots -/
  Ks : Nat
  /-- the world -/
  Y : Lay D
  /-- `main` runs at this depth -/
  depth : Nat
  /-- the roots, each on a thread of its own with the `j`-th stack after `main`'s -/
  roots : List D.Fn

def lowFunE (P : Programm D) (Y : Lay D) (name : D.Fn → String) (A : D.Fn → Nat) (g : D.Fn) : Except String (List II × Nat) :=
  match lowFun P A Y g with
  | some ct => .ok ct
  | none => .error ("ir: the function " ++ name g ++ " uses a form outside the IR fragment")

/-- Every function of `fs`, lowered with the addresses `A`. -/
def lowAll (P : Programm D) (Y : Lay D) (name : D.Fn → String) (A : D.Fn → Nat) : List D.Fn → Except String (List (List II × Nat))
  | [] => .ok []
  | g :: gs => do
    let c ← lowFunE P Y name A g
    let r ← lowAll P Y name A gs
    pure (c :: r)

/-- The largest stack need of the functions (at least 1). -/
def maxTop (cs : List (List II × Nat)) : Nat := cs.foldl (fun a c => max a c.2) 1

def depthOf (K L : Nat) : Nat := (K - FB) / L - 1

/-- What `bild` checks of the finished layout. -/
def BildGut (D : Deklaration) (main : D.Fn) (roots : List D.Fn) (lens : List Nat) (cs : List (List II × Nat))
    (fp0 Ks K : Nat) (Y : Lay D) (code : List II) : Prop :=
  (D.params main).isEmpty = true ∧ roots.all (fun f => (D.params f).isEmpty) = true ∧
    D.gruende main = 0 ∧ roots.all (fun f => decide (D.gruende f = 0)) = true ∧ cs.map (·.1.length) = lens ∧
    fp0 + 8 * K < 2 ^ 31 ∧ FB + 2 * maxTop cs ≤ Ks ∧ exitSlot + 8 ≤ Ks ∧
    code.all (fun i => decide (i.o < 256)) = true ∧ fp0 + 8 * (Ks * (roots.length + 1)) ≤ Y.lo ∧ Y.hi ≤ fp0 + 8 * K ∧
    Y.sye ≤ fp0 + 8 * K

instance (D : Deklaration) (main : D.Fn) (roots : List D.Fn) (lens : List Nat) (cs : List (List II × Nat))
    (fp0 Ks K : Nat) (Y : Lay D) (code : List II) : Decidable (BildGut D main roots lens cs fp0 Ks K Y code) := by
  unfold BildGut; infer_instance

/-- The image of a program, or why not: `Ks` slots of stack, the world laid out by `Y` from its first byte. -/
def bild (P : Programm D) (Y : Nat → Lay D) (fs : List D.Fn) (pos : D.Fn → Nat) (name : D.Fn → String) (main : D.Fn)
    (roots : List D.Fn) (Ks : Nat) : Except String (Bild D) :=
  match lowAll P (Y 0) name (fun _ => 0) fs with
  | .error e => .error e
  | .ok cs0 =>
    let lens := cs0.map (·.1.length)
    let k := roots.length
    let A : D.Fn → Nat := fun g => (addrs (codeBase + 16 * headLen k) lens).getD (pos g) 0
    let fp0 := codeBase + 16 * (headLen k + lens.sum)
    let Yb := { Y (fp0 + 8 * (Ks * (k + 1))) with fa := A, sb := fp0, st := 8 * Ks }
    let K := Ks * (k + 1) + (Yb.sye - Yb.lo + 7) / 8
    match lowAll P Yb name A fs with
    | .error e => .error e
    | .ok cs =>
      let body := cs.flatMap (·.1)
      let n := depthOf Ks (maxTop cs)
      let sp := (List.range k).map fun j => (codeBase + 16 * (3 * k + startLen + startLen * j), fp0 + 8 * (Ks * (j + 1)))
      let code := spawnC sp ++ startC A main n 231 true ++ rootsC A n roots ++ body
      if BildGut D main roots lens cs fp0 Ks K Yb code ∧ fp0 = codeBase + 16 * (headLen k + body.length) then
        .ok ⟨code, A, fp0, K, Ks, Yb, n, roots⟩
      else if D.gruende main != 0 then .error "ir: main has an uncaught reason channel"
      else if (roots.all fun f => decide (D.gruende f = 0)) = false then .error "ir: a root has an uncaught reason channel"
      else if (D.params main).isEmpty = false then .error "ir: main takes parameters"
      else if (roots.all fun f => (D.params f).isEmpty) = false then .error "ir: a root takes parameters"
      else if cs.map (·.1.length) != lens then .error "ir: a code length moved with the addresses"
      else if fp0 + 8 * K ≥ 2 ^ 31 then .error "ir: the image does not fit below 2^31"
      else if Ks < FB + 2 * maxTop cs ∨ Ks < exitSlot + 8 then .error "ir: the stack is too small for one call"
      else if (code.all fun i => decide (i.o < 256)) = false then .error "ir: an opcode above 255"
      else .error "ir: the world does not lie above the stack"

def encII (i : II) : List Runner.B := Runner.Prog.insB i.o i.a i.b i.c

/-- The file the runner loads. -/
def Bild.bytes (b : Bild D) : List Runner.B :=
  Runner.Prog.leN 8 b.fp0 ++ Runner.Prog.leN 8 0 ++ b.code.flatMap encII ++ List.replicate (8 * b.K) (0 : Runner.B)

end Gabbro.Stage0.Senke
