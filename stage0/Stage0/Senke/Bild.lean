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

  `bild` then checks the finished layout as one decidable proposition (`BildGut`): the roots without parameters,
  the lengths unmoved, the image below `2^31`, room for one call and for each start's scratch, every opcode a byte.

  The start code sets the depth to `n + 1` (G's `fuel`: `main` runs as `rufAt n`), calls `main` with its frame at
  slot `FB` and ends with `exit_group` of `main`'s result (`0` for a `main` without one). `n` is as large as the
  stack allows: every call needs at most `L` slots (the largest `top`), so `main` at depth `n` needs `(n + 1) * L`.

  **Parameters of `main`.** The words of `main`'s environment (`encodeEnv`, the one parameter encoding of every call)
  are the image's own bytes: the first stack frame holds them at the slots `FB + FB ..` where the callee's parameter
  span lies, every other slot of the stack and the world is zero. The scratch of a start (the spawns, the exit code)
  lies above that span, the shared result area and the status word (`startScratch`, the `receiveTop` of the root's
  signature), so neither the spawns nor the call write a parameter word.
-/
import Stage0.Senke.Rekursion
import Stage0.Senke.Welt.StartLayout
import Runner.Prog.IRAsm

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

/-- The first `pc`: the loader starts the IR thread at `IMG + 16`. -/
def codeBase : Nat := Runner.Prog.IMG + 16

/-- The first scratch slot of a start in the frame of its root `f`, whose callee frame lies at slot `FB`: above the
    header, the complete parameter span, the shared result area and the status word of that call (`receiveTop`). -/
def startScratch (f : D.Fn) : Nat := receiveTop (D.signatur f) FB

theorem startScratch_eq (f : D.Fn) : startScratch f =
    FB + FB + contextWords (D.params f) + returnWords (D.erg f) (D.gruende f) + 1 := rfl

attribute [irreducible] startScratch

/-- The code a thread starts with, in its frame: the depth `n + 1`, the call of its root `f`, then the system call `e`
    (`exit_group` 231 for `main`, with `main`'s result; `exit` 60 for a root, with 0). -/
def startC (A : D.Fn → Nat) (f : D.Fn) (n e : Nat) (keep : Bool) : List II :=
  [ci 1 2 ((n + 1 : Nat) : Int) 0] ++ callTail A f FB ++
    [ci 1 (startScratch f) e 0,
     if keep && (D.erg f).isSome then ci 2 ((startScratch f + 1 : Nat) : Int) ((FB + 2 : Nat) : Int) 0
     else ci 1 ((startScratch f + 1 : Nat) : Int) 0 0,
     ci 23 ((startScratch f + 7 : Nat) : Int) (startScratch f) 0]

def startLen : Nat := 8

theorem startC_len (A : D.Fn → Nat) (f : D.Fn) (n e : Nat) (keep : Bool) : (startC A f n e keep).length = startLen := rfl

/-- `main`'s first code: for every root, its start code's address and its frame's address into the scratch slots `s`,
    `s + 1` (`s` is `main`'s `startScratch`), then `spawn` (the thread id into `s + 2`). -/
def spawnC (s : Nat) : List (Nat × Nat) → List II
  | [] => []
  | (a, f) :: r => [ci 1 s a 0, ci 1 ((s + 1 : Nat) : Int) f 0,
      ci 24 ((s + 2 : Nat) : Int) s 0] ++ spawnC s r

theorem spawnC_len (s : Nat) : (l : List (Nat × Nat)) → (spawnC s l).length = 3 * l.length
  | [] => rfl
  | _ :: r => by simp only [spawnC, List.length_append, List.length_cons, List.length_nil, spawnC_len s r]; omega

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
  /-- The environment fuel compiled into every forever loop. -/
  passes : Nat
  /-- the roots, each on a thread of its own with the `j`-th stack after `main`'s -/
  roots : List D.Fn
  /-- the words of `main`'s environment, in the first stack frame at the callee's parameter span -/
  args : List Runner.W

def lowFunE (passes : Nat) (P : Programm D) (Y : Lay D) (name : D.Fn → String) (A : D.Fn → Nat) (g : D.Fn) : Except String (List II × Nat) :=
  match lowFun passes P A Y g with
  | some ct => .ok ct
  | none => .error ("ir: the function " ++ name g ++
      if (oldCells (P.ensures g)).length > 1 then
        " needs multiple old occurrences; the IR entry header currently holds one snapshot word"
      else if (lowEns Y (P.ensures g) (FB + (contextWords (D.params g)) + 1)).isNone then
        " has an unsupported postcondition; old table indices must be literal constants (possibly widened)"
      else " uses a form outside the IR fragment")

/-- Every function of `fs`, lowered with the addresses `A`. -/
def lowAll (passes : Nat) (P : Programm D) (Y : Lay D) (name : D.Fn → String) (A : D.Fn → Nat) : List D.Fn → Except String (List (List II × Nat))
  | [] => .ok []
  | g :: gs => do
    let c ← lowFunE passes P Y name A g
    let r ← lowAll passes P Y name A gs
    pure (c :: r)

/-- The largest stack need of the functions (at least 1). -/
def maxTop (cs : List (List II × Nat)) : Nat := cs.foldl (fun a c => max a c.2) 1

def depthOf (K L : Nat) : Nat := (K - FB) / L - 1

/-- What `bild` checks of the finished layout. -/
def BildGut (D : Deklaration) (main : D.Fn) (roots : List D.Fn) (lens : List Nat) (cs : List (List II × Nat))
    (fp0 Ks K : Nat) (Y : Lay D) (code : List II) : Prop :=
  roots.all (fun f => (D.params f).isEmpty) = true ∧
    D.gruende main = 0 ∧ roots.all (fun f => decide (D.gruende f = 0)) = true ∧ cs.map (·.1.length) = lens ∧
    fp0 + 8 * K < 2 ^ 31 ∧ FB + 2 * maxTop cs ≤ Ks ∧ (main :: roots).all (fun f => decide (startScratch f + 8 ≤ Ks)) = true ∧
    code.all (fun i => decide (i.o < 256)) = true ∧ fp0 + 8 * (Ks * (roots.length + 1)) ≤ Y.lo ∧ Y.hi ≤ fp0 + 8 * K ∧
    Y.sye ≤ fp0 + 8 * K

instance (D : Deklaration) (main : D.Fn) (roots : List D.Fn) (lens : List Nat) (cs : List (List II × Nat))
    (fp0 Ks K : Nat) (Y : Lay D) (code : List II) : Decidable (BildGut D main roots lens cs fp0 Ks K Y code) := by
  unfold BildGut; infer_instance

/-- The image of a program, or why not: `Ks` slots of stack, the world laid out by `Y` from its first byte, `main`
    started with the environment `ρ` (its words in the first frame). -/
def bild (passes : Nat) (P : Programm D) (Y : Nat → Lay D) (fs : List D.Fn) (pos : D.Fn → Nat) (name : D.Fn → String) (main : D.Fn)
    (ρ : Env D (D.params main)) (roots : List D.Fn) (Ks : Nat) : Except String (Bild D) :=
  match lowAll passes P (Y 0) name (fun _ => 0) fs with
  | .error e => .error e
  | .ok cs0 =>
    let lens := cs0.map (·.1.length)
    let k := roots.length
    let A : D.Fn → Nat := fun g => (addrs (codeBase + 16 * headLen k) lens).getD (pos g) 0
    let fp0 := codeBase + 16 * (headLen k + lens.sum)
    let Yb := { Y (fp0 + 8 * (Ks * (k + 1))) with fa := A, sb := fp0, st := 8 * Ks }
    let K := Ks * (k + 1) + (Yb.sye - Yb.lo + 7) / 8
    match lowAll passes P Yb name A fs with
    | .error e => .error e
    | .ok cs =>
      let body := cs.flatMap (·.1)
      let n := depthOf Ks (maxTop cs)
      let sp := (List.range k).map fun j => (codeBase + 16 * (3 * k + startLen + startLen * j), fp0 + 8 * (Ks * (j + 1)))
      let code := spawnC (startScratch main) sp ++ startC A main n 231 true ++ rootsC A n roots ++ body
      if BildGut D main roots lens cs fp0 Ks K Yb code ∧ fp0 = codeBase + 16 * (headLen k + body.length) then
        .ok ⟨code, A, fp0, K, Ks, Yb, n, passes, roots, encodeEnv Yb ρ⟩
      else if D.gruende main != 0 then .error "ir: main has an uncaught reason channel"
      else if (roots.all fun f => decide (D.gruende f = 0)) = false then .error "ir: a root has an uncaught reason channel"
      else if (roots.all fun f => (D.params f).isEmpty) = false then .error "ir: a root takes parameters"
      else if cs.map (·.1.length) != lens then .error "ir: a code length moved with the addresses"
      else if fp0 + 8 * K ≥ 2 ^ 31 then .error "ir: the image does not fit below 2^31"
      else if Ks < FB + 2 * maxTop cs ∨ ((main :: roots).all fun f => decide (startScratch f + 8 ≤ Ks)) = false then
        .error "ir: the stack is too small for one call"
      else if (code.all fun i => decide (i.o < 256)) = false then .error "ir: an opcode above 255"
      else .error "ir: the world does not lie above the stack"

def encII (i : II) : List Runner.B := Runner.Prog.insB i.o i.a i.b i.c

/-- The file the runner loads: header, code, `main`'s frame with its parameter words, then the zero bytes of the roots'
    stacks and the world. -/
def Bild.bytes (b : Bild D) : List Runner.B :=
  Runner.Prog.leN 8 b.fp0 ++ Runner.Prog.leN 8 0 ++ b.code.flatMap encII ++
    ((startFrameBytes b.Ks (FB + FB) b.args).getD [] ++ List.replicate (8 * (b.K - b.Ks)) (0 : Runner.B))

end Gabbro.Stage0.Senke
