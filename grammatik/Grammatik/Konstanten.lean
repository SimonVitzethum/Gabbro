/-
  File:      Grammatik/Konstanten.lean
  Subject:   COMPILE-TIME CONSTANTS, FIRST CUT (PLAN-BITS.md section 6).

  The checker evaluates total, effect-free const initializers and const
  tables element-wise and prints the values as a certificate: a `List Nat`
  literal plus the defining equation as a `List.all` predicate (encoding N
  of the certificate measurement). This file carries the Lean side: the
  certificate predicate shape and the generic lemma that a closed
  certificate yields every entry's defining equation, with the range proofs
  attached afterwards as the measurement recommends.

  Lane 121: the defining function is translated from the `const fn`
  SOURCE (`konst_lean`), never handed in -- `quad` below is exactly what
  the printer emits for `quad(i)`, and `quad_aus_syntax` proves
  evaluation of the syntax equals it, so the certificate ties the
  values to the source.
-/

namespace Gabbro.Grammatik.Konstanten

/-- Certificate predicate (encoding N): the defining equation `f`
    (index to value to check) over every entry of `t`, through `zipIdx`
    so the equation sees the index. -/
def konstZert (t : List Nat) (f : Nat → Nat → Bool) : Bool :=
  t.zipIdx.all fun p => f p.2 p.1

/-- The empty table is trivially certified. -/
theorem konstZert_nil (f : Nat → Nat → Bool) : konstZert [] f = true :=
  rfl

/-- Membership at an offset: `t[j]? = some v` puts `(v, n + j)` into
    `t.zipIdx n`. The offset generalizes the induction; the public lemma
    below instantiates it at `0`. -/
theorem mem_zipIdx_aux {t : List Nat} {n j v : Nat}
    (hm : t[j]? = some v) : (v, n + j) ∈ t.zipIdx n := by
  induction t generalizing n j with
  | nil => simp at hm
  | cons a rest ih =>
    cases j with
    | zero =>
      simp at hm
      subst hm
      simp [List.zipIdx]
    | succ j =>
      simp at hm
      have hmem := ih (n := n + 1) (j := j) hm
      have heq : n + (j + 1) = (n + 1) + j := by omega
      rw [heq]
      simp [List.zipIdx]
      exact Or.inr hmem

/-- `t[j]? = some v` puts `(v, j)` into `t.zipIdx`. -/
theorem mem_zipIdx_of_getElem? {t : List Nat} {j v : Nat}
    (hm : t[j]? = some v) : (v, j) ∈ t.zipIdx := by
  have h := mem_zipIdx_aux (t := t) (n := 0) (j := j) (v := v) hm
  simpa using h

/-- Generic certificate lemma: a closed certificate yields every entry's
    defining equation. Every premise is used: `h` supplies the closed
    `List.all`, `hm` locates the entry. -/
theorem konstZert_mem {t : List Nat} {f : Nat → Nat → Bool}
    (h : konstZert t f = true) {j v : Nat}
    (hm : t[j]? = some v) : f j v = true := by
  unfold konstZert at h
  rw [List.all_eq_true] at h
  have hmem := mem_zipIdx_of_getElem? hm
  have hfv := h _ hmem
  simpa using hfv

/-! ## Translated source: the const fragment as syntax (lane 121) -/

/-- Binary operators of the const fragment: arithmetic, bit, comparison
    (as `0`/`1`), and logic (as `0`/`1`). No negation, no `~`, no
    wrap/saturate -- the printer refuses those, like `lean.rs`. -/
inductive KBinOp where
  | add | sub | mul | div | mod
  | land | lor | xor | shl | shr
  | eq | ne | lt | le | gt | ge
  | and | or
deriving DecidableEq, Repr

/-- Unary operators of the const fragment: logical negation only. -/
inductive KUnaOp where
  | not
deriving DecidableEq, Repr

/-- The translated expression language: literals, the parameter, named
    consts (by name, read off an environment), calls (by name, read off
    a function environment), and operator applications. -/
inductive KExpr where
  | lit : Nat → KExpr
  | param : KExpr
  | konst : String → KExpr
  | una : KUnaOp → KExpr → KExpr
  | bin : KBinOp → KExpr → KExpr → KExpr
  | ruf : String → List KExpr → KExpr

/-- Operator evaluation on `Nat`, mirroring the printed Lean operators. -/
def KBinOp.eval : KBinOp → Nat → Nat → Nat
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .land, a, b => Nat.land a b
  | .lor, a, b => Nat.lor a b
  | .xor, a, b => Nat.xor a b
  | .shl, a, b => Nat.shiftLeft a b
  | .shr, a, b => Nat.shiftRight a b
  | .eq, a, b => if a == b then 1 else 0
  | .ne, a, b => if !(a == b) then 1 else 0
  | .lt, a, b => if a < b then 1 else 0
  | .le, a, b => if a <= b then 1 else 0
  | .gt, a, b => if a > b then 1 else 0
  | .ge, a, b => if a >= b then 1 else 0
  | .and, a, b => if a == 0 || b == 0 then 0 else 1
  | .or, a, b => if a == 0 && b == 0 then 0 else 1

mutual
/-- Expression evaluation: the parameter reads the index, names read
    the environments, calls apply the named function to the values. -/
def KExpr.eval (env : String → Nat) (fns : String → List Nat → Nat) :
    KExpr → Nat → Nat
  | .lit n, _ => n
  | .param, i => i
  | .konst c, _ => env c
  | .una .not e, i => if e.eval env fns i == 0 then 1 else 0
  | .bin op a b, i => op.eval (a.eval env fns i) (b.eval env fns i)
  | .ruf f args, i => fns f (KExprList.eval env fns args i)

def KExprList.eval (env : String → Nat)
    (fns : String → List Nat → Nat) : List KExpr → Nat → List Nat
  | [], _ => []
  | e :: es, i => e.eval env fns i :: KExprList.eval env fns es i
end

/-- No named consts in scope: every name reads `0`. -/
def leerEnv : String → Nat := fun _ => 0

/-- No const fns in scope: every call reads `0`. -/
def leerFns : String → List Nat → Nat := fun _ _ => 0

/-- The `quad` body as syntax: `i * i`. -/
def quadSyntax : KExpr := .bin .mul .param .param

/-- The PRINTED function: exactly what `konst_lean::funktion_lean` emits
    for the `quad` source (`def quad (i : Nat) : Nat := i * i`). The Rust
    exact-string test holds this line against the printer output. -/
def quad (i : Nat) : Nat := i * i

/-- Soundness: evaluation of the syntax equals the printed function. -/
theorem quad_aus_syntax (i : Nat) :
    quadSyntax.eval leerEnv leerFns i = quad i := by
  simp only [quadSyntax, quad, KExpr.eval, KBinOp.eval]

/-- Literals and addition: `3 + 4`. -/
def dreiPlusVierSyntax : KExpr := .bin .add (.lit 3) (.lit 4)

theorem dreiPlusVier_aus_syntax :
    dreiPlusVierSyntax.eval leerEnv leerFns 0 = 7 := by decide

/-- A named const reads the environment: `C` with `C ↦ 41`. -/
def constUmgebung : String → Nat
  | "C" => 41
  | _ => 0

def constSyntax : KExpr := .konst "C"

theorem konst_aus_syntax :
    constSyntax.eval constUmgebung leerFns 0 = 41 := by decide

/-- A nested call applies the named function to the values:
    `doppelt(plusEins(n))` with the printed functions. -/
def doppelt (n : Nat) : Nat := n + n

def plusEins (n : Nat) : Nat := n + 1

def zweimalPlusEinsFunktionen : String → List Nat → Nat
  | "doppelt", [n] => doppelt n
  | "plusEins", [n] => plusEins n
  | _, _ => 0

def zweimalPlusEinsSyntax : KExpr :=
  .ruf "doppelt" [.ruf "plusEins" [.param]]

theorem ruf_aus_syntax (i : Nat) :
    zweimalPlusEinsSyntax.eval leerEnv zweimalPlusEinsFunktionen i =
      doppelt (plusEins i) := by
  simp only [zweimalPlusEinsSyntax, doppelt, plusEins, KExpr.eval,
    KExprList.eval, zweimalPlusEinsFunktionen]

/-- The 64-entry square table: the witness the checker evaluates and
    certifies (`i * i` for `i` in `0 .. 64`). -/
def squares64 : List Nat :=
  [0, 1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225, 256,
    289, 324, 361, 400, 441, 484, 529, 576, 625, 676, 729, 784, 841, 900,
    961, 1024, 1089, 1156, 1225, 1296, 1369, 1444, 1521, 1600, 1681, 1764,
    1849, 1936, 2025, 2116, 2209, 2304, 2401, 2500, 2601, 2704, 2809, 2916,
    3025, 3136, 3249, 3364, 3481, 3600, 3721, 3844, 3969]

/-- The square table satisfies its defining function, entry by entry,
    closed by `decide` (encoding N). The function is the TRANSLATED
    source (`quad` above), not a hand-written formula. -/
theorem squares64_zert :
    konstZert squares64 (fun i v => v == quad i) = true := by
  decide

/-- Witness for `konstZert_mem`: all premises instantiated jointly at the
    square table -- the table, the translated function, the closed
    certificate, and entry 63 (`3969 = quad 63`). -/
theorem konstZert_mem_zeuge :
    (fun i v => v == quad i) 63 3969 = true :=
  konstZert_mem squares64_zert (j := 63) (v := 3969) rfl

/-- The certificate tied to the SYNTAX: with soundness the same check
    reads as values against evaluation of the source expression. -/
theorem squares64_aus_syntax :
    konstZert squares64
      (fun i v => v == quadSyntax.eval leerEnv leerFns i) = true := by
  have h : ∀ i, quadSyntax.eval leerEnv leerFns i = quad i :=
    quad_aus_syntax
  simp only [h]
  exact squares64_zert

/-- Joint witness for the soundness theorem: the probe point `7 ↦ 49`
    through evaluation of the syntax, together with the full 64-entry
    certificate over the translated function. The only binder `i` is
    instantiated; both conjuncts are used. -/
theorem quad_aus_syntax_zeuge :
    quadSyntax.eval leerEnv leerFns 7 = 49 ∧
      konstZert squares64 (fun i v => v == quad i) = true := by
  refine ⟨?_, ?_⟩ <;> decide

end Gabbro.Grammatik.Konstanten

/- CUTS: what is not proved.
   - Range attachment afterwards: `konstZert_mem` at
     `f := fun _ v => decide (v < bound)` yields every entry's range fact,
     but that instantiation is not stated as its own theorem here.
   - The printed `def quad` line versus `quad` above is held by the Rust
     exact-string test (`tests/konstanten.rs`), not by a theorem: a drift
     breaks the build on the Rust side. The same test holds the printed
     literal against `squares64`, so the `decide` closes over the
     checker's values.
   - No proved link between the checker's `i128` folder
     (`Umgebung::konst_wert`) and `KExpr.eval` on `Nat`: both compute the
     same operators on values that stay in `Nat`, and the two sides meet
     only at the shared numbers. A body the checker cannot evaluate
     yields no table and no certificate.
   - The printer refuses negation, `~`, wrap/saturate operators, floats,
     counts, built-ins and indirect calls; `KExpr` covers exactly the
     printable arms, so there is no syntax the printer accepts and `eval`
     does not -- but that correspondence is by construction, not a
     theorem.
   - No block fallback: at 64 entries the single `decide` is far below any
     cliff (the measurement closes 2048 the same way); larger tables
     re-measure before use.
-/

#print axioms Gabbro.Grammatik.Konstanten.konstZert_nil
#print axioms Gabbro.Grammatik.Konstanten.mem_zipIdx_aux
#print axioms Gabbro.Grammatik.Konstanten.mem_zipIdx_of_getElem?
#print axioms Gabbro.Grammatik.Konstanten.konstZert_mem
#print axioms Gabbro.Grammatik.Konstanten.squares64_zert
#print axioms Gabbro.Grammatik.Konstanten.konstZert_mem_zeuge
#print axioms Gabbro.Grammatik.Konstanten.quad_aus_syntax
#print axioms Gabbro.Grammatik.Konstanten.dreiPlusVier_aus_syntax
#print axioms Gabbro.Grammatik.Konstanten.konst_aus_syntax
#print axioms Gabbro.Grammatik.Konstanten.ruf_aus_syntax
#print axioms Gabbro.Grammatik.Konstanten.squares64_aus_syntax
#print axioms Gabbro.Grammatik.Konstanten.quad_aus_syntax_zeuge
