/-
  File:      Grammatik/Konstanten.lean
  Subject:   CONST CERTIFICATE FROM THE SOURCE (lane 121) -- the fragment
             of `const fn` bodies the checker prints to Lean, its `Nat`
             evaluation, and the soundness of the printed square function:
             evaluation of the SYNTAX equals the printed function, so the
             `List.all` certificate ties the values to the source.
-/

namespace Gabbro.Grammatik

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

/-! ## 1. Empty environments -/

/-- No named consts in scope: every name reads `0`. -/
def leerEnv : String → Nat := fun _ => 0

/-- No const fns in scope: every call reads `0`. -/
def leerFns : String → List Nat → Nat := fun _ _ => 0

/-! ## 2. The square function, from syntax to printed form -/

/-- The `quad` body as syntax: `i * i`. -/
def quadSyntax : KExpr := .bin .mul .param .param

/-- The PRINTED function: exactly what `konst_lean::funktion_lean` emits
    for the `quad` source (`def quad (i : Nat) : Nat := i * i`). -/
def quad (i : Nat) : Nat := i * i

/-- Soundness: evaluation of the syntax equals the printed function. -/
theorem quad_aus_syntax (i : Nat) :
    quadSyntax.eval leerEnv leerFns i = quad i := by
  simp only [quadSyntax, quad, KExpr.eval, KBinOp.eval]

/-! ## 3. The remaining fragment arms, one probe each -/

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
    `doppelt(doppelt(n))` with the printed `doppelt`. -/
def doppelt (n : Nat) : Nat := n + n

def doppeltFunktionen : String → List Nat → Nat
  | "doppelt", [n] => doppelt n
  | _, _ => 0

def vierfachSyntax : KExpr :=
  .ruf "doppelt" [.ruf "doppelt" [.param]]

theorem ruf_aus_syntax (i : Nat) :
    vierfachSyntax.eval leerEnv doppeltFunktionen i =
      doppelt (doppelt i) := by
  simp only [vierfachSyntax, doppelt, KExpr.eval, KExprList.eval,
    doppeltFunktionen]

/-! ## 4. The 64-entry square certificate over the PRINTED function -/

/-- The evaluated square table: `quad 0 .. quad 63`, as the checker
    folder computes them. Kept byte-identical to the printer output
    pinned by `crates/gabbro-check/tests/konstanten.rs`. -/
def quadTabelle : List Nat :=
  [0, 1, 4, 9, 16, 25, 36, 49, 64, 81, 100, 121, 144, 169, 196, 225, 256, 289, 324, 361, 400, 441, 484, 529, 576, 625, 676, 729, 784, 841, 900, 961, 1024, 1089, 1156, 1225, 1296, 1369, 1444, 1521, 1600, 1681, 1764, 1849, 1936, 2025, 2116, 2209, 2304, 2401, 2500, 2601, 2704, 2809, 2916, 3025, 3136, 3249, 3364, 3481, 3600, 3721, 3844, 3969]

/-- The certificate: every table value equals the PRINTED function at
    its index. Encoding N (`List.all` over bare `Nat`, closed by
    `decide`); the pair order is `(value, index)` as `List.zipIdx`
    yields it. -/
def quadPruefe : Bool :=
  List.all quadTabelle.zipIdx (fun (v, i) => v == quad i)

/-- The certificate holds, by computation. -/
theorem quadPruefe_holds : quadPruefe = true := by decide

/-- The certificate tied to the SYNTAX: with soundness the same check
    reads as values against evaluation of the source expression. -/
theorem quadTabelle_aus_syntax :
    List.all quadTabelle.zipIdx
      (fun (v, i) => v == quadSyntax.eval leerEnv leerFns i) = true := by
  have h : ∀ i, quadSyntax.eval leerEnv leerFns i = quad i :=
    quad_aus_syntax
  simp only [h]
  exact quadPruefe_holds

/-- Joint witness for the soundness theorem: the probe point `7 ↦ 49`
    through evaluation of the syntax, together with the full 64-entry
    certificate. The only binder `i` is instantiated; both conjuncts
    are used. -/
theorem quad_aus_syntax_zeuge :
    quadSyntax.eval leerEnv leerFns 7 = 49 ∧ quadPruefe = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-!
CUTS:
- The table `quadTabelle` is hand-copied from the printer output; only
  the Rust test (`konstanten.rs`, exact string match) checks that the
  printer still emits exactly these bytes. A drift between the two is
  loud on the Rust side, silent here.
- No proved link between the checker's `i128` folder (`Umgebung.auswerten`)
  and `KExpr.eval` on `Nat`: both compute the same operators on values
  that stay in `Nat`, and the two sides meet only at the shared numbers
  (the Rust test evaluates via the checker, Lean checks via `decide`).
  A body the checker cannot evaluate yields no table and no certificate.
- The printer refuses negation, `~`, wrap/saturate operators, floats,
  counts, built-ins and indirect calls (`None`); `KExpr` covers exactly
  the printable arms, so there is no syntax the printer accepts and
  `eval` does not -- but that correspondence is by construction, not a
  theorem.
-/

#print axioms quad_aus_syntax
#print axioms dreiPlusVier_aus_syntax
#print axioms konst_aus_syntax
#print axioms ruf_aus_syntax
#print axioms quadPruefe_holds
#print axioms quadTabelle_aus_syntax
#print axioms quad_aus_syntax_zeuge

end Gabbro.Grammatik
