/-
  File:      Grammatik/X86/ExpressionLowering.lean
  Subject:   Generic direct typed-source expression to pilot machine code.

  Lane 599: lower the actual typed source AST (`Syntax.Expr` over `Ty.int`
  ranges, `Semantik.eval` over `Zahl`) to canonical pilot `Befehl`
  lists (`Codec.encode`, `Ausfuehrung.schritt`, `Byteschritt` fetch),
  with NO second SSA IR and no new source interpreter. Covered fragment:
  integer literals, integer variables, and one bounded ADD/SUB level over
  atomic operands; every other form refuses with `none`. Environment
  representation (`EnvRepr`), register freshness (`Frisch`) and the
  signed-64 representation bounds are explicit checkable premises.
  No source checker, Spec, goal or friend-reserved optimiser file is touched.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.FlagBeweis
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Modular integer-to-word conversion: `n mod 2^64` as a word.
    Same shape as `ScalarFloat.intWort`; the signed reading is `sint`. -/
def intWort (n : Int) : Wort := BitVec.ofNat 64 (n % (2 ^ 64 : Int)).toNat

/-- Explicit checkable environment representation: every integer variable
    of the context reads, in the pre-state register file, the modular word
    of its actual source value. No Rust-produced AST is trusted: `ρ.get`
    is the single source model. -/
def EnvRepr {D : Deklaration} {Γ : Ctx} (ρ : Env D Γ) (regs : Register → Wort)
    (abb : ∀ (τ : Ty), Var Γ τ → Register) : Prop :=
  ∀ (lo hi : Int) (x : Var Γ (.int lo hi)),
    regs (abb _ x) = intWort (ρ.get x).n

/-- Register freshness: no source variable lives in the two working
    registers (pre-state aliases are refused by premise, not renamed away),
    and the two working registers differ (else `add dst dst` doubles). -/
def Frisch {Γ : Ctx} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp : Register) : Prop :=
  (∀ (τ : Ty) (x : Var Γ τ), abb τ x ≠ dst ∧ abb τ x ≠ tmp) ∧ dst ≠ tmp

/-- Atom lowering: literals and variables lower to one instruction;
    every other integer form refuses with `none`. -/
def senkAtom {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ (.int lo hi)) (dst : Register) : Option (List Befehl) :=
  match e with
  | .lit n => some [.movImm64 dst (intWort n)]
  | .var x => some [.movReg64 dst (abb _ x)]
  | _ => none

/-- Fragment lowering: atoms as above, plus ONE bounded ADD/SUB level over
    atomic operands. Deeper nesting refuses (the atom lowering says `none`),
    as does every non-arithmetic form. No new IR is built: the result is a
    canonical `Befehl` list. -/
def senkFrag {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ (.int lo hi)) (dst tmp : Register) : Option (List Befehl) :=
  match e with
  | .lit n => some [.movImm64 dst (intWort n)]
  | .var x => some [.movReg64 dst (abb _ x)]
  | .add a b =>
    match senkAtom abb a dst, senkAtom abb b tmp with
    | some pa, some pb => some (pa ++ pb ++ [.addReg64 dst tmp])
    | _, _ => none
  | .sub a b =>
    match senkAtom abb a dst, senkAtom abb b tmp with
    | some pa, some pb => some (pa ++ pb ++ [.subReg64 dst tmp])
    | _, _ => none
  | _ => none

/-- Shape: literals lower to one immediate move. -/
theorem senkFrag_lit {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (n : Int) (dst tmp : Register) :
    senkFrag abb (Expr.lit (Γ := Γ) (Λ := Λ) n) dst tmp =
      some [.movImm64 dst (intWort n)] := rfl

/-- Shape: variables lower to one register move from their mapped register. -/
theorem senkFrag_var {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (x : Var Γ (.int lo hi)) (dst tmp : Register) :
    senkFrag abb (Expr.var (Λ := Λ) x) dst tmp =
      some [.movReg64 dst (abb _ x)] := rfl

/-- Shape: a bounded ADD over two lowered atoms. -/
theorem senkFrag_add {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (dst tmp : Register) (pa pb : List Befehl)
    (ha : senkAtom abb a dst = some pa) (hb : senkAtom abb b tmp = some pb) :
    senkFrag abb (Expr.add a b) dst tmp =
      some (pa ++ pb ++ [.addReg64 dst tmp]) := by
  simp only [senkFrag, ha, hb]

/-- Shape: a bounded SUB over two lowered atoms. -/
theorem senkFrag_sub {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    {l1 h1 l2 h2 : Int} (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2))
    (dst tmp : Register) (pa pb : List Befehl)
    (ha : senkAtom abb a dst = some pa) (hb : senkAtom abb b tmp = some pb) :
    senkFrag abb (Expr.sub a b) dst tmp =
      some (pa ++ pb ++ [.subReg64 dst tmp]) := by
  simp only [senkFrag, ha, hb]

/-- PLANTED REFUSAL: multiplication is outside the fragment. -/
theorem senkFrag_verweigert_mul {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (dst tmp : Register) :
    senkFrag abb
      (Expr.mul (Expr.lit (Γ := Γ) (Λ := Λ) 2) (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst tmp = none := rfl

/-- PLANTED REFUSAL: a nested ADD (depth two) is outside the fragment. -/
theorem senkFrag_verweigert_tief {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register) (dst tmp : Register) :
    senkFrag abb
      (Expr.add
        (Expr.add (Expr.lit (Γ := Γ) (Λ := Λ) 1) (Expr.lit (Γ := Γ) (Λ := Λ) 2))
        (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst tmp = none := rfl

/-- MODULAR HOMOMORPHISM (add): the word sum is the exact sum wrapped.
    Overflow is therefore never silent in the statement: the main theorem
    equates the register with `intWort` of the exact source value. -/
theorem intWort_add (a b : Int) :
    intWort a + intWort b = intWort (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [intWort, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- MODULAR HOMOMORPHISM (sub): the word difference is the exact one wrapped. -/
theorem intWort_sub (a b : Int) :
    intWort a - intWort b = intWort (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [intWort, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- SIGNED ROUNDTRIP: an in-range integer survives the modular conversion
    with its signed reading intact. Out-of-range values wrap (honest
    `bmod` behaviour); the overflow-bound theorem names when that happens. -/
theorem intWort_sint (n : Int) (hlo : -(2 ^ 63 : Int) ≤ n) (hhi : n < 2 ^ 63) :
    sint (intWort n) = n := by
  unfold sint intWort
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat]
  have hnn : 0 ≤ n % (2 ^ 64 : Int) := by omega
  have hlt : (n % (2 ^ 64 : Int)).toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt, Int.toNat_of_nonneg hnn]
  by_cases hn : 0 ≤ n
  · have hv : n % (2 ^ 64 : Int) = n := by omega
    rw [hv]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  · have hv : n % (2 ^ 64 : Int) = n + 2 ^ 64 := by omega
    rw [hv]
    have hb := bmod_high (n + 2 ^ 64) (by omega) (by omega)
    omega

/- CUTS:
    Conversion homomorphism (`intWort_add/sub`), the signed roundtrip
    (`intWort_sint`), the lowering-correctness theorems, the overflow-bound
    theorem and the fetched-byte witness are not proved yet.
    Unsupported expression forms refuse with `none` (two planted refusals).
-/

end Gabbro.Grammatik.X86
