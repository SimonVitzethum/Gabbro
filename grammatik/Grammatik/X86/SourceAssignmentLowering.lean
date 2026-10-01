/-
  File:      Grammatik/X86/SourceAssignmentLowering.lean
  Subject:   Direct typed-source assignment to pilot machine code (lane 628).

  Lower the actually covered typed `Stmt.assignSlot` (an `.int lo hi` field
  admitted by the accepted `SourceMemory570` `repOk`, with its value
  expression in the accepted `ExpressionLowering599` `senkFrag` fragment)
  into generated pilot instructions (`prog ++ [store64]`), and prove the
  source `execStmt` world update matches the target `lauf` execution under
  the one representation map (`zahlWort`/`intWort` bridge). No second IR,
  no new interpreter, no source/checker/emitter edit.
-/
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.ScalarFloat
import Grammatik.X86.SourceMemory
import Grammatik.X86.ExpressionLowering

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Direct lowering of one admitted assignment: the value fragment lowered
    by `senkFrag` (599), followed by one `store64` through the admitted
    slot base register. `none` is the explicit unsupported-expression
    refusal; admission of the slot itself stays with `repOk` (570). -/
def senkAssign {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp base : Register) (disp : BitVec 32) :
    Option (List Befehl) :=
  match senkFrag abb e dst tmp with
  | some prog => some (prog ++ [Befehl.store64 base dst disp])
  | none => none

/-- VALUE BRIDGE: on a `repOk`-admitted nonnegative range below
    `2 ^ 64`, the modular expression word (`intWort`, reused from 599) is
    the representation word (`zahlWort`, reused from 570). Both bounds
    are used: `hLo`/`hHi` place the value for the modulo identity. -/
theorem intWort_zahlWort {lo hi : Int} (v : Zahl lo hi)
    (hLo : 0 ≤ lo) (hHi : hi < 2 ^ 64) :
    intWort v.n = zahlWort v := by
  obtain ⟨n, hlo, hhi⟩ := v
  have hnn : 0 ≤ n := by omega
  have hlt : n < 2 ^ 64 := by omega
  have hmod : n % (2 ^ 64 : Int) = n := by omega
  simp only [intWort, zahlWort, hmod]

/-- SHAPE: a successful fragment lowering extends with the slot store. -/
theorem senkAssign_ok {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (e : Expr D Γ Λ τ) (dst tmp base : Register) (disp : BitVec 32)
    (prog : List Befehl) (h : senkFrag abb e dst tmp = some prog) :
    senkAssign abb e dst tmp base disp =
      some (prog ++ [Befehl.store64 base dst disp]) := by
  unfold senkAssign
  rw [h]

/-- PLANTED REFUSAL (unsupported expression): multiplication has no
    lowering, so no assignment sequence is generated for it. -/
theorem senkAssign_verweigert_mul {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp base : Register) (disp : BitVec 32) :
    senkAssign abb
      (Expr.mul (Expr.lit (Γ := Γ) (Λ := Λ) 2) (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst tmp base disp = none := by
  unfold senkAssign
  rw [senkFrag_verweigert_mul]

/-- PLANTED REFUSAL (unsupported nesting): a depth-two add has no
    lowering, so no assignment sequence is generated for it. -/
theorem senkAssign_verweigert_tief {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}
    (abb : ∀ (τ : Ty), Var Γ τ → Register)
    (dst tmp base : Register) (disp : BitVec 32) :
    senkAssign abb
      (Expr.add
        (Expr.add (Expr.lit (Γ := Γ) (Λ := Λ) 1) (Expr.lit (Γ := Γ) (Λ := Λ) 2))
        (Expr.lit (Γ := Γ) (Λ := Λ) 3))
      dst tmp base disp = none := by
  unfold senkAssign
  rw [senkFrag_verweigert_tief]

/-- RANGE REFUSAL: a range starting below zero is refused by the checked
    admission (the modular word mapping would clip the negative part). -/
theorem assignRepOk_negativ_verweigert :
    repOk (.int (-5) 100) 8192 16 0 = false := by
  decide

/-- CODE-ALIAS REFUSAL at region level: a code extent overlapping the
    admitted slot extent shares bytes, so image/region separation refuses
    it (`regionDisjunkt = false`). -/
theorem assignCodeAlias_verweigert :
    regionDisjunkt
      (alsRegion { tab := 0, basis := 4096, len := 32, ausr := 8 })
      (alsRegion { tab := 1, basis := 4120, len := 16, ausr := 8 }) =
      false := by
  decide

/- CUTS:
     - Bridge and refusal surface only: value mapping agreement,
       lowering shape, unsupported-expression/nesting refusals,
       negative-range and code-alias region refusals.
     - No statement-level correspondence yet (`senkAssign_korrekt` OPEN).
     - Pilot integer fragment only; sums/FP/locks/calls outside.
     - Full source-to-final-loaded-bytes remains OPEN.
-/

#print axioms senkAssign
#print axioms intWort_zahlWort
#print axioms senkAssign_ok
#print axioms senkAssign_verweigert_mul
#print axioms senkAssign_verweigert_tief
#print axioms assignRepOk_negativ_verweigert
#print axioms assignCodeAlias_verweigert

end Gabbro.Grammatik.X86
