module

public import Core.Ast.Semantik.Elaborierung
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

/-- Executing the elaborated instructions of an expression leaves its statically
    inferred type in the destination slot and preserves every lower temporary. -/
theorem expr_ergebnis_typ (slot : Nat) (tree : Expr scope type) (frame : Rahmen) :
    let out := (expr slot tree).code.foldl (fun f b => b.auswerten f) frame
    (out.temp slot).typ = type ∧ ∀ i, i < slot → out.temp i = frame.temp i := by
  induction tree generalizing slot frame with
  | lit value =>
    change (Function.update frame.temp slot (Ganzzahl.literal value) slot).typ = _ ∧
      ∀ i, i < slot → Function.update frame.temp slot (Ganzzahl.literal value) i = frame.temp i
    refine ⟨?_, fun i lower => Function.update_of_ne (Nat.ne_of_lt lower) _ _⟩
    rw [Function.update_self]
    rfl
  | @binary lo₁ hi₁ lo₂ hi₂ op left right leftIH rightIH =>
    simp only [expr, Fragment.anhaengen, Fragment.einzel, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    let l := (expr slot left).code.foldl (fun f b => b.auswerten f) frame
    let r := (expr (slot + 1) right).code.foldl (fun f b => b.auswerten f) l
    obtain ⟨leftType, leftPreserves⟩ := leftIH slot frame
    obtain ⟨rightType, rightPreserves⟩ := rightIH (slot + 1) l
    change (Function.update r.temp slot (Ganzzahl.binaer op (r.temp slot) (r.temp (slot + 1))) slot).typ =
        op.result lo₁ hi₁ lo₂ hi₂ ∧
      ∀ i, i < slot →
        Function.update r.temp slot (Ganzzahl.binaer op (r.temp slot) (r.temp (slot + 1))) i = frame.temp i
    refine ⟨?_, ?_⟩
    · rw [Function.update_self, rightPreserves slot (Nat.lt_succ_self slot)]
      obtain ⟨leftLo, leftHi⟩ := Ty.int.inj leftType
      obtain ⟨rightLo, rightHi⟩ := Ty.int.inj rightType
      change op.result (l.temp slot).lo (l.temp slot).hi (r.temp (slot + 1)).lo (r.temp (slot + 1)).hi = _
      change (l.temp slot).lo = lo₁ at leftLo
      change (l.temp slot).hi = hi₁ at leftHi
      change (r.temp (slot + 1)).lo = lo₂ at rightLo
      change (r.temp (slot + 1)).hi = hi₂ at rightHi
      rw [leftLo, leftHi, rightLo, rightHi]
    · intro i lower
      exact (Function.update_of_ne (Nat.ne_of_lt lower) _ _).trans
        ((rightPreserves i (Nat.lt_succ_of_lt lower)).trans (leftPreserves i lower))

end Gabbro.Core.Ast.Semantik
