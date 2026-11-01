import Grammatik.Parser.Elab.ExportRelations

namespace Gabbro.Grammatik.Parser.ExportPreservation
open Uebersetze UebersetzeAllg UebersetzeAllg2

/-- All six existing string comparisons retain their actual maxima and byte terms.
    The IR emitter decides representation support; no scalar ABI is selected here. -/
theorem strings_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty)
    (a b : USide) (n m : Nat) (x : Expr (declOf u) Γ Λ (.str n)) (y : Expr (declOf u) Γ Λ (.str m))
    (gate : u.exportGate = .ok ())
    (first : lowWertE u Γ Λ fn er a = .ok ⟨.str n, x⟩)
    (last : lowWertE u Γ Λ fn er b = .ok ⟨.str m, y⟩) :
    lowCmp u Γ Λ fn er "==" a b = .ok (.strEq x y) ∧
    lowCmp u Γ Λ fn er "!=" a b = .ok (.not (.strEq x y)) ∧
    lowCmp u Γ Λ fn er "<" a b = .ok (.strLt x y) ∧
    lowCmp u Γ Λ fn er "<=" a b = .ok (.or (.strLt x y) (.strEq x y)) ∧
    lowCmp u Γ Λ fn er ">" a b = .ok (.strLt y x) ∧
    lowCmp u Γ Λ fn er ">=" a b = .ok (.or (.strLt y x) (.strEq x y)) := by
  simp [lowCmp, first, last, gate, bind, Except.bind, pure, Except.pure]

/-- Every successful string comparison retains the original unit duty check. -/
theorem strings_gate (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty)
    (op : String) (a b : USide) (n m : Nat)
    (x : Expr (declOf u) Γ Λ (.str n)) (y : Expr (declOf u) Γ Λ (.str m))
    (first : lowWertE u Γ Λ fn er a = .ok ⟨.str n, x⟩)
    (last : lowWertE u Γ Λ fn er b = .ok ⟨.str m, y⟩)
    (value : Expr (declOf u) Γ Λ .bool) (success : lowCmp u Γ Λ fn er op a b = .ok value) :
    u.exportGate = .ok () := by
  cases gate : u.exportGate with
  | error error => simp only [lowCmp, first, last, gate, bind, Except.bind] at success; contradiction
  | ok unit => cases unit; rfl

/-- Equality and order are the canonical byte/length relations, with both operand footprints. -/
theorem strings_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {n m : Nat}
    (x : Expr D Γ Λ (.str n)) (y : Expr D Γ Λ (.str m))
    (entry state : World D) (env : Env D Γ) :
    eval entry (.strEq x y) state env = strEqW (eval entry x state env) (eval entry y state env) ∧
    eval entry (.strLt x y) state env = strLtW (eval entry x state env) (eval entry y state env) ∧
    (Expr.strEq x y).orte = x.orte ++ y.orte ∧ (Expr.strLt x y).orte = x.orte ++ y.orte :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Reference comparison keeps the same region in its type and consumes the original-source
    duty gate. It grants no dereference or arithmetic operation. -/
theorem references_lower (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (er : Option Ty)
    (a b : USide) (region : Nat) (x y : Expr (declOf u) Γ Λ (.ref region))
    (gate : u.exportGate = .ok ())
    (first : lowWertE u Γ Λ fn er a = .ok ⟨.ref region, x⟩)
    (last : lowWertE u Γ Λ fn er b = .ok ⟨.ref region, y⟩) :
    lowCmp u Γ Λ fn er "==" a b = .ok (.refEq x y) ∧
    lowCmp u Γ Λ fn er "!=" a b = .ok (.not (.refEq x y)) := by
  simp [lowCmp, first, last, gate, bind, Except.bind, pure, Except.pure]

/-- Canonical reference equality compares cell identity within the already equal region. -/
theorem references_meaning {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {region : Nat}
    (x y : Expr D Γ Λ (.ref region)) (entry state : World D) (env : Env D Γ) :
    eval entry (.refEq x y) state env = decide ((eval entry x state env).zelle = (eval entry y state env).zelle) ∧
    (Expr.refEq x y).orte = x.orte ++ y.orte := ⟨rfl, rfl⟩

def referenceFunction : UFn := {name := "same", params := [("a", .ref 0), ("b", .ref 0)], kinds := [.ref 0, .ref 0], res := none, held := [], puts := [], gives := [], body := [], ret := .empty}

/-- Two genuine reference variables in one region; this does not supply a provider binding. -/
theorem references_lower_zeuge :
    (lowCmp relationUnit [.ref 0, .ref 0] [] referenceFunction none "==" (.param "a") (.param "b")).toOption.isSome = true ∧
    (lowCmp relationUnit [.ref 0, .ref 0] [] referenceFunction none "!=" (.param "a") (.param "b")).toOption.isSome = true := ⟨rfl, rfl⟩

/-- Unequal lengths and distinct bytes exercise both string relations. -/
theorem strings_lower_zeuge :
    (lowCmp relationUnit [] [] relationFunction none "<" (.text []) (.text [65])).toOption.isSome = true ∧
    (lowCmp relationUnit [] [] relationFunction none ">=" (.text [66]) (.text [65])).toOption.isSome = true := ⟨rfl, rfl⟩

/-- Concrete distinct and equal cell identities make reference comparison nonvacuous.
    These are mathematical comparison inputs, not a source provider realization. -/
theorem references_meaning_zeuge (entry state : World (declOf relationUnit)) :
    let first : Expr (declOf relationUnit) [.ref 0, .ref 0] [] (.ref 0) := .var .here
    let second : Expr (declOf relationUnit) [.ref 0, .ref 0] [] (.ref 0) := .var (.there .here)
    let equal : Env (declOf relationUnit) [.ref 0, .ref 0] := .cons (Val.vonZelle 0) (.cons (Val.vonZelle 0) .nil)
    let distinct : Env (declOf relationUnit) [.ref 0, .ref 0] := .cons (Val.vonZelle 0) (.cons (Val.vonZelle 1) .nil)
    eval entry (.refEq first second) state equal = true ∧
    eval entry (.refEq first second) state distinct = false := ⟨rfl, rfl⟩

end Gabbro.Grammatik.Parser.ExportPreservation
