/-
  File:      Grammatik/Gen/Text/Invers/Namen.lean
  Subject:   THE NAMES OF THE DELABORATOR ARE READ BACK UNIQUELY: `strEq` on two printed names of one kind is the
             equality of their numbers (`nVar a` names `nVar b` exactly when `a = b`, through the lexer's own number
             reading `lex_zahl_allein`), names of two kinds never meet (their first letters differ), and the
             elaborator's name lookups (`uParamNrAux`, `uTabNrAux`, `find?`) over a list of printed names find the
             position of the number.
-/
import Grammatik.Gen.Text.Delab

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Parser

theorem toString_nat_inj {a b : Nat} (h : (toString a).toList = (toString b).toList) : a = b := by
  have h' : toString a = toString b := String.toList_inj.1 h
  have ha := lex_zahl_allein a
  rw [h', lex_zahl_allein b] at ha
  simp at ha
  exact ha.symm

theorem nVar_toList (k : Nat) : (nVar k).toList = 'v' :: (toString k).toList := by
  simp only [nVar, String.toList_append]; rfl
theorem nTab_toList (k : Nat) : (nTab k).toList = 'T' :: (toString k).toList := by
  simp only [nTab, String.toList_append]; rfl
theorem nFeld_toList (k : Nat) : (nFeld k).toList = 'f' :: (toString k).toList := by
  simp only [nFeld, String.toList_append]; rfl
theorem nGlob_toList (k : Nat) : (nGlob k).toList = 'g' :: (toString k).toList := by
  simp only [nGlob, String.toList_append]; rfl
theorem nLock_toList (k : Nat) : (nLock k).toList = 'L' :: (toString k).toList := by
  simp only [nLock, String.toList_append]; rfl
theorem nReg_toList (k : Nat) : (nReg k).toList = 'r' :: (toString k).toList := by
  simp only [nReg, String.toList_append]; rfl
theorem nZeiger_toList (k : Nat) : (nZeiger k).toList = 'p' :: (toString k).toList := by
  simp only [nZeiger, String.toList_append]; rfl

/-- Two names of one kind: `strEq` is the equality of the numbers. -/
theorem strEq_kind {c : Char} {a b : Nat} {x y : String} (hx : x.toList = c :: (toString a).toList)
    (hy : y.toList = c :: (toString b).toList) : strEq x y = (a == b) := by
  unfold strEq
  rw [hx, hy]
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (c :: (toString a).toList = c :: (toString b).toList) := fun e =>
      h (toString_nat_inj (List.cons.inj e).2)
    rw [beq_eq_false_iff_ne.2 this, beq_eq_false_iff_ne.2 h]

/-- Two names whose first letters differ never meet. -/
theorem strEq_kopf {c d : Char} {r s : List Char} {x y : String} (hx : x.toList = c :: r)
    (hy : y.toList = d :: s) (h : c ≠ d) : strEq x y = false := by
  unfold strEq
  rw [hx, hy]
  simp [h]

@[simp] theorem strEq_nVar (a b : Nat) : strEq (nVar a) (nVar b) = (a == b) :=
  strEq_kind (nVar_toList a) (nVar_toList b)
@[simp] theorem strEq_nTab (a b : Nat) : strEq (nTab a) (nTab b) = (a == b) :=
  strEq_kind (nTab_toList a) (nTab_toList b)
@[simp] theorem strEq_nFeld (a b : Nat) : strEq (nFeld a) (nFeld b) = (a == b) :=
  strEq_kind (nFeld_toList a) (nFeld_toList b)
@[simp] theorem strEq_nGlob (a b : Nat) : strEq (nGlob a) (nGlob b) = (a == b) :=
  strEq_kind (nGlob_toList a) (nGlob_toList b)
@[simp] theorem strEq_nLock (a b : Nat) : strEq (nLock a) (nLock b) = (a == b) :=
  strEq_kind (nLock_toList a) (nLock_toList b)
@[simp] theorem strEq_nReg (a b : Nat) : strEq (nReg a) (nReg b) = (a == b) :=
  strEq_kind (nReg_toList a) (nReg_toList b)
@[simp] theorem strEq_nZeiger (a b : Nat) : strEq (nZeiger a) (nZeiger b) = (a == b) :=
  strEq_kind (nZeiger_toList a) (nZeiger_toList b)

@[simp] theorem strEq_nVar_nZeiger (a b : Nat) : strEq (nVar a) (nZeiger b) = false :=
  strEq_kopf (nVar_toList a) (nZeiger_toList b) (by decide)
@[simp] theorem strEq_nZeiger_nVar (a b : Nat) : strEq (nZeiger a) (nVar b) = false :=
  strEq_kopf (nZeiger_toList a) (nVar_toList b) (by decide)
@[simp] theorem strEq_nVar_nTab (a b : Nat) : strEq (nVar a) (nTab b) = false :=
  strEq_kopf (nVar_toList a) (nTab_toList b) (by decide)
@[simp] theorem strEq_nZeiger_nTab (a b : Nat) : strEq (nZeiger a) (nTab b) = false :=
  strEq_kopf (nZeiger_toList a) (nTab_toList b) (by decide)
@[simp] theorem strEq_nVar_nGlob (a b : Nat) : strEq (nVar a) (nGlob b) = false :=
  strEq_kopf (nVar_toList a) (nGlob_toList b) (by decide)
@[simp] theorem strEq_nZeiger_nGlob (a b : Nat) : strEq (nZeiger a) (nGlob b) = false :=
  strEq_kopf (nZeiger_toList a) (nGlob_toList b) (by decide)

/-- A name of the body scope: a variable `v{k}` or a function pointer `p{k}`. -/
def RumpfName (n : String) : Prop := (∃ k, n = nVar k) ∨ (∃ k, n = nZeiger k)

theorem strEq_rumpf_nTab {n : String} (h : RumpfName n) (b : Nat) : strEq n (nTab b) = false := by
  rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp

theorem strEq_rumpf_nGlob {n : String} (h : RumpfName n) (b : Nat) : strEq n (nGlob b) = false := by
  rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> simp

/-- A table or static name is no name of a body scope: the parameter lookup fails. -/
theorem uParamNrAux_fremd (ns : List String) (hn : ∀ n ∈ ns, RumpfName n) (k : Nat) (x : String)
    (hx : ∀ n ∈ ns, strEq n x = false) : ∃ e, Uebersetze.uParamNrAux ns k x = .error e := by
  induction ns generalizing k with
  | nil => exact ⟨_, rfl⟩
  | cons q rest ih =>
    simp only [Uebersetze.uParamNrAux]
    rw [hx q List.mem_cons_self]
    exact ih (fun n hm => hn n (List.mem_cons_of_mem _ hm)) (k + 1)
      (fun n hm => hx n (List.mem_cons_of_mem _ hm))

/-- `strEq` is string equality. -/
theorem strEq_eq (a b : String) : strEq a b = decide (a = b) := by
  unfold strEq
  by_cases h : a = b
  · subst h; simp
  · have : a.toList ≠ b.toList := fun e => h (String.toList_inj.1 e)
    rw [beq_eq_false_iff_ne.2 this]
    simp [h]

end Gabbro.Grammatik.Gen.Text