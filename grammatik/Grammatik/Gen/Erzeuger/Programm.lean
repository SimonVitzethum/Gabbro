/-
  File:      Grammatik/Gen/Erzeuger/Programm.lean
  Subject:   The generator of PROGRAMS (`Programm D`: per invariant its predicate, per function `requires`,
             `ensures`, a body that does not fall off, and the handler flag) and its COMPLETENESS
             (`genProg_vollst`): every program of size at most `m` is generated. A program is a family of
             terms over the finite index lists of the declaration, so `genPi` builds the families from the
             per-index choices.
-/
import Grammatik.Gen.Erzeuger.BlockVollst

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

variable {D : Deklaration} [Aufz D]

/-! ## Families over a finite index list -/

/-- All families `i ↦ x i` over the indices of a list, from the choices `L i` at each index. -/
def genPi {ι : Type} [DecidableEq ι] {X : ι → Type} (L : ∀ i, List (X i)) :
    (alle : List ι) → List (∀ i, i ∈ alle → X i)
  | [] => [fun _ h => absurd h (List.not_mem_nil)]
  | a :: as => (L a).flatMap fun x => (genPi L as).map fun f =>
      fun i h => if h' : i = a then h' ▸ x else f i ((List.mem_cons.1 h).resolve_left h')

/-- Completeness of `genPi`: a family whose every value is a choice is built. -/
theorem genPi_vollst {ι : Type} [DecidableEq ι] {X : ι → Type} {L : ∀ i, List (X i)} (g : ∀ i, X i) :
    ∀ (alle : List ι), (∀ i ∈ alle, g i ∈ L i) → (fun i _ => g i) ∈ genPi L alle := by
  intro alle
  induction alle with
  | nil =>
    intro _
    simp only [genPi, List.mem_singleton]
    funext i h
    exact absurd h List.not_mem_nil
  | cons a as ih =>
    intro h
    simp only [genPi, List.mem_flatMap, List.mem_map]
    refine ⟨g a, h a List.mem_cons_self, fun i _ => g i, ih (fun i hi => h i (List.mem_cons_of_mem _ hi)), ?_⟩
    funext i hi
    by_cases h' : i = a
    · subst h'; simp
    · simp [h']

/-! ## Size -/

/-- The sizes of the components, summed over the index lists. -/
def groesseProg (P : Programm D) : Nat :=
  (Aufz.inv.map fun i => groesseExpr (P.invariante i)).sum +
  (Aufz.fn.map fun f => groesseExpr (P.requires f) + groesseExpr (P.ensures f) + groesseEnd (P.rumpf f) +
    (if P.unterbricht f then 1 else 0)).sum

theorem le_summe {α : Type} {l : List α} {a : α} (f : α → Nat) (h : a ∈ l) : f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h; simp only [List.map_cons, List.sum_cons]; omega

/-! ## The generator -/

/-- **The generator of programs**: all programs of size at most `m`. -/
def genProg (m : Nat) : List (Programm D) :=
  (genPi (fun i => ofTy (genExpr m [] (invSicht D i)) .bool) Aufz.inv).flatMap fun inv =>
  (genPi (fun f => ofTy (genExpr m (D.params f) (Signatur.anfang D (D.signatur f))) .bool) Aufz.fn).flatMap
    fun req =>
  (genPi (fun f => ofTy (genExpr m (ErgCtx (D.params f) (D.erg f)) (vertragVon D f).ende) .bool) Aufz.fn).flatMap
    fun ens =>
  (genPi (fun f => (genRek (vertragVon D f) m).en false (D.params f) (Signatur.anfang D (D.signatur f)))
    Aufz.fn).flatMap fun rump =>
  (genPi (fun _ => [false, true]) Aufz.fn).map fun unt =>
    { invariante := fun i => inv i (Aufz.inv_mem i)
      requires := fun f => req f (Aufz.fn_mem f)
      ensures := fun f => ens f (Aufz.fn_mem f)
      rumpf := fun f => rump f (Aufz.fn_mem f)
      unterbricht := fun f => unt f (Aufz.fn_mem f) }

/-- **Completeness of the program generator**: every program of size at most `m` is generated. -/
theorem genProg_vollst (m : Nat) (P : Programm D) (h : groesseProg P ≤ m) : P ∈ genProg m := by
  have hi : ∀ i ∈ (Aufz.inv : List D.Inv), groesseExpr (P.invariante i) ≤ m := by
    intro i hi
    have := le_summe (fun i => groesseExpr (P.invariante i)) hi
    unfold groesseProg at h
    omega
  have hf : ∀ f ∈ (Aufz.fn : List D.Fn), groesseExpr (P.requires f) + groesseExpr (P.ensures f) +
      groesseEnd (P.rumpf f) + (if P.unterbricht f then 1 else 0) ≤ m := by
    intro f hf
    have := le_summe (fun f => groesseExpr (P.requires f) + groesseExpr (P.ensures f) + groesseEnd (P.rumpf f) +
      (if P.unterbricht f then 1 else 0)) hf
    unfold groesseProg at h
    omega
  unfold genProg
  simp only [List.mem_flatMap, List.mem_map]
  refine ⟨_, genPi_vollst (L := fun i => ofTy (genExpr m [] (invSicht D i)) .bool) P.invariante Aufz.inv
      (fun i hi' => mem_ofTy (genExpr_vollst m _ _ _ _ (hi i hi'))), ?_⟩
  refine ⟨_, genPi_vollst (L := fun f => ofTy (genExpr m (D.params f) (Signatur.anfang D (D.signatur f))) .bool)
      P.requires Aufz.fn (fun f hf' => mem_ofTy (genExpr_vollst m _ _ _ _ (by have := hf f hf'; omega))), ?_⟩
  refine ⟨_, genPi_vollst (L := fun f => ofTy (genExpr m (ErgCtx (D.params f) (D.erg f)) (vertragVon D f).ende) .bool)
      P.ensures Aufz.fn (fun f hf' => mem_ofTy (genExpr_vollst m _ _ _ _ (by have := hf f hf'; omega))), ?_⟩
  refine ⟨_, genPi_vollst (L := fun f => (genRek (vertragVon D f) m).en false (D.params f)
      (Signatur.anfang D (D.signatur f))) P.rumpf Aufz.fn
      (fun f hf' => (genRek_vollst (vertragVon D f) m).2.2 _ _ _ _ (by have := hf f hf'; omega)), ?_⟩
  refine ⟨_, genPi_vollst (L := fun _ => [false, true]) P.unterbricht Aufz.fn
      (fun f _ => by cases P.unterbricht f <;> simp), ?_⟩
  rfl

end Gabbro.Grammatik.Gen
