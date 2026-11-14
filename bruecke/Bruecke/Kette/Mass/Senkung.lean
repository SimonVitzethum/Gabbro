module
public import Grammatik.Parser.Stmt.LibraryFixtureProofs
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export
public section

/-! # Lowering a unit whose functions all declare a measure

`LibraryFixtureProofs.lowering_ok` assembles the lowering of a unit WITHOUT `decreases` clauses.
`lowering_ok_mass` is its counterpart for a unit where EVERY function declares one: each
exported tuple then has length one, so the cycle-length gate (`cycleLengths`) holds without
asking the call graph. Only witness modules import this module.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The per-function successes give the list success. -/
theorem lowerEach_ok (u : UProg) :
    ∀ fs : List (Fin u.fns.length),
      (∀ f ∈ fs, (lowerFnAt u f).toOption.isSome = true) → lowerEach u fs = .ok ()
  | [], _ => rfl
  | f :: fs, success => by
    rw [lowerEach, Gabbro.Grammatik.except_ok_get (ε := String)
      (α := EnsTy u f × RumpTy u f × ReqTy u f) (x := lowerFnAt u f)
      (success f (List.mem_cons_self ..))]
    exact lowerEach_ok u fs (fun g hg => success g (List.mem_cons_of_mem _ hg))

/-- The per-index successes give the success of the dependent collector. -/
theorem collect_ok : ∀ (n : Nat) (T : Fin n → Type)
    (get : (i : Fin n) → Except String (T i)),
    (∀ i, (get i).toOption.isSome = true) →
      (Measures.collect n T get).toOption.isSome = true
  | 0, _, _, _ => rfl
  | n + 1, T, get, success => by
    have head := Gabbro.Grammatik.except_ok_get (ε := String) (α := T 0)
      (x := get 0) (success 0)
    have tail := collect_ok n (fun i => T i.succ) (fun i => get i.succ)
      (fun i => success i.succ)
    have tailValue := Gabbro.Grammatik.except_ok_get (ε := String)
      (α := (i : Fin n) → T i.succ)
      (x := Measures.collect n (fun i => T i.succ) (fun i => get i.succ)) tail
    rw [Measures.collect, head]
    dsimp only [bind, Except.bind]
    rw [tailValue]
    rfl

/-- Every function's measure lowers: the export succeeds. -/
theorem lowerMeasures_ok (u : UProg)
    (h : ∀ f : Fin u.fns.length, (Measures.lowerAt u f).toOption.isSome = true) :
    (Measures.lowerMeasures u).toOption.isSome = true := by
  have collected := Gabbro.Grammatik.except_ok_get (ε := String)
    (α := (f : Fin u.fns.length) → Measures.At u f)
    (x := Measures.collect u.fns.length (Measures.At u) (Measures.lowerAt u))
    (collect_ok u.fns.length (Measures.At u) (Measures.lowerAt u) h)
  unfold Measures.lowerMeasures
  rw [collected]
  rfl

/-- Where every function declares a measure, every exported tuple has length one. -/
theorem mass_laenge_eins (u : UProg) (ex : Measures.Export u)
    (h : ∀ f : Fin u.fns.length, (fnAt u f).decreases.isSome = true)
    (f : Fin u.fns.length) : (ex.mass f).length = 1 := by
  have hs := ex.source f
  cases hd : (fnAt u f).decreases with
  | none =>
    have hf := h f
    rw [hd] at hf
    cases hf
  | some m =>
    simp only [Measures.SourceTuple, hd] at hs
    obtain ⟨c, hc, _⟩ := hs
    rw [hc]
    rfl

/-- **The lowering of a unit whose functions all declare a measure.** -/
theorem lowering_ok_mass (u : UProg) (noInvs : u.invs = []) (contracts : contractGate u = true)
    (functions : ∀ f : Fin u.fns.length, (lowerFnAt u f).toOption.isSome = true ∧
      (Measures.lowerAt u f).toOption.isSome = true ∧ (fnAt u f).decreases.isSome = true) :
    (lowerAllg u).toOption.isSome = true := by
  have measures := lowerMeasures_ok u (fun f => (functions f).2.1)
  let exported : Measures.Export u := (Measures.lowerMeasures u).toOption.get measures
  have measured : Measures.lowerMeasures u = .ok exported :=
    Gabbro.Grammatik.except_ok_get (ε := String) (α := Measures.Export u)
      (x := Measures.lowerMeasures u) measures
  have one : ∀ f, (exported.mass f).length = 1 :=
    mass_laenge_eins u exported (fun f => (functions f).2.2)
  have checked : ∀ P : Programm (declOf u),
      (Measures.checkedProgram u P).toOption.isSome = true := by
    intro P
    have lengths : Measures.cycleLengths u P exported.mass = true := by
      unfold Measures.cycleLengths
      apply List.all_eq_true.mpr
      intro f _
      apply List.all_eq_true.mpr
      intro g _
      rw [one f, one g]
      change (!zykS P (List.finRange u.fns.length) f g || true) = true
      exact Bool.or_true _
    unfold Measures.checkedProgram
    rw [measured]
    dsimp only
    split
    · rfl
    · contradiction
  have invs : lowerInvs u (List.finRange u.invs.length) = .ok () := by
    cases enumeration : List.finRange u.invs.length with
    | nil => rfl
    | cons i rest =>
      have length : u.invs.length = 0 := congrArg List.length noInvs
      have bound := i.isLt
      omega
  have each := lowerEach_ok u (List.finRange u.fns.length) (fun f _ => (functions f).1)
  unfold lowerAllg
  split
  · rename_i error failed
    rw [invs] at failed
    cases failed
  · split
    · rename_i error failed
      rw [each] at failed
      cases failed
    · split
      · exact checked _
      · contradiction

end Gabbro.Bruecke
