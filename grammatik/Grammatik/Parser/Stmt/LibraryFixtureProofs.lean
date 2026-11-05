module

public import Grammatik.Logik.Vertraege.Uebersetzung
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest2a
import all Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Export

public section

namespace Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs

open Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

-- Each computed phase supplies the next phase's concrete canonical input. The
-- public getD definitions are retained, but success never follows from a default.
theorem certifyPhases (characters : List Char) (call : SLibraryCall)
    (retained : List SItemTief → Prop)
    (phases : ∃ tokens items members library unit,
      lexL characters = .ok tokens ∧ parseTopTief tokens = .ok items ∧
      Aufloesung.loeseL (Aufloesung.quelle items) [] items = members ∧ retained members ∧
      libraryDecl members call = .ok library ∧
      elabU (pre108 (translatorItems members library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true) :
    let tokens := (lexL characters).toOption.getD []
    let items := (parseTopTief tokens).toOption.getD []
    let members := Aufloesung.loeseL (Aufloesung.quelle items) [] items
    lexL characters = .ok tokens ∧ parseTopTief tokens = .ok items ∧ retained members ∧
      ∃ library unit, libraryDecl members call = .ok library ∧
        elabU (pre108 (translatorItems members library)) = .ok unit ∧
        (lowerAllg unit).toOption.isSome = true := by
  obtain ⟨tokens, items, members, library, unit, lexed, parsed, resolved, kept,
    found, elaborated, lowered⟩ := phases
  dsimp only
  have tokenEq : (lexL characters).toOption.getD [] = tokens := by rw [lexed]; rfl
  rw [tokenEq]
  have itemEq : (parseTopTief tokens).toOption.getD [] = items := by rw [parsed]; rfl
  rw [itemEq, resolved]
  exact ⟨lexed, parsed, kept, library, unit, found, elaborated, lowered⟩

theorem lowerFromPhases (members : List SItemTief) (call : SLibraryCall)
    (present : (libraryDecl members call).toOption.isSome = true)
    (phases : ∃ library unit, libraryDecl members call = .ok library ∧
      elabU (pre108 (translatorItems members library)) = .ok unit ∧
      (lowerAllg unit).toOption.isSome = true) :
    (lowerAllg ((elabU (pre108 (translatorItems members
      ((libraryDecl members call).toOption.get present)))).toOption.getD
        { tabs := [], locks := [], fns := [] })).toOption.isSome = true := by
  obtain ⟨library, unit, found, elaborated, lowered⟩ := phases
  have selected : (libraryDecl members call).toOption.get present = library := by
    exact (Except.ok.inj (found.symm.trans (except_ok_get present))).symm
  rw [selected, elaborated]
  exact lowered

/-- Assemble the actual per-function successes through the existing list producer. -/
private theorem lowerEach_certified (u : Uebersetze.UProg) :
    ∀ fs : List (Fin u.fns.length),
      (∀ f ∈ fs, (lowerFnAt u f).toOption.isSome = true) → lowerEach u fs = .ok ()
  | [], _ => rfl
  | f :: fs, success => by
    rw [lowerEach, Gabbro.Grammatik.except_ok_get (ε := String)
      (α := EnsTy u f × RumpTy u f × ReqTy u f) (x := lowerFnAt u f)
      (success f (List.mem_cons_self ..))]
    exact lowerEach_certified u fs (fun g hg => success g (List.mem_cons_of_mem _ hg))

/-- Success follows the canonical dependent collector without reducing a concrete unit
    underneath its indexed motive. Every entry is supplied by its actual producer. -/
private theorem collect_certified : ∀ (n : Nat) (T : Fin n → Type)
    (get : (i : Fin n) → Except String (T i)),
    (∀ i, (get i).toOption.isSome = true) →
      (Measures.collect n T get).toOption.isSome = true
  | 0, _, _, _ => rfl
  | n + 1, T, get, success => by
    have head := Gabbro.Grammatik.except_ok_get (ε := String) (α := T 0)
      (x := get 0) (success 0)
    have tail := collect_certified n (fun i => T i.succ) (fun i => get i.succ)
      (fun i => success i.succ)
    have tailValue := Gabbro.Grammatik.except_ok_get (ε := String)
      (α := (i : Fin n) → T i.succ)
      (x := Measures.collect n (fun i => T i.succ) (fun i => get i.succ)) tail
    rw [Measures.collect, head]
    dsimp only [bind, Except.bind]
    rw [tailValue]
    rfl

private theorem absent_measures (u : Uebersetze.UProg)
    (absent : ∀ f : Fin u.fns.length, (fnAt u f).decreases = none) :
    (Measures.lowerMeasures u).toOption.isSome = true := by
  have entries := collect_certified u.fns.length (fun f => Measures.At u f)
    (fun f => Measures.lowerAt u f) (fun f => by
      unfold Measures.lowerAt
      split
      · rfl
      · rename_i source selected
        rw [absent f] at selected
        cases selected)
  have collected := Gabbro.Grammatik.except_ok_get (ε := String)
    (α := (f : Fin u.fns.length) → Measures.At u f)
    (x := Measures.collect u.fns.length (Measures.At u) (Measures.lowerAt u)) entries
  unfold Measures.lowerMeasures
  rw [collected]
  rfl

/-- Assemble the unchanged lowering from its actual component certificates. The
    measure gate sees empty tuples at every function, including recursive edges. -/
theorem lowering_ok (u : UProg) (noInvs : u.invs = []) (contracts : contractGate u = true)
    (functions : ∀ f : Fin u.fns.length,
      (lowerFnAt u f).toOption.isSome = true ∧ (fnAt u f).decreases = none) :
    (lowerAllg u).toOption.isSome = true := by
  have measures := absent_measures u (fun f => (functions f).2)
  let exported : Measures.Export u := (Measures.lowerMeasures u).toOption.get measures
  have measured : Measures.lowerMeasures u = .ok exported :=
    Gabbro.Grammatik.except_ok_get (ε := String) (α := Measures.Export u)
      (x := Measures.lowerMeasures u) measures
  have empty : ∀ f, exported.mass f = [] :=
    fun f => Measures.lowerMeasures_absent u exported f ((functions f).2)
  have checked : ∀ P : Programm (declOf u),
      (Measures.checkedProgram u P).toOption.isSome = true := by
    intro P
    have lengths : Measures.cycleLengths u P exported.mass = true := by
      unfold Measures.cycleLengths
      apply List.all_eq_true.mpr
      intro f _
      apply List.all_eq_true.mpr
      intro g _
      rw [empty f, empty g]
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
  have each := lowerEach_certified u (List.finRange u.fns.length) (fun f _ => (functions f).1)
  have lowered : (lowerAllg u).toOption.isSome = true := by
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
  exact lowered

end Gabbro.Grammatik.Uebersetzung.LibraryFixtureProofs
