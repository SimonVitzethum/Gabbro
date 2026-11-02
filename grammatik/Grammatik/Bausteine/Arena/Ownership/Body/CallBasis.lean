module
public import Grammatik.Bausteine.Arena.Ownership.Body.Plan
@[expose] public section


/-! The whole call, on the ledger. From the caller's invariant and a fitting
plan: the callee's interface precondition holds at the handoff ledger of a
fresh activation; and from nothing but the callee's interface postcondition
the caller's invariant holds again after the return, with every consumed
origin dead and an owning result bound under a new origin. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-! ## 1. The handed handles -/

def movedHandles (g : Ghost) (ms : List (Option PassingMode)) (os : List (Option Nat)) : List Handle :=
  (List.range ms.length).filterMap fun u => match ms[u]?, os[u]? with
    | some (some .owned), some (some i) => g i
    | _, _ => none

def lentHandles (g : Ghost) (ms : List (Option PassingMode)) (os : List (Option Nat)) : List Handle :=
  (List.range ms.length).filterMap fun u => match ms[u]?, os[u]? with
    | some (some .borrowed), some (some i) => g i
    | _, _ => none

variable {g : Ghost} {ms : List (Option PassingMode)} {os : List (Option Nat)}

theorem mem_handles {m : PassingMode} {h : Handle}
    (hm : h ∈ (List.range ms.length).filterMap fun u => match ms[u]?, os[u]? with
      | some (some m'), some (some i) => if m' = m then g i else none
      | _, _ => none) :
    ∃ (u i : Nat), ms[u]? = some (some m) ∧ os[u]? = some (some i) ∧ g i = some h := by
  obtain ⟨u, _, hu⟩ := List.mem_filterMap.mp hm
  revert hu
  cases hmu : ms[u]? with
  | none => intro h; cases h
  | some mo =>
    cases mo with
    | none => intro h; cases h
    | some m' =>
      cases hou : os[u]? with
      | none => intro h; cases h
      | some o =>
        cases o with
        | none => intro h; cases h
        | some i =>
          intro hu
          by_cases he : m' = m
          · subst he; simp only [ite_true] at hu; exact ⟨u, i, hmu, hou, hu⟩
          · simp only [he, ↓reduceIte, reduceCtorEq] at hu

theorem mem_moved {h : Handle} (hm : h ∈ movedHandles g ms os) :
    ∃ (u i : Nat), ms[u]? = some (some PassingMode.owned) ∧ os[u]? = some (some i) ∧ g i = some h := by
  apply mem_handles (m := .owned)
  obtain ⟨u, hu, he⟩ := List.mem_filterMap.mp hm
  refine List.mem_filterMap.mpr ⟨u, hu, ?_⟩
  revert he
  cases ms[u]? with
  | none => intro h; cases h
  | some mo => cases mo with
    | none => intro h; cases h
    | some m => cases os[u]? with
      | none => cases m <;> intro h <;> cases h
      | some o => cases o with
        | none => cases m <;> intro h <;> cases h
        | some i => cases m <;> simp only [↓reduceIte, imp_self, reduceCtorEq]

theorem mem_lent {h : Handle} (hm : h ∈ lentHandles g ms os) :
    ∃ (u i : Nat), ms[u]? = some (some PassingMode.borrowed) ∧ os[u]? = some (some i) ∧ g i = some h := by
  apply mem_handles (m := .borrowed)
  obtain ⟨u, hu, he⟩ := List.mem_filterMap.mp hm
  refine List.mem_filterMap.mpr ⟨u, hu, ?_⟩
  revert he
  cases ms[u]? with
  | none => intro h; cases h
  | some mo => cases mo with
    | none => intro h; cases h
    | some m => cases os[u]? with
      | none => cases m <;> intro h <;> cases h
      | some o => cases o with
        | none => cases m <;> intro h <;> cases h
        | some i => cases m <;> simp only [reduceCtorEq, ↓reduceIte, imp_self]

theorem moved_of {u i : Nat} {h : Handle} (hmu : ms[u]? = some (some .owned)) (hou : os[u]? = some (some i))
    (hg : g i = some h) : h ∈ movedHandles g ms os := by
  refine List.mem_filterMap.mpr ⟨u, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hmu).1, ?_⟩
  simp only [hmu, hou, hg]

theorem lent_of {u i : Nat} {h : Handle} (hmu : ms[u]? = some (some .borrowed)) (hou : os[u]? = some (some i))
    (hg : g i = some h) : h ∈ lentHandles g ms os := by
  refine List.mem_filterMap.mpr ⟨u, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hmu).1, ?_⟩
  simp only [hmu, hou, hg]


end Gabbro.Grammatik.ArenaOwnership.Body
