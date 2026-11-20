module
public import Bruecke.Anweisung.Lokal.Umfang
public import Bruecke.Anweisung.Lokal.Namen
@[expose] public section

/-!
# Positional local-state relation

Every active entry is related, including an outer entry hidden by a source name. The
identifier list is independent of source spelling and has no duplicates. Scope exit
therefore only removes the first identifier and needs no equality about source names.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

/-- The source scope and the Body identifiers have exactly the same positions. -/
structure PositionalLRel {D : Deklaration} {Γ : Ctx} (fn : UFn) (ids : List String)
    (sh : Nat) (ρ : Env D Γ) (β : Gabbro.Body.Binding) : Prop where
  length : ids.length = fn.params.length
  distinct : ids.Nodup
  values : ∀ j id, ids[j]? = some id → β id = nthVal ρ (sh + j)

namespace PositionalLRel

/-- The existing expression simulation consumes the visible projection of the full relation. -/
theorem visible {D : Deklaration} {Γ : Ctx} {fn : UFn} {ns : BodyNames} {sh : Nat}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ns.active sh ρ β) :
    LRel fn sh ρ (ns.visible fn β) := by
  intro p j hj
  have hlt : j < ns.active.length := by
    rw [h.length]
    exact paramPos_lt fn.params p j hj
  have hid : ns.active[j]? = some ns.active[j] := List.getElem?_eq_getElem hlt
  show (match ns.lookup fn p with | some id => β id | none => β p) = _
  rw [BodyNames.lookup, hj]
  dsimp only
  rw [hid]
  exact h.values j _ hid

/-- Resolve the visible source entry, then read its own Body identifier. -/
theorem lookup {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String} {sh : Nat}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ids sh ρ β)
    {x : String} {j : Nat} (hj : paramPos fn.params x = .ok j) :
    ∃ id, ids[j]? = some id ∧ β id = nthVal ρ (sh + j) := by
  have hlt : j < ids.length := by
    rw [h.length]
    exact paramPos_lt fn.params x j hj
  refine ⟨ids[j], ?_, ?_⟩
  · exact List.getElem?_eq_getElem hlt
  · exact h.values j _ (List.getElem?_eq_getElem hlt)

/-- Push one identifier; source shadowing imposes no condition. -/
theorem push {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ids 0 ρ β)
    (x id : String) (w : Int × Int) (hi : id ∉ ids) {τ : Ty} (v : Wert D τ) :
    PositionalLRel (fn.mitBindung x w) (id :: ids) 0 (Env.cons v ρ)
      (Gabbro.Body.bindLocal β id (valOf τ v)) := by
  refine ⟨congrArg Nat.succ h.length, List.nodup_cons.mpr ⟨hi, h.distinct⟩, ?_⟩
  intro j other hj
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    subst other
    exact Gabbro.Body.bindLocal_here β id (valOf τ v)
  | succ j =>
    have hj' : ids[j]? = some other := hj
    have hne : other ≠ id := by
      intro he
      apply hi
      rw [← he]
      exact List.mem_of_getElem? hj'
    rw [Gabbro.Body.bindLocal_elsewhere _ _ _ _ hne]
    simpa only [Nat.zero_add, nthVal_cons_succ] using h.values j other hj'

/-- Scope exit restores all outer entries, including hidden entries, without an equality premise. -/
theorem tail {D : Deklaration} {Γ : Ctx} {τ : Ty} {fn : UFn} {ids : List String}
    {id x : String} {w : Int × Int} {ρ : Env D (τ :: Γ)} {β : Gabbro.Body.Binding}
    (h : PositionalLRel (fn.mitBindung x w) (id :: ids) 0 ρ β) :
    PositionalLRel fn ids 0 ρ.tail β := by
  refine ⟨Nat.succ.inj h.length, (List.nodup_cons.mp h.distinct).2, ?_⟩
  intro j other hj
  have hv := h.values (j + 1) other (show (id :: ids)[j + 1]? = some other from hj)
  cases ρ with
  | cons v rest =>
    simpa only [Nat.zero_add, nthVal_cons_succ, Env.tail] using hv

/-- Updating the first-match position preserves every other entry, including hidden outers. -/
theorem set {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ids 0 ρ β)
    {j : Nat} {id : String} (hid : ids[j]? = some id) {τ : Ty}
    (var : Var Γ τ) (hv : lowVar Γ j τ = .ok var) (v : Wert D τ) :
    PositionalLRel fn ids 0 (ρ.set var v) (Gabbro.Body.bindLocal β id (valOf τ v)) := by
  refine ⟨h.length, h.distinct, ?_⟩
  intro k other hk
  rw [Nat.zero_add, nthVal_set Γ j τ var ρ v k hv]
  by_cases he : k = j
  · subst k
    have hn : other = id := Option.some.inj (hk.symm.trans hid)
    subst other
    rw [Gabbro.Body.bindLocal_here, if_pos rfl]
  · have hne : other ≠ id := by
      intro hn
      have hlt : k < ids.length := (List.getElem?_eq_some_iff.mp hk).1
      apply he
      apply h.distinct.eq_of_getElem?_eq hlt
      rw [hk, hid, hn]
    rw [if_neg he, Gabbro.Body.bindLocal_elsewhere _ _ _ _ hne]
    simpa only [Nat.zero_add] using h.values k other hk

/-- Declared entry names are distinct, so their visible relation covers every position. -/
theorem start {D : Deklaration} {Γ : Ctx} {fn : UFn} {sh : Nat} {ρ : Env D Γ}
    {β : Gabbro.Body.Binding} (hN : NamenEindeutig fn) (h : LRel fn sh ρ β) :
    PositionalLRel fn (BodyNames.start fn).active sh ρ β := by
  refine ⟨(by simp only [BodyNames.start, List.length_map]), hN, ?_⟩
  intro j id hid
  change (fn.params.map (·.1))[j]? = some id at hid
  rw [List.getElem?_map] at hid
  cases hj : fn.params[j]? with
  | none => rw [hj] at hid; cases hid
  | some q =>
    rw [hj] at hid
    simp only [Option.map_some, Option.some.injEq] at hid
    have hp : fn.params[j]? = some (id, q.2) := by
      cases q with
      | mk name ty =>
        dsimp only at hid
        subst id
        exact hj
    exact h id j (paramPos_of_nodup _ j id q.2 hN hp)

end PositionalLRel

end Gabbro.Bruecke
