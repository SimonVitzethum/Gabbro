module

public import Grammatik.Parser.Elab.Generic.SignatureData
public import Grammatik.Kern.Syntax.Marken.Owner.Interface

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-! ## C09 move/mint flow: `bewegt`/`praegt` through the mark table -/

/-- The linearly handed-over owner marks of a function (C09): its `moves`
    names resolved against the unit's mark table at stage 0, keeping ONLY
    table owners: a handoff is an `OwnerMove` handback (`after := some 0`),
    so a non-owner resolves to nothing here (the front end refuses it loudly
    via `uBewegtPruef`). -/
def bewegtAt (u : UProg) (f : UFn) : List (Fin u.marken.length × Nat) :=
  f.bewegt.filterMap fun m =>
    match markFin u.marken m with
    | none => none
    | some i => if u.tabs.any (fun t => decide (t.owner = some m)) then some (i, 0) else none

/-- The handback moves of a function: the same nominal identity at the same
    stage on every returning channel (`after := some`). -/
def bewegtMovesAt (u : UProg) (f : UFn) : List (OwnerMove (Fin u.marken.length)) :=
  (bewegtAt u f).map fun p => ⟨p.1, p.2, some p.2⟩

/-- The checked mints of a function (C09): its `mints` names resolved against
    the unit's mark table at stage 0, keeping ONLY table owners: a mint is an
    `OwnerFlow.mints` entry, so a non-owner resolves to nothing here (the
    front end refuses it loudly via `uMintPruef`). -/
def praegtAt (u : UProg) (f : UFn) : List (Fin u.marken.length × Nat) :=
  f.praegt.filterMap fun m =>
    match markFin u.marken m with
    | none => none
    | some i => if u.tabs.any (fun t => decide (t.owner = some m)) then some (i, 0) else none

/-- A resolved handoff names a table owner: the named table's `owner` is the same name. -/
theorem bewegtAt_eigner (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ bewegtAt u f) :
    ∃ t : Fin u.tabs.length, (tabAt u t).owner = some (u.marken.get i) := by
  unfold bewegtAt at h
  obtain ⟨m, _, hmi⟩ := List.mem_filterMap.mp h
  cases hm : markFin u.marken m with
  | none =>
    simp only [hm, reduceCtorEq] at hmi
  | some j =>
    cases hall : (u.tabs.any (fun t => decide (t.owner = some m))) with
    | false =>
      simp only [hm, hall, reduceCtorEq] at hmi
    | true =>
      simp only [hm, hall, Option.some_injEq] at hmi
      obtain ⟨rfl, rfl⟩ := hmi
      obtain ⟨x, hxu, hx⟩ := List.any_eq_true.mp hall
      have hxown : x.owner = some m := of_decide_eq_true hx
      obtain ⟨n, hn, hxn⟩ := List.mem_iff_get.mp hxu
      refine ⟨⟨n, hn⟩, ?_⟩
      have htab : tabAt u ⟨n, hn⟩ = x := by unfold tabAt; rw [hxn]
      rw [htab, hxown, markFin_get u.marken m i hm]

/-- Every resolved handoff is a stage-0 mark. -/
theorem bewegtAt_stufe (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ bewegtAt u f) : s = 0 := by
  unfold bewegtAt at h
  obtain ⟨m, _, hmi⟩ := List.mem_filterMap.mp h
  cases hm : markFin u.marken m with
  | none =>
    simp only [hm, reduceCtorEq] at hmi
  | some j =>
    cases hall : (u.tabs.any (fun t => decide (t.owner = some m))) with
    | false =>
      simp only [hm, hall, reduceCtorEq] at hmi
    | true =>
      simp only [hm, hall, Option.some_injEq] at hmi
      obtain ⟨_, hs⟩ := hmi
      exact hs.symm

/-- A resolved mint names a table owner: the named table's `owner` is the same name. -/
theorem praegtAt_eigner (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ praegtAt u f) :
    ∃ t : Fin u.tabs.length, (tabAt u t).owner = some (u.marken.get i) := by
  unfold praegtAt at h
  obtain ⟨m, _, hmi⟩ := List.mem_filterMap.mp h
  cases hm : markFin u.marken m with
  | none =>
    simp only [hm, reduceCtorEq] at hmi
  | some j =>
    cases hall : (u.tabs.any (fun t => decide (t.owner = some m))) with
    | false =>
      simp only [hm, hall, reduceCtorEq] at hmi
    | true =>
      simp only [hm, hall, Option.some_injEq] at hmi
      obtain ⟨rfl, rfl⟩ := hmi
      obtain ⟨x, hxu, hx⟩ := List.any_eq_true.mp hall
      have hxown : x.owner = some m := of_decide_eq_true hx
      obtain ⟨n, hn, hxn⟩ := List.mem_iff_get.mp hxu
      refine ⟨⟨n, hn⟩, ?_⟩
      have htab : tabAt u ⟨n, hn⟩ = x := by unfold tabAt; rw [hxn]
      rw [htab, hxown, markFin_get u.marken m i hm]

/-- Every resolved mint is a stage-0 mark. -/
theorem praegtAt_stufe (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ praegtAt u f) : s = 0 := by
  unfold praegtAt at h
  obtain ⟨m, _, hmi⟩ := List.mem_filterMap.mp h
  cases hm : markFin u.marken m with
  | none =>
    simp only [hm, reduceCtorEq] at hmi
  | some j =>
    cases hall : (u.tabs.any (fun t => decide (t.owner = some m))) with
    | false =>
      simp only [hm, hall, reduceCtorEq] at hmi
    | true =>
      simp only [hm, hall, Option.some_injEq] at hmi
      obtain ⟨_, hs⟩ := hmi
      exact hs.symm

/-- The handback moves contribute exactly the resolved handoff inventory as
    outputs: the same nominal identity at the same stage. -/
theorem bewegtMovesAt_outputs (u : UProg) (f : UFn) :
    (bewegtMovesAt u f).filterMap (fun x => x.after.map (fun s => (x.mark, s))) =
      bewegtAt u f := by
  unfold bewegtMovesAt
  rw [List.filterMap_map]
  have hcomp : (fun x => x.after.map (fun s => (x.mark, s))) ∘
      (fun p => (⟨p.1, p.2, some p.2⟩ : OwnerMove (Fin u.marken.length))) = some := by
    funext p
    cases p with
    | mk a b => rfl
  rw [hcomp]
  exact List.filterMap_some

/-- The handback moves name exactly the resolved handoff inventory as inputs. -/
theorem bewegtMovesAt_inputs (u : UProg) (f : UFn) :
    (bewegtMovesAt u f).map (fun x => (x.mark, x.before)) = bewegtAt u f := by
  unfold bewegtMovesAt
  rw [List.map_map]
  have hcomp : (fun x => (x.mark, x.before)) ∘
      (fun p => (⟨p.1, p.2, some p.2⟩ : OwnerMove (Fin u.marken.length))) = id := by
    funext p
    cases p with
    | mk a b => rfl
  rw [hcomp]
  exact List.map_id _

end Gabbro.Grammatik.Parser.UebersetzeAllg
