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

/-- Moves retain the same owner entries as the canonical owner-name resolver. -/
private theorem bewegtAt_loanEntries (u : UProg) (f : UFn) :
    bewegtAt u f = leihtAt u { f with leiht := f.bewegt } := by
  unfold bewegtAt leihtAt
  apply congrArg (fun resolve : String → Option (Fin u.marken.length × Nat) =>
    f.bewegt.filterMap resolve)
  funext m
  cases resolved : markFin u.marken m <;> rfl

/-- Mints retain the same owner entries as the canonical owner-name resolver. -/
private theorem praegtAt_loanEntries (u : UProg) (f : UFn) :
    praegtAt u f = leihtAt u { f with leiht := f.praegt } := by
  unfold praegtAt leihtAt
  apply congrArg (fun resolve : String → Option (Fin u.marken.length × Nat) =>
    f.praegt.filterMap resolve)
  funext m
  cases resolved : markFin u.marken m <;> rfl

/-- A resolved handoff names a table owner: the named table's `owner` is the same name. -/
theorem bewegtAt_eigner (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ bewegtAt u f) :
    ∃ t : Fin u.tabs.length, (tabAt u t).owner = some (u.marken.get i) := by
  rw [bewegtAt_loanEntries] at h
  exact leihtAt_eigner u { f with leiht := f.bewegt } i s h

/-- Every resolved handoff is a stage-0 mark. -/
theorem bewegtAt_stufe (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ bewegtAt u f) : s = 0 := by
  rw [bewegtAt_loanEntries] at h
  exact leihtAt_stufe u { f with leiht := f.bewegt } i s h

/-- A resolved mint names a table owner: the named table's `owner` is the same name. -/
theorem praegtAt_eigner (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ praegtAt u f) :
    ∃ t : Fin u.tabs.length, (tabAt u t).owner = some (u.marken.get i) := by
  rw [praegtAt_loanEntries] at h
  exact leihtAt_eigner u { f with leiht := f.praegt } i s h

/-- Every resolved mint is a stage-0 mark. -/
theorem praegtAt_stufe (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ praegtAt u f) : s = 0 := by
  rw [praegtAt_loanEntries] at h
  exact leihtAt_stufe u { f with leiht := f.praegt } i s h

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

/-- `consumes m` on a table owner is a terminal move: the existing owner-name
    resolver selects exactly those consumed marks that name table owners. -/
def terminalMovesAt (u : UProg) (f : UFn) : List (OwnerMove (Fin u.marken.length)) :=
  (bewegtAt u { f with bewegt := f.nimmt }).map fun p => ⟨p.1, p.2, none⟩

/-- One call interface for handback and terminal moves. Ordinary `nimmtAt`
    excludes these owners, so a terminal input is not consumed twice. -/
def ownerMovesAt (u : UProg) (f : UFn) : List (OwnerMove (Fin u.marken.length)) :=
  bewegtMovesAt u f ++ terminalMovesAt u f

/-- Terminal transfers return no owner on either outcome channel. -/
theorem terminalMovesAt_outputs (u : UProg) (f : UFn) :
    (terminalMovesAt u f).filterMap (fun x => x.after.map (fun s => (x.mark, s))) = [] := by
  simp [terminalMovesAt, List.filterMap_map]

/-- Only handback moves contribute to the return inventory. -/
theorem ownerMovesAt_outputs (u : UProg) (f : UFn) :
    (ownerMovesAt u f).filterMap (fun x => x.after.map (fun s => (x.mark, s))) =
      bewegtAt u f := by
  simp [ownerMovesAt, List.filterMap_append, bewegtMovesAt_outputs, terminalMovesAt_outputs]

end Gabbro.Grammatik.Parser.UebersetzeAllg
