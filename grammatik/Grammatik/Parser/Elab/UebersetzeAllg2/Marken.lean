module

public import Grammatik.Parser.Elab.UebersetzeAllg2.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- Find the actual held stage, including stages reached by an advance. -/
def heldMarkStage {D : Deklaration} (m : D.Marke) : List (Res D) → Option Nat
  | [] => none
  | .held _ :: rest => heldMarkStage m rest
  | .marke n a :: rest => if n = m then some a else heldMarkStage m rest

/-- Stage lookup never manufactures a held resource. -/
theorem heldMarkStage_mem {D : Deklaration} (m : D.Marke) (Λ : List (Res D))
    (a : Nat) (h : heldMarkStage m Λ = some a) : Res.marke m a ∈ Λ := by
  induction Λ with
  | nil => cases h
  | cons r rest ih =>
    cases r with
    | held L => exact List.mem_cons_of_mem _ (ih h)
    | marke n b =>
      by_cases hn : n = m
      · have hb : b = a := by simpa only [heldMarkStage, hn, ↓reduceIte, Option.some.injEq] using h
        simp [hn, hb]
      · have ht : heldMarkStage m rest = some a := by
          simpa only [heldMarkStage, hn, ↓reduceIte] using h
        exact List.mem_cons_of_mem _ (ih ht)

/-- Retire the held stage. Loans belong to the original caller signature and
    cannot be discharged. `none` adds no named hardware assumption. -/
def lowRetiresL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (Λ : List (Res (declOf u))) (name : String) :
    Except String (Σ Λ', Stmt (declOf u) (verOf u caller) l Γ Λ Λ') :=
  if (fnAt u caller).leiht.any (strEq · name) then
    .error ("retire of borrowed mark: " ++ name)
  else match markFin u.marken name with
    | none => .error ("retire of unknown mark: " ++ name)
    | some m =>
      match hs : heldMarkStage m Λ with
      | none => .error ("retire without held mark: " ++ name)
      | some a =>
        .ok ⟨Λ.erase (.marke m a), Stmt.retires (D := declOf u) (V := verOf u caller) (l := l) (Γ := Γ) (Λ := Λ) m a (heldMarkStage_mem m Λ a hs) none⟩

/-- Successful retirement is the canonical rule at the actual held stage. -/
theorem lowRetiresL_exact {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (Λ : List (Res (declOf u))) (name : String) (m : Fin u.marken.length) (a : Nat)
    (hb : (fnAt u caller).leiht.any (strEq · name) = false)
    (hm : markFin u.marken name = some m) (hs : heldMarkStage m Λ = some a) :
    lowRetiresL (l := l) u caller Γ Λ name =
      .ok ⟨Λ.erase (.marke m a), Stmt.retires (D := declOf u) (V := verOf u caller) (l := l) (Γ := Γ) (Λ := Λ) m a (heldMarkStage_mem m Λ a hs) none⟩ := by
  simp only [lowRetiresL, hb, Bool.false_eq_true, ↓reduceIte, hm]
  split
  · rename_i absent
    cases absent.symm.trans hs
  · rename_i stage found
    have same : stage = a := Option.some.inj (found.symm.trans hs)
    cases same
    rfl

/-- A callee loan is never a disposable owner, even while held. -/
theorem lowRetiresL_borrowed {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (Λ : List (Res (declOf u))) (name : String)
    (hb : (fnAt u caller).leiht.any (strEq · name) = true) :
    lowRetiresL (l := l) u caller Γ Λ name = .error ("retire of borrowed mark: " ++ name) := by
  simp only [lowRetiresL, hb, ↓reduceIte]

/-- Retiring twice or without an input is refused at every stage. -/
theorem lowRetiresL_unheld {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (Λ : List (Res (declOf u))) (name : String) (m : Fin u.marken.length)
    (hb : (fnAt u caller).leiht.any (strEq · name) = false)
    (hm : markFin u.marken name = some m) (hs : heldMarkStage m Λ = none) :
    lowRetiresL (l := l) u caller Γ Λ name = .error ("retire without held mark: " ++ name) := by
  simp only [lowRetiresL, hb, Bool.false_eq_true, ↓reduceIte, hm]
  split
  · rfl
  · rename_i stage found
    cases found.symm.trans hs

/-- A resolved source step with its checked declaration bound. -/
structure AdvanceHit (u : UProg) where
  mark : Fin u.marken.length
  stage : Nat
  bounded : stage + 1 < (declOf u).stufen mark

/-- Resolve unqualified labels against exactly one declared mark, preserving
    source order. A terminal stage, skipped/backward edge, unknown label or
    ambiguous mark is refused by name before a G statement is constructed. -/
def resolveAdvance (u : UProg) (source target : String) : Except String (AdvanceHit u) :=
  match (List.finRange u.marken.length).filter
      (fun m => (markStages u m).any (strEq · source)) with
  | [] => .error ("advance of unknown stage: " ++ source)
  | [m] =>
    match (markStages u m).findIdx? (strEq · source) with
    | none => .error ("advance of unknown stage: " ++ source)
    | some a =>
      if hs : a + 1 < (declOf u).stufen m then
        if (markStages u m)[a + 1]? = some target then .ok ⟨m, a, hs⟩
        else .error ("advance is not the next declared stage: " ++ source ++ " -> " ++ target)
      else .error ("advance from last stage: " ++ u.marken.get m ++ ": " ++ source)
  | _ => .error ("advance of ambiguous stage: " ++ source)

/-- Advance exactly the held stage. A loan must return at its original stage,
    so it cannot advance. The dependent result carries the canonical erase/add. -/
def lowAdvancesL {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (Λ : List (Res (declOf u))) (source target : String) :
    Except String (Σ Λ', Stmt (declOf u) (verOf u caller) l Γ Λ Λ') :=
  match resolveAdvance u source target with
  | .error error => .error error
  | .ok hit =>
    if (fnAt u caller).leiht.any (strEq · (u.marken.get hit.mark)) then
      .error ("advance of borrowed mark: " ++ u.marken.get hit.mark)
    else if held : Res.marke hit.mark hit.stage ∈ Λ then
      .ok ⟨Λ.erase (.marke hit.mark hit.stage) ++ [.marke hit.mark (hit.stage + 1)],
        Stmt.advances (D := declOf u) (V := verOf u caller) (l := l) (Γ := Γ) (Λ := Λ) hit.mark hit.stage held hit.bounded⟩
    else .error ("advance without held stage: " ++ u.marken.get hit.mark ++ ": " ++ source)

/-- Elaboration correctness: the actual lowering produces exactly the existing
    G advance rule, with its possession and declared-count proofs. -/
theorem lowAdvancesL_exact {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx)
    (Λ : List (Res (declOf u))) (source target : String) (hit : AdvanceHit u)
    (hr : resolveAdvance u source target = .ok hit)
    (hb : (fnAt u caller).leiht.any (strEq · (u.marken.get hit.mark)) = false)
    (held : Res.marke hit.mark hit.stage ∈ Λ) :
    lowAdvancesL (l := l) u caller Γ Λ source target =
      .ok ⟨Λ.erase (.marke hit.mark hit.stage) ++ [.marke hit.mark (hit.stage + 1)],
        Stmt.advances (D := declOf u) (V := verOf u caller) (l := l) (Γ := Γ) (Λ := Λ) hit.mark hit.stage held hit.bounded⟩ := by
  simp only [lowAdvancesL, hr, hb, Bool.false_eq_true, ↓reduceIte, dite_eq_left held]

end Gabbro.Grammatik.Parser.UebersetzeAllg2
