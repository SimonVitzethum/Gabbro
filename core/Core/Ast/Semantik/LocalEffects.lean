module

public import Core.Ast.Semantik.Auswertung
public import Core.Ast.Semantik.Quellform

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme

-- Mirror Local.visible_unique using the type index at Local.here.
theorem local_binding_type (ref : Local scope type) : ref.binding.type = type := by
  induction ref with
  | here => rfl
  | there ref ih => exact ih

def wertInhalt (type : Ty .value) (value : Wert type) : Int ⊕ Bool :=
  match type, value with
  | .int _ _, number => .inl number.wert
  | .bool, bit => .inr bit

-- Mirror literal_ausserhalb_verweigert with interval containment in the successful direction.
theorem wertIn_widen (fits : Fits source target) (value : Wert source) :
    ∃ widened : Wert target, wertIn target ⟨source, value⟩ = some ⟨target, widened⟩ ∧
      wertInhalt source value = wertInhalt target widened := by
  cases source with
  | bool =>
      cases target with
      | bool =>
          refine ⟨value, ?_, rfl⟩
          rfl
      | int tlo thi => cases fits
  | int slo shi =>
      cases target with
      | bool => cases fits
      | int tlo thi =>
          have lower : tlo ≤ value.wert := Int.le_trans fits.1 value.unten
          have upper : value.wert ≤ thi := Int.le_trans value.oben fits.2
          refine ⟨⟨value.wert, lower, upper⟩, ?_, rfl⟩
          simp only [wertIn, dif_pos (show tlo ≤ value.wert ∧ value.wert ≤ thi from ⟨lower, upper⟩)]

-- Mirror Fragment.guard_am_schnitt by exposing the two operand magnitudes at the division head.
theorem division_guard_exact (frame : Rahmen) (slot : Nat)
    (a : Zahl lo₁ hi₁) (b : Zahl lo₂ hi₂)
    (left : frame.temp slot = some ⟨.int lo₁ hi₁, a⟩)
    (right : frame.temp (slot + 1) = some ⟨.int lo₂ hi₂, b⟩)
    (nonzero : Divisor lo₂ hi₂) :
    (Befehl.teilen slot).guard frame = some ⟨.division, (a.wert.natAbs, b.wert.natAbs)⟩ ∧
    waechterBedarf .division (a.wert.natAbs, b.wert.natAbs) := by
  have hbne : b.wert ≠ 0 := by
    rcases nonzero with positive | negative
    · have lower : (1 : Int) ≤ b.wert := Int.le_trans positive b.unten
      omega
    · have upper : b.wert ≤ (-1 : Int) := Int.le_trans b.oben negative
      omega
  have habs : b.wert.natAbs ≠ 0 := by
    intro zero
    exact hbne (Int.natAbs_eq_zero.mp zero)
  constructor
  · simp only [Befehl.guard, Rahmen.zahl, alsGanzzahl, left, right,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · exact habs

-- Mirror expr_ergebnis_typ's temporary-frame proof using List.set and wertIn_widen.
theorem assignment_effect (ref : Local scope (.int lo hi)) (visible : ref.visible)
    (writable : ref.binding.mutable = true) (fits : Fits source (.int lo hi))
    (value : Wert source) (frame : Rahmen) (env : Umgebung scope)
    (bound : frame.traegt env) (temp : frame.temp slot = some ⟨source, value⟩) :
    let after := (Befehl.zuweisen slot ref.index ref.binding.type).auswerten frame
    ∃ widened : Wert (.int lo hi),
      after.lokale[ref.index]? = some (some ⟨.int lo hi, widened⟩) ∧
      wertInhalt source value = wertInhalt (.int lo hi) widened ∧
      (∀ i, i ≠ ref.index → after.lokale[i]? = frame.lokale[i]?) ∧
      after.pc = frame.pc + 1 ∧ after.rueckgabe = frame.rueckgabe := by
  dsimp only
  rw [local_binding_type ref]
  obtain ⟨widened, valueEq, contents⟩ := wertIn_widen fits value
  have typed : (frame.temp slot).bind (wertIn (.int lo hi)) = some ⟨.int lo hi, widened⟩ := by
    rw [temp]
    exact valueEq
  simp only [Befehl.auswerten, typed]
  refine ⟨widened, ?_, contents, ?_, ?_, ?_⟩
  · have b := bound ref
    have hlt : ref.index < frame.lokale.length := by
      by_contra hnot
      rw [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hnot)] at b
      cases b
    rw [List.getElem?_set_self hlt]
  · intro i different
    rw [List.getElem?_set]
    simp only [if_neg (Ne.symm different)]
  · trivial
  · trivial

-- Mirror Quellform.realisiert's instruction lookup, using wertIn_widen to establish a return.
theorem return_effect (fits : Fits source target) (value : Wert source) (s : Zustand)
    (temp : (s.lokal eintritt).temp slot = some ⟨source, value⟩) :
    let after := (Befehl.zurueck slot target).nach eintritt s
    ∃ widened : Wert target,
      (after.lokal eintritt).rueckgabe = some ⟨target, widened⟩ ∧
      wertInhalt source value = wertInhalt target widened ∧
      ∀ code, kopf code after eintritt = none := by
  dsimp only
  obtain ⟨widened, valueEq, contents⟩ := wertIn_widen fits value
  have typed : ((s.lokal eintritt).temp slot).bind (wertIn target) = some ⟨target, widened⟩ := by
    rw [temp]
    exact valueEq
  refine ⟨widened, ?_, contents, ?_⟩
  · simp only [Befehl.nach, Befehl.auswerten, Function.update_self, typed]
  · intro code
    unfold kopf
    rw [if_pos rfl]
    simp only [Befehl.nach]
    cases hstatus : (s.status eintritt) with
    | ruht => rfl
    | beendet _ => rfl
    | laeuft =>
      have hret : (Function.update s.lokal eintritt
          ((Befehl.zurueck slot target).auswerten (s.lokal eintritt)) eintritt).rueckgabe =
          some ⟨target, widened⟩ := by
        simp only [Function.update_self, Befehl.auswerten, typed]
      rw [hret]

-- Mirror the pc equality of expr_ergebnis_typ and split on the actual Boolean input.
theorem branch_effect (frame : Rahmen) (bit : Bool)
    (value : frame.temp slot = some ⟨.bool, bit⟩) :
    let after := (Befehl.springeWenn slot whenValue offset).auswerten frame
    after.pc = frame.pc + (if bit = whenValue then offset else 1) ∧
      after.lokale = frame.lokale ∧ after.temp = frame.temp ∧ after.rueckgabe = frame.rueckgabe := by
  dsimp only
  by_cases h : bit = whenValue
  · have hs : some bit = some whenValue := congrArg some h
    simp only [Befehl.auswerten, value, alsBoolean, Option.bind_some, if_pos hs, if_pos h,
      if_true]
    repeat' constructor <;> trivial
  · have hs : some bit ≠ some whenValue := by
      intro same
      exact h (Option.some.inj same)
    simp only [Befehl.auswerten, value, alsBoolean, Option.bind_some, if_neg hs, if_neg h,
      if_false]
    repeat' constructor <;> trivial

-- Mirror Block.printItems_reads by following the scope extension through each statement.
theorem block_scope_extends (body : Block result before after) : before <:+ after := by
  refine @Block.rec result
    (fun b a t => b <:+ a)
    (fun b a t => b <:+ a)
    (fun b t => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ before after body
  · intro scope type name ordinary value
    exact List.suffix_cons _ _
  · intro scope lo hi valueLo valueHi ref visible writable value fits
    exact List.suffix_refl _
  · intro expected scope type declared value fits
    exact List.suffix_refl _
  · intro scope condition yes no yesIH noIH
    exact List.suffix_refl _
  · intro scope
    exact List.suffix_refl _
  · intro before middle after first rest firstIH restIH
    exact firstIH.trans restIH
  · intro before after body bodyIH
    trivial

end Gabbro.Core.Ast.Semantik
