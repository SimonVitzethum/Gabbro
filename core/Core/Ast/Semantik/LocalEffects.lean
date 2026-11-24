module

public import Core.Ast.Semantik.Auswertung
public import Core.Ast.Semantik.Quellform
import Core.Ast.Semantik.Runtime.ValueCoercion

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme

-- Mirror Local.visible_unique using the type index at Local.here.
theorem local_binding_type (ref : Local scope type) : ref.binding.type = type := by
  induction ref with
  | here => rfl
  | there ref ih => exact ih

def wertInhalt (type : Ty .value) (value : Wert type) : Int ⊕ Bool ⊕ Option Dynamisch :=
  match type, value with
  | .int _ _, number => .inl number.wert
  | .bool, bit => .inr (.inl bit)
  | .array _ 0, _ => .inr (.inr none)
  | .text _, text =>
    .inr (.inr (some ⟨.text text.bytes.size, ⟨text.bytes, Nat.le_refl _⟩⟩))
  | type, value => .inr (.inr (some ⟨type, value⟩))

private theorem wertInhalt_widen (fits : Fits source target) (value : Wert source) :
    wertInhalt source value = wertInhalt target (Wert.widen source target fits value) := by
  cases source
  case array source count =>
    cases count <;> cases target
    case zero.array target other => cases other
    case succ.array n target other => cases other
    all_goals first | rfl | cases fits <;> rfl
  all_goals
    cases target <;> first | rfl | cases fits <;> rfl

theorem wertIn_widen (fits : Fits source target) (value : Wert source) :
    ∃ widened : Wert target, wertIn target ⟨source, value⟩ = some ⟨target, widened⟩ ∧
      wertInhalt source value = wertInhalt target widened := by
  refine ⟨Wert.widen source target fits value, ?_, wertInhalt_widen fits value⟩
  rw [wertIn, wertAls_widen source target fits]
  rfl

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

/-- Return a widened value to the entry context or restore the saved caller.
    A caller with no result binding discards the value. -/
theorem return_effect (fits : Fits source target) (value : Wert source) (s : Zustand)
    (temp : (s.lokal eintritt).temp slot = some ⟨source, value⟩) :
    let after := (Befehl.zurueck slot target).nach eintritt s
    ∃ widened : Wert target,
      wertInhalt source value = wertInhalt target widened ∧
      match (s.lokal eintritt).fortsetzungen with
      | [] =>
        (after.lokal eintritt).rueckgabe = some ⟨target, widened⟩ ∧
          ∀ code, kopf code after eintritt = none
      | saved :: stack =>
        after.lokal eintritt = { s.lokal eintritt with
          pc := saved.pc, temp := saved.temp,
          lokale := match saved.eingang with
            | none => saved.lokale
            | some written => wertIn written ⟨target, widened⟩ :: saved.lokale,
          zaehler := saved.zaehler, obergrenzen := saved.obergrenzen,
          funktion := saved.funktion, mass := saved.mass, fortsetzungen := stack } := by
  dsimp only
  obtain ⟨widened, valueEq, contents⟩ := wertIn_widen fits value
  have typed : ((s.lokal eintritt).temp slot).bind (wertIn target) = some ⟨target, widened⟩ := by
    rw [temp]
    exact valueEq
  have afterFrame : ((Befehl.zurueck slot target).nach eintritt s).lokal eintritt =
      (s.lokal eintritt).rueckkehr (some ⟨target, widened⟩) := by
    simp only [Befehl.nach, Function.update_self, Befehl.auswerten, typed]
  refine ⟨widened, contents, ?_⟩
  cases stackEq : (s.lokal eintritt).fortsetzungen with
  | nil =>
    have returned : (((Befehl.zurueck slot target).nach eintritt s).lokal eintritt).rueckgabe =
        some ⟨target, widened⟩ := by
      rw [afterFrame]
      simp only [Rahmen.rueckkehr, stackEq]
    refine ⟨returned, ?_⟩
    intro code
    simp only [kopf, if_pos rfl, returned]
    change (match s.status eintritt with
      | .ruht => none
      | .laeuft => none
      | .beendet _ => none) = (none : Option Befehl)
    cases s.status eintritt <;> rfl
  | cons saved stack =>
    rw [afterFrame]
    cases incoming : saved.eingang <;> simp only [Rahmen.rueckkehr, stackEq, incoming, Option.bind_some]

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

/-- A sequential block prepends fresh bindings while preserving the entry scope. -/
theorem block_scope_extends (body : Block result before after) : before <:+ after := by
  refine @Block.rec result
    (fun b a _ => b <:+ a)
    (fun b a _ => b <:+ a)
    (fun _ _ => True)
    (fun _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ before after body
  all_goals
    intros
    first
    | exact List.suffix_refl _
    | exact List.suffix_cons _ _
    | exact List.suffix_append _ _
    | trivial
    | apply List.IsSuffix.trans <;> assumption

end Gabbro.Core.Ast.Semantik
