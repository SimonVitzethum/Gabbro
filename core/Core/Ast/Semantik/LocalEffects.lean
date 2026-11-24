module

public import Core.Ast.Semantik.Auswertung
public import Core.Ast.Semantik.Quellform

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme

-- Mirror Local.visible_unique using the type index at Local.here.
theorem local_binding_type (ref : Local scope type) : ref.binding.type = type := by
  sorry

def wertInhalt (type : Ty .value) (value : Wert type) : Int ⊕ Bool :=
  match type, value with
  | .int _ _, number => .inl number.wert
  | .bool, bit => .inr bit

-- Mirror literal_ausserhalb_verweigert with interval containment in the successful direction.
theorem wertIn_widen (fits : Fits source target) (value : Wert source) :
    ∃ widened : Wert target, wertIn target ⟨source, value⟩ = some ⟨target, widened⟩ ∧
      wertInhalt source value = wertInhalt target widened := by
  sorry

-- Mirror Fragment.guard_am_schnitt by exposing the two operand magnitudes at the division head.
theorem division_guard_exact (frame : Rahmen) (slot : Nat)
    (a : Zahl lo₁ hi₁) (b : Zahl lo₂ hi₂)
    (left : frame.temp slot = some ⟨.int lo₁ hi₁, a⟩)
    (right : frame.temp (slot + 1) = some ⟨.int lo₂ hi₂, b⟩)
    (nonzero : Divisor lo₂ hi₂) :
    (Befehl.teilen slot).guard frame = some ⟨.division, (a.wert.natAbs, b.wert.natAbs)⟩ ∧
    waechterBedarf .division (a.wert.natAbs, b.wert.natAbs) := by
  sorry

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
  sorry

-- Mirror Quellform.realisiert's instruction lookup, using wertIn_widen to establish a return.
theorem return_effect (fits : Fits source target) (value : Wert source) (s : Zustand)
    (temp : (s.lokal eintritt).temp slot = some ⟨source, value⟩) :
    let after := (Befehl.zurueck slot target).nach eintritt s
    ∃ widened : Wert target,
      (after.lokal eintritt).rueckgabe = some ⟨target, widened⟩ ∧
      wertInhalt source value = wertInhalt target widened ∧
      ∀ code, kopf code after eintritt = none := by
  sorry

-- Mirror the pc equality of expr_ergebnis_typ and split on the actual Boolean input.
theorem branch_effect (frame : Rahmen) (bit : Bool)
    (value : frame.temp slot = some ⟨.bool, bit⟩) :
    let after := (Befehl.springeWenn slot whenValue offset).auswerten frame
    after.pc = frame.pc + (if bit = whenValue then offset else 1) ∧
      after.lokale = frame.lokale ∧ after.temp = frame.temp ∧ after.rueckgabe = frame.rueckgabe := by
  sorry

-- Mirror Block.printItems_reads by following the scope extension through each statement.
theorem block_scope_extends (body : Block result before after) : before <:+ after := by
  sorry

end Gabbro.Core.Ast.Semantik
