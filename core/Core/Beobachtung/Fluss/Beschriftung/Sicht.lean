module

public import Core.Beobachtung.Fluss.Quellregel
public import Core.Ast.Semantik.Elaborierung

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine

/-- Declared flow levels of a source fragment (PLAN B15: levels on types and places).
    The tables are indexed by the program counter, so one frame component may change its
    level along the code. A temporary is addressed by its slot, a local by its position from
    the top of the scope stack, exactly as the instructions address them. The entry levels
    are `lokal 0`: the locals at the first cut are the entry bindings in scope order.
    `ergebnis` is the level of the returned value. Control state (`pc`, stop reason, counters,
    saved continuations, function table, platform data) has no table: it is always public. -/
structure Beschriftung where
  temp : Nat → Nat → Beobachtung.Etikett := fun _ _ => ∅
  lokal : Nat → Nat → Beobachtung.Etikett := fun _ _ => ∅
  ergebnis : Beobachtung.Etikett := ∅

/-- The declaration with every component public. -/
def Beschriftung.alleOeffentlich : Beschriftung := {}

/-- Mask the entries of a local stack whose level is not public; `i` is the position of the head. -/
def maskiere (label : Nat → Beobachtung.Etikett) :
    Nat → List (Option Dynamisch) → List (Option Dynamisch)
  | _, [] => []
  | i, x :: xs =>
    (if Beobachtung.oeffentlich (label i) = true then x else none) :: maskiere label (i + 1) xs

/-- The public view of a frame at its own program counter: secret temporaries, locals and
    the result are replaced by `none`, everything else is kept. Two frames are public-equal
    exactly when their views are equal. -/
def Rahmen.sicht (β : Beschriftung) (r : Rahmen) : Rahmen :=
  { r with
    temp := fun s => if Beobachtung.oeffentlich (β.temp r.pc s) = true then r.temp s else none
    lokale := maskiere (β.lokal r.pc) 0 r.lokale
    rueckgabe := if Beobachtung.oeffentlich β.ergebnis = true then r.rueckgabe else none }

theorem oeffentlich_leer : Beobachtung.oeffentlich (∅ : Beobachtung.Etikett) = true := by
  simp only [Beobachtung.oeffentlich, decide_eq_true_eq]

theorem maskiere_leer (i : Nat) (xs : List (Option Dynamisch)) :
    maskiere (fun _ => (∅ : Beobachtung.Etikett)) i xs = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    simp only [maskiere, oeffentlich_leer, if_true, ih]

/-- With every component public the view is the frame itself. -/
theorem sicht_alleOeffentlich (r : Rahmen) : r.sicht .alleOeffentlich = r := by
  simp only [Rahmen.sicht, Beschriftung.alleOeffentlich, oeffentlich_leer, if_true, maskiere_leer]

/-- Equal views have equal program counters: control is never masked. -/
theorem sicht_pc {β : Beschriftung} {r₁ r₂ : Rahmen} (h : r₁.sicht β = r₂.sicht β) :
    r₁.pc = r₂.pc :=
  (congrArg Rahmen.pc h : (r₁.sicht β).pc = (r₂.sicht β).pc)

end Gabbro.Core.Ast.Semantik
