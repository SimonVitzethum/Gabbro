/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Einbettung.lean
  Subject:   THE UNITS THAT CARRY STEP FORMS (MK-03). The duties of an effect class are stated for every unit
             that EMBEDS a form of the class: its rule for the form is the class rule and it reads memory
             through the handles and objects of the elaborated model (`Schrittform.Eingebettet`). The unit is
             generic in its form type, so a duty of a class that has no instruction yet is still a statement
             about real units. Two side conditions the duties need are bound to the form here, not left free:
             the stack bound its transfer respects (`Stapelschranke`) and the label rule of its operands
             (`Operandensicht`).
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Schritt
public import Core.Beobachtung.Fluss.Quellregel

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- The units that carry step forms: the interpretation of memory is the elaborated one. -/
abbrev Klasseneinheit (ι : Type) := Maschine.Einheit Nat Zelle Int Nat Rahmen PUnit PUnit PUnit ι

/-- **A unit embeds a form**: the unit's rule for its form `f` is the rule of the step form `F`, and the
    unit reads memory through the handles and objects of the elaborated model. -/
structure Schrittform.Eingebettet {ι : Type} (E : Klasseneinheit ι) (f : ι) (F : Schrittform) : Prop where
  regel : E.system.regel f = F.regel
  griff : E.einrichtung.speicherGriff = Zustand.griff
  objekt : E.einrichtung.speicherObjekt = Zelle.objekt

/-- **The transfer of a form respects the declared stack bound of its unit**: a frame within the bound stays
    within it. A class that does not push a continuation (every class but `ruf`) has this from its stack
    effect; a class that pushes one refuses at the bound, as `Rahmen.ruf` does. -/
def Schrittform.Stapelschranke {ι : Type} (E : Klasseneinheit ι) (F : Schrittform) : Prop :=
  ∀ (r : Rahmen) (live : Nat → Bool) (v : Int) (n : Nat), E.schranken.stapel = some n →
    r.fortsetzungen.length ≤ n → (F.uebertrag r live v).fortsetzungen.length ≤ n

/-- **The operands of a form are visible to the observer**: from source states that agree on the public
    part, the form names the same operands (the same cell, value, lock and question). This is the label
    rule of an access: an address that depends on a secret is a leak through the memory trace. -/
def Schrittform.Operandensicht {ι : Type} (E : Klasseneinheit ι) (F : Schrittform) : Prop :=
  ∀ (c : Kontext) (v₁ v₂ : Zustand), Beobachtung.QuellzustandGleich E v₁ v₂ →
    F.operand (v₁.lokal c) = F.operand (v₂.lokal c)

end Gabbro.Core.Ast.Semantik
