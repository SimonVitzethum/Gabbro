/-
  File:      core/Core/Maschine/Regel.lean
  Subject:   THE STATEMENT INTERFACE (PERFECT-MODEL §3.1, §3.4, §3.5, step M4): what a form contributes when
             its constructor enters in M6, and how the machines are composed of the forms. M4 has NO
             constructor; it fixes the interface:
             * `Regel`: one form's implementation step and its `I` step for the context at whose head it
               stands, with the memory events and the resolution of its choice points;
             * `System`: the forms of a language, which form stands at the head of a context (`kopf`), when
               a context is finished, and why it is blocked;
             * `ImplSchritt`, `ISchritt`: a step of a context is a step of the form at its head.
-/
module

public import Core.Maschine.Kontext

@[expose] public section

namespace Gabbro.Core.Maschine

/-- **The rules of one form.** `S` the states, `Ev` the events a step records, `Wahl` the
    resolution of the choice points of an `I` step (scheduler order at synchronisation points, the
    outside answers it consumes, explicit choice forms). -/
structure Regel (S Ev Wahl : Type) where
  impl : Kontext → S → Wahl → List Ev → S → Prop
  ideal : Kontext → S → Wahl → List Ev → S → Prop

/-- **A system of forms**: the rule of every form `i : ι`, the form at the head of a context
    (`none`: nothing left to do), finished contexts, and blocking with a reason `B`. -/
structure System (S Ev Wahl B ι : Type) where
  regel : ι → Regel S Ev Wahl
  kopf : S → Kontext → Option ι
  fertig : S → Kontext → Prop
  blockiert : S → Kontext → B → Prop

namespace System

variable {S Ev Wahl B ι : Type} (Sy : System S Ev Wahl B ι)

/-- **A step of the implementation machine** of a context: a step of the form at its head. -/
def ImplSchritt (c : Kontext) (s : S) (w : Wahl) (es : List Ev) (s' : S) : Prop :=
  ∃ i, Sy.kopf s c = some i ∧ (Sy.regel i).impl c s w es s'

/-- **A step of `I`** of a context: an `I` step of the form at its head. -/
def ISchritt (c : Kontext) (s : S) (w : Wahl) (es : List Ev) (s' : S) : Prop :=
  ∃ i, Sy.kopf s c = some i ∧ (Sy.regel i).ideal c s w es s'

/-- The states `I` reaches from `s0`, with the steps of every context interleaved. -/
inductive IErreichbar (s0 : S) : S → Prop
  | start : IErreichbar s0 s0
  | schritt {s s' : S} (c : Kontext) (w : Wahl) (es : List Ev) :
      IErreichbar s0 s → Sy.ISchritt c s w es s' → IErreichbar s0 s'

/-- The states the implementation machine reaches from `s0`, every interleaving. -/
inductive ImplErreichbar (s0 : S) : S → Prop
  | start : ImplErreichbar s0 s0
  | schritt {s s' : S} (c : Kontext) (w : Wahl) (es : List Ev) :
      ImplErreichbar s0 s → Sy.ImplSchritt c s w es s' → ImplErreichbar s0 s'

/-- Only the form at the head steps. -/
theorem ISchritt.kopf {Sy : System S Ev Wahl B ι} {c : Kontext} {s : S} {w : Wahl} {es : List Ev}
    {s' : S} (h : Sy.ISchritt c s w es s') : ∃ i, Sy.kopf s c = some i :=
  let ⟨i, hi, _⟩ := h
  ⟨i, hi⟩

end System

end Gabbro.Core.Maschine
