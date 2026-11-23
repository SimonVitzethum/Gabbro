/-
  File:      core/Core/Speicher/MoLetzte.lean
  Subject:   THE LAST WRITE IN MODIFICATION ORDER exists (`mo_letzte_existiert`): in a finite
             consistent graph, a location with a write has a write that every other write of it
             precedes in `mo`. A read that takes it, or a write appended after it, is the sink step
             of `Anhaengen.lean` that every machine of M4 takes for its memory accesses.
-/
module

public import Core.Speicher.Senke
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace Gabbro.Core.Speicher

namespace Graph

variable {E Ort Wert : Type}

/-- **A write last in `mo`** at location `x`. -/
def MoLetzte (G : Graph E Ort Wert) (x : Ort) (w : E) : Prop :=
  G.schreibt w ∧ G.ort w = x ∧ ∀ v, G.schreibt v → G.ort v = x → v = w ∨ G.mo v w

/-- **In a finite well-formed graph a location with a write has a write last in `mo`.** -/
theorem mo_letzte_existiert [Finite E] {G : Graph E Ort Wert} (hw : G.Wohlgeformt) {x : Ort}
    (h : ∃ w, G.schreibt w ∧ G.ort w = x) : ∃ w, G.MoLetzte x w := by
  let r : E → E → Prop := fun a b => G.mo b a
  have : IsTrans E r := ⟨fun a b c h1 h2 => hw.mo_trans _ _ _ h2 h1⟩
  have : Std.Irrefl r := ⟨fun a h => hw.mo_irrefl a h⟩
  obtain ⟨w0, hw0⟩ := h
  obtain ⟨w, hwS, hmin⟩ := (Finite.wellFounded_of_trans_of_irrefl r).has_min
    {v | G.schreibt v ∧ G.ort v = x} ⟨w0, hw0⟩
  refine ⟨w, hwS.1, hwS.2, fun v hv hvx => ?_⟩
  by_cases e : v = w
  · exact Or.inl e
  · rcases hw.mo_total v w hv hwS.1 (hvx.trans hwS.2.symm) e with h1 | h1
    · exact Or.inr h1
    · exact absurd h1 (hmin v ⟨hv, hvx⟩)

/-- The write last in `mo` is unique. -/
theorem MoLetzte.eindeutig {G : Graph E Ort Wert} (hw : G.Wohlgeformt) {x : Ort} {w w' : E}
    (h : G.MoLetzte x w) (h' : G.MoLetzte x w') : w = w' := by
  rcases h'.2.2 w h.1 h.2.1 with e | e
  · exact e
  · rcases h.2.2 w' h'.1 h'.2.1 with e' | e'
    · exact e'.symm
    · exact absurd (hw.mo_trans _ _ _ e e') (hw.mo_irrefl w)

end Graph

end Gabbro.Core.Speicher
