module
public import Bruecke.Anweisung.Schleife.Ausgang
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {τ : Ty}

/-- Lift a simulation of a real pass through the exact canonical ordered index list.
    The pass relation shrinks the index context, preserving updates to outer locals.
    `next` continues, `leave` consumes the loop, and both result channels propagate.
    The invariant here is explicitly true, as in the currently admitted source form. -/
theorem traverse_operational_sim
    (state : World D → Env D Γ → Gabbro.Body.State → Prop)
    (result : World D → ErgVal D V.erg → Gabbro.Body.State → Option Gabbro.Body.Value → Prop)
    (reason : World D → Fin V.gruende → Gabbro.Body.State → Option Gabbro.Body.Value → Prop)
    (pass : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ))
    (number : Wert D τ → Int) (ρB : Gabbro.Body.Env) (binder : String)
    (body : List Gabbro.Body.Stmt)
    (hpass : ∀ i σ ρ s, state σ ρ s →
      OperationalRel state result reason (pass σ (.cons i ρ)).schrumpf
        (Gabbro.Body.exec ρB body
          ⟨s.world, Gabbro.Body.bindLocal s.local' binder (.int (number i))⟩)) :
    ∀ indices σ ρ s, state σ ρ s →
      OperationalRel state result reason
        (traverseLauf (l := l) pass (fun σ _ => (σ, true)) indices σ ρ)
        (Gabbro.Body.step ρB (.forEach binder (indices.map number) body) s)
  | [], σ, ρ, s, hs => hs
  | i :: indices, σ, ρ, s, hs => by
      have hp := hpass i σ ρ s hs
      cases hg : pass σ (.cons i ρ) with
      | ok σ₁ ρ₁ =>
          cases hb : Gabbro.Body.exec ρB body
              ⟨s.world, Gabbro.Body.bindLocal s.local' binder (.int (number i))⟩ <;>
            simp only [hg, Ausgang.schrumpf, hb, OperationalRel] at hp
          rename_i t
          rw [List.map_cons, Gabbro.Body.forEach_cons_running ρB binder (number i)
            (indices.map number) body s t hb]
          simpa only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hg] using
            traverse_operational_sim state result reason pass number ρB binder body hpass
              indices σ₁ ρ₁.tail t hp
      | next h σ₁ ρ₁ =>
          cases hb : Gabbro.Body.exec ρB body
              ⟨s.world, Gabbro.Body.bindLocal s.local' binder (.int (number i))⟩ <;>
            simp only [hg, Ausgang.schrumpf, hb, OperationalRel] at hp
          rename_i t
          rw [List.map_cons, Gabbro.Body.forEach_cons_next ρB binder (number i)
            (indices.map number) body s t hb]
          simpa only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hg] using
            traverse_operational_sim state result reason pass number ρB binder body hpass
              indices σ₁ ρ₁.tail t hp
      | leave h σ₁ ρ₁ =>
          cases hb : Gabbro.Body.exec ρB body
              ⟨s.world, Gabbro.Body.bindLocal s.local' binder (.int (number i))⟩ <;>
            simp only [hg, Ausgang.schrumpf, hb, OperationalRel] at hp
          rename_i t
          rw [List.map_cons, Gabbro.Body.forEach_cons_leave ρB binder (number i)
            (indices.map number) body s t hb]
          simpa only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hg, OperationalRel] using hp
      | zurueck σ₁ v =>
          cases hb : Gabbro.Body.exec ρB body
              ⟨s.world, Gabbro.Body.bindLocal s.local' binder (.int (number i))⟩ <;>
            simp only [hg, Ausgang.schrumpf, hb, OperationalRel] at hp
          rename_i t value
          rw [List.map_cons, Gabbro.Body.forEach_cons_returned ρB binder (number i)
            (indices.map number) body s t value hb]
          simpa only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hg, OperationalRel] using hp
      | why σ₁ r =>
          cases hb : Gabbro.Body.exec ρB body
              ⟨s.world, Gabbro.Body.bindLocal s.local' binder (.int (number i))⟩ <;>
            simp only [hg, Ausgang.schrumpf, hb, OperationalRel] at hp
          rename_i t value
          rw [List.map_cons, Gabbro.Body.forEach_cons_returned ρB binder (number i)
            (indices.map number) body s t value hb]
          simpa only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hg, OperationalRel] using hp
      | logik e =>
          cases hb : Gabbro.Body.exec ρB body
              ⟨s.world, Gabbro.Body.bindLocal s.local' binder (.int (number i))⟩ <;>
            simp only [hg, Ausgang.schrumpf, hb, OperationalRel] at hp
          simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hg, List.map_cons,
            Gabbro.Body.step, Gabbro.Body.traverseRun, hb, OperationalRel]
      | hardware e =>
          cases hb : Gabbro.Body.exec ρB body
              ⟨s.world, Gabbro.Body.bindLocal s.local' binder (.int (number i))⟩ <;>
            simp only [hg, Ausgang.schrumpf, hb, OperationalRel] at hp
          simp only [traverseLauf, Bool.true_eq_false, ↓reduceIte, hg, List.map_cons,
            Gabbro.Body.step, Gabbro.Body.traverseRun, hb, OperationalRel]

end Gabbro.Bruecke
