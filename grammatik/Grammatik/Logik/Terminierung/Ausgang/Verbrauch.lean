module
public import Grammatik.Logik.Terminierung.Klasse
public import Grammatik.Logik.Terminierung.Ausgang.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}
private theorem ohneAus_verbrauch {l : Bool} {Γ : Ctx} {eb : Bool} (t : D.Tab)
    (schritt : World D → Env D (.index (D.count t) :: Γ) →
      Ausgang V true (.index (D.count t) :: Γ))
    (inv : World D → Env D Γ → World D × Bool)
    (sel : World D → Env D Γ → World D × Option (Wert D (.index (D.count t))) × Bool)
    (massW : World D → Env D Γ → World D × Int) (bound : Int)
    (hs : ∀ σ ρ, OhneAus false (schritt σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ),
      OhneAus eb (verbrauchLauf (l := l) t schritt inv sel massW bound n σ ρ)
  | 0, _, _ => trivial
  | n + 1, σ, ρ => by
      simp only [verbrauchLauf]
      split
      · trivial
      · split
        · trivial
        · trivial
        · rename_i σr k _ hsel
          have h := hs (massW σr ρ).1 (.cons k ρ)
          split
          · split
            · exact ohneAus_verbrauch t schritt inv sel massW bound hs n _ _
            · trivial
          · split
            · exact ohneAus_verbrauch t schritt inv sel massW bound hs n _ _
            · trivial
          · split
            · split <;> trivial
            · trivial
          · rename_i he; rw [he] at h; exact h
          · rename_i he; rw [he] at h; exact h
          · trivial
          · trivial

end Gabbro.Grammatik
