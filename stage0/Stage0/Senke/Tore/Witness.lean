/- Gate satisfiability includes the provider's representation contract. -/
module
public import Stage0.Senke.Anweisung.Bindung.Tor
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration}

/-- **Witness** (the assumption is not empty): a kernel that may give any answer, and an oracle that leaves the
    world and answers 0, meet it for every layout. -/
theorem torOK_zeuge (L : Lay D) (O : Orakel D) (hO : ∀ a σ ρ, O.wirkt a σ ρ = (σ, 0))
    (href : ∀ a n, D.aerg a = some (.ref n) → L.tor a ≠ none →
      ValueValid L (.ref n) (Val.vonZelle 0)) :
    @TorOK ⟨fun _ _ _ _ => True⟩ D L O := by
  letI : Kern := ⟨fun _ _ _ _ => True⟩
  refine ⟨fun a b _ _ _ σ ρ q m _ _ _ hW => ⟨0, 0, m, trivial, ⟨rfl, rfl, fun _ _ => rfl⟩, ?_, ?_⟩,
    fun a b _ _ j nt rw t f _ _ _ hτ σ ρ q m _ _ _ hW hB => ⟨0, 0, m, trivial, rfl, rfl, fun _ _ => rfl, ?_, ?_, ?_⟩, ?_⟩
  · rw [hO]; exact hW
  · rw [hO]; simp [rohW]
  · rw [hO]; exact ⟨fun t' f' k hk _ => hW.1 t' f' k hk, hW.2.1⟩
  · intro k hk
    rw [hO]
    obtain ⟨w, hw, he⟩ := ValueAt.cellWord (by rw [hτ]; trivial) (hW.1 t f k (L.bounded (by omega)))
    have hwk : wAt m (L.elem t f k) = w := wAt_of hw
    cases rw
    · simp only [Bool.false_eq_true, ↓reduceIte, hwk]; exact he
    · simp only [↓reduceIte]
      let ws : Nat → Runner.W := fun k => if k < (D.count t).toNat then wAt m (L.elem t f k) else 0
      have hws : ∀ k, (ws k).toNat < 256 := fun k => by
        simp only [ws]; split
        · next hk' =>
          obtain ⟨w', hw', he'⟩ := ValueAt.cellWord (by rw [hτ]; trivial) (hW.1 t f k (L.bounded (by omega)))
          rw [wAt_of hw']; exact enc_byte hτ he'
        · decide
      have hb := hB (k / 8) (by simp only [pufW]; omega)
      rw [packV_congr (ws' := ws) (fun k hk => by simp only [ws, hk, ↓reduceIte])] at hb
      simp only [byteOf, hb, Option.getD_some]
      rw [byte_packV ws _ _ _ (by omega) hws, if_pos (by omega)]
      simp only [ws, show 8 * (k / 8) + k % 8 = k by omega, hk, ↓reduceIte, hwk]
      exact he
  · rw [hO]; simp [rohW]

  · intro a n he hb σ ρ raw relation nonnegative
    have zero : raw = 0 := by
      rcases relation with direct | fallible
      · simpa only [hO] using direct
      · simpa only [hO, Int.zero_ediv] using fallible
    subst raw
    exact href a n he hb

end Gabbro.Stage0.Senke
