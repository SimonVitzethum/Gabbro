import Grammatik.Berechenbarkeit.BrainfuckG.Lege
import Grammatik.Berechenbarkeit.Storage.GStack.MultiWitnesses

/-! Witnesses of `lege_ok` and `lege_voll` over the two-stack declaration of `MultiWitnesses`: in `w1` (counter 2 of 4,
free list empty) pushing the head byte `7` on stack 0 gives stack 0 = `[7, 0]` and leaves stack 1 = `[0]`; in `w2`
(counter 4 of 4, free list empty) the same push runs the failure block. -/

namespace Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.LegeWitnesses

open ArenaKette InvDynZeuge Storage.GStack Storage.GStack.MultiWitnesses

theorem hp : MD.typ MA.tab MA.feld = ByteTy := rfl

/-- The head local holds `7`. -/
def ρ7 : Env MD [ByteTy] := .cons ⟨7, by decide, by decide⟩ .nil

/-- **Push witness**: the head byte `7` lands on stack 0; stack 1 keeps its cell. -/
theorem lege_ok_zeuge (O : Orakel MD) (passes : Nat)
    (R : ∀ f : MD.Fn, World MD → Env MD (MD.params f) → RufAusgang f) :
    ∃ σ', execBlock O passes R (lege ML heads 0 hp .here rfl mdarf rfl (mgdarf _) rfl (mgdarf _) rfl (mgdarf _)
        failure) MultiWitnesses.w1 ρ7 = .ok σ' ρ7 ∧
      MultiRep ML heads σ' (zwei [seven, zero] [zero]) ∧ MA.FreiOk σ' := by
  obtain ⟨σ', hexec, hm, hf⟩ := lege_ok O passes R ML heads heads_inj 0 hp .here rfl mdarf rfl (mgdarf _) rfl
    (mgdarf _) rfl (mgdarf _) failure MultiWitnesses.w1 ρ7 (fun _ => [zero]) multi_w1 frei_w1 (.inr (by decide))
  refine ⟨σ', hexec, ?_, hf⟩
  have he : Function.update (fun _ : Fin 2 => [zero]) 0
      (Wert.umTyp hp.symm (ρ7.get .here) :: [zero]) = zwei [seven, zero] [zero] := by
    funext k
    rcases k with ⟨_ | _ | k, hk⟩
    · rfl
    · rfl
    · omega
  rw [← he]
  exact hm

/-- Counter 4 of 4, free list empty: the arena is full. -/
def w2 : World MD where
  slots := MultiWitnesses.w1.slots
  globs := fun g => if g = 0 then zc 4 else MultiWitnesses.w1.globs g
  spur := []

/-- **Out-of-memory witness**: in the full arena the push runs the failure block. -/
theorem lege_voll_zeuge (O : Orakel MD) (passes : Nat)
    (R : ∀ f : MD.Fn, World MD → Env MD (MD.params f) → RufAusgang f) :
    execBlock O passes R (lege ML heads 0 hp .here rfl mdarf rfl (mgdarf _) rfl (mgdarf _) rfl (mgdarf _)
        failure) w2 ρ7 =
      (execEnd O passes R failure ((w2.lese [] (freeEmpty (Γ := [ByteTy]) MA (mgdarf _)).orte).lese []
        [Sum.inr MA.zaehl]) ρ7).zuAusgang :=
  lege_voll O passes R ML heads 0 hp .here rfl mdarf rfl (mgdarf _) rfl (mgdarf _) rfl (mgdarf _) failure w2 ρ7
    rfl rfl

end Gabbro.Grammatik.Berechenbarkeit.BrainfuckG.LegeWitnesses
