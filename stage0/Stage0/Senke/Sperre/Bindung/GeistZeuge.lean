/- Joint non-degeneracy for the strategy-parametric safety interface. -/
module
public import Stage0.Senke.Sperre.Bindung.Simulation
public import Stage0.Senke.Sperre.Faeden.Zeuge
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden.WaitWitness
open Gabbro.Code (Conf)
open Gabbro.Code.Lower (Tkt)

/-- The existing nineteen-step Linux contention/wake/handover fixture, through
    precisely the same interface used by the freestanding binding. -/
def linux : WaitRun (waitModel .futex) where
  z := Zeuge.zeuge.z
  akt := Zeuge.zeuge.akt
  step := Zeuge.zeuge.schritt
  stutter := Zeuge.zeuge.stotter

/-- A real outstanding second ticket retries behind a holder. Both threads
    have already drawn; no thread is sleeping or registered as a waiter. -/
def spin : WaitRun (waitModel .spin) where
  z _ := Zeuge.z7
  akt _ := some 1
  step := by
    intro _ t ht
    cases ht
    exact Or.inr ⟨1, by decide, by decide, rfl⟩
  stutter := by intro _ h; cases h

/-- Both instances satisfy the invariant and the same nonempty FIFO fixture. -/
theorem waitModel_zeuge :
    Inv 2 (linux.z 0) ∧ Inv 2 (spin.z 0) ∧
    bild (spin.z 0) = ⟨some 0, [1]⟩ ∧
    (waitModel (N := 2) .spin).step (spin.z 0) 1 (spin.z 1) ∧
    (waitModel (N := 2) .futex).step (linux.z 10) 1 (linux.z 11) := by
  refine ⟨Zeuge.zeuge_inv, ?_, ?_, spin.step 0 1 rfl, Zeuge.s10⟩
  · have h0 : Inv 2 Zeuge.z0 := Inv.start
    have h1 := h0.schritt (by decide) Zeuge.s0
    have h2 := h1.schritt (by decide) Zeuge.s1
    have h3 := h2.schritt (by decide) Zeuge.s2
    have h4 := h3.schritt (by decide) Zeuge.s3
    have h5 := h4.schritt (by decide) Zeuge.s4
    have h6 := h5.schritt (by decide) Zeuge.s5
    exact h6.schritt (by decide) Zeuge.s6
  · rfl

/-- The generic ghost theorem has jointly satisfiable premises with a waiting
    thread, a distinct holder and actual spin retry steps. -/
theorem WaitRun_tkt_zeuge [Conf] (width : 4 < 2 ^ Conf.wbits) :
    ∃ gh : Nat → Tkt, (∀ n, Passt (gh n) ((bild (spin.z n)).karte Fin.val)) ∧
      (∀ n, Nach ((spin.akt n).map Fin.val) (gh n) (gh (n + 1))) ∧
      tHalter (gh 0) = some 0 ∧ 1 ∈ tWarte (gh 0) := by
  have invariant : Inv 2 (spin.z 0) := waitModel_zeuge.2.1
  obtain ⟨gh, matches, steps⟩ := spin.tkt (by decide) invariant (fun n => by
    change 1 + 2 < 2 ^ Conf.wbits
    omega)
  refine ⟨gh, matches, steps, ?_, ?_⟩
  · exact (matches 0).halter.symm
  · rw [(matches 0).warte]
    exact List.mem_singleton_self 1

end Gabbro.Stage0.Senke.Faeden.WaitWitness
