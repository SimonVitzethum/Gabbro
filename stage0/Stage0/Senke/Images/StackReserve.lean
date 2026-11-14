/- Automatic stack sizing reuses the frame high-water mark already computed by
   image emission. Runtime guards and all frame/execution relations stay intact. -/
module
public import Stage0.Senke.Images.Bild
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Explicit capacities retain the existing checked builder behavior. -/
theorem stackReserve_explicit (requested largest scratch : Nat) (positive : requested ≠ 0) :
    stackReserve requested largest scratch = requested := by
  simp only [stackReserve, if_neg positive]

/-- An automatic reserve keeps the old image geometry whenever its floor suffices. -/
theorem stackReserve_unchanged (largest scratch : Nat)
    (frames : FB + (stackReserveDepth + 1) * largest ≤ stackReserveFloor)
    (startup : scratch ≤ stackReserveFloor) :
    stackReserve 0 largest scratch = stackReserveFloor := by
  simp only [stackReserve, ↓reduceIte, ite_true]
  omega

/-- The reservation covers the floor, all requested frame levels and startup scratch. -/
theorem stackReserve_bounds (largest scratch : Nat) :
    stackReserveFloor ≤ stackReserve 0 largest scratch ∧
    FB + (stackReserveDepth + 1) * largest ≤ stackReserve 0 largest scratch ∧
    scratch ≤ stackReserve 0 largest scratch := by
  simp only [stackReserve, ↓reduceIte, ite_true]
  omega

/-- Frame width cannot reduce the depth selected from that same high-water mark. -/
theorem stackReserve_depth (largest scratch : Nat) (positive : 0 < largest) :
    stackReserveDepth ≤ depthOf (stackReserve 0 largest scratch) largest := by
  have room := (stackReserve_bounds largest scratch).2.1
  have quotient : stackReserveDepth + 1 ≤ (stackReserve 0 largest scratch - FB) / largest :=
    (Nat.le_div_iff_mul_le positive).mpr (by omega)
  unfold depthOf
  omega

/-- The actual final lowering, rather than an assumed address-independent frame size,
    certifies the depth of every accepted automatic image. -/
theorem bild_auto_depth {D : Deklaration} {passes : Nat} {P : Programm D}
    {Y : Nat → Lay D} {fs : List D.Fn} {pos : D.Fn → Nat} {name : D.Fn → String}
    {main : D.Fn} {args : Env D (D.params main)}
    {starts : List (Σ f : D.Fn, Env D (D.params f))} {req : Nat} {image : Bild D}
    (emitted : bild passes P Y fs pos name main args starts 0 req = .ok image) :
    stackReserveDepth ≤ image.depth := by
  simp only [bild] at emitted
  split at emitted
  · cases emitted
  · next preliminary firstPass =>
    split at emitted
    · cases emitted
    · next relocated secondPass =>
      split at emitted
      · next accepted =>
        simp only [Except.ok.injEq] at emitted
        subst image
        rcases accepted.2.2 with nonzero | enough
        · exact False.elim (nonzero rfl)
        · exact enough
      · exfalso
        revert emitted
        repeat' split
        all_goals intro emitted; cases emitted

/-- Small frames retain 4 MiB; wide frames get 65 complete levels; an explicit
    capacity is never silently enlarged. -/
theorem stackReserve_zeuge :
    stackReserve 0 170 32 = stackReserveFloor ∧
    stackReserve 0 40970 32 = 2663054 ∧
    depthOf (stackReserve 0 40970 32) 40970 = 64 ∧
    stackReserve 1024 40970 32 = 1024 := by
  decide +kernel

end Gabbro.Stage0.Senke
