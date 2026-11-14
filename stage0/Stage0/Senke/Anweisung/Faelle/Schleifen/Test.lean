/- One real retry condition and its two branches, retaining the read world. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Retrying.Image
@[expose] public section

namespace Gabbro.Stage0.Senke.Retrying.Image
open Gabbro.Grammatik Runner Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {P : Programm D} {f : D.Fn}
variable {Γ : Ctx} {reserved : Nat} (x : Image L P f Γ reserved)

/-- The condition executes once in its canonical read world. A true result
    exits; false reaches the counter. Both paths preserve the reserved pair. -/
theorem test_run {Λ : List (Res D)} {bis : Expr D Γ Λ .bool} {tc : Nat}
    (lowered : lowE (reserved := reserved) L bis (frei Γ reserved) = some (x.condition, tc))
    (top : tc ≤ x.Ks) {m : Mem} {σ : World D} {ρ : Env D Γ}
    (ready : x.Ready m σ ρ) :
    let σr := σ.lese Λ bis.orte
    let b := wahr? (eval σr bis σr ρ)
    ∃ m', Star ⟨x.pc, x.fp⟩ m
        ⟨if b then x.addr x.exitIndex else x.addr x.controlIndex, x.fp⟩ m' ∧
      AgreeW L x.fp x.lo x.K m m' ∧
      Keeps x.fp (x.counter :: x.one :: x.pr) m m' ∧ x.Ready m' σr ρ := by
  let σr := σ.lese Λ bis.orte
  change ∃ m', Star ⟨x.pc, x.fp⟩ m
      ⟨if wahr? (eval σr bis σr ρ) then x.addr x.exitIndex else x.addr x.controlIndex, x.fp⟩ m' ∧
    AgreeW L x.fp x.lo x.K m m' ∧
    Keeps x.fp (x.counter :: x.one :: x.pr) m m' ∧ x.Ready m' σr ρ
  have pre := PreS.welt ready.condition x.layout.ks ready.world x.layout.lay
    (by have := x.layout.lo; omega)
  obtain ⟨m1, run, frame, w, read, value⟩ := lowE_ok
    (same := by intro _; rfl) σr σr (fun _ h => h) x.layout.lay bis
      (frei Γ reserved) x.condition tc lowered top m x.pc ρ pre |>.word trivial
  have bound : frei Γ reserved ≤ x.K := by have := x.room; have := x.layout.ks; omega
  have low : x.lo ≤ frei Γ reserved := by have := x.controls; unfold frei; omega
  have full := Agree.widen frame x.layout.ks
  have changed := agreeW_of (D := D) (L := L) (full.mono low)
  have world : WeltAt m1 L σr :=
    weltAt_stab x.layout.lay x.layout.top m m1 ready.world (full.mono (Nat.zero_le _))
  have final := ready.after changed
    (envAt_agree ready.pre.env full ready.pre.frame (Nat.le_refl _) bound) world
  have kept : Keeps x.fp (x.counter :: x.one :: x.pr) m m1 := by
    apply keeps_of_agreeW x.layout (agreeW_of (D := D) (L := L) full)
    · intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | rfl | hj
      · have := x.controls; unfold frei; omega
      · have := x.controls; unfold frei; omega
      · exact (x.kept j hj).1
    · exact bound
  have scratch : frei Γ reserved < x.K := by have := x.room; have := x.layout.ks; omega
  have small := ready.pre.small
  have falseTarget : x.addr x.condition.length + BitVec.ofInt 64 32 = x.addr x.controlIndex :=
    adr_eq x.pc (x := x.condition.length) (y := x.controlIndex) (by
      dsimp only [controlIndex]; omega)
  have trueStart : x.addr x.condition.length + BitVec.ofNat 64 (16 * 1) =
      x.addr (x.condition.length + 1) := step_eq x.pc (by omega)
  have trueTarget : x.addr (x.condition.length + 1) +
      BitVec.ofInt 64 (16 * (x.body.length + x.overflow.length + 4 : Nat)) =
      x.addr x.exitIndex := adr_eq x.pc (x := x.condition.length + 1) (y := x.exitIndex) (by
        dsimp only [exitIndex]; omega)
  change w = (if wahr? (eval σr bis σr ρ) = true then 1 else 0) at value
  cases hb : wahr? (eval σr bis σr ρ) with
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    have v : w = 0 := by simpa only [hb, Bool.false_eq_true, ↓reduceIte] using value
    have branch := brz_go final.test scratch small (by decide)
      (by rw [← v]; exact read)
    rw [falseTarget] at branch
    exact ⟨m1, run.trans branch, changed, kept, final⟩
  | true =>
    simp only [hb, ↓reduceIte]
    have v : w = 1 := by simpa only [hb, ↓reduceIte] using value
    have branch := brz_stay final.test scratch small read (by rw [v]; decide)
    rw [trueStart] at branch
    have jump := jmp_go (fp := x.fp) final.exitJump (retry_displacements _ _ _ x.sized).1
    rw [show (16 * ((x.body.length : Int) + x.overflow.length + 4)) =
      16 * ((x.body.length + x.overflow.length + 4 : Nat) : Int) by omega, trueTarget] at jump
    exact ⟨m1, run.trans (branch.trans jump), changed, kept, final⟩

end Gabbro.Stage0.Senke.Retrying.Image
