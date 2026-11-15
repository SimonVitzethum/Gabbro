/- The image return of a block binder, including the complete frame-slot copy. -/
module
public import Stage0.Senke.Bild.Block.Rand
public import Stage0.Senke.Anweisung.Faelle.BlockRuf
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Stage0.Senke Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable {D : Deklaration} [Kern]

/-- A normal result is copied from the callee's shared return area into the new
    lexical variable's complete frame slot. The following block starts with its
    extended environment; no part of that block is executed by this lemma. -/
theorem BodyFrame.randBIR_bindCall {B : BodyFrame D} (hB : B.Ok) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : Ty} {g : D.Fn} {args : Args D Γ Λ (D.params g)}
    {he : D.erg g = some τ} {hp : RufPasst D (vertragVon D B.f) (D.signatur g) Λ}
    {hr : D.gruende g = 0} {rest : Block D (vertragVon D B.f) l (τ :: Γ) (nach D g Λ) Λ'}
    {pc : Runner.W} {m : Runner.Mem} {σ σ2 : World D} {ρ : Env D Γ} {v : ErgVal D (D.erg g)}
    (h : B.RandBIR (.bindCall g args he hp hr rest) pc m σ ρ)
    (hR : B.R g (σ.lese Λ args.orte) (rufEnv g σ Λ args ρ) = .ok σ2 v) :
    ∃ (n : Nat) (m2 : Runner.Mem),
      Star ⟨pc, B.fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * n), B.fp⟩ m2 ∧
      AgreeW B.L B.fp B.lo B.K m m2 ∧
      ValueAt B.L m2 B.fp (frei Γ B.reserved) τ (ergWert he v) ∧
      B.RandBIR rest (pc + BitVec.ofNat 64 (16 * n)) m2 σ2 (.cons (ergWert he v) ρ) := by
  obtain ⟨c, top, hl, ht, hs, pre, hlo, hu, hk, hw, hpr, hH⟩ := h
  simp only [lowB, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hl
  obtain ⟨⟨ca, ta⟩, hca, ⟨cr, tr⟩, hcr, hc⟩ := hl
  simp only [Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [List.length_append] at hs
  have hW := hB.win
  have hks := hW.ks
  have hct : frei Γ B.reserved + FB + contextWords (D.params g) + 1 ≤
      callTop g (frei Γ B.reserved) ta := by simp only [callTop]; omega
  have hc := callC_ok (same := rfl) hB.spec (hB.addr g) args (σ.lese Λ args.orte)
    (σ.lese Λ args.orte) hca (by omega) pre.left.left hu hW hw
    (HeldIn.ruf (V := vertragVon D B.f) hH hp)
  rw [hR] at hc
  obtain ⟨m1, s1, a1, ⟨result, _, _⟩, hw1⟩ := hc
  have pre1 := pre.left.nextW hW a1 (by have := pre.ctx; omega) (Nat.le_refl _) (by omega)
  obtain ⟨m2, s2, a2s, copied, _⟩ := receive_run (D.signatur g)
    (frameOK_sub pre1.frame hks) (by have := pre.small; omega) (by omega) pre1.code
    (codeFar_sub2 pre1.far hks)
  rw [← pc_add1] at s2
  have a2 : Agree B.fp (frei Γ B.reserved) B.K m1 m2 := Agree.widen a2s hks
  have received : ValueAt B.L m2 B.fp (frei Γ B.reserved) τ (ergWert he v) := by
    have source := ValueAt.frame_shift.mp (resultAt_wert he result)
    apply source.copy_region ?_ (by simpa only [Deklaration.params, Nat.add_assoc] using copied)
    have width := resultWords_le_returnWords (D.erg g) (D.gruende g)
    change valueWords τ ≤ returnWords (D.erg g) (D.gruende g)
    simpa only [he, resultWords] using width
  have hw2 : WeltAt m2 B.L σ2 :=
    weltAt_stab hW.lay (by have := hW.lo; omega) m1 m2 hw1 (a2s.mono (Nat.zero_le _))
  have a := a1.trans (agreeW_of a2)
  have pre2 := pre.nextW hW a (d' := frei (τ :: Γ) B.reserved)
    (by have := pre.ctx; omega) (by simp only [frei_cons]; omega) (by omega)
  have preR : PreS B.L m2 _ B.fp B.K (frei (τ :: Γ) B.reserved) cr
      (Env.cons (ergWert he v) ρ) B.reserved :=
    ⟨Nat.le_refl _, pre2.small, pre2.frame, pre2.code, pre2.far,
      envAt_cons pre2.env received, trivial, wstab_true _ _⟩
  have hloR : B.lo ≤ frei (τ :: Γ) B.reserved := by simp only [frei_cons]; omega
  refine ⟨(callC B.A g (frei Γ B.reserved) ca ++ receiveC (D.signatur g) (frei Γ B.reserved)).length,
    m2, s1.trans s2, a.mono hlo, received, cr, tr, hcr, by omega, by omega, preR, hloR,
    hu.agreeW hW a (by simp only [frei]; omega), hk.agreeW hW a (by rw [← hB.lo0]; exact hlo), hw2, ?_, ?_⟩
  · intro i hi
    have := hpr i hi
    simp only [frei_cons]
    omega
  · exact hH.sig

#print axioms BodyFrame.randBIR_bindCall

end Gabbro.Stage0.Senke.BildLauf
