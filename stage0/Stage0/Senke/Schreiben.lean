/-
  File:      stage0/Stage0/Senke/Schreiben.lean
  Subject:   A statement that writes one cell of the world (`assignGlob`, `assignSlot`, `assignThru`): the value into
             slot `s = frei Γ`, the cell's address into `s + 1`, `st` (`store_ok`). Both parts run in the frame below
             `Ks`, so the world stays until the store; the store writes the cell's word, which lies in the world, so
             the frame below stays and the memory holds the new world (`weltAt_glob`, `weltAt_slot`).
-/
import Stage0.Senke.Aufruf
import Stage0.Senke.Welt.Schreib
import Stage0.Senke.Ausdruck.Lesen

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration}

/-- `st (s+1) s`: the word of slot `s` to the address in slot `s + 1`. -/
theorem st_step {m : Runner.Mem} {pc fp : Runner.W} {K s : Nat} {va vb : Runner.W} {m' : Runner.Mem}
    (hc : CodeAt m pc [ci 16 ((s + 1 : Nat) : Int) s 0]) (hK : s + 1 < K) (hK2 : K < 2 ^ 31)
    (ha : m.rd64 (slot fp (BitVec.ofNat 64 (s + 1))) = some va) (hb : m.rd64 (slot fp (BitVec.ofNat 64 s)) = some vb)
    (hw : m.wr64 va vb = some m') : Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * 1), fp⟩ m' := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  refine star_ins hc (by simp [ci]) ?_
  simp only [ci]
  exact run_st (t := ⟨pc, fp⟩) hi (by rw [sx_nat (by omega)]; exact ha) (by rw [sx_nat (by omega)]; exact hb) hw

/-- The store of a cell at address `a`: the value code `ce` into `s`, the address code `ca` into `s + 1`, `st`. -/
theorem store_ok {m : Runner.Mem} {pc fp : Runner.W} {K Ks lo a : Nat} {Γ : Ctx} {ρ : Env D Γ} {L : Lay D}
    {σ σ' : World D} {ce ca : List II} {Pe : Runner.W → Prop}
    (hp : PreS m pc fp K (frei Γ) (ce ++ ca ++ [stC (frei Γ)]) ρ)
    (hW : WIn L fp Ks K) (hWa : WeltAt m L σ) (hlo : lo ≤ frei Γ) (htop : frei Γ + 2 ≤ Ks)
    (hE : ∀ m pc, Pre m pc fp Ks (frei Γ) ce ρ (fun m => WeltAt m L σ) → Ok m pc fp Ks (frei Γ) ce Pe)
    (hA : ∀ m pc, Pre m pc fp Ks (frei Γ + 1) ca ρ (fun m => WeltAt m L σ) →
      Ok m pc fp Ks (frei Γ + 1) ca (· = BitVec.ofNat 64 a))
    (ha : L.lo ≤ a ∧ a + 8 ≤ L.hi)
    (hnew : ∀ m w, WeltAt m L σ → Pe w → WeltAt (write m (BitVec.ofNat 64 a) 8 w.toNat) L σ') :
    ∃ m', Star ⟨pc, fp⟩ m
        ⟨pc + BitVec.ofNat 64 (16 * (ce ++ ca ++ [stC (frei Γ)]).length), fp⟩ m' ∧
      Agree fp lo K m m' ∧ EnvAt m' fp ρ ∧ WeltAt m' L σ' := by
  have hks := hW.ks
  have hwl := hW.lo
  have hwh := hW.hi
  have hsm := hp.small
  have hq : PreS m pc fp K (frei Γ) (ce ++ (ca ++ [stC (frei Γ)])) ρ := by
    simpa [List.append_assoc] using hp
  -- the value
  have hpw := PreS.welt hq.left hks hWa hW.lay (by omega)
  obtain ⟨m1, s1, a1s, w, hw, hpe⟩ := hE m pc hpw
  have hWa1 : WeltAt m1 L σ := hpw.wstab m m1 hWa (a1s.mono (Nat.zero_le _))
  have a1 := Agree.widen a1s hks
  have hq1 := hq.next a1 (Nat.le_refl _) (by omega)
  -- the address
  have hpa := PreS.welt (hq1.left.up (d' := frei Γ + 1) (by omega)) hks hWa1 hW.lay (by omega)
  obtain ⟨m2, s2, a2s, adr, hadr, hae⟩ := hA m1 _ hpa
  have a2 := Agree.widen a2s hks
  have hF2 := hq1.frame.agree a2
  have hw2 : m2.rd64 (slot fp (BitVec.ofNat 64 (frei Γ))) = some w := by
    rw [agree_rd_low a2s (frameOK_sub hq1.frame hks).room (Nat.lt_succ_self _) (by omega)]; exact hw
  have hWa2 : WeltAt m2 L σ := hpa.wstab m1 m2 hWa1 (a2s.mono (Nat.zero_le _))
  have hq2 := hq1.next (a := ca) (a2.mono (Nat.le_succ _)) (Nat.le_refl _) (by omega)
  -- the store
  have hroom := hF2.room
  have hwr := frame_wr_at hF2 (a := a) (by omega) (by omega)
  subst hae
  have s3 := st_step hq2.code (by omega) hsm hadr hw2 (wr64_some hwr)
  have a3 : Agree fp (frei Γ) K m2 (write m2 (BitVec.ofNat 64 a) 8 w.toNat) :=
    agree_write_at hroom (by omega) (by omega) _
  have a13 : Agree fp (frei Γ) K m (write m2 (BitVec.ofNat 64 a) 8 w.toNat) :=
    a1.trans ((a2.mono (Nat.le_succ _)).trans a3)
  refine ⟨_, s1.trans (s2.trans ?_), a13.mono hlo, envAt_agree hp.env a13 hp.frame (Nat.le_refl _) (by omega),
    hnew m2 w hWa2 hpe⟩
  have e : pc + BitVec.ofNat 64 (16 * (ce ++ ca ++ [stC (frei Γ)]).length) =
      pc + BitVec.ofNat 64 (16 * ce.length) + BitVec.ofNat 64 (16 * ca.length) + BitVec.ofNat 64 (16 * 1) := by
    simp only [List.length_append, List.length_singleton, pc_add]
  rw [e]; exact s3

end Gabbro.Stage0.Senke
