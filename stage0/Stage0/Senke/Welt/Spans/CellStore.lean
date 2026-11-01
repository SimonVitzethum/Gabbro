/- Connected complete table-cell read and write: expression child, address producer, runtime
   transport and the canonical source-world update compose under the original generic
   expression precondition. -/
import Stage0.Senke.Welt.Spans.Cell
import Stage0.Senke.Welt.Spans.StoreWorld
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem slotValueC_top {t : D.Tab} {f : D.Feld t} {d : Nat} {index : List II × Nat}
    {code : List II} {top : Nat} (made : slotValueC L t f d index = some (code, top)) :
    index.2 ≤ top ∧ d + valueWords (D.typ t f) + 2 ≤ top := by
  unfold slotValueC at made
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
  obtain ⟨⟨ca, ta⟩, hca, -, rfl⟩ := made
  have := cellAddressC_top hca
  simp only at this ⊢
  omega

/-- A complete cell read: the whole `ValueAt` span of the addressed cell is produced. -/
theorem slotValueC_ok {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {σ : World D} {idx : Nat} {d K reserved top : Nat}
    {code : List II} {index : List II × Nat} {m : Runner.Mem} {pc fp : Runner.W} {ρ : Env D Γ}
    {W : Runner.Mem → Prop}
    (made : slotValueC L t f d index = some (code, top)) (room : top ≤ K)
    (cell : (idx : Int) < L.count t) (layout : LayIn L)
    (ih : ∀ m pc, Pre L m pc fp K (d + valueWords (D.typ t f)) index.1 ρ W reserved →
      Ok m pc fp K (d + valueWords (D.typ t f)) index.1 (· = BitVec.ofNat 64 idx))
    (world : ∀ m, W m → WeltAt m L σ) (pre : Pre L m pc fp K d code ρ W reserved) :
    ValueOk L m pc fp K d code (D.typ t f) (σ.slots t idx f) := by
  have tops := slotValueC_top made
  have hin := layout.1 t f idx cell
  have top31 := layout.2.2
  unfold slotValueC at made
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
  obtain ⟨⟨ca, ta⟩, hca, rfl, rfl⟩ := made
  exact pointerWorldValue_ok (a := BitVec.ofNat 64 (L.elem t f idx)) (by omega) (by omega) pre
    (fun m pc hp => cellAddressC_ok hca (by have := cellAddressC_top hca; omega) ih hp)
    (fun m hm => (world m hm).1 t f idx cell)

theorem slotStoreC_top {t : D.Tab} {f : D.Feld t} {d : Nat} {child index : List II × Nat}
    {code : List II} {top : Nat} (made : slotStoreC L t f d child index = some (code, top)) :
    child.2 ≤ top ∧ index.2 ≤ top ∧ d + valueWords (D.typ t f) + 2 ≤ top := by
  unfold slotStoreC at made
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
  obtain ⟨⟨ca, ta⟩, hca, -, rfl⟩ := made
  have := cellAddressC_top hca
  simp only at this ⊢
  omega

/-- Connected expression evaluation, address production and the actual complete cell store. -/
theorem slotStoreC_ok {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {σ : World D} {kn : Nat} {d K reserved top : Nat}
    {v : Wert D (D.typ t f)} {code : List II} {child index : List II × Nat}
    {m : Runner.Mem} {pc fp : Runner.W} {ρ : Env D Γ}
    (made : slotStoreC L t f d child index = some (code, top)) (fits : top ≤ K)
    (cell : (kn : Int) < L.count t) (layout : LayIn L) (apart : LayDis L)
    (separated : fp.toNat + 8 * K ≤ L.lo)
    (pre : Pre L m pc fp K d code ρ (fun m => WeltAt m L σ) reserved)
    (expression : ∀ m pc, Pre L m pc fp K d child.1 ρ (fun m => WeltAt m L σ) reserved →
      ValueOk L m pc fp K d child.1 (D.typ t f) v)
    (indexOk : ∀ m pc, Pre L m pc fp K (d + valueWords (D.typ t f)) index.1 ρ
        (fun m => WeltAt m L σ) reserved →
      Ok m pc fp K (d + valueWords (D.typ t f)) index.1 (· = BitVec.ofNat 64 kn)) :
    ∃ m', Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩ m' ∧
      AgreeW L fp d K m m' ∧ WeltAt m' L (σ.storeSlot t kn f v) := by
  have tops := slotStoreC_top made
  have hin := layout.1 t f kn cell
  have top31 := layout.2.2
  unfold slotStoreC at made
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at made
  obtain ⟨⟨ca, ta⟩, hca, rfl, rfl⟩ := made
  have caTop := cellAddressC_top hca
  simp only at caTop tops
  have firstAddress : (BitVec.ofNat 64 (L.elem t f kn)).toNat = L.elem t f kn := by
    simp only [BitVec.toNat_ofNat]; omega
  obtain ⟨m1, s1, a1, value⟩ := expression m pc pre.left.left
  have next := pre.left.next (d' := d + valueWords (D.typ t f)) a1 (Nat.le_add_right d _) (by omega)
  obtain ⟨m2, s2, a2, w2, r2, e2⟩ := cellAddressC_ok hca (by omega) indexOk next
  subst e2
  have a12 : Agree fp d K m m2 := a1.trans (a2.mono (Nat.le_add_right d _))
  have kept : ValueAt L m2 fp d (D.typ t f) v :=
    value.agree_low a2 (by have := pre.frame.room; omega) (Nat.le_refl _) (by omega)
  have after := pre.next a12 (Nat.le_refl _) (by omega)
  have old := after.welt.1 t f kn cell
  have wrAll : ∀ i, i < valueWords (D.typ t f) →
      all m2.wr (BitVec.ofNat 64 ((BitVec.ofNat 64 (L.elem t f kn)).toNat + 8 * i)) 8 = true := by
    intro i hi'
    rw [firstAddress]
    exact after.welt.2.2.word (by omega) (by omega) top31
  have rdAll : ∀ i, i < valueWords (D.typ t f) →
      all m2.rd (BitVec.ofNat 64 ((BitVec.ofNat 64 (L.elem t f kn)).toNat + 8 * i)) 8 = true := by
    intro i hi'
    rw [firstAddress]
    exact rd64_some_all (by
      simpa only [Nat.zero_add, absolute_slot] using old.2 i (by simpa only [encodeWords_length] using hi'))
  obtain ⟨m3, s3, effect, output, -⟩ := storePointerValue_run layout separated pre.small
    (Nat.lt_succ_self _) (by omega) after.frame (Nat.le_refl _) (by omega)
    (by rw [firstAddress]; omega) (by rw [firstAddress]; omega)
    after.code (by simpa only [storePointerSpan_length] using after.far) r2 kept wrAll rdAll
  rw [firstAddress] at effect output
  have newWorld := weltAt_slot_effect after.welt layout apart (by omega) cell effect output
  have changed : AgreeW L fp d K m m3 :=
    (agreeW_of a12).trans ((effect.agreeW (by omega) (by omega) (by omega)).mono (by omega))
  refine ⟨m3, ?_, changed, newWorld⟩
  have pcEq : pc + BitVec.ofNat 64 (16 * (child.1 ++ ca).length) =
      pc + BitVec.ofNat 64 (16 * child.1.length) + BitVec.ofNat 64 (16 * ca.length) := by
    rw [List.length_append, pc_add]
  rw [pcEq] at s3
  have combined := s1.trans (s2.trans s3)
  simpa [List.length_append, storePointerSpan_length, Nat.mul_add, ← Nat.mul_assoc,
    BitVec.ofNat_add, BitVec.add_assoc] using combined

end Gabbro.Stage0.Senke
