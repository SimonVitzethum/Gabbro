/-
  File:      stage0/Stage0/Senke/Anweisung/PufferLauf.lean
  Subject:   The steps around a gate's buffer: `lea` of the buffer into the pointer's register (`lea_step`), arguments
             whose pointer word changed (`argsW_ptr`), a word whose bytes are kept (`rd64_keep`), and where the
             pointer parameter is (`ptrParam_spec`).
-/
import Stage0.Senke.Anweisung.Puffer

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

/-- `lea d a`: slot `d` gets the address of slot `a`. -/
theorem lea_step {m : Runner.Mem} {pc fp : Runner.W} {K d a : Nat} (hc : CodeAt m pc [ci 17 d a 0])
    (hF : FrameOK m fp K) (hd : d < K) (ha : a < 2 ^ 31) (hK : K < 2 ^ 31) :
    Star ⟨pc, fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * [ci 17 d a 0].length), fp⟩
      (write m (slot fp (BitVec.ofNat 64 d)) 8 (slot fp (BitVec.ofNat 64 a)).toNat) := by
  have hi := hc 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  refine star_ins hc (by simp [ci]) ?_
  simp only [ci, op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (d := d) (by omega), sx_nat (d := a) ha]
  exact run_wr64 (wr64_some (hF.wr d hd))

/-- Arguments whose words agree apart from pointers. -/
theorem argsW_ptr {f g : Nat → Runner.W} : {τs : List Ty} → (ρ : Env D τs) →
    (∀ i, i < τs.length → f i = g i ∨ ∃ n rw, τs[i]? = some (.ptr n rw)) → ArgsW f ρ → ArgsW g ρ
  | [], .nil, _, _ => trivial
  | τ :: τs, .cons _ ρ, he, h => by
    simp only [ArgsW] at h ⊢
    refine ⟨?_, argsW_ptr ρ (fun i hi => by
      rcases he (i + 1) (by simp; omega) with e | ⟨n, rw, e⟩
      · exact .inl e
      · exact .inr ⟨n, rw, by simpa using e⟩) h.2⟩
    rcases he 0 (by simp) with e | ⟨n, rw, e⟩
    · rw [← e]; exact h.1
    · simp only [List.length_cons, Nat.lt_add_one_iff, List.getElem?_cons_zero, Option.some.injEq] at e
      subst e; trivial

/-- A word whose bytes and readability are kept reads the same. -/
theorem ptrParam_spec {τs : List Ty} {j n : Nat} {rw : Bool} (h : ptrParam τs = some (j, n, rw)) :
    j < τs.length ∧ τs[j]? = some (.ptr n rw) := by
  simp only [ptrParam] at h
  split at h
  · next j' hj =>
    split at h
    · next n' rw' he =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨(List.findIdx?_eq_some_iff_getElem.mp hj).1, he⟩
    · cases h
  · cases h

/-- A slot written is not a word of the world above the frame. -/
theorem rd64_write_slot {m : Runner.Mem} {fp : Runner.W} {Ks i a : Nat} {v : Nat} (hr : fp.toNat + 8 * Ks ≤ 2 ^ 64)
    (hi : i < Ks) (ha : fp.toNat + 8 * Ks ≤ a) (ha2 : a + 8 ≤ 2 ^ 64) :
    (write m (slot fp (BitVec.ofNat 64 i)) 8 v).rd64 (BitVec.ofNat 64 a) = m.rd64 (BitVec.ofNat 64 a) := by
  apply rd64_write_far
  have hs := slot_toNat (i := i) hr hi
  have : (BitVec.ofNat 64 a).toNat = a := by simp only [BitVec.toNat_ofNat]; omega
  unfold Far; rw [hs, this]; omega

/-- **The oracle's world after a buffer**: the world apart from the byte field as before, the field's elements the
    words now in its cells. -/
theorem weltAt_puf {L : Lay D} {t : D.Tab} {f : D.Feld t} {σ' : World D} {m0 mF : Runner.Mem} {fp : Runner.W}
    {Ks : Nat} (hl : LayIn L) (hd : LayDis L) (hwlo : fp.toNat + 8 * Ks ≤ L.lo) (hO : WeltOhne m0 L σ' t f)
    (hcol : ∀ k, k < (D.count t).toNat → ∃ w, mF.rd64 (BitVec.ofNat 64 (L.elem t f k)) = some w ∧
      Enc (D.typ t f) (σ'.slots t k f) w)
    (hrest : ∀ a : Nat, a + 8 ≤ 2 ^ 64 → fp.toNat + 8 * Ks ≤ a →
      (∀ k, k < (D.count t).toNat → Far (BitVec.ofNat 64 a) 8 (BitVec.ofNat 64 (L.elem t f k)) 8) →
      mF.rd64 (BitVec.ofNat 64 a) = m0.rd64 (BitVec.ofNat 64 a)) (hwr : WeltWr mF L) :
    WeltAt mF L σ' := by
  have hl3 := hl.2.2
  have far : ∀ (c : Zelle D), c.da → (∀ k : Nat, c ≠ .elem t f k) → ∀ k, k < (D.count t).toNat →
      Far (BitVec.ofNat 64 (c.adr L)) 8 (BitVec.ofNat 64 (L.elem t f k)) 8 := fun c hc hne k hk => by
    have hin : c.adr L + 8 ≤ L.hi := by
      cases c with
      | glob g => exact (hl.2.1 g).2
      | elem t' f' k' => exact (hl.1 t' f' k' hc).2
    have hk' := (hl.1 t f k (by omega)).2
    have := cell_far (c := c) (c' := .elem t f k) hl hd hc (by simp [Zelle.da]; omega) hin
      (by simpa [Zelle.adr] using hk') (hne k)
    simpa [Zelle.adr] using this
  have lo : ∀ (c : Zelle D), c.da → L.lo ≤ c.adr L := fun c hc => by
    cases c with
    | glob g => exact (hl.2.1 g).1
    | elem t' f' k' => exact (hl.1 t' f' k' hc).1
  refine ⟨fun t' f' k hk => ?_, fun g => ?_, hwr⟩
  · by_cases hc : ∃ k'' : Nat, (Zelle.elem t' f' k : Zelle D) = .elem t f k''
    · obtain ⟨k'', he⟩ := hc
      cases he
      exact hcol k (by omega)
    · have hne : ∀ k'' : Nat, (Zelle.elem t' f' k : Zelle D) ≠ .elem t f k'' := fun k'' e => hc ⟨k'', e⟩
      obtain ⟨w, hw, he⟩ := hO.1 t' f' k hk hne
      refine ⟨w, ?_, he⟩
      have h1 := (hl.1 t' f' k hk).2
      have h2 := lo (.elem t' f' k) hk
      simp only [Zelle.adr] at h2
      have hf := far (.elem t' f' k) hk hne
      simp only [Zelle.adr] at hf
      rw [hrest (L.elem t' f' k) (by omega) (by omega) hf]
      exact hw
  · obtain ⟨w, hw, he⟩ := hO.2 g
    refine ⟨w, ?_, he⟩
    have h1 := (hl.2.1 g).2
    have h2 := (hl.2.1 g).1
    have hf := far (.glob g) trivial (fun _ e => by cases e)
    simp only [Zelle.adr] at hf
    rw [hrest (L.ga g) (by omega) (by omega) hf]
    exact hw

end Gabbro.Stage0.Senke
