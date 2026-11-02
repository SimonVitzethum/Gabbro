/-
  File:      stage0/Stage0/Senke/Anweisung/Puffer/Lauf.lean
  Subject:   The steps around a gate's buffer: `lea` of the buffer into the pointer's register (`lea_step`), arguments
             whose pointer word changed (`argsW_ptr`), a word whose bytes are kept (`rd64_keep`), and where the
             pointer parameter is (`ptrParam_spec`).
-/
module
public import Stage0.Senke.Anweisung.Puffer.Basis
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

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
    (∀ i, i < τs.length → f i = g i ∨ ∃ n rw, τs[i]? = some (.ptr n rw)) → ArgsW L f ρ → ArgsW L g ρ
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
      subst e; simp only [isPtr, if_true]

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

/-- A word of a cell's span is apart from the first word of any other cell whose span has a word. -/
theorem far_word_span {L : Lay D} (hd : LayDis L) {c c' : Zelle D} (hc : c.da L) (hc' : c'.da L) (hne : c ≠ c')
    {i : Nat} (hi : 8 * (i + 1) ≤ c.bytes) (h8 : 8 ≤ c'.bytes)
    (ha : c.adr L + c.bytes < 2 ^ 31) (hb : c'.adr L + c'.bytes < 2 ^ 31) :
    Far (BitVec.ofNat 64 (c.adr L + 8 * i)) 8 (BitVec.ofNat 64 (c'.adr L)) 8 := by
  have spans := hd.spans c c' hc hc' hne
  have e1 : (BitVec.ofNat 64 (c.adr L + 8 * i)).toNat = c.adr L + 8 * i := by
    simp only [BitVec.toNat_ofNat]; omega
  have e2 : (BitVec.ofNat 64 (c'.adr L)).toNat = c'.adr L := by
    simp only [BitVec.toNat_ofNat]; omega
  unfold Far
  rw [e1, e2]
  omega

/-- **The oracle's world after a buffer**: the world apart from the byte field as before, the field's elements the
    words now in its cells. The byte field's cells are one word each. -/
theorem weltAt_puf {L : Lay D} {t : D.Tab} {f : D.Feld t} {σ' : World D} {m0 mF : Runner.Mem} {fp : Runner.W}
    {Ks : Nat} (hw1 : valueWords (D.typ t f) = 1) (hl : LayIn L) (hd : LayDis L)
    (hwlo : fp.toNat + 8 * Ks ≤ L.lo) (hcount : L.count t = D.count t) (hO : WeltOhne m0 L σ' t f)
    (hcol : ∀ k, k < (D.count t).toNat →
      ValueAt L mF (BitVec.ofNat 64 (L.elem t f k)) 0 (D.typ t f) (σ'.slots t k f))
    (hrest : ∀ a : Nat, a + 8 ≤ 2 ^ 64 → fp.toNat + 8 * Ks ≤ a →
      (∀ k, k < (D.count t).toNat → Far (BitVec.ofNat 64 a) 8 (BitVec.ofNat 64 (L.elem t f k)) 8) →
      mF.rd64 (BitVec.ofNat 64 a) = m0.rd64 (BitVec.ofNat 64 a)) (hwr : WeltWr mF L) :
    WeltAt mF L σ' := by
  have hl3 := hl.2.2
  have bounds : ∀ c : Zelle D, c.da L → L.lo ≤ c.adr L ∧ c.adr L + c.bytes ≤ L.hi := fun c hc => by
    cases c with
    | glob g => simpa only [Zelle.adr, Zelle.bytes] using hl.2.1 g
    | elem t' f' k' => simpa only [Zelle.adr, Zelle.bytes] using hl.1 t' f' k' hc
  have keepAt : ∀ (c : Zelle D) (τ : Ty) (v : Wert D τ), c.da L → (∀ k : Nat, c ≠ .elem t f k) →
      c.bytes = 8 * valueWords τ → ValueAt L m0 (BitVec.ofNat 64 (c.adr L)) 0 τ v →
      ValueAt L mF (BitVec.ofNat 64 (c.adr L)) 0 τ v := by
    intro c τ v hc hne hbytes input
    refine ⟨input.1, fun i hi => ?_⟩
    have idx : i < valueWords τ := by simpa only [encodeWords_length] using hi
    have addr : slot (BitVec.ofNat 64 (c.adr L)) (BitVec.ofNat 64 (0 + i)) =
        BitVec.ofNat 64 (c.adr L + 8 * i) := by
      simp only [Nat.zero_add, slot]
      change BitVec.ofNat 64 (c.adr L) + BitVec.ofNat 64 i * BitVec.ofNat 64 8 = _
      rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
      congr 1; omega
    have h := input.2 i hi
    rw [addr] at h ⊢
    have bnd := bounds c hc
    rw [hrest (c.adr L + 8 * i) (by omega) (by omega) (fun k hk => by
      have cell := hl.1 t f k (L.bounded (by omega))
      refine far_word_span hd hc (by simp only [Zelle.da]; apply L.bounded; omega) (hne k)
        (i := i) (by omega) (by simp only [Zelle.bytes, hw1]; omega) (by omega)
        (by simp only [Zelle.adr, Zelle.bytes, hw1]; rw [hw1] at cell; omega))]
    exact h
  refine ⟨fun t' f' k hk => ?_, fun g => ?_, hwr⟩
  · by_cases hc : ∃ k'' : Nat, (Zelle.elem t' f' k : Zelle D) = .elem t f k''
    · obtain ⟨k'', he⟩ := hc
      cases he
      exact hcol k (by rw [hcount] at hk; omega)
    · have hne : ∀ k'' : Nat, (Zelle.elem t' f' k : Zelle D) ≠ .elem t f k'' := fun k'' e => hc ⟨k'', e⟩
      exact keepAt (.elem t' f' k) _ _ hk hne rfl (hO.1 t' f' k hk hne)
  · exact keepAt (.glob g) _ _ trivial (fun _ e => by cases e) rfl (hO.2 g)

end Gabbro.Stage0.Senke
