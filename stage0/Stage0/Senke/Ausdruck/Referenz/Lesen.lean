/- Subject: Open-table references are checked cell indices in separately supplied regions.
   No word is converted to a pointer: slotA derives addresses from the layout's column base.
   Enc ties the index to its declared open table and represented cells, without bounding G. -/
import Stage0.Senke.Ausdruck.Lesen
import Stage0.Senke.Ausdruck.Aggregat.Wort

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- The declared table of an encoded reference contains its represented cell. -/
theorem enc_ref_cell {n k : Nat} {w : Runner.W} {t : D.Tab}
    (h : Enc L (.ref n) k w) (ht : D.tabNr n = some t) : (k : Int) < L.count t := by
  obtain ⟨_, _, t', ht', _, hk⟩ := h
  have : t' = t := Option.some.inj (ht'.symm.trans ht)
  subst t'
  exact hk

/-- A reference's column address, retaining the region membership needed by reads and writes. -/
theorem slotRefA_ok {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {n k : Nat}
    {d top K : Nat} {cr : List II × Nat} {c : List II} {m : Runner.Mem} {pc fp : Runner.W}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} (ht : D.tabNr n = some t)
    (hs : slotA L t f d cr = some (c, top)) (hK : top ≤ K)
    (ih : ∀ m pc, Pre L m pc fp K d cr.1 ρ W reserved → Ok m pc fp K d cr.1 (Enc L (.ref n) k))
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (fun w => w = BitVec.ofNat 64 (L.elem t f k) ∧ (k : Int) < L.count t) := by
  have hs0 := hs
  simp only [slotA] at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨_, _, _, _, _, he⟩ := ih m pc hp.left
    have hk := enc_ref_cell he ht
    have ha := slotA_value_ok (k := (k : Int)) (Int.natCast_nonneg k) hs0 hK
      (fun m pc hp => (ih m pc hp).mono fun w hw => hw.1.trans (BitVec.ofInt_natCast 64 k).symm) hp
    exact ha.mono fun w hw => ⟨by simpa only [Int.toNat_natCast] using hw, hk⟩
  · cases hs

/-- A field read through a reference uses the same load and column layout as bounded tables. -/
theorem slotRefC_ok {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {n k : Nat}
    {σ : World D} {d top K : Nat} {cr : List II × Nat} {c : List II} {m : Runner.Mem}
    {pc fp : Runner.W} {ρ : Env D Γ} {W : Runner.Mem → Prop} (ht : D.tabNr n = some t)
    (hs : slotC L t f d cr = some (c, top)) (hK : top ≤ K)
    (ih : ∀ m pc, Pre L m pc fp K d cr.1 ρ W reserved → Ok m pc fp K d cr.1 (Enc L (.ref n) k))
    (hWL : ∀ m, W m → WeltAt m L σ) (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L (D.typ t f) (σ.slots t (k : Int) f)) := by
  simp only [slotC] at hs
  split at hs
  · simp only [Option.map_eq_some_iff] at hs
    obtain ⟨⟨a, ta⟩, ha, he⟩ := hs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hb := slotA_top ha
    refine ok_seq hp (slotRefA_ok ht ha hK ih hp.left) (fun m' w hp' hr he => ?_) (by omega)
    obtain ⟨v, hv, hev⟩ := (hWL m' hp'.welt).1 t f k he.2
    rw [he.1] at hr
    exact (ld_ok hp' (by omega) hr hv).mono fun w hw => hw ▸ hev
  · cases hs

/-- Reference equality is word equality because Enc excludes truncation, including at 2^64. -/
theorem refEq_ok {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {σ₀ σ : World D}
    {fp pc : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (a b : Expr D Γ Λ (.ref n))
    (iha : ∀ ca ta, lowE L (reserved := reserved) a d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca (Enc L (.ref n) (eval σ₀ a σ ρ)))
    (ihb : ∀ cb tb, lowE L (reserved := reserved) b (d + 1) = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb (Enc L (.ref n) (eval σ₀ b σ ρ)))
    (h : lowE L (reserved := reserved) (.refEq a b) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L .bool (eval σ₀ (.refEq a b) σ ρ)) := by
  refine wordL_ok h hK iha ihb (g := fun x y => some (Runner.IR.bool (x == y))) ?_ rfl (by decide) hp
  intro wa wb ha hb
  refine ⟨_, rfl, ?_⟩
  have he : (BitVec.ofNat 64 (eval σ₀ a σ ρ).zelle == BitVec.ofNat 64 (eval σ₀ b σ ρ).zelle) =
      decide ((eval σ₀ a σ ρ).zelle = (eval σ₀ b σ ρ).zelle) := by
    by_cases h : (eval σ₀ a σ ρ).zelle = (eval σ₀ b σ ρ).zelle
    · simp [h]
    · have hn : BitVec.ofNat 64 (eval σ₀ a σ ρ).zelle ≠ BitVec.ofNat 64 (eval σ₀ b σ ρ).zelle := by
        intro e
        have e' := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha.2.1, Nat.mod_eq_of_lt hb.2.1] at e'
        exact h e'
      simp [h, hn]
  simp only [Enc, eval, wahr?, ha.1, hb.1, he, bool_word]
  rfl

end Gabbro.Stage0.Senke
