/-
  File:      stage0/Stage0/Senke/Ausdruck/Lesen.lean
  Subject:   Reading the world: a global (`glob_ok`) and an element of a column (`slotC_ok`) are loaded from their
             address in the layout (`Lay`), where the world in memory (`WeltAt`) holds their word.
-/
import Stage0.Senke.Ausdruck.Top
import Stage0.Senke.Ausdruck.Quant.OkSeq
import Stage0.Senke.Welt.WeltAt
import Stage0.Senke.Ausdruck.Aggregat.Scalar

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

theorem slotC_fits {D : Deklaration} {L : Lay D} {t : D.Tab} {f : D.Feld t}
    {d top : Nat} {child : List II × Nat} {c : List II}
    (lower : slotC L t f d child = some (c, top)) : aggregateFits (D.typ t f) = true := by
  simp only [slotC] at lower
  split at lower
  · next fits => exact fits
  · cases lower

theorem aggregateFits_width {τ : Ty} (h : aggregateFits τ = true) : valueWords τ = 1 := by
  simp only [aggregateFits, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem aggregateFits_compat {τ : Ty} (h : aggregateFits τ = true) : WordCompatible τ := by
  simp only [aggregateFits, Bool.and_eq_true, decide_eq_true_eq] at h
  exact wordCompatB_sound τ h.2

theorem slotC_width {D : Deklaration} {L : Lay D} {t : D.Tab} {f : D.Feld t}
    {d top : Nat} {child : List II × Nat} {c : List II}
    (lower : slotC L t f d child = some (c, top)) : valueWords (D.typ t f) = 1 :=
  aggregateFits_width (slotC_fits lower)

variable {D : Deklaration} {L : Lay D} {reserved : Nat}

theorem enc_transport {τ τ' : Ty} (h : τ = τ') (v : Wert D τ) (w : Runner.W) :
    Enc L τ v w ↔ Enc L τ' (h ▸ v) w := by
  cases h; rfl

theorem enc_int_cast {τ : Ty} {a b : Int} (h : τ = .int a b) (v : Wert D τ) (w : Runner.W) :
    Enc L τ v w ↔ w = BitVec.ofInt 64 (h ▸ v : Wert D (.int a b)).n := by
  cases h; rfl

theorem enc_int_back {τ : Ty} {a b : Int} (h : τ = .int a b) (v : Wert D (.int a b)) (w : Runner.W) :
    Enc L τ (h ▸ v) w ↔ w = BitVec.ofInt 64 v.n := by
  cases h; rfl

/-- `ld d d`: slot `d` holds an address, the word there into slot `d`. -/
theorem ld_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a v : Runner.W} (h : Pre L m pc fp K d [ci 15 d d 0] ρ W reserved) (hd : d < K)
    (ha : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some a) (hv : m.rd64 a = some v) :
    Ok m pc fp K d [ci 15 d d 0] (· = v) := by
  have := h.small
  refine one_ok h (by simp [ci]) hd rfl fun m' hw => ?_
  have hi := h.code 0 (by simp)
  simp only [ci, List.getElem_cons_zero, Nat.mul_zero, BitVec.add_zero] at hi
  simp only [ci, op]
  refine f2_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  refine run_rd64 ha ?_
  refine run_rd64 hv ?_
  simp only [ret1]
  refine f1_run (t := ⟨pc, fp⟩) hi ?_
  rw [sx_nat (by omega)]
  exact run_wr64 hw

theorem slot_zero (a : Runner.W) : slot a (BitVec.ofNat 64 0) = a := by
  simp [slot]

/-- A complete cell of a word-compatible type is its single stored word in the scalar view. -/
theorem ValueAt.cellWord {D : Deklaration} {L : Lay D} {m : Runner.Mem} {a : Nat} {τ : Ty} {v : Wert D τ}
    (compatible : WordCompatible τ) (h : ValueAt L m (BitVec.ofNat 64 a) 0 τ v) :
    ∃ w, m.rd64 (BitVec.ofNat 64 a) = some w ∧ Enc L τ v w := by
  obtain ⟨w, read, encoded⟩ := ValueAt.word τ v compatible h
  rw [slot_zero] at read
  exact ⟨w, read, encoded⟩

theorem ValueAt.ofCellWord {D : Deklaration} {L : Lay D} {m : Runner.Mem} {a : Nat} {τ : Ty} {v : Wert D τ}
    {w : Runner.W} (width : valueWords τ = 1) (read : m.rd64 (BitVec.ofNat 64 a) = some w) (encoded : Enc L τ v w) :
    ValueAt L m (BitVec.ofNat 64 a) 0 τ v :=
  ValueAt.of_enc width (by rw [slot_zero]; exact read) encoded

/-- A global of a word-compatible type: its address, the word there. -/
theorem glob_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {L : Lay D} {σ : World D} {g : D.Glob} (hl : lit32 (L.ga g) = true) (hc : WordCompatible (D.gtyp g))
    (h : Pre L m pc fp K d [ci 1 d (L.ga g) 0, ci 15 d d 0] ρ W reserved) (hWL : ∀ m, W m → WeltAt m L σ) (hd : d < K) :
    Ok m pc fp K d [ci 1 d (L.ga g) 0, ci 15 d d 0] (Enc L (D.gtyp g) (σ.globs g)) := by
  have h' : Pre L m pc fp K d ([ci 1 d (L.ga g) 0] ++ [ci 15 d d 0]) ρ W reserved := h
  refine ok_seq h' (const_ok h'.left hl hd) (fun m' w hp' hr hw => ?_) (by omega)
  obtain ⟨v, hv, he⟩ := ValueAt.word _ _ hc ((hWL m' hp'.welt).2.1 g)
  rw [slot_zero] at hv
  rw [hw, BitVec.ofInt_natCast] at hr
  exact (ld_ok hp' hd hr hv).mono fun x hx => hx ▸ he

theorem slotA_top {L : Lay D} {t : D.Tab} {f : D.Feld t} {d : Nat} {ci' : List II × Nat} {c : List II} {top : Nat}
    (hs : slotA L t f d ci' = some (c, top)) : ci'.2 ≤ top ∧ d + 2 ≤ top := by
  simp only [slotA] at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; omega
  · cases hs

theorem slotC_top {L : Lay D} {t : D.Tab} {f : D.Feld t} {d : Nat} {ci' : List II × Nat} {c : List II} {top : Nat}
    (hs : slotC L t f d ci' = some (c, top)) : ci'.2 ≤ top := by
  simp only [slotC] at hs
  split at hs
  · simp only [Option.map_eq_some_iff] at hs
    obtain ⟨⟨a, ta⟩, ha, he⟩ := hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact (slotA_top ha).1
  · cases hs

/-- The address of an element (`slotA`): the index, times 8, plus the column. -/
theorem slotA_value_ok {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {k : Int} (hn0 : 0 ≤ k)
    (hw : valueWords (D.typ t f) = 1)
    {L : Lay D} {d : Nat} {ci' : List II × Nat} {c : List II} {top K : Nat} {m : Runner.Mem}
    {pc fp : Runner.W} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (hs : slotA L t f d ci' = some (c, top)) (hK : top ≤ K)
    (ih : ∀ m pc, Pre L m pc fp K d ci'.1 ρ W reserved → Ok m pc fp K d ci'.1 (· = BitVec.ofInt 64 k))
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (· = BitVec.ofNat 64 (L.elem t f k.toNat)) := by
  simp only [slotA] at hs
  split at hs
  · next hcol =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have hq : Pre L m pc fp K d (ci'.1 ++ ([ci 1 (d + 1) 8 0, ci 5 d d (d + 1)] ++
        [ci 1 (d + 1) (L.col t f) 0, ci 3 d d (d + 1)])) ρ W reserved := by
      simpa [List.append_assoc] using hp
    have := hq.small
    have hc := ok_seq hq (ih m pc hq.left) (Pb := (· = BitVec.ofNat 64 (L.elem t f k.toNat)))
      (fun m1 w1 hp1 r1 e1 => ok_seq hp1 (binK_ok hp1.left r1 (by decide) rfl (by decide) rfl (by omega))
        (Pb := (· = BitVec.ofNat 64 (L.elem t f k.toNat)))
        (fun m2 w2 hp2 r2 e2 => (binK_ok hp2 r2 hcol rfl (by decide) rfl (by omega)).mono fun x hx => by
          have := addr_w (s := 8) (c := L.col t f) hn0
          rw [e2, e1] at hx
          rw [hx, Lay.elem, hw]; exact this) (by omega))
      (by omega)
    simpa [List.append_assoc] using hc
  · cases hs

theorem slotA_ok {Λ : List (Res D)} {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {i : Expr D Γ Λ (.index (D.count t))}
    {σ₀ σ : World D} {L : Lay D} {d : Nat} {ci' : List II × Nat} {c : List II} {top K : Nat} {m : Runner.Mem}
    {pc fp : Runner.W} {ρ : Env D Γ} {W : Runner.Mem → Prop} (hw : valueWords (D.typ t f) = 1)
    (hs : slotA L t f d ci' = some (c, top)) (hK : top ≤ K)
    (ih : ∀ m pc, Pre L m pc fp K d ci'.1 ρ W reserved → Ok m pc fp K d ci'.1 (Enc L (.index (D.count t)) (eval σ₀ i σ ρ)))
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (· = BitVec.ofNat 64 (L.elem t f (eval σ₀ i σ ρ).n.toNat)) :=
  slotA_value_ok (eval σ₀ i σ ρ).lo_le hw hs hK ih hp

/-- An element of a column (`slotC`): its address, the word there. -/
theorem slotC_value_ok {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {k : Zahl 0 (D.count t - 1)}
    {σ : World D} {L : Lay D} {d : Nat} {ci' : List II × Nat} {c : List II} {top K : Nat} {m : Runner.Mem}
    {pc fp : Runner.W} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (hs : slotC L t f d ci' = some (c, top)) (hK : top ≤ K)
    (ih : ∀ m pc, Pre L m pc fp K d ci'.1 ρ W reserved → Ok m pc fp K d ci'.1 (Enc L (.index (D.count t)) k))
    (hWL : ∀ m, W m → WeltAt m L σ) (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L (D.typ t f) (σ.slots t k.n f)) := by
  have hs0 := hs
  simp only [slotC] at hs
  split at hs
  · simp only [Option.map_eq_some_iff] at hs
    obtain ⟨⟨a, ta⟩, ha, he⟩ := hs
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have ht := slotA_top ha
    have hn0 := k.lo_le
    have hkc : (k.n.toNat : Int) < D.count t := by have := k.le_hi; omega
    have hkn : ((k.n.toNat : Nat) : Int) = k.n := Int.toNat_of_nonneg hn0
    refine ok_seq hp (slotA_value_ok k.lo_le (slotC_width hs0) ha hK ih hp.left) (fun m3 w3 hp3 r3 e3 => ?_) (by have := hp.small; omega)
    obtain ⟨v, hv, he⟩ := ValueAt.word _ _ (aggregateFits_compat (slotC_fits hs0))
      ((hWL m3 hp3.welt).1 t f _ (L.bounded hkc))
    rw [slot_zero] at hv
    rw [e3] at r3
    rw [hkn] at he
    exact (ld_ok hp3 (by omega) r3 hv).mono fun x hx => hx ▸ he
  · cases hs

theorem slotC_ok {Λ : List (Res D)} {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {i : Expr D Γ Λ (.index (D.count t))}
    {σ₀ σ : World D} {L : Lay D} {d : Nat} {ci' : List II × Nat} {c : List II} {top K : Nat} {m : Runner.Mem}
    {pc fp : Runner.W} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (hs : slotC L t f d ci' = some (c, top)) (hK : top ≤ K)
    (ih : ∀ m pc, Pre L m pc fp K d ci'.1 ρ W reserved → Ok m pc fp K d ci'.1 (Enc L (.index (D.count t)) (eval σ₀ i σ ρ)))
    (hWL : ∀ m, W m → WeltAt m L σ) (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L (D.typ t f) (σ.slots t (eval σ₀ i σ ρ).n f)) :=
  slotC_value_ok hs hK ih hWL hp

end Gabbro.Stage0.Senke
