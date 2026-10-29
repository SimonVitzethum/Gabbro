/-
  File:      stage0/Stage0/Senke/Ausdruck/Lesen.lean
  Subject:   Reading the world: a global (`glob_ok`) and an element of a column (`slotC_ok`) are loaded from their
             address in the layout (`Lay`), where the world in memory (`WeltAt`) holds their word.
-/
import Stage0.Senke.Ausdruck.Top
import Stage0.Senke.Welt.WeltAt

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration} {L : Lay D}

theorem enc_int_cast {τ : Ty} {a b : Int} (h : τ = .int a b) (v : Wert D τ) (w : Runner.W) :
    Enc L τ v w ↔ w = BitVec.ofInt 64 (h ▸ v : Wert D (.int a b)).n := by
  cases h; rfl

theorem enc_int_back {τ : Ty} {a b : Int} (h : τ = .int a b) (v : Wert D (.int a b)) (w : Runner.W) :
    Enc L τ (h ▸ v) w ↔ w = BitVec.ofInt 64 v.n := by
  cases h; rfl

/-- Code in two parts: what the first leaves in slot `d` is what the second starts from. -/
theorem ok_seq {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {a b : List II} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {Pa Pb : Runner.W → Prop} (h : Pre L m pc fp K d (a ++ b) ρ W)
    (ha : Ok m pc fp K d a Pa)
    (hb : ∀ m' w, Pre L m' (pc + BitVec.ofNat 64 (16 * a.length)) fp K d b ρ W →
      m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some w → Pa w →
      Ok m' (pc + BitVec.ofNat 64 (16 * a.length)) fp K d b Pb)
    (hK : d ≤ K) : Ok m pc fp K d (a ++ b) Pb := by
  obtain ⟨m1, s1, a1, w, r, p⟩ := ha
  have hp1 := h.next a1 (Nat.le_refl _) hK
  obtain ⟨m2, s2, a2, w2, r2, p2⟩ := hb m1 w hp1 r p
  refine ⟨m2, s1.trans ?_, a1.trans a2, w2, r2, p2⟩
  have e : pc + BitVec.ofNat 64 (16 * (a ++ b).length) =
      pc + BitVec.ofNat 64 (16 * a.length) + BitVec.ofNat 64 (16 * b.length) := by
    rw [List.length_append, pc_add]
  rw [e]; exact s2

/-- Nothing to run: slot `d` keeps its word. -/
theorem ok_nil {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {w : Runner.W}
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some w) : Ok m pc fp K d [] (· = w) :=
  ⟨m, by simpa using Star.refl _ m, Agree.refl _ _ _ _, w, hr, rfl⟩

/-- `d := g (slot d) k`: the constant into `d+1`, then the instruction `o`. -/
theorem binK_ok {m : Runner.Mem} {pc fp : Runner.W} {K d o : Nat} {k : Int} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {w r : Runner.W} {g : Runner.W → Runner.W → Option Runner.W}
    (h : Pre L m pc fp K d [ci 1 (d + 1) k 0, ci o d d (d + 1)] ρ W)
    (hr : m.rd64 (slot fp (BitVec.ofNat 64 d)) = some w) (hk : lit32 k = true) (hop : op o = bin g) (ho : o < 256)
    (hg : g w (BitVec.ofInt 64 k) = some r) (hK : d + 1 < K) :
    Ok m pc fp K d [ci 1 (d + 1) k 0, ci o d d (d + 1)] (· = r) := by
  have h' : Pre L m pc fp K d ([] ++ [ci 1 (d + 1) k 0] ++ [ci o d d (d + 1)]) ρ W := by simpa using h
  have := bin_ok2 (ca := []) (cb := [ci 1 (d + 1) k 0]) (Pa := (· = w)) (P := (· = r)) (ok_nil hr)
    (Pb := (· = BitVec.ofInt 64 k))
    (fun m' pc' hp' => const_ok (k := k) (d := d + 1) (by rw [show ((d + 1 : Nat) : Int) = (d : Int) + 1 by omega]; exact hp') hk hK) (fun wa wb pa pb => ⟨r, by rw [pa, pb]; exact hg, rfl⟩) hop ho hK h'
  simpa using this

/-- `ld d d`: slot `d` holds an address, the word there into slot `d`. -/
theorem ld_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a v : Runner.W} (h : Pre L m pc fp K d [ci 15 d d 0] ρ W) (hd : d < K)
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

/-- A global: its address, the word there. -/
theorem glob_ok {m : Runner.Mem} {pc fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {L : Lay D} {σ : World D} {g : D.Glob} (hl : lit32 (L.ga g) = true)
    (h : Pre L m pc fp K d [ci 1 d (L.ga g) 0, ci 15 d d 0] ρ W) (hWL : ∀ m, W m → WeltAt m L σ) (hd : d < K) :
    Ok m pc fp K d [ci 1 d (L.ga g) 0, ci 15 d d 0] (Enc L (D.gtyp g) (σ.globs g)) := by
  have h' : Pre L m pc fp K d ([ci 1 d (L.ga g) 0] ++ [ci 15 d d 0]) ρ W := h
  refine ok_seq h' (const_ok h'.left hl hd) (fun m' w hp' hr hw => ?_) (by omega)
  obtain ⟨v, hv, he⟩ := (hWL m' hp'.welt).2.1 g
  rw [hw, BitVec.ofInt_natCast] at hr
  exact (ld_ok hp' hd hr hv).mono fun x hx => hx ▸ he

/-- The address of element `k`: the index word times the stride plus the column. -/
theorem addr_w {n : Int} {s c : Nat} (hn : 0 ≤ n) :
    BitVec.ofInt 64 n * BitVec.ofInt 64 (s : Int) + BitVec.ofInt 64 (c : Int) = BitVec.ofNat 64 (c + s * n.toNat) := by
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_mul, ← BitVec.ofInt_add]
  congr 1
  rw [Int.natCast_add, Int.natCast_mul, Int.toNat_of_nonneg hn]
  rw [Int.mul_comm, Int.add_comm]

theorem slotA_top {L : Lay D} {t : D.Tab} {f : D.Feld t} {d : Nat} {ci' : List II × Nat} {c : List II} {top : Nat}
    (hs : slotA L t f d ci' = some (c, top)) : ci'.2 ≤ top ∧ d + 2 ≤ top := by
  simp only [slotA] at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; omega
  · cases hs

theorem slotC_top {L : Lay D} {t : D.Tab} {f : D.Feld t} {d : Nat} {ci' : List II × Nat} {c : List II} {top : Nat}
    (hs : slotC L t f d ci' = some (c, top)) : ci'.2 ≤ top := by
  simp only [slotC, Option.map_eq_some_iff] at hs
  obtain ⟨⟨a, ta⟩, ha, he⟩ := hs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact (slotA_top ha).1

/-- The address of an element (`slotA`): the index, times 8, plus the column. -/
theorem slotA_ok {Λ : List (Res D)} {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {i : Expr D Γ Λ (.index (D.count t))}
    {σ₀ σ : World D} {L : Lay D} {d : Nat} {ci' : List II × Nat} {c : List II} {top K : Nat} {m : Runner.Mem}
    {pc fp : Runner.W} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (hs : slotA L t f d ci' = some (c, top)) (hK : top ≤ K)
    (ih : ∀ m pc, Pre L m pc fp K d ci'.1 ρ W → Ok m pc fp K d ci'.1 (Enc L (.index (D.count t)) (eval σ₀ i σ ρ)))
    (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (· = BitVec.ofNat 64 (L.elem t f (eval σ₀ i σ ρ).n.toNat)) := by
  simp only [slotA] at hs
  split at hs
  · next hcol =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have hn0 := (eval σ₀ i σ ρ).lo_le
    have hq : Pre L m pc fp K d (ci'.1 ++ ([ci 1 (d + 1) 8 0, ci 5 d d (d + 1)] ++
        [ci 1 (d + 1) (L.col t f) 0, ci 3 d d (d + 1)])) ρ W := by
      simpa [List.append_assoc] using hp
    have := hq.small
    have hc := ok_seq hq (ih m pc hq.left) (Pb := (· = BitVec.ofNat 64 (L.elem t f (eval σ₀ i σ ρ).n.toNat)))
      (fun m1 w1 hp1 r1 e1 => ok_seq hp1 (binK_ok hp1.left r1 (by decide) rfl (by decide) rfl (by omega))
        (Pb := (· = BitVec.ofNat 64 (L.elem t f (eval σ₀ i σ ρ).n.toNat)))
        (fun m2 w2 hp2 r2 e2 => (binK_ok hp2 r2 hcol rfl (by decide) rfl (by omega)).mono fun x hx => by
          simp only [Enc] at e1
          have := addr_w (s := 8) (c := L.col t f) hn0
          rw [e2, e1] at hx
          rw [hx]; exact this) (by omega))
      (by omega)
    simpa [List.append_assoc] using hc
  · cases hs

/-- An element of a column (`slotC`): its address, the word there. -/
theorem slotC_ok {Λ : List (Res D)} {Γ : Ctx} {t : D.Tab} {f : D.Feld t} {i : Expr D Γ Λ (.index (D.count t))}
    {σ₀ σ : World D} {L : Lay D} {d : Nat} {ci' : List II × Nat} {c : List II} {top K : Nat} {m : Runner.Mem}
    {pc fp : Runner.W} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (hs : slotC L t f d ci' = some (c, top)) (hK : top ≤ K)
    (ih : ∀ m pc, Pre L m pc fp K d ci'.1 ρ W → Ok m pc fp K d ci'.1 (Enc L (.index (D.count t)) (eval σ₀ i σ ρ)))
    (hWL : ∀ m, W m → WeltAt m L σ) (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (Enc L (D.typ t f) (σ.slots t (eval σ₀ i σ ρ).n f)) := by
  simp only [slotC, Option.map_eq_some_iff] at hs
  obtain ⟨⟨a, ta⟩, ha, he⟩ := hs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have ht := slotA_top ha
  have hn0 := (eval σ₀ i σ ρ).lo_le
  have hkc : ((eval σ₀ i σ ρ).n.toNat : Int) < D.count t := by have := (eval σ₀ i σ ρ).le_hi; omega
  have hkn : (((eval σ₀ i σ ρ).n.toNat : Nat) : Int) = (eval σ₀ i σ ρ).n := Int.toNat_of_nonneg hn0
  refine ok_seq hp (slotA_ok ha hK ih hp.left) (fun m3 w3 hp3 r3 e3 => ?_) (by have := hp.small; omega)
  obtain ⟨v, hv, he⟩ := (hWL m3 hp3.welt).1 t f _ hkc
  rw [e3] at r3
  rw [hkn] at he
  exact (ld_ok hp3 (by omega) r3 hv).mono fun x hx => hx ▸ he

end Gabbro.Stage0.Senke
