/-
  File:      stage0/Stage0/Senke/Welt/WeltAt.lean
  Subject:   The world in memory (`WeltAt`): every element of every column and every global at its address (`Lay`), as
             the word of its value; an element of a byte column is the low byte of the word read there.

  The world lies above everything a frame uses (`fp + 8K ≤ lo`), so code that writes only its frame keeps it
  (`weltAt_stab`). It describes the slots and globals only, so asking or reading (`lese`, `fragt`, which only
  record events) keeps it by definition.
-/
import Stage0.Senke.Ausdruck.Sim

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration} {L : Lay D}

/-- Every element and every global, one word each, inside `[lo, hi)`, below `2^31`. -/
def LayIn (L : Lay D) : Prop :=
  (∀ t f (k : Nat), (k : Int) < D.count t → L.lo ≤ L.elem t f k ∧ L.elem t f k + 8 ≤ L.hi) ∧
  (∀ g, L.lo ≤ L.ga g ∧ L.ga g + 8 ≤ L.hi) ∧ L.hi < 2 ^ 31

/-- A cell of the world: a global, or element `k` of column `f` of table `t`. -/
inductive Zelle (D : Deklaration) where
  | glob (g : D.Glob)
  | elem (t : D.Tab) (f : D.Feld t) (k : Nat)

/-- The address of a cell. -/
def Zelle.adr (L : Lay D) : Zelle D → Nat
  | .glob g => L.ga g
  | .elem t f k => L.elem t f k

/-- A cell the world has: every global, the elements below the table's count. -/
def Zelle.da : Zelle D → Prop
  | .glob _ => True
  | .elem t _ k => (k : Int) < D.count t

/-- No two cells share a word: different cells have different addresses, all on one grid of 8. -/
structure LayDis (L : Lay D) : Prop where
  inj : ∀ c c' : Zelle D, c.da → c'.da → c.adr L = c'.adr L → c = c'
  grid : ∀ c : Zelle D, c.da → c.adr L % 8 = L.lo % 8

/-- Two different cells: their words do not overlap. -/
theorem LayDis.far {L : Lay D} (h : LayDis L) {c c' : Zelle D} (hc : c.da) (hc' : c'.da) (hne : c ≠ c') :
    c.adr L + 8 ≤ c'.adr L ∨ c'.adr L + 8 ≤ c.adr L := by
  have h1 := h.grid c hc
  have h2 := h.grid c' hc'
  have h3 : c.adr L ≠ c'.adr L := fun e => hne (h.inj c c' hc hc' e)
  omega

/-- Every byte of the world may be written. -/
def WeltWr (m : Runner.Mem) (L : Lay D) : Prop :=
  ∀ x : Nat, L.lo ≤ x → x < L.hi → m.wr (BitVec.ofNat 64 x) = true

def WeltAt (m : Runner.Mem) (L : Lay D) (σ : World D) : Prop :=
  (∀ t f (k : Nat), (k : Int) < D.count t → ∃ w, m.rd64 (BitVec.ofNat 64 (L.elem t f k)) = some w ∧
    Enc L (D.typ t f) (σ.slots t k f) w) ∧
  (∀ g, ∃ w, m.rd64 (BitVec.ofNat 64 (L.ga g)) = some w ∧ Enc L (D.gtyp g) (σ.globs g) w) ∧
  WeltWr m L

/-- A word of the world may be written. -/
theorem WeltWr.word {m : Runner.Mem} {L : Lay D} (h : WeltWr m L) {a : Nat} (h1 : L.lo ≤ a) (h2 : a + 8 ≤ L.hi)
    (hl : L.hi < 2 ^ 31) : Runner.Mem.all m.wr (BitVec.ofNat 64 a) 8 = true := by
  refine all_of fun j hj => ?_
  have e : BitVec.ofNat 64 a + BitVec.ofNat 64 j = BitVec.ofNat 64 (a + j) := by rw [BitVec.ofNat_add]
  rw [e]
  exact h (a + j) (by omega) (by omega)

theorem WeltWr.keep {m m' : Runner.Mem} {L : Lay D} (h : WeltWr m L) (hw : m'.wr = m.wr) : WeltWr m' L := by
  intro x h1 h2; rw [hw]; exact h x h1 h2

/-- A word outside the changed slots reads the same. -/
theorem rd64_agree_out {m m' : Runner.Mem} {fp : Runner.W} {lo K a : Nat} (ha : Agree fp lo K m m')
    (h1 : a + 8 ≤ 2 ^ 64) (h2 : a + 8 ≤ fp.toNat + 8 * lo ∨ fp.toNat + 8 * K ≤ a) :
    m'.rd64 (BitVec.ofNat 64 a) = m.rd64 (BitVec.ofNat 64 a) := by
  simp only [Runner.Mem.rd64, ha.rd]
  rw [le_congr (m := m') (m' := m) (fun j hj => ha.b _ fun ⟨g1, g2⟩ => by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at g1 g2
    omega)]

theorem weltAt_stab {L : Lay D} {σ : World D} {fp : Runner.W} {K : Nat} (hl : LayIn L)
    (hwl : fp.toNat + 8 * K ≤ L.lo) : WStab (fun m => WeltAt m L σ) fp K := by
  intro m m' hm ha
  obtain ⟨hs, hg, hwr⟩ := hm
  obtain ⟨hl1, hl2, hl3⟩ := hl
  refine ⟨fun t f k hk => ?_, fun g => ?_, hwr.keep ha.wr⟩
  · obtain ⟨w, hw, he⟩ := hs t f k hk
    have := hl1 t f k hk
    exact ⟨w, by rw [rd64_agree_out ha (by omega) (Or.inr (by omega))]; exact hw, he⟩
  · obtain ⟨w, hw, he⟩ := hg g
    have := hl2 g
    exact ⟨w, by rw [rd64_agree_out ha (by omega) (Or.inr (by omega))]; exact hw, he⟩

/-! ## What a statement changes: its frame's slots from `lo` and the world -/

/-- The byte `x` lies in the world. -/
def InWelt (L : Lay D) (x : Runner.W) : Prop := L.lo ≤ x.toNat ∧ x.toNat < L.hi

/-- Outside the slots `lo .. K-1` of the frame at `fp` and outside the world, the memory is kept; no permission
    changes. What a statement of one thread may change. -/
structure AgreeW (L : Lay D) (fp : Runner.W) (lo K : Nat) (m m' : Runner.Mem) : Prop where
  rd : m'.rd = m.rd
  wr : m'.wr = m.wr
  b : ∀ x, ¬ inSlots fp lo K x → ¬ InWelt L x → m'.b x = m.b x

theorem agreeW_of {L : Lay D} {fp : Runner.W} {lo K : Nat} {m m' : Runner.Mem} (h : Agree fp lo K m m') :
    AgreeW L fp lo K m m' := ⟨h.rd, h.wr, fun x hx _ => h.b x hx⟩

/-- A change of the frame's slots alone is a statement's change. -/
instance {L : Lay D} {fp : Runner.W} {lo K : Nat} {m m' : Runner.Mem} :
    Coe (Agree fp lo K m m') (AgreeW L fp lo K m m') := ⟨agreeW_of⟩

theorem AgreeW.refl (L : Lay D) (fp : Runner.W) (lo K : Nat) (m : Runner.Mem) : AgreeW L fp lo K m m :=
  ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem AgreeW.trans {L : Lay D} {fp : Runner.W} {lo K : Nat} {m1 m2 m3 : Runner.Mem}
    (h1 : AgreeW L fp lo K m1 m2) (h2 : AgreeW L fp lo K m2 m3) : AgreeW L fp lo K m1 m3 :=
  ⟨h2.rd.trans h1.rd, h2.wr.trans h1.wr, fun x hx hw => (h2.b x hx hw).trans (h1.b x hx hw)⟩

theorem AgreeW.mono {L : Lay D} {fp : Runner.W} {lo lo' K : Nat} {m m' : Runner.Mem} (h : AgreeW L fp lo' K m m')
    (hl : lo ≤ lo') : AgreeW L fp lo K m m' :=
  ⟨h.rd, h.wr, fun x hx hw => h.b x (fun ⟨h1, h2⟩ => hx ⟨by omega, h2⟩) hw⟩

theorem AgreeW.widen {L : Lay D} {fp : Runner.W} {lo Ks K : Nat} {m m' : Runner.Mem} (h : AgreeW L fp lo Ks m m')
    (hs : Ks ≤ K) : AgreeW L fp lo K m m' :=
  ⟨h.rd, h.wr, fun x hx hw => h.b x (fun ⟨h1, h2⟩ => hx ⟨h1, by omega⟩) hw⟩

/-- A slot below `lo` keeps its word, the world lying above the frame. -/
theorem agreeW_rd_low {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {lo K i : Nat} (ha : AgreeW L fp lo K m m')
    (hr : fp.toNat + 8 * K ≤ L.lo) (hr' : fp.toNat + 8 * K ≤ 2 ^ 64) (hi : i < lo) (hK : lo ≤ K) :
    m'.rd64 (slot fp (BitVec.ofNat 64 i)) = m.rd64 (slot fp (BitVec.ofNat 64 i)) := by
  have hs := slot_toNat (i := i) hr' (by omega)
  simp only [Runner.Mem.rd64, ha.rd]
  rw [le_congr (fun j hj => ha.b _ (fun ⟨h1, h2⟩ => by
      have := fp.isLt
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs] at h1
      omega)
    (fun ⟨h1, h2⟩ => by
      have := fp.isLt
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs] at h1
      omega))]

/-- Writing a word of the world. -/
theorem agreeW_write_welt {L : Lay D} {m : Runner.Mem} {fp : Runner.W} {lo K a : Nat} (h1 : L.lo ≤ a)
    (h2 : a + 8 ≤ L.hi) (hl : L.hi < 2 ^ 31) (v : Nat) : AgreeW L fp lo K m (write m (BitVec.ofNat 64 a) 8 v) := by
  refine ⟨rfl, rfl, fun x _ hx => ?_⟩
  show (if _ then _ else _) = _
  split
  · next h =>
    exfalso; apply hx
    have := x.isLt
    have ha : (BitVec.ofNat 64 a).toNat = a := by simp only [BitVec.toNat_ofNat]; omega
    simp only [BitVec.toNat_sub, ha] at h
    unfold InWelt; omega
  · rfl

/-- What a statement keeps, as a frame agreement reaching to the top of memory: everything below the slot `lo` is kept. -/
theorem agreeW_big {L : Lay D} {fp : Runner.W} {lo K : Nat} {m m' : Runner.Mem} (h : AgreeW L fp lo K m m')
    (hK : fp.toNat + 8 * K ≤ L.lo) (hl : L.hi < 2 ^ 31) (hord : L.lo ≤ L.hi) (hlK : lo ≤ K) :
    Agree fp lo ((2 ^ 64 - fp.toNat) / 8) m m' := by
  refine ⟨h.rd, h.wr, fun x hx => h.b x (fun ⟨h1, h2⟩ => hx ⟨h1, ?_⟩) (fun ⟨h1, h2⟩ => hx ⟨?_, ?_⟩)⟩
  · have := x.isLt; have := fp.isLt; omega
  · omega
  · have := x.isLt; have := fp.isLt; omega

theorem codeAt_agreeW {L : Lay D} {fp : Runner.W} {lo K : Nat} {m m' : Runner.Mem} (ha : AgreeW L fp lo K m m')
    (hK : fp.toNat + 8 * K ≤ L.lo) (hl : L.hi < 2 ^ 31) (hord : L.lo ≤ L.hi) {pc : Runner.W} {is : List II}
    (hc : CodeAt m pc is) (hf : CodeFar pc is.length fp K) : CodeAt m' pc is :=
  hc.agree (agreeW_big (ha.mono (Nat.zero_le _)) hK hl hord (Nat.zero_le _) |>.mono (Nat.zero_le _)) (by obtain ⟨h1, _, h3⟩ := hf; have := fp.isLt; exact ⟨h1, by omega, h3⟩)

theorem frameOK_agreeW {L : Lay D} {m m' : Runner.Mem} {fp : Runner.W} {K lo K' : Nat} (h : FrameOK m fp K)
    (ha : AgreeW L fp lo K' m m') : FrameOK m' fp K :=
  ⟨h.lt, fun i hi => by rw [ha.rd]; exact h.rd i hi, fun i hi => by rw [ha.wr]; exact h.wr i hi⟩

theorem frameOK_sub {m : Runner.Mem} {fp : Runner.W} {K Ks : Nat} (h : FrameOK m fp K) (hs : Ks ≤ K) :
    FrameOK m fp Ks :=
  ⟨by have := h.lt; omega, fun i hi => h.rd i (by omega), fun i hi => h.wr i (by omega)⟩

theorem codeFar_sub2 {pc fp : Runner.W} {n K Ks : Nat} (h : CodeFar pc n fp K) (hs : Ks ≤ K) : CodeFar pc n fp Ks := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, by omega, by omega⟩

theorem Agree.widen {m m' : Runner.Mem} {fp : Runner.W} {lo Ks K : Nat} (h : Agree fp lo Ks m m') (hs : Ks ≤ K) :
    Agree fp lo K m m' :=
  ⟨h.rd, h.wr, fun x hx => h.b x fun ⟨h1, h2⟩ => hx ⟨h1, by omega⟩⟩

/-- An expression of a statement runs in the frame below `Ks`, with the world above it. -/
theorem PreS.welt {m : Runner.Mem} {pc fp : Runner.W} {K Ks d : Nat} {c : List II} {Γ : Ctx} {ρ : Env D Γ}
    {L : Lay D} {σ : World D} (hp : PreS L m pc fp K d c ρ) (hs : Ks ≤ K) (hw : WeltAt m L σ) (hl : LayIn L)
    (hwl : fp.toNat + 8 * Ks ≤ L.lo) : Pre L m pc fp Ks d c ρ (fun m => WeltAt m L σ) :=
  ⟨hp.ctx, by have := hp.small; omega, frameOK_sub hp.frame hs, hp.code, codeFar_sub2 hp.far hs, hp.env, hw, weltAt_stab hl hwl⟩

end Gabbro.Stage0.Senke
