/- Complete canonical world values at typed physical addresses. Full-span bounds
   and separation protect every limb; frame changes preserve recursive validity. -/
module
public import Stage0.Senke.Ausdruck.Sim
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR Runner.Mem

variable {D : Deklaration} {L : Lay D}

/-- Every element and every global, one word each, inside `[lo, hi)`, below `2^31`. -/
def LayIn (L : Lay D) : Prop :=
  (∀ t f (k : Nat), (k : Int) < L.count t → L.lo ≤ L.elem t f k ∧ L.elem t f k + 8 * valueWords (D.typ t f) ≤ L.hi) ∧
  (∀ g, L.lo ≤ L.ga g ∧ L.ga g + 8 * valueWords (D.gtyp g) ≤ L.hi) ∧ L.hi < 2 ^ 31

/-- A cell of the world: a global, or element `k` of column `f` of table `t`. -/
inductive Zelle (D : Deklaration) where
  | glob (g : D.Glob)
  | elem (t : D.Tab) (f : D.Feld t) (k : Nat)

/-- The address of a cell. -/
def Zelle.adr (L : Lay D) : Zelle D → Nat
  | .glob g => L.ga g
  | .elem t f k => L.elem t f k

/-- A cell the world has: every global, the elements below the table's count. -/
def Zelle.da (L : Lay D) : Zelle D → Prop
  | .glob _ => True
  | .elem t _ k => (k : Int) < L.count t

/-- Complete byte extent of a typed cell, using the single canonical ABI. -/
def Zelle.bytes : Zelle D → Nat
  | .glob g => 8 * valueWords (D.gtyp g)
  | .elem t f _ => 8 * valueWords (D.typ t f)

/-- No two cells share a word: different cells have different addresses, all on one grid of 8. -/
structure LayDis (L : Lay D) : Prop where
  spans : ∀ c c' : Zelle D, c.da L → c'.da L → c ≠ c' →
    c.adr L + c.bytes ≤ c'.adr L ∨ c'.adr L + c'.bytes ≤ c.adr L
  inj : ∀ c c' : Zelle D, c.da L → c'.da L → c.adr L = c'.adr L → c = c'
  grid : ∀ c : Zelle D, c.da L → c.adr L % 8 = L.lo % 8

/-- Two different cells: their words do not overlap. -/
theorem LayDis.far {L : Lay D} (h : LayDis L) {c c' : Zelle D} (hc : c.da L) (hc' : c'.da L) (hne : c ≠ c') :
    c.adr L + 8 ≤ c'.adr L ∨ c'.adr L + 8 ≤ c.adr L := by
  have h1 := h.grid c hc
  have h2 := h.grid c' hc'
  have h3 : c.adr L ≠ c'.adr L := fun e => hne (h.inj c c' hc hc' e)
  omega

/-- Every byte of the world may be written. -/
def WeltWr (m : Runner.Mem) (L : Lay D) : Prop :=
  ∀ x : Nat, L.lo ≤ x → x < L.hi → m.wr (BitVec.ofNat 64 x) = true

def WeltAt (m : Runner.Mem) (L : Lay D) (σ : World D) : Prop :=
  (∀ t f (k : Nat), (k : Int) < L.count t →
    ValueAt L m (BitVec.ofNat 64 (L.elem t f k)) 0 (D.typ t f) (σ.slots t k f)) ∧
  (∀ g, ValueAt L m (BitVec.ofNat 64 (L.ga g)) 0 (D.gtyp g) (σ.globs g)) ∧
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

/-- Frame-only changes preserve every word and all recursive validity of a cell. -/
theorem valueAt_world_stab {m m' : Runner.Mem} {fp : Runner.W} {K address : Nat}
    {τ : Ty} {v : Wert D τ} (changed : Agree fp 0 K m m')
    (sep : fp.toNat + 8 * K ≤ address)
    (bound : address + 8 * valueWords τ < 2 ^ 31)
    (input : ValueAt L m (BitVec.ofNat 64 address) 0 τ v) :
    ValueAt L m' (BitVec.ofNat 64 address) 0 τ v := by
  refine ⟨input.1, fun i hi => ?_⟩
  have index : i < valueWords τ := by simpa only [encodeWords_length] using hi
  have addr : slot (BitVec.ofNat 64 address) (BitVec.ofNat 64 (0 + i)) =
      BitVec.ofNat 64 (address + 8 * i) := by
    simp only [Nat.zero_add, slot]
    change BitVec.ofNat 64 address + BitVec.ofNat 64 i * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1; omega
  rw [addr, rd64_agree_out changed (by omega) (Or.inr (by omega))]
  have h := input.2 i hi
  rwa [addr] at h

theorem weltAt_stab {L : Lay D} {σ : World D} {fp : Runner.W} {K : Nat} (hl : LayIn L)
    (hwl : fp.toNat + 8 * K ≤ L.lo) : WStab (fun m => WeltAt m L σ) fp K := by
  intro m m' hm ha
  obtain ⟨hs, hg, hwr⟩ := hm
  refine ⟨fun t f k hk => ?_, fun g => ?_, hwr.keep ha.wr⟩
  · have hin := hl.1 t f k hk
    exact valueAt_world_stab ha (by omega) (by have := hl.2.2; omega) (hs t f k hk)
  · have hin := hl.2.1 g
    exact valueAt_world_stab ha (by omega) (by have := hl.2.2; omega) (hg g)

/-! ## What a statement changes: its frame's slots from `lo` and the world -/

/-- The byte `x` lies in the world. -/
def InWelt (L : Lay D) (x : Runner.W) : Prop := L.lo ≤ x.toNat ∧ x.toNat < L.hi

/-- The byte `x` lies in the lock words: above the world, below `sye` (`LaySync`), in a layout whose lock
    words end below `2 ^ 31` (as every layout with locks does, `TicketSync.sye`). -/
def InSync (L : Lay D) (x : Runner.W) : Prop :=
  L.lo ≤ x.toNat ∧ L.hi ≤ x.toNat ∧ x.toNat < L.sye ∧ L.sye < 2 ^ 31

/-- The three words of the lock at `a` lie outside the slots `lo .. K-1` of the frame at `fp` and outside
    the world, byte by byte. -/
def LockFern (L : Lay D) (fp : Runner.W) (lo K a : Nat) : Prop :=
  ∀ k j, k ≤ 2 → j < 8 →
    ¬ inSlots fp lo K (BitVec.ofNat 64 (a + 8 * k) + BitVec.ofNat 64 j) ∧
    ¬ InWelt L (BitVec.ofNat 64 (a + 8 * k) + BitVec.ofNat 64 j)

/-- What a statement keeps of the ticket lock at `a`: for the words next `n`, serving `s` and waiters `w` read at
    `a`, `a + 8`, `a + 16` in `m`, the words `n'`, `s'`, `w'` in `m'` are readable with `n' - s' = n - s` (BitVec
    subtraction) and `w' = w`. The difference is what the free/mine invariant needs (`TicketSync`); a `locks`
    statement leaves both tickets of its lock one higher and keeps the class. -/
def TicketKlasse (m m' : Runner.Mem) (a : Nat) : Prop :=
  ∀ n s w, m.rd64 (BitVec.ofNat 64 a) = some n → m.rd64 (BitVec.ofNat 64 (a + 8)) = some s →
    m.rd64 (BitVec.ofNat 64 (a + 16)) = some w →
    ∃ n' s' w', m'.rd64 (BitVec.ofNat 64 a) = some n' ∧ m'.rd64 (BitVec.ofNat 64 (a + 8)) = some s' ∧
      m'.rd64 (BitVec.ofNat 64 (a + 16)) = some w' ∧ n' - s' = n - s ∧ w' = w

theorem TicketKlasse.refl (m : Runner.Mem) (a : Nat) : TicketKlasse m m a :=
  fun _ _ _ h1 h2 h3 => ⟨_, _, _, h1, h2, h3, rfl, rfl⟩

theorem TicketKlasse.trans {m1 m2 m3 : Runner.Mem} {a : Nat} (h1 : TicketKlasse m1 m2 a)
    (h2 : TicketKlasse m2 m3 a) : TicketKlasse m1 m3 a := fun n s w e1 e2 e3 => by
  obtain ⟨n1, s1, w1, f1, f2, f3, d1, q1⟩ := h1 n s w e1 e2 e3
  obtain ⟨n2, s2, w2, g1, g2, g3, d2, q2⟩ := h2 n1 s1 w1 f1 f2 f3
  exact ⟨n2, s2, w2, g1, g2, g3, by rw [d2, d1], by rw [q2, q1]⟩

/-- Equal words keep the ticket class. -/
theorem TicketKlasse.ofWords {m m' : Runner.Mem} {a : Nat}
    (h : ∀ k, k ≤ 2 → m'.rd64 (BitVec.ofNat 64 (a + 8 * k)) = m.rd64 (BitVec.ofNat 64 (a + 8 * k))) :
    TicketKlasse m m' a :=
  fun n s w e1 e2 e3 => by
    have z0 : a + 8 * 0 = a := by omega
    have z1 : a + 8 * 1 = a + 8 := by omega
    have z2 : a + 8 * 2 = a + 16 := by omega
    have e0 := h 0 (by omega)
    have e1' := h 1 (by omega)
    have e2' := h 2 (by omega)
    rw [z0] at e0
    rw [z1] at e1'
    rw [z2] at e2'
    have f0 : m'.rd64 (BitVec.ofNat 64 a) = some n := by rw [e0]; exact e1
    have f1 : m'.rd64 (BitVec.ofNat 64 (a + 8)) = some s := by rw [e1']; exact e2
    have f2 : m'.rd64 (BitVec.ofNat 64 (a + 16)) = some w := by rw [e2']; exact e3
    exact ⟨n, s, w, f0, f1, f2, rfl, rfl⟩

/-- Outside the slots `lo .. K-1` of the frame at `fp`, outside the world and outside the lock words, the
    memory is kept; no permission changes; every lock keeps its ticket class (`TicketKlasse`). What a statement
    of one thread may change. -/
structure AgreeW (L : Lay D) (fp : Runner.W) (lo K : Nat) (m m' : Runner.Mem) : Prop where
  rd : m'.rd = m.rd
  wr : m'.wr = m.wr
  b : ∀ x, ¬ inSlots fp lo K x → ¬ InWelt L x → ¬ InSync L x → m'.b x = m.b x
  sync : ∀ Lk, LockFern L fp lo K (L.lk Lk) → TicketKlasse m m' (L.lk Lk)

/-- A change that keeps every byte outside the slots and the world keeps the lock words with them. -/
theorem AgreeW.stark {L : Lay D} {fp : Runner.W} {lo K : Nat} {m m' : Runner.Mem} (rd : m'.rd = m.rd)
    (wr : m'.wr = m.wr) (b : ∀ x, ¬ inSlots fp lo K x → ¬ InWelt L x → m'.b x = m.b x) :
    AgreeW L fp lo K m m' := by
  refine ⟨rd, wr, fun x hx hw _ => b x hx hw, fun Lk fern => TicketKlasse.ofWords fun k hk => ?_⟩
  simp only [Runner.Mem.rd64, rd]
  rw [le_congr (m := m') (m' := m) (fun j hj => b _ (fern k j hk hj).1 (fern k j hk hj).2)]

theorem agreeW_of {L : Lay D} {fp : Runner.W} {lo K : Nat} {m m' : Runner.Mem} (h : Agree fp lo K m m') :
    AgreeW L fp lo K m m' := AgreeW.stark h.rd h.wr fun x hx _ => h.b x hx

/-- A change of the frame's slots alone is a statement's change. -/
instance {L : Lay D} {fp : Runner.W} {lo K : Nat} {m m' : Runner.Mem} :
    Coe (Agree fp lo K m m') (AgreeW L fp lo K m m') := ⟨agreeW_of⟩

theorem AgreeW.refl (L : Lay D) (fp : Runner.W) (lo K : Nat) (m : Runner.Mem) : AgreeW L fp lo K m m :=
  ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ => TicketKlasse.refl _ _⟩

theorem AgreeW.trans {L : Lay D} {fp : Runner.W} {lo K : Nat} {m1 m2 m3 : Runner.Mem}
    (h1 : AgreeW L fp lo K m1 m2) (h2 : AgreeW L fp lo K m2 m3) : AgreeW L fp lo K m1 m3 :=
  ⟨h2.rd.trans h1.rd, h2.wr.trans h1.wr, fun x hx hw hs => (h2.b x hx hw hs).trans (h1.b x hx hw hs),
    fun Lk fern => (h1.sync Lk fern).trans (h2.sync Lk fern)⟩

theorem AgreeW.mono {L : Lay D} {fp : Runner.W} {lo lo' K : Nat} {m m' : Runner.Mem} (h : AgreeW L fp lo' K m m')
    (hl : lo ≤ lo') : AgreeW L fp lo K m m' :=
  ⟨h.rd, h.wr, fun x hx hw => h.b x (fun ⟨h1, h2⟩ => hx ⟨by omega, h2⟩) hw,
    fun Lk fern => h.sync Lk fun k j hk hj =>
      ⟨fun ⟨h1, h2⟩ => (fern k j hk hj).1 ⟨by omega, h2⟩, (fern k j hk hj).2⟩⟩

theorem AgreeW.widen {L : Lay D} {fp : Runner.W} {lo Ks K : Nat} {m m' : Runner.Mem} (h : AgreeW L fp lo Ks m m')
    (hs : Ks ≤ K) : AgreeW L fp lo K m m' :=
  ⟨h.rd, h.wr, fun x hx hw => h.b x (fun ⟨h1, h2⟩ => hx ⟨h1, by omega⟩) hw,
    fun Lk fern => h.sync Lk fun k j hk hj =>
      ⟨fun ⟨h1, h2⟩ => (fern k j hk hj).1 ⟨h1, by omega⟩, (fern k j hk hj).2⟩⟩

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
      omega)
    (fun ⟨h1, _, _⟩ => by
      have := fp.isLt
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hs] at h1
      omega))]

/-- Writing a word of the world. -/
theorem agreeW_write_welt {L : Lay D} {m : Runner.Mem} {fp : Runner.W} {lo K a : Nat} (h1 : L.lo ≤ a)
    (h2 : a + 8 ≤ L.hi) (hl : L.hi < 2 ^ 31) (v : Nat) : AgreeW L fp lo K m (write m (BitVec.ofNat 64 a) 8 v) := by
  refine AgreeW.stark rfl rfl fun x _ hx => ?_
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
  refine ⟨h.rd, h.wr, fun x hx => h.b x (fun ⟨h1, h2⟩ => hx ⟨h1, ?_⟩) (fun ⟨h1, h2⟩ => hx ⟨?_, ?_⟩)
    (fun ⟨h1, _, h3, h4⟩ => hx ⟨?_, ?_⟩)⟩
  · have := x.isLt; have := fp.isLt; omega
  · omega
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
theorem PreS.welt {reserved : Nat} {m : Runner.Mem} {pc fp : Runner.W} {K Ks d : Nat} {c : List II} {Γ : Ctx} {ρ : Env D Γ}
    {L : Lay D} {σ : World D} (hp : PreS L m pc fp K d c ρ reserved) (hs : Ks ≤ K) (hw : WeltAt m L σ) (hl : LayIn L)
    (hwl : fp.toNat + 8 * Ks ≤ L.lo) : Pre L m pc fp Ks d c ρ (fun m => WeltAt m L σ) reserved :=
  ⟨hp.ctx, by have := hp.small; omega, frameOK_sub hp.frame hs, hp.code, codeFar_sub2 hp.far hs, hp.env, hw, weltAt_stab hl hwl⟩

end Gabbro.Stage0.Senke
