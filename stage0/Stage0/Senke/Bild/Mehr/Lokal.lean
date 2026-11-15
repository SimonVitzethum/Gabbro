/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Lokal.lean
  Subject:   Memory locality of one request (multi-thread image theorem, package MT1). A request the memory answers
             (`memAns`) touches at most the eight bytes from its address (`fussOp`, the window `fenster`): it changes
             no permission and no byte outside them (`memAns_nurIn`), a request that does not write changes nothing
             (`memAns_lesen`), and two memories that agree there -- bytes and both permissions, `GleichAuf` -- answer
             it alike and agree there afterwards (`memAns_gleich`). This is what lets a thread's request be answered
             in the shared memory exactly as in the thread's own solo memory.
-/
module
public import Runner.IR.NativeRun
public import Runner.Basis.MemLemma
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR

/-- The eight bytes from `a` (with wrap-around): the bytes a request at `a` may touch. -/
def fenster (a y : W) : Prop := (y - a).toNat < 8

/-- The bytes a request may touch; a system call and a floating request touch none. -/
def fussOp : Op → W → Prop
  | .rd _ a => fenster a
  | .wr a _ => fenster a
  | .cas a _ _ => fenster a
  | .sys _ => fun _ => False
  | .fp _ _ _ => fun _ => False

/-- The requests that may write: `wr` and `cas`. -/
def schreibtOp : Op → Bool
  | .wr _ _ => true
  | .cas _ _ _ => true
  | _ => false

/-- Two memories agree at the byte `y`: its value and both permissions. -/
def GleichAt (m m' : Mem) (y : W) : Prop := m.b y = m'.b y ∧ m.rd y = m'.rd y ∧ m.wr y = m'.wr y

/-- Two memories agree on the bytes `F`. -/
def GleichAuf (F : W → Prop) (m m' : Mem) : Prop := ∀ y, F y → GleichAt m m' y

/-- `m'` is `m` changed inside `F` only: every permission and every byte outside `F` are kept. -/
structure NurIn (F : W → Prop) (m m' : Mem) : Prop where
  rd : m'.rd = m.rd
  wr : m'.wr = m.wr
  b : ∀ y, ¬ F y → m'.b y = m.b y

theorem GleichAt.refl (m : Mem) (y : W) : GleichAt m m y := ⟨rfl, rfl, rfl⟩

theorem GleichAt.symm {m m' : Mem} {y : W} (h : GleichAt m m' y) : GleichAt m' m y :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem GleichAt.trans {m1 m2 m3 : Mem} {y : W} (h1 : GleichAt m1 m2 y) (h2 : GleichAt m2 m3 y) :
    GleichAt m1 m3 y :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem NurIn.refl (F : W → Prop) (m : Mem) : NurIn F m m := ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Outside `F` the changed memory agrees with the old one. -/
theorem NurIn.gleichAt {F : W → Prop} {m m' : Mem} (h : NurIn F m m') {y : W} (hy : ¬ F y) : GleichAt m' m y :=
  ⟨h.b y hy, congrFun h.rd y, congrFun h.wr y⟩

/-! ## The window -/

theorem fenster_add (a : W) {j : Nat} (hj : j < 8) : fenster a (a + BitVec.ofNat 64 j) := by
  have := a.isLt
  simp only [fenster, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem fenster_self (a : W) : fenster a a := by
  have := a.isLt
  simp only [fenster, BitVec.toNat_sub]
  omega

theorem gleich_rd8 {m m' : Mem} {a : W} (h : GleichAuf (fenster a) m m') : m.rd8 a = m'.rd8 a := by
  obtain ⟨hb, hr, _⟩ := h a (fenster_self a)
  simp only [Mem.rd8, hb, hr]

theorem gleich_rd32 {m m' : Mem} {a : W} (h : GleichAuf (fenster a) m m') : m.rd32 a = m'.rd32 a := by
  have hb : Mem.le m a 4 = Mem.le m' a 4 := Mem.le_congr fun j hj => (h _ (fenster_add a (by omega))).1
  have hr : Mem.all m.rd a 4 = Mem.all m'.rd a 4 :=
    Mem.all_congr fun j hj => (h _ (fenster_add a (by omega))).2.1
  simp only [Mem.rd32, hb, hr]

theorem gleich_rd64 {m m' : Mem} {a : W} (h : GleichAuf (fenster a) m m') : m.rd64 a = m'.rd64 a := by
  have hb : Mem.le m a 8 = Mem.le m' a 8 := Mem.le_congr fun j hj => (h _ (fenster_add a hj)).1
  have hr : Mem.all m.rd a 8 = Mem.all m'.rd a 8 := Mem.all_congr fun j hj => (h _ (fenster_add a hj)).2.1
  simp only [Mem.rd64, hb, hr]

theorem gleich_wr {m m' : Mem} {a : W} (h : GleichAuf (fenster a) m m') : Mem.all m.wr a 8 = Mem.all m'.wr a 8 :=
  Mem.all_congr fun j hj => (h _ (fenster_add a hj)).2.2

theorem gleich_rdall {m m' : Mem} {a : W} (h : GleichAuf (fenster a) m m') :
    Mem.all m.rd a 8 = Mem.all m'.rd a 8 :=
  Mem.all_congr fun j hj => (h _ (fenster_add a hj)).2.1

theorem gleich_le {m m' : Mem} {a : W} (h : GleichAuf (fenster a) m m') : Mem.le m a 8 = Mem.le m' a 8 :=
  Mem.le_congr fun j hj => (h _ (fenster_add a hj)).1

/-- A word written at `a` changes the window of `a` only. -/
theorem write_nurIn (m : Mem) (a : W) (v : Nat) : NurIn (fenster a) m (Mem.write m a 8 v) :=
  ⟨rfl, rfl, fun y hy => by
    simp only [Mem.write]
    split
    · next h => exact absurd h hy
    · rfl⟩

/-- The same word written into two memories that agree on the window: they agree there afterwards. -/
theorem gleich_write {m m' : Mem} {a : W} (h : GleichAuf (fenster a) m m') (v : Nat) :
    GleichAuf (fenster a) (Mem.write m a 8 v) (Mem.write m' a 8 v) := by
  intro y hy
  refine ⟨?_, (h y hy).2.1, (h y hy).2.2⟩
  have hy' : (y - a).toNat < 8 := hy
  simp only [Mem.write, if_pos hy']

/-! ## The answers -/

/-- The answer to a read, from the three reads at its address (the shape of `memAns`). -/
def rdAntwort : Nat → Option B → Option (BitVec 32) → Option W → Ans
  | 1, r8, _, _ => r8.map fun v => (v.setWidth 64, 0)
  | 4, _, r32, _ => r32.map fun v => (v.setWidth 64, 0)
  | _, _, _, r64 => r64.map fun v => (v, 0)

theorem memAns_rd (m : Mem) : ∀ (n : Nat) (x : W),
    memAns m (.rd n x) = some (rdAntwort n (m.rd8 x) (m.rd32 x) (m.rd64 x), m)
  | 0, _ => by first | rfl | simp [memAns, rdAntwort]
  | 1, _ => by first | rfl | simp [memAns, rdAntwort]
  | 2, _ => by first | rfl | simp [memAns, rdAntwort]
  | 3, _ => by first | rfl | simp [memAns, rdAntwort]
  | 4, _ => by first | rfl | simp [memAns, rdAntwort]
  | _ + 5, _ => by first | rfl | simp [memAns, rdAntwort]

theorem memAns_wr (m : Mem) (x v : W) :
    memAns m (.wr x v) = some (match m.wr64 x v with | some m' => (some (0, 0), m') | none => (none, m)) := rfl

theorem memAns_cas (m : Mem) (x e n : W) :
    memAns m (.cas x e n) = some (match m.cas x e n with | some (o, m') => (some (o, 0), m') | none => (none, m)) :=
  rfl

theorem wr64_eq (m : Mem) (x v : W) :
    m.wr64 x v = if Mem.all m.wr x 8 = true then some (Mem.write m x 8 v.toNat) else none := rfl

theorem cas_eq (m : Mem) (x e n : W) :
    m.cas x e n = if (Mem.all m.rd x 8 && Mem.all m.wr x 8) = true then
      some (BitVec.ofNat 64 (Mem.le m x 8),
        if BitVec.ofNat 64 (Mem.le m x 8) = e then Mem.write m x 8 n.toNat else m)
    else none := rfl

/-! ## Locality -/

/-- **A request changes its window only.** -/
theorem memAns_nurIn {m m' : Mem} {o : Op} {a : Ans} (h : memAns m o = some (a, m')) : NurIn (fussOp o) m m' := by
  cases o with
  | rd n x =>
    rw [memAns_rd] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact NurIn.refl _ _
  | wr x v =>
    rw [memAns_wr, wr64_eq] at h
    by_cases hc : Mem.all m.wr x 8 = true
    · rw [if_pos hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact write_nurIn m x v.toNat
    · rw [if_neg hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact NurIn.refl _ _
  | cas x e n =>
    rw [memAns_cas, cas_eq] at h
    by_cases hc : (Mem.all m.rd x 8 && Mem.all m.wr x 8) = true
    · rw [if_pos hc] at h
      by_cases he : BitVec.ofNat 64 (Mem.le m x 8) = e
      · rw [if_pos he] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact write_nurIn m x n.toNat
      · rw [if_neg he] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact NurIn.refl _ _
    · rw [if_neg hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact NurIn.refl _ _
  | sys q => simp only [memAns, reduceCtorEq] at h
  | fp kind x y => simp only [memAns, reduceCtorEq] at h

/-- **A request that does not write changes nothing.** -/
theorem memAns_lesen {m m' : Mem} {o : Op} {a : Ans} (hs : schreibtOp o = false) (h : memAns m o = some (a, m')) :
    m' = m := by
  cases o with
  | rd n x =>
    rw [memAns_rd] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  | wr x v => simp only [schreibtOp, Bool.true_eq_false] at hs
  | cas x e n => simp only [schreibtOp, Bool.true_eq_false] at hs
  | sys q => simp only [memAns, reduceCtorEq] at h
  | fp kind x y => simp only [memAns, reduceCtorEq] at h

/-- Outside a set `Wr` that holds the window of every writing request, a request changes nothing. -/
theorem memAns_aussen {m m' : Mem} {o : Op} {a : Ans} (h : memAns m o = some (a, m')) {Wr : W → Prop}
    (hW : schreibtOp o = true → ∀ y, fussOp o y → Wr y) (y : W) (hy : ¬ Wr y) : GleichAt m' m y := by
  cases hs : schreibtOp o with
  | true => exact (memAns_nurIn h).gleichAt fun hf => hy (hW hs y hf)
  | false =>
    rw [memAns_lesen hs h]
    exact GleichAt.refl _ _

/-- **Two memories that agree on the window answer a request alike**, and agree there afterwards. -/
theorem memAns_gleich {m1 m2 m1' : Mem} {o : Op} {a : Ans} (hg : GleichAuf (fussOp o) m1 m2)
    (h : memAns m1 o = some (a, m1')) : ∃ m2', memAns m2 o = some (a, m2') ∧ GleichAuf (fussOp o) m1' m2' := by
  cases o with
  | rd n x =>
    have hg' : GleichAuf (fenster x) m1 m2 := hg
    rw [memAns_rd] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨m2, ?_, hg⟩
    rw [memAns_rd, gleich_rd8 hg', gleich_rd32 hg', gleich_rd64 hg']
  | wr x v =>
    have hg' : GleichAuf (fenster x) m1 m2 := hg
    rw [memAns_wr, wr64_eq] at h
    rw [memAns_wr, wr64_eq, ← gleich_wr hg']
    by_cases hc : Mem.all m1.wr x 8 = true
    · rw [if_pos hc] at h ⊢
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, gleich_write hg' v.toNat⟩
    · rw [if_neg hc] at h ⊢
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m2, rfl, hg⟩
  | cas x e n =>
    have hg' : GleichAuf (fenster x) m1 m2 := hg
    rw [memAns_cas, cas_eq] at h
    rw [memAns_cas, cas_eq, ← gleich_rdall hg', ← gleich_wr hg', ← gleich_le hg']
    by_cases hc : (Mem.all m1.rd x 8 && Mem.all m1.wr x 8) = true
    · rw [if_pos hc] at h ⊢
      by_cases he : BitVec.ofNat 64 (Mem.le m1 x 8) = e
      · rw [if_pos he] at h ⊢
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, rfl, gleich_write hg' n.toNat⟩
      · rw [if_neg he] at h ⊢
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨m2, rfl, hg⟩
    · rw [if_neg hc] at h ⊢
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m2, rfl, hg⟩
  | sys q => simp only [memAns, reduceCtorEq] at h
  | fp kind x y => simp only [memAns, reduceCtorEq] at h

end Gabbro.Stage0.Senke.BildMehr
