/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Fuss.lean
  Subject:   Footprints of the threads and the shared memory (multi-thread image theorem, package MT1). Every live
             runner thread carries a `Solo`: its state `r`, its solo memory `m` (where its own run stands), the bytes
             `F` its current segment may touch and the bytes `Wr` it may write. `Verschmolzen m S`: each solo memory
             agrees with the shared memory `m` on its footprint, a thread writes inside its footprint, and what one
             thread may write no other thread may touch (code, the dispatch table and read-only data may lie in
             several footprints, they are in no write set). `verschmolzen_ask`: the memory answers a request of
             thread `i` that lies in its footprint (in its write set if it writes) in the shared memory as in `i`'s
             solo memory, and afterwards the shared memory and every thread's solo memory are related again; the
             shared memory changed inside `i`'s write set only.
-/
module
public import Stage0.Senke.Bild.Mehr.Lokal
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR

/-- What one runner thread carries. -/
structure Solo where
  r : Res T
  m : Mem
  F : W → Prop
  Wr : W → Prop

/-- Thread `i`'s entry replaced by `s`. -/
def setzeS (S : Nat → Option Solo) (i : Nat) (s : Solo) (j : Nat) : Option Solo := if j = i then some s else S j

theorem setzeS_self (S : Nat → Option Solo) (i : Nat) (s : Solo) : setzeS S i s i = some s := by
  show (if i = i then some s else S i) = some s
  exact if_pos rfl

theorem setzeS_ne (S : Nat → Option Solo) {i j : Nat} (s : Solo) (h : j ≠ i) : setzeS S i s j = S j := by
  show (if j = i then some s else S j) = S j
  exact if_neg h

/-- An entry after the replacement: the new one at `i`, the old one elsewhere. -/
theorem setzeS_fall {S : Nat → Option Solo} {i j : Nat} {s u : Solo} (h : setzeS S i s j = some u) :
    (j = i ∧ u = s) ∨ (j ≠ i ∧ S j = some u) := by
  by_cases hj : j = i
  · rw [hj, setzeS_self] at h
    exact Or.inl ⟨hj, (Option.some.inj h).symm⟩
  · rw [setzeS_ne S s hj] at h
    exact Or.inr ⟨hj, h⟩

/-- A replacement with the same footprint and write set: every entry has an old one with the same sets. -/
theorem setzeS_fuss {S : Nat → Option Solo} {i j : Nat} {s s' u : Solo} (hi : S i = some s) (hF : s'.F = s.F)
    (hW : s'.Wr = s.Wr) (h : setzeS S i s' j = some u) : ∃ u0, S j = some u0 ∧ u.F = u0.F ∧ u.Wr = u0.Wr := by
  rcases setzeS_fall h with ⟨rfl, rfl⟩ | ⟨_, h⟩
  · exact ⟨s, hi, hF, hW⟩
  · exact ⟨u, h, rfl, rfl⟩

/-- **The memory part of the relation.** -/
structure Verschmolzen (m : Mem) (S : Nat → Option Solo) : Prop where
  gleich : ∀ i s, S i = some s → GleichAuf s.F m s.m
  wrF : ∀ i s, S i = some s → ∀ y, s.Wr y → s.F y
  getrennt : ∀ i j s u, i ≠ j → S i = some s → S j = some u → ∀ y, s.Wr y → ¬ u.F y

/-- The request of a thread lies in its footprint, and in its write set if it writes: the step is not a lock or an
    atomic step (lock words and shared atomics lie in no thread's private footprint). -/
def ImFuss (s : Solo) : Prop :=
  ∀ o k, s.r = .ask o k → (∀ y, fussOp o y → s.F y) ∧ (schreibtOp o = true → ∀ y, fussOp o y → s.Wr y)

/-- The footprints and write sets alone decide `wrF` and `getrennt`: a replacement that keeps them keeps both. -/
theorem verschmolzen_sets {m m' : Mem} {S : Nat → Option Solo} (hV : Verschmolzen m S) {i : Nat} {s s' : Solo}
    (hi : S i = some s) (hF : s'.F = s.F) (hW : s'.Wr = s.Wr)
    (hg : ∀ j u, setzeS S i s' j = some u → GleichAuf u.F m' u.m) : Verschmolzen m' (setzeS S i s') where
  gleich := hg
  wrF := by
    intro j u hu y hy
    obtain ⟨u0, hu0, e1, e2⟩ := setzeS_fuss hi hF hW hu
    rw [e1]
    rw [e2] at hy
    exact hV.wrF j u0 hu0 y hy
  getrennt := by
    intro j1 j2 u1 u2 hne hu1 hu2 y hy
    obtain ⟨v1, hv1, _, e1⟩ := setzeS_fuss hi hF hW hu1
    obtain ⟨v2, hv2, e2, _⟩ := setzeS_fuss hi hF hW hu2
    rw [e2]
    rw [e1] at hy
    exact hV.getrennt j1 j2 v1 v2 hne hv1 hv2 y hy

/-- **The memory step of a thread inside its footprint.** The memory answers the request of thread `i` in the
    shared memory `m` as in `i`'s solo memory (`m2'`), the relation holds again with `i`'s new state and solo memory,
    and the shared memory changed inside `i`'s write set only. -/
theorem verschmolzen_ask {m m' : Mem} {S : Nat → Option Solo} (hV : Verschmolzen m S) {i : Nat} {s : Solo}
    (hi : S i = some s) {o : Op} {k : Ans → Res T} (hr : s.r = .ask o k) (hF : ImFuss s) {a : Ans}
    (hm : memAns m o = some (a, m')) :
    ∃ m2', memAns s.m o = some (a, m2') ∧
      Verschmolzen m' (setzeS S i { s with r := k a, m := m2' }) ∧ ∀ y, ¬ s.Wr y → GleichAt m' m y := by
  obtain ⟨hFo, hWo⟩ := hF o k hr
  have hg : GleichAuf (fussOp o) m s.m := fun y hy => hV.gleich i s hi y (hFo y hy)
  obtain ⟨m2', hm2, hg'⟩ := memAns_gleich hg hm
  have hn1 := memAns_nurIn hm
  have hn2 := memAns_nurIn hm2
  have hau : ∀ y, ¬ s.Wr y → GleichAt m' m y := fun y hy => memAns_aussen hm hWo y hy
  refine ⟨m2', hm2, verschmolzen_sets (s' := { s with r := k a, m := m2' }) hV hi rfl rfl ?_, hau⟩
  intro j u hu y hy
  rcases setzeS_fall hu with ⟨rfl, rfl⟩ | ⟨hj, hu⟩
  · by_cases ho : fussOp o y
    · exact hg' y ho
    · exact ((hn1.gleichAt ho).trans (hV.gleich _ s hi y hy)).trans (hn2.gleichAt ho).symm
  · exact (hau y fun hw => hV.getrennt i j s u (Ne.symm hj) hi hu y hw hy).trans (hV.gleich j u hu y hy)

/-- A replacement that keeps the solo memory and the sets keeps the relation (the start of an instruction). -/
theorem verschmolzen_gleich {m : Mem} {S : Nat → Option Solo} (hV : Verschmolzen m S) {i : Nat} {s s' : Solo}
    (hi : S i = some s) (hF : s'.F = s.F) (hW : s'.Wr = s.Wr) (hM : s'.m = s.m) :
    Verschmolzen m (setzeS S i s') := by
  refine verschmolzen_sets hV hi hF hW ?_
  intro j u hu y hy
  rcases setzeS_fall hu with ⟨rfl, rfl⟩ | ⟨_, hu⟩
  · rw [hM]
    rw [hF] at hy
    exact hV.gleich _ s hi y hy
  · exact hV.gleich j u hu y hy

end Gabbro.Stage0.Senke.BildMehr
