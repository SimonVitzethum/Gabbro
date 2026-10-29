/-
  File:      stage0/Stage0/Senke/Sperre/Paar.lean
  Subject:   Taking and giving as a pair, from a lock word state `SyncOK` allows: free (owner 0, count 0) or mine
             (owner me, count `c ≥ 1`). The take leaves the lock mine with the count `c1 = c + 1` (1 when free) and
             room for one take less; the give, from there, puts back exactly the owner and count it found
             (`nimm_paar`, `gib_paar`).
-/
import Stage0.Senke.Sperre.Lauf

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner Runner.IR Runner.Mem

set_option linter.unusedSectionVars false

variable [Kern]

variable {D : Deklaration}

theorem At.mid (xs ys zs : List II) : At (xs ++ ys ++ zs) xs.length ys := fun j hj => by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]

theorem At.one {code : List II} {p : Nat} {x : II} (h : At code p [x]) : code[p]? = some x := by
  simpa using h.get (j := 0) rfl

section
variable {m0 m : Mem} {pc fp : W} {s a : Nat} {code : List II} {f : Nat → W} {o c w : W}

/-- The start state of the lock code: the scratch slots hold what they hold. -/
theorem ls_init (E : LE m0 pc fp s a code) (ho : m0.rd64 (BitVec.ofNat 64 a) = some o)
    (hc : m0.rd64 (BitVec.ofNat 64 (a + 8)) = some c) (hw : m0.rd64 (BitVec.ofNat 64 (a + 16)) = some w) :
    ∃ f, LS m0 m0 fp s a f o c w :=
  ⟨fun j => (m0.rd64 (slot fp (BitVec.ofNat 64 (s + j)))).getD 0, fun j hj => by
    simp only [Mem.rd64, E.frame.rd (s + j) (by omega), ite_true, Option.getD_some], ho, hc, hw,
    AgreeK.refl _ _ _ _⟩

/-- `jmp X`: on at `X` bytes from the jump. -/
theorem ls_jmp_int (E : LE m0 pc fp s a code) (h : AgreeK fp s a m0 m) {i : Nat} {X : Int}
    (hi : code[i]? = some (ci 18 X 0 0)) (hX : lit32 X = true) :
    Star ⟨pc + BitVec.ofNat 64 (16 * i), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 X, fp⟩ m := by
  have hI := E.ins h hi
  simp only [ci] at hI
  refine Star.one (run_step (t := ⟨_, fp⟩) hI (by decide) ?_)
  simp only [op]
  refine f1_run hI ?_
  rw [sx_lit hX]
  exact .next

/-- What `SyncOK` allows of one lock: free, or mine with a count `c ≥ 1` leaving room for `Ks` takes. -/
def LockSt (L : Lay D) (fp : W) (Ks : Nat) (o c : W) : Prop :=
  (o = 0 ∧ c = 0) ∨ (o = meW L fp ∧ 1 ≤ c.toNat ∧ c.toNat + Ks < 2 ^ 62)

/-- The take, from either state: mine, the count `c1` with `c1 - 1 = c`, room for one take less. -/
theorem nimm_paar {L : Lay D} {Ks : Nat} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f o c w) {p : Nat}
    (hc : At code p (nimmC L a s)) (hme : MeOK L fp) (hst : LockSt L fp Ks o c) (hKs : 1 ≤ Ks) (hK31 : Ks < 2 ^ 31) :
    ∃ m' f' c1, Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 48)), fp⟩ m' ∧
      LS m0 m' fp s a f' (meW L fp) c1 w ∧ c1 - 1 = c ∧ 1 ≤ c1.toNat ∧ c1.toNat + (Ks - 1) < 2 ^ 62 := by
  rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, h1, h2⟩
  · obtain ⟨m', f', s1, h'⟩ := nimm_frei E h hc hme
    have h1 : (1 : W).toNat = 1 := rfl
    exact ⟨m', f', 1, s1, h', rfl, by omega, by omega⟩
  · obtain ⟨m', f', s1, h'⟩ := nimm_mein E h hc hme
    have h1' : (1 : W).toNat = 1 := rfl
    have e : (c + 1).toNat = c.toNat + 1 := by
      rw [BitVec.toNat_add, h1']; omega
    exact ⟨m', f', c + 1, s1, h', BitVec.add_sub_cancel c 1, by omega, by omega⟩

/-- The give, after the take: owner and count back as the take found them. -/
theorem gib_paar {L : Lay D} {Ks : Nat} {c1 : W} (E : LE m0 pc fp s a code) (h : LS m0 m fp s a f (meW L fp) c1 0)
    {p : Nat} (hc : At code p (gibC L a s)) (hme : MeOK L fp) (hst : LockSt L fp Ks o c) (hc1 : c1 - 1 = c) :
    ∃ m' f', Star ⟨pc + BitVec.ofNat 64 (16 * p), fp⟩ m ⟨pc + BitVec.ofNat 64 (16 * (p + 29)), fp⟩ m' ∧
      LS m0 m' fp s a f' o c 0 := by
  rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, h1, h2⟩
  · exact gib_letzt E h hc hme hc1
  · have hne : c1 - 1 ≠ 0 := by
      rw [hc1]; intro h0; rw [h0] at h1; simp at h1
    obtain ⟨m', f', s1, h'⟩ := gib_mehr E h hc hne
    exact ⟨m', f', s1, h'.congr rfl hc1 rfl⟩

end

/-- The bytes of a lock whose three words read as before are as before. -/
theorem lk_bytes {m m' : Mem} {a : Nat} {o c w : W} (ha : a + 24 < 2 ^ 31)
    (ho : m.rd64 (BitVec.ofNat 64 a) = some o) (hc : m.rd64 (BitVec.ofNat 64 (a + 8)) = some c)
    (hw : m.rd64 (BitVec.ofNat 64 (a + 16)) = some w) (ho' : m'.rd64 (BitVec.ofNat 64 a) = some o)
    (hc' : m'.rd64 (BitVec.ofNat 64 (a + 8)) = some c) (hw' : m'.rd64 (BitVec.ofNat 64 (a + 16)) = some w)
    (x : W) (hx : InLk a x) : m'.b x = m.b x := by
  obtain ⟨h1, h2⟩ := hx
  have hxl := x.isLt
  have e : ∀ y, y + 8 < 2 ^ 31 → y ≤ x.toNat → x.toNat < y + 8 →
      x = BitVec.ofNat 64 y + BitVec.ofNat 64 (x.toNat - y) := fun y hy h3 h4 => by
    apply BitVec.eq_of_toNat_eq
    rw [lk_byte (by omega) (by omega)]; omega
  by_cases k0 : x.toNat < a + 8
  · rw [e a (by omega) h1 k0]; exact bytes_of_rd64 ho ho' _ (by omega)
  · by_cases k1 : x.toNat < a + 16
    · rw [e (a + 8) (by omega) (by omega) k1]; exact bytes_of_rd64 hc hc' _ (by omega)
    · rw [e (a + 16) (by omega) (by omega) (by omega)]; exact bytes_of_rd64 hw hw' _ (by omega)

end Gabbro.Stage0.Senke
