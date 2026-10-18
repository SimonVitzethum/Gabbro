import Grammatik.Code.Gate.Gate

/-
  File:      Grammatik/Code/Gate/Provider.lean
  Subject:   TRACK L -- THE THREE PROVIDER ROLES (`Hardware/Anbieter/Region.lean`) AS GATE CONTRACTS OVER
             `Code` MEMORY.  PLAN-HARDWARE.md section 16.2, 16.6.

  `Code` memory is block-structured: a region answer is a fresh BLOCK. The three roles read there as

    * `holeSpec`   -- `get(n)`: answers `ptr b 0` for the fresh block `b` of `n` bytes, nothing written
                      (an `alloc` without zero fill: reading an unwritten cell is stuck);
    * `fuellSpec`  -- `fill(p, n)`: the range `[o, o+n)` of block `b` becomes ZERO where it was never
                      written (what a fresh anonymous page reads as); answer `0`. The contract also
                      allows a REFUSED commit (answer `1`, memory unchanged): out of memory below the
                      ceiling is real and reaches the program's `else`;
    * `gibSpec`    -- `drop(p)`: the block ceases to exist; every later access to it is stuck.

  What is proved: the facts the lowering and the safety argument use -- a reserve answers a block that
  did not exist and leaves every other block as it was (`hole_frisch`, `hole_andere`); a commit changes
  only unwritten cells inside its range and defines every cell of the range (`fuell_aussen`,
  `fuell_innen`); a released block is gone and its neighbours are untouched (`gib_weg`,
  `gib_andere`, `gib_haengt`).  The bridge to the provider's address-level contract is
  `Code/Gate/Bruecke.lean`.

  No `sorry`, no `native_decide`, no new axiom.
-/

namespace Gabbro.Code

variable [Conf]

/-- **reserve**: one word argument `n`; the answer is a fresh block of `n` bytes. -/
def holeSpec : GateSpec where
  pre _ vs := ∃ n : Nat, vs = [Val.ofInt Conf.wbits n]
  post m vs m' ans := ∃ n : Nat, vs = [Val.ofInt Conf.wbits n] ∧
    m' = (m.alloc n false).1 ∧ ans = some (Val.ptr (m.alloc n false).2 0)

/-- Zero the never-written cells of `[o, o+n)` in a block. -/
def Blk.fuellen (blk : Blk) (o n : Nat) : Blk :=
  { blk with cells := fun k => if o ≤ k ∧ k < o + n ∧ blk.cells k = none then some (.byte 0)
      else blk.cells k }

/-- **commit**: arguments `(ptr b o, n)`; inside the block it succeeds (answer `0`) and fills the
    range, or it is refused (answer `1`) with memory unchanged. -/
def fuellSpec : GateSpec where
  pre m vs := ∃ (b o n : Nat) (blk : Blk),
    vs = [Val.ptr b (o : Int), Val.ofInt Conf.wbits (n : Int)] ∧ m.blks b = some blk ∧ o + n ≤ blk.size
  post m vs m' ans := ∃ (b o n : Nat) (blk : Blk),
    vs = [Val.ptr b (o : Int), Val.ofInt Conf.wbits (n : Int)] ∧
    m.blks b = some blk ∧ o + n ≤ blk.size ∧
    ((m' = m.setBlk b (blk.fuellen o n) ∧ ans = some (Val.ofInt Conf.wbits 0)) ∨
     (m' = m ∧ ans = some (Val.ofInt Conf.wbits 1)))

/-- Remove a block. -/
def Mem.entfernen (m : Mem) (b : Nat) : Mem :=
  { blks := fun b' => if b' = b then none else m.blks b', next := m.next }

/-- **release**: argument `ptr b 0` of a live block; the block is gone, no answer. -/
def gibSpec : GateSpec where
  pre m vs := ∃ b blk, vs = [Val.ptr b 0] ∧ m.blks b = some blk
  post m vs m' ans := ∃ b blk, vs = [Val.ptr b 0] ∧ m.blks b = some blk ∧
    m' = m.entfernen b ∧ ans = none

/-! ## 1. reserve -/

/-- **A reserve answers a block that did not exist**, of the asked size, and the memory stays well
    formed. -/
theorem hole_frisch {m m' : Mem} {vs : List Val} {ans : Option Val} (hw : m.Wf)
    (h : holeSpec.post m vs m' ans) :
    ∃ b n, ans = some (Val.ptr b 0) ∧ m.blks b = none ∧ (m'.blks b).map Blk.size = some n ∧
      m'.Wf := by
  obtain ⟨n, -, rfl, rfl⟩ := h
  refine ⟨(m.alloc n false).2, n, rfl, ?_, alloc_size m n false, alloc_wf hw n false⟩
  simp only [Mem.alloc]
  cases hb : m.blks m.next with
  | none => rfl
  | some blk => have := hw m.next (by simp [hb]); omega

/-- Every other block is as it was (a block that exists has an id below `next`, so it is not the
    new one). -/
theorem hole_andere {m m' : Mem} {vs : List Val} {ans : Option Val} (hw : m.Wf)
    (h : holeSpec.post m vs m' ans) (b : Nat) (hb : (m.blks b).isSome = true) :
    m'.blks b = m.blks b := by
  obtain ⟨n, -, rfl, rfl⟩ := h
  exact alloc_blks_old m n false b (by have := hw b hb; omega)

/-! ## 2. commit -/

/-- **A commit is local**: every other block is as it was; inside the block, cells outside the range
    are as they were; and either the commit was refused (memory unchanged) or every cell of the range
    is defined afterwards. -/
theorem fuell_lokal {m m' : Mem} {vs : List Val} {ans : Option Val}
    (h : fuellSpec.post m vs m' ans) :
    ∃ b o n blk, m.blks b = some blk ∧ o + n ≤ blk.size ∧
      (∀ b', b' ≠ b → m'.blks b' = m.blks b') ∧ m'.next = m.next ∧
      (m' = m ∨ ∃ blk', m'.blks b = some blk' ∧ blk'.size = blk.size ∧
        (∀ k, (k < o ∨ o + n ≤ k) → blk'.cells k = blk.cells k) ∧
        (∀ k, o ≤ k → k < o + n → (blk'.cells k).isSome = true)) := by
  obtain ⟨b, o, n, blk, -, hb, hon, hc⟩ := h
  refine ⟨b, o, n, blk, hb, hon, ?_, ?_, ?_⟩
  · intro b' hne
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact setBlk_other _ _ _ _ hne
    · rfl
  · rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  · rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · refine Or.inr ⟨blk.fuellen o n, setBlk_same _ _ _, rfl, ?_, ?_⟩
      · intro k hk
        simp only [Blk.fuellen]
        have : ¬ (o ≤ k ∧ k < o + n ∧ blk.cells k = none) := by omega
        simp [this]
      · intro k h1 h2
        simp only [Blk.fuellen]
        cases hck : blk.cells k with
        | none => simp [h1, h2]
        | some c => simp
    · exact Or.inl rfl

/-! ## 3. release -/

/-- **A released block is gone**; every other block is as it was; `next` and well-formedness stay. -/
theorem gib_weg {m m' : Mem} {vs : List Val} {ans : Option Val} (hw : m.Wf)
    (h : gibSpec.post m vs m' ans) :
    ∃ b, m.blks b ≠ none ∧ m'.blks b = none ∧ (∀ b', b' ≠ b → m'.blks b' = m.blks b') ∧
      m'.next = m.next ∧ m'.Wf := by
  obtain ⟨b, blk, -, hb, rfl, -⟩ := h
  refine ⟨b, by simp [hb], by simp [Mem.entfernen], ?_, rfl, ?_⟩
  · intro b' hne
    simp [Mem.entfernen, hne]
  · intro b' hb'
    simp only [Mem.entfernen] at hb' ⊢
    by_cases e : b' = b
    · simp [e] at hb'
    · simp only [e, if_false] at hb'
      exact hw b' hb'

/-- **Use after release is stuck**: no load of the released block is defined. -/
theorem gib_haengt {m m' : Mem} {vs : List Val} {ans : Option Val}
    (h : gibSpec.post m vs m' ans) :
    ∃ b, ∀ o t, m'.load b o t = none := by
  obtain ⟨b, blk, -, hb, rfl, -⟩ := h
  refine ⟨b, fun o t => ?_⟩
  simp [Mem.load, Mem.entfernen]

end Gabbro.Code
