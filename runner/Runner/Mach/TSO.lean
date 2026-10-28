import Runner.Mach.Folge

/-! # x86-TSO: one memory and a store buffer per thread (Sewell, Owens et al., CACM 2010)

* A write goes into the writing thread's buffer (the write permission is checked then: the page walk happens when
  the store executes); a buffer drains its oldest write into the memory on its own (`tau`).
* A read sees the thread's own buffer first, then the memory (`view`).
* A locked read-modify-write (`lock cmpxchg`) needs the thread's buffer empty and acts on the memory at once.
* The kernel answers a system call with any result and any new state that keeps the runner's table.
The table is never written: it is not writable, so no write enters a buffer for it (`Inv`). `tso_fixed`: a read
of the table answers the table's word, so `runner_mt` holds on x86-TSO. That the processor implements x86-TSO for
`mov` and `lock cmpxchg` is a named assumption, checked by litmus tests on the processor (`Runner/Test/`). -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog Runner.Mach

/-- A byte of the dispatch table. -/
def TB (L : Lay) (y : W) : Prop := ∃ op, op < 256 ∧ ∃ j, j < 8 ∧ y = taddr L (BitVec.ofNat 64 op) + BitVec.ofNat 64 j

structure TSt where
  m : Mem
  buf : Nat → List (W × W)

/-- Thread `i`'s view: the memory with its own buffer applied, oldest write first. -/
def TSt.view (s : TSt) (i : Nat) : Mem := (s.buf i).foldl (fun m e => Mem.write m e.1 8 e.2.toNat) s.m

def TSt.setBuf (s : TSt) (i : Nat) (l : List (W × W)) : TSt :=
  { s with buf := fun j => if j = i then l else s.buf j }

/-- The table in the memory, and no buffered write touches it. -/
def TInv (L : Lay) (s : TSt) : Prop :=
  TabInv L s.m ∧ ∀ i e, e ∈ s.buf i → ∀ j, j < 8 → ¬ TB L (e.1 + BitVec.ofNat 64 j)

def TSO (L : Lay) : MemSys where
  St := { s : TSt // TInv L s }
  ans s i o a s' := match o with
    | .rd n x => s' = s ∧ ∃ w, a = (rdN (s.1.view i) n x).map (·, w)
    | .wr x v =>
      (Mem.all s.1.m.wr x 8 = false ∧ a = none ∧ s' = s) ∨
      (Mem.all s.1.m.wr x 8 = true ∧ a = some (0, 0) ∧ s'.1 = s.1.setBuf i (s.1.buf i ++ [(x, v)]))
    | .cas x e n => s.1.buf i = [] ∧
      ((s.1.m.cas x e n = none ∧ a = none ∧ s' = s) ∨
       (∃ old m, s.1.m.cas x e n = some (old, m) ∧ a = some (old, 0) ∧ s'.1 = { s.1 with m := m }))
    | .sys _ => True
  tau s s' := ∃ i x v rest, s.1.buf i = (x, v) :: rest ∧
    s'.1 = { (s.1.setBuf i rest) with m := Mem.write s.1.m x 8 v.toNat }

/-! ## Reading the table through a buffer -/

theorem write_far {m : Mem} {a y : W} {v : Nat} (h : ∀ j, j < 8 → y ≠ a + BitVec.ofNat 64 j) :
    (Mem.write m a 8 v).b y = m.b y ∧ (Mem.write m a 8 v).rd y = m.rd y := by
  refine ⟨?_, rfl⟩
  simp only [Mem.write]
  split
  · next hlt => exact absurd (sub_add_ofNat a y).symm (h _ hlt)
  · rfl

theorem foldl_far {y : W} : ∀ (l : List (W × W)) (m : Mem), (∀ e ∈ l, ∀ j, j < 8 → y ≠ e.1 + BitVec.ofNat 64 j) →
    (l.foldl (fun m e => Mem.write m e.1 8 e.2.toNat) m).b y = m.b y ∧
    (l.foldl (fun m e => Mem.write m e.1 8 e.2.toNat) m).rd y = m.rd y
  | [], _, _ => ⟨rfl, rfl⟩
  | e :: l, m, h => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_far l (Mem.write m e.1 8 e.2.toNat) fun e' he' => h e' (List.mem_cons_of_mem _ he')
    obtain ⟨h3, h4⟩ := write_far (m := m) (v := e.2.toNat) (h e (List.mem_cons_self ..))
    exact ⟨h1.trans h3, h2.trans h4⟩

theorem foldl_wr : ∀ (l : List (W × W)) (m : Mem),
    (l.foldl (fun m e => Mem.write m e.1 8 e.2.toNat) m).wr = m.wr
  | [], _ => rfl
  | e :: l, m => by simp only [List.foldl_cons]; rw [foldl_wr l]; rfl

theorem view_table {L : Lay} {s : TSt} (hs : TInv L s) (i : Nat) {op : Nat} (hop : op < 256) :
    MBytes (s.view i) (taddr L (BitVec.ofNat 64 op)) (wbytes (L.H op)) := by
  intro j hj
  have hj8 : j < 8 := by simpa [wbytes] using hj
  obtain ⟨hb, hr, hw⟩ := hs.1 op hop j hj
  have far : ∀ e ∈ s.buf i, ∀ j', j' < 8 →
      taddr L (BitVec.ofNat 64 op) + BitVec.ofNat 64 j ≠ e.1 + BitVec.ofNat 64 j' :=
    fun e he j' hj' heq => hs.2 i e he j' hj' ⟨op, hop, j, hj8, heq.symm⟩
  obtain ⟨fb, fr⟩ := foldl_far (s.buf i) s.m far
  refine ⟨?_, ?_, ?_⟩
  · simp only [TSt.view]; rw [fb]; exact hb
  · simp only [TSt.view]; rw [fr]; exact hr
  · simp only [TSt.view]; rw [foldl_wr]; exact hw

theorem tso_fixed (L : Lay) : Fixed (TSO L) L := by
  intro s i op a s' hop h
  obtain ⟨rfl, w, rfl⟩ := h
  refine ⟨rfl, w, ?_⟩
  simp only [rdN, rd64_bytes (view_table s'.2 i hop), Option.map_some]

end Runner.Beweis
