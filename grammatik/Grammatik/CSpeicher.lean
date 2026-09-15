/-
  File:      Grammatik/CSpeicher.lean
  Subject:   The C memory model for translation validation (plan step 1):
             a block-offset memory in the style of CompCert, restricted to
             the objects the emitter creates.

  Successor of the memory in `CSemantik.lean` (lane 128), whose
  `CMem := Nat → Nat → Nat → Int` (table, index, field) carries exactly
  the five easy forms and none of the pointer, volatile or atomic forms.
  The design document is `dokumente/C-SPEICHERMODELL.md`; its section 1
  is the measured object inventory this file is sized to.

  THE MODEL IN ONE PARAGRAPH
    Memory is a set of BLOCKS, one per C object the emitter creates
    (`CBlk`: table storage, file-scope globals, arena storage, `static
    const` data, stack locals of a frame, device register windows). A
    POINTER is a block and an offset (`CPtr`); pointer arithmetic moves
    the offset and never the block, which is the whole provenance rule
    (`ptrAdd_blk`). Each block has a TYPED LAYOUT taken from the
    emitter's own declarations (`RecLay`: `count` records of `nf`
    scalar fields at byte offsets, record size `ssize`, so `T_slot
    slots[N]`, `uintN_t x`, `uint8_t buf[N]` and `_Atomic T a[N]` are
    all one shape). A cell is a (block, offset) where the layout puts a
    field; a load or store must hit a cell of exactly its type (the
    C11 6.5p6-7 effective-type rule, so the model needs no bytes: the
    emitter never reinterprets ordinary memory -- measured, see the
    document). Everything else is UNDEFINED and the semantics is STUCK:
    the inventory is `AccUB`, `PtrUB`, `LoadUB`, `StoreUB`, `OrdUB`.
    Volatile (device) and atomic accesses append to a separate
    OBSERVATION TRACE (`CObs`), so a later lane can relate them to the
    concurrency model of machine G; a volatile load takes its value
    from the environment (`DevOrc`), like Gabbro's `Orakel`.

  WHAT IS PROVED HERE
    1. The access discipline: each inventoried UB is stuck, each clean
       access makes progress, and the checker is complete (a failed
       check names its inventory entry) -- `accOk_iff`.
    2. Load/store algebra: read-over-write, cell separation, frames
       (stack blocks die at `leaveFrame`: dangling access is stuck).
    3. REFINEMENT of lane 128: the five forms re-expressed on the new
       memory (`bEval`, `bExec`), and the old `(table, index, field)`
       view is a projection of the new memory (`projMem`) under which
       both semantics agree step for step, stuck for stuck
       (`bEval_refines`, `bExec_refines`). `cCorr_assignSlot` carries
       over as `cCorr_assignSlot_blk`, derived FROM the old theorem.
    4. CORRESPONDENCE to Gabbro's `World`: `corrW` under an emitter
       layout given as data (`EmitLay`), preserved by `schreibSlot`
       against the emitted store `t->slots[i].f = v` for ANY table and
       field (`corr_schreibSlot`), read by the emitted load
       (`corr_leseSlot`), and the same for globals, plain and atomic.
    5. Witness on `refD`: the emitted layout of `Konto`, a store and a
       load, the relation preserved (`refKonto_zeuge`).
-/
import Grammatik.CSemantik

namespace Gabbro.Grammatik

/-! ## 1. Cell types -/

/-- The scalar C types a cell can have: the integer types of lane 128
    (`uintN_t`/`intN_t`, `bool` as `uint8_t`) and object pointers. -/
inductive CTy where
  | int (sgn : Bool) (w : CWidth)
  | ptr
  deriving DecidableEq, Repr

/-- Bytes per width. -/
def CWidth.bytes : CWidth → Nat
  | .w8 => 1 | .w16 => 2 | .w32 => 4 | .w64 => 8

/-- `sizeof` of a cell type (x86-64 SysV: pointers are 8 bytes). The
    alignment is the size (natural alignment, the only kind the emitter
    produces: no `_Alignas`, no packed structs in the census). -/
def CTy.size : CTy → Nat
  | .int _ w => w.bytes
  | .ptr => 8

theorem CTy.size_pos (τ : CTy) : 0 < τ.size := by
  cases τ with
  | int s w => show 0 < w.bytes; cases w <;> decide
  | ptr => decide

/-! ## 2. Blocks, pointers, values -/

/-- The C objects the emitter creates -- and no others: there is no
    `malloc` in emitted C (arenas are static arrays). Numbers name the
    object within its kind; `stk fr x` is local `x` of frame `fr`. -/
inductive CBlk where
  /-- `static T T_speicher;`, or the table object behind `T *restrict t`. -/
  | tab (t : Nat)
  /-- A file-scope object: `static uintN_t g = …;`, `_Atomic T g;`,
      `static uintN_t a[N] = {0};`, `static _Atomic T g_zellen[N];`. -/
  | glob (g : Nat)
  /-- `static A_arena A_arena_speicher;` -- `buf[hi]` and `used`. -/
  | arena (a : Nat)
  /-- `static const uintN_t c = …;` (`.rodata`). -/
  | ro (c : Nat)
  /-- A stack local whose address the emitted code takes or whose
      storage is an array (`uint8_t bytes[KAP]`, out-parameters `&e`). -/
  | stk (fr x : Nat)
  /-- A device register window, `(volatile uint8_t *)(uintptr_t)BASE`. -/
  | dev (d : Nat)
  /-- An object handed in by foreign code: the driver's buffer behind a
      byte view, the result of an `extern` function returning `T *`, the
      node a traversal callback returns. Its layout is the pointee type's;
      its provenance is the foreign call (an assumption, not a proof). -/
  | ext (n : Nat)
  deriving DecidableEq, Repr

/-- A pointer: a block and a byte offset. The offset is an `Int` so that
    arithmetic that leaves the block is representable -- and stuck. -/
structure CPtr where
  blk : CBlk
  off : Int
  deriving DecidableEq, Repr

/-- The content of a cell: an integer, a pointer, or nothing yet
    (a fresh stack local; reading it is UB 8 of `BEWEIS.md` §2). -/
inductive CVal where
  | int (v : Int)
  | ptr (p : CPtr)
  | undef
  deriving DecidableEq, Repr

/-- The integer a cell holds, `0` for a pointer or `undef` (only used by
    the projection onto lane 128's integer memory). -/
def CVal.toInt : CVal → Int
  | .int v => v
  | _ => 0

/-! ## 3. Typed record layouts, from the emitter's declarations -/

/-- The layout of one C object: `count` records, each of `nf` scalar
    fields; field `j` has type `fty j` at byte offset `off j`; a record is
    `ssize` bytes. A table is `typedef struct { f₀; … } T_slot;
    typedef struct { T_slot slots[N]; } T;` with `count = N`; a scalar
    global is `count = 1, nf = 1`; `uint8_t buf[N]` is `count = N,
    nf = 1, ssize = 1`. -/
structure RecLay where
  count : Nat
  nf : Nat
  fty : Nat → CTy
  off : Nat → Nat
  ssize : Nat

/-- `sizeof` of the whole object. -/
def RecLay.size (R : RecLay) : Nat := R.count * R.ssize

/-- Every field fits in the record and is aligned, in the record and
    across records. -/
def RecLay.fitsB (R : RecLay) : Bool :=
  (List.range R.nf).all fun j =>
    decide (R.off j + (R.fty j).size ≤ R.ssize) &&
    decide (R.off j % (R.fty j).size = 0) &&
    decide (R.ssize % (R.fty j).size = 0)

/-- No two fields overlap. -/
def RecLay.disjB (R : RecLay) : Bool :=
  (List.range R.nf).all fun j => (List.range R.nf).all fun j' =>
    decide (j = j') || decide (R.off j + (R.fty j).size ≤ R.off j') ||
    decide (R.off j' + (R.fty j').size ≤ R.off j)

/-- Well-formedness: decidable, so a certificate's layout is checked by
    `decide` per program. -/
def RecLay.wf (R : RecLay) : Bool := R.fitsB && R.disjB

/-- The field whose offset is `r`, if any. -/
def RecLay.fieldAt (R : RecLay) (r : Nat) : Option Nat :=
  (List.range R.nf).find? fun j => R.off j == r

/-- The cell starting at byte `o` of the object: its type, or `none`
    (past the end, inside a field, or in padding). -/
def RecLay.cell (R : RecLay) (o : Nat) : Option CTy :=
  if o < R.size then (R.fieldAt (o % R.ssize)).map R.fty else none

/-- The one-cell layout of a scalar object. -/
def scalarRec (τ : CTy) : RecLay :=
  { count := 1, nf := 1, fty := fun _ => τ, off := fun _ => 0, ssize := τ.size }

theorem RecLay.wf_fits {R : RecLay} (h : R.wf = true) {j : Nat} (hj : j < R.nf) :
    R.off j + (R.fty j).size ≤ R.ssize := by
  have h1 : R.fitsB = true := by
    unfold RecLay.wf at h
    cases hf : R.fitsB <;> simp_all
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  exact h2.1.1

theorem RecLay.wf_disj {R : RecLay} (h : R.wf = true) {j j' : Nat} (hj : j < R.nf)
    (hj' : j' < R.nf) (hne : j ≠ j') :
    R.off j + (R.fty j).size ≤ R.off j' ∨ R.off j' + (R.fty j').size ≤ R.off j := by
  have h1 : R.disjB = true := by
    unfold RecLay.wf at h
    cases hf : R.disjB <;> simp_all
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  have h3 := List.all_eq_true.mp h2 j' (List.mem_range.mpr hj')
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h3
  rcases h3 with (h4 | h4) | h4
  · exact absurd h4 hne
  · exact Or.inl h4
  · exact Or.inr h4

/-- A field starts inside the record. -/
theorem RecLay.off_lt {R : RecLay} (h : R.wf = true) {j : Nat} (hj : j < R.nf) :
    R.off j < R.ssize := by
  have := R.wf_fits h hj
  have := (R.fty j).size_pos
  omega

/-- Distinct fields have distinct offsets. -/
theorem RecLay.off_inj {R : RecLay} (h : R.wf = true) {j j' : Nat} (hj : j < R.nf)
    (hj' : j' < R.nf) (e : R.off j = R.off j') : j = j' := by
  cases Classical.em (j = j') with
  | inl hh => exact hh
  | inr hne =>
      have := (R.fty j).size_pos
      have := (R.fty j').size_pos
      rcases R.wf_disj h hj hj' hne with h4 | h4 <;> omega

/-- The offset of a field names that field. -/
theorem RecLay.fieldAt_off {R : RecLay} (h : R.wf = true) {j : Nat} (hj : j < R.nf) :
    R.fieldAt (R.off j) = some j := by
  unfold RecLay.fieldAt
  cases hf : (List.range R.nf).find? (fun j' => R.off j' == R.off j) with
  | none =>
      have := (List.find?_eq_none.mp hf) j (List.mem_range.mpr hj)
      simp at this
  | some j' =>
      have hp := List.find?_some hf
      have hm := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      simp only [beq_iff_eq] at hp
      rw [R.off_inj h hm hj hp]

/-- Position arithmetic: a byte position in the object is one record and
    one field, and no other. -/
theorem RecLay.pos_inj {R : RecLay} (h : R.wf = true) {j j' : Nat} (hj : j < R.nf)
    (hj' : j' < R.nf) {k k' : Nat} (e : k * R.ssize + R.off j = k' * R.ssize + R.off j') :
    k = k' ∧ j = j' := by
  have hl := R.off_lt h hj
  have hl' := R.off_lt h hj'
  have hd : (k * R.ssize + R.off j) / R.ssize = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hl]; omega
  have hd' : (k' * R.ssize + R.off j') / R.ssize = k' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hl']; omega
  have hm : (k * R.ssize + R.off j) % R.ssize = R.off j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  have hm' : (k' * R.ssize + R.off j') % R.ssize = R.off j' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl']
  refine ⟨?_, ?_⟩
  · rw [← hd, ← hd', e]
  · apply R.off_inj h hj hj'
    rw [← hm, ← hm', e]

/-- The cell of record `k`, field `j` has the field's type. -/
theorem RecLay.cell_pos {R : RecLay} (h : R.wf = true) {j : Nat} (hj : j < R.nf)
    {k : Nat} (hk : k < R.count) :
    R.cell (k * R.ssize + R.off j) = some (R.fty j) := by
  have hl := R.off_lt h hj
  have hm : (k * R.ssize + R.off j) % R.ssize = R.off j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hl]
  have hs : k * R.ssize + R.off j < R.size := by
    unfold RecLay.size
    have : (k + 1) * R.ssize ≤ R.count * R.ssize := Nat.mul_le_mul_right _ hk
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  unfold RecLay.cell
  rw [if_pos hs, hm, R.fieldAt_off h hj]
  rfl

/-- The natural-alignment offset of the next field: `x` rounded up to a
    multiple of `a` (`a` is a size, so `0 < a`). -/
def alignUp (x a : Nat) : Nat := (x + a - 1) / a * a

/-- Offsets of a field list laid out from cursor `cur`, C's rule. -/
def natOffs : List CTy → Nat → List Nat
  | [], _ => []
  | τ :: ts, cur => alignUp cur τ.size :: natOffs ts (alignUp cur τ.size + τ.size)

/-- The end of the last field. -/
def natEnd : List CTy → Nat → Nat
  | [], cur => cur
  | τ :: ts, cur => natEnd ts (alignUp cur τ.size + τ.size)

/-- The strictest alignment of a field list (`1` for none). -/
def maxAlign : List CTy → Nat
  | [] => 1
  | τ :: ts => Nat.max τ.size (maxAlign ts)

/-- The layout the emitter's `typedef struct { … } T_slot; T_slot
    slots[N];` gets from a C compiler: natural alignment, tail padding to
    the strictest alignment. This is the layout ABI the plan names as an
    assumption about the C compiler (x86-64 SysV). -/
def natLay (count : Nat) (fs : List CTy) : RecLay where
  count := count
  nf := fs.length
  fty := fun j => fs.getD j (.int false .w8)
  off := fun j => (natOffs fs 0).getD j 0
  ssize := alignUp (natEnd fs 0) (maxAlign fs)

/-! ## 4. Block layouts and the program layout -/

/-- What kind of object a block is: ordinary, read-only (`static
    const`), atomic (`_Atomic`), or a device register window (MMIO). -/
inductive BKind where
  | plain | readonly | atomic | mmio
  deriving DecidableEq, Repr

/-- The four ways the emitted C touches a cell: plain read, plain write,
    `atomic_*_explicit`, and a `volatile` access. -/
inductive AccMode where
  | rd | wr | atom | vol
  deriving DecidableEq, Repr

/-- Which access a block kind admits. A plain access to an `_Atomic`
    object, and a plain access to a device window, are outside the
    emitted subset (the census finds none) and stuck. -/
def BKind.permits : BKind → AccMode → Bool
  | .plain, .rd => true
  | .plain, .wr => true
  | .readonly, .rd => true
  | .atomic, .atom => true
  | .mmio, .vol => true
  | _, _ => false

/-- A block: its record layout, its kind, and for a device window its
    declared physical base address. -/
structure BlkLay where
  lay : RecLay
  kind : BKind
  base : Nat

/-- The program layout: which blocks exist, and their layouts. It comes
    from the emitter's declarations; stack blocks are the same for every
    frame of a function (their liveness is in the state, `CSt.live`). -/
def CLayout := CBlk → Option BlkLay

/-! ## 5. State and observations -/

/-- The memory orders the emitter names (`memory_order_*`). -/
inductive COrd where
  | relaxed | acquire | release | acqRel | seqCst
  deriving DecidableEq, Repr

/-- One observation. Volatile device reads and writes, atomic loads,
    stores and compare-exchanges with their orders, and port I/O. -/
inductive CObs where
  | vrd (p : CPtr) (τ : CTy) (v : Int)
  | vwr (p : CPtr) (τ : CTy) (v : Int)
  | ard (p : CPtr) (o : COrd) (v : Int)
  | awr (p : CPtr) (o : COrd) (v : Int)
  | acas (p : CPtr) (os of : COrd) (seen des : Int) (ok : Bool)
  | pin (port : Int) (v : Int)
  | pout (port : Int) (v : Int)
  deriving DecidableEq, Repr

/-- The C state: cell contents, which blocks are alive (stack blocks come
    and go with frames), and the observation trace, newest first (like
    Gabbro's `spur`). -/
structure CSt where
  mem : CBlk → Nat → CVal
  live : CBlk → Bool
  obs : List CObs

/-! ## 6. The access discipline and its UB inventory -/

/-- The check every access makes: the block exists and is alive, its kind
    admits the access, the offset is not negative, and a cell of exactly
    type `τ` starts there. -/
def accOk (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (md : AccMode) : Bool :=
  match L p.blk with
  | none => false
  | some B =>
      st.live p.blk && B.kind.permits md && decide (0 ≤ p.off) &&
        decide (B.lay.cell p.off.toNat = some τ)

/-- The access UB inventory. Each constructor is one C11 undefined
    behaviour or one restriction of the emitted subset:
    - `noBlock`  -- no such object (a pointer not derived from one);
    - `dead`     -- the object's lifetime ended (C11 6.2.4p2, dangling);
    - `mode`     -- a plain access to `_Atomic`/device storage, or a store
                    to `const` storage (6.7.3p6);
    - `negOff`   -- before the object (6.5.6p8);
    - `pastEnd`  -- at or past its end (6.5.6p8, J.2 out-of-range);
    - `noCell`   -- inside the object but not at a cell of this type:
                    padding, the middle of a field, or the wrong type
                    (the effective-type rule, 6.5p7, and misalignment,
                    6.3.2.3p7). -/
inductive AccUB (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (md : AccMode) : Prop where
  | noBlock (h : L p.blk = none)
  | dead (B : BlkLay) (hB : L p.blk = some B) (h : st.live p.blk = false)
  | mode (B : BlkLay) (hB : L p.blk = some B) (h : B.kind.permits md = false)
  | negOff (h : p.off < 0)
  | pastEnd (B : BlkLay) (hB : L p.blk = some B) (h : B.lay.size ≤ p.off.toNat)
  | noCell (B : BlkLay) (hB : L p.blk = some B) (h : B.lay.cell p.off.toNat ≠ some τ)

/-- Every inventoried access UB fails the check. -/
theorem accUB_not_ok (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (md : AccMode)
    (h : AccUB L st p τ md) : accOk L st p τ md = false := by
  unfold accOk
  cases h with
  | noBlock h => rw [h]
  | dead B hB h => rw [hB]; simp [h]
  | mode B hB h => rw [hB]; simp [h]
  | negOff h =>
      cases hL : L p.blk with
      | none => rfl
      | some B =>
          have : ¬ (0 ≤ p.off) := by omega
          simp [this]
  | pastEnd B hB h =>
      rw [hB]
      have hc : B.lay.cell p.off.toNat = none := by
        unfold RecLay.cell
        rw [if_neg (by omega)]
      simp [hc]
  | noCell B hB h => rw [hB]; simp [h]

/-- Checker completeness: a failed check names its inventory entry. -/
theorem accOk_false_UB (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (md : AccMode)
    (h : accOk L st p τ md = false) : AccUB L st p τ md := by
  unfold accOk at h
  cases hL : L p.blk with
  | none => exact .noBlock hL
  | some B =>
      rw [hL] at h
      cases hl : st.live p.blk with
      | false => exact .dead B hL hl
      | true =>
          cases hm : B.kind.permits md with
          | false => exact .mode B hL hm
          | true =>
              cases Classical.em (0 ≤ p.off) with
              | inr hn => exact .negOff (by omega)
              | inl hp =>
                  cases Classical.em (B.lay.cell p.off.toNat = some τ) with
                  | inl hc => simp [hl, hm, hp, hc] at h
                  | inr hc => exact .noCell B hL hc

/-- The check is exactly the absence of access UB. -/
theorem accOk_iff (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (md : AccMode) :
    accOk L st p τ md = false ↔ AccUB L st p τ md :=
  ⟨accOk_false_UB L st p τ md, accUB_not_ok L st p τ md⟩

/-- What a clean check gives: the block, alive, of an admitting kind, and
    a cell of type `τ` at a non-negative offset. -/
theorem accOk_spec {L : CLayout} {st : CSt} {p : CPtr} {τ : CTy} {md : AccMode}
    (h : accOk L st p τ md = true) :
    ∃ B, L p.blk = some B ∧ st.live p.blk = true ∧ B.kind.permits md = true ∧
      0 ≤ p.off ∧ B.lay.cell p.off.toNat = some τ := by
  unfold accOk at h
  cases hL : L p.blk with
  | none => rw [hL] at h; simp at h
  | some B =>
      rw [hL] at h
      dsimp only at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨B, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A clean check at a cell of a well-formed object lies inside it. -/
theorem accOk_inside {L : CLayout} {st : CSt} {p : CPtr} {τ : CTy} {md : AccMode}
    {B : BlkLay} (hB : L p.blk = some B) (h : accOk L st p τ md = true) :
    p.off.toNat < B.lay.size := by
  obtain ⟨B', hB', -, -, -, hc⟩ := accOk_spec h
  rw [hB] at hB'
  cases hB'
  unfold RecLay.cell at hc
  cases Classical.em (p.off.toNat < B.lay.size) with
  | inl hl => exact hl
  | inr hl => rw [if_neg hl] at hc; exact absurd hc (by simp)

/-! ## 7. Load and store -/

/-- Does a value fit a cell type: the declared range for integers (the
    emitter's range guarantee, lane 128's `hrange`), a pointer for a
    pointer cell. -/
def valFits : CTy → CVal → Bool
  | .int sgn w, .int v => decide (cLo sgn w ≤ v ∧ v ≤ cHi sgn w)
  | .ptr, .ptr _ => true
  | _, _ => false

/-- One cell updated. -/
def memUpd (m : CBlk → Nat → CVal) (b : CBlk) (o : Nat) (v : CVal) : CBlk → Nat → CVal :=
  fun b' o' => if b' = b ∧ o' = o then v else m b' o'

/-- A plain load: `none` is STUCK -- access UB, or an uninitialised cell. -/
def bLoad (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) : Option CVal :=
  if accOk L st p τ .rd then
    match st.mem p.blk p.off.toNat with
    | .undef => none
    | v => some v
  else none

/-- A plain store: `none` is STUCK -- access UB, or a value outside the
    cell type. Nothing but the one cell changes; the trace is untouched. -/
def bStore (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (v : CVal) : Option CSt :=
  if accOk L st p τ .wr && valFits τ v then
    some { st with mem := memUpd st.mem p.blk p.off.toNat v }
  else none

/-- Load UB: access UB, or the cell was never written (C11 6.7.9p10 for
    automatic storage; `BEWEIS.md` §2 row 8). -/
inductive LoadUB (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) : Prop where
  | acc (h : AccUB L st p τ .rd)
  | uninit (h : st.mem p.blk p.off.toNat = .undef)

/-- Store UB: access UB, or a value outside the declared type. -/
inductive StoreUB (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (v : CVal) : Prop where
  | acc (h : AccUB L st p τ .wr)
  | range (h : valFits τ v = false)

theorem loadUB_stuck (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy)
    (h : LoadUB L st p τ) : bLoad L st p τ = none := by
  unfold bLoad
  cases h with
  | acc h => rw [accUB_not_ok L st p τ .rd h]; rfl
  | uninit h =>
      cases accOk L st p τ .rd
      · rfl
      · simp only [if_true, h]

theorem storeUB_stuck (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (v : CVal)
    (h : StoreUB L st p τ v) : bStore L st p τ v = none := by
  unfold bStore
  cases h with
  | acc h => rw [accUB_not_ok L st p τ .wr h]; rfl
  | range h => simp [h]

/-- Load progress: a clean check on a written cell loads it. -/
theorem bLoad_progress (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy)
    (h : accOk L st p τ .rd = true) (hv : st.mem p.blk p.off.toNat ≠ .undef) :
    bLoad L st p τ = some (st.mem p.blk p.off.toNat) := by
  unfold bLoad
  rw [if_pos h]
  cases hm : st.mem p.blk p.off.toNat with
  | undef => exact absurd hm hv
  | int v => rfl
  | ptr q => rfl

/-- Store progress. -/
theorem bStore_progress (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (v : CVal)
    (h : accOk L st p τ .wr = true) (hv : valFits τ v = true) :
    bStore L st p τ v = some { st with mem := memUpd st.mem p.blk p.off.toNat v } := by
  unfold bStore
  rw [h, hv]
  rfl

/-- Read over write, same cell. -/
theorem memUpd_same (m : CBlk → Nat → CVal) (b : CBlk) (o : Nat) (v : CVal) :
    memUpd m b o v b o = v := by
  simp [memUpd]

/-- Read over write, another cell: the store is invisible there. Distinct
    cells of a well-formed layout do not overlap (`RecLay.pos_inj`), and
    cells of distinct blocks never do -- that is the aliasing model. -/
theorem memUpd_other (m : CBlk → Nat → CVal) (b b' : CBlk) (o o' : Nat) (v : CVal)
    (h : ¬ (b' = b ∧ o' = o)) : memUpd m b o v b' o' = m b' o' := by
  simp only [memUpd]
  rw [if_neg h]

/-- A store changes no liveness and no observation. -/
theorem bStore_frame {L : CLayout} {st st' : CSt} {p : CPtr} {τ : CTy} {v : CVal}
    (h : bStore L st p τ v = some st') : st'.live = st.live ∧ st'.obs = st.obs := by
  unfold bStore at h
  cases hc : (accOk L st p τ .wr && valFits τ v) with
  | false => rw [hc] at h; exact absurd h (by simp)
  | true =>
      rw [hc] at h
      cases h
      exact ⟨rfl, rfl⟩

/-! ## 8. Pointer arithmetic, with provenance -/

/-- `p + n` over elements of `es` bytes. Defined while the result stays
    in `[0, size]` of p's block -- one past the end is a valid pointer
    that must not be dereferenced (C11 6.5.6p8); the block never changes. -/
def ptrAdd (L : CLayout) (p : CPtr) (n : Int) (es : Nat) : Option CPtr :=
  match L p.blk with
  | none => none
  | some B =>
      if 0 ≤ p.off + n * es ∧ p.off + n * es ≤ (B.lay.size : Int) then
        some ⟨p.blk, p.off + n * es⟩
      else none

/-- Pointer-arithmetic UB: no object, or the result leaves it. -/
inductive PtrUB (L : CLayout) (p : CPtr) (n : Int) (es : Nat) : Prop where
  | noBlock (h : L p.blk = none)
  | below (B : BlkLay) (hB : L p.blk = some B) (h : p.off + n * es < 0)
  | above (B : BlkLay) (hB : L p.blk = some B) (h : (B.lay.size : Int) < p.off + n * es)

theorem ptrUB_stuck (L : CLayout) (p : CPtr) (n : Int) (es : Nat) (h : PtrUB L p n es) :
    ptrAdd L p n es = none := by
  unfold ptrAdd
  cases h with
  | noBlock h => rw [h]
  | below B hB h => rw [hB]; exact if_neg (by omega)
  | above B hB h => rw [hB]; exact if_neg (by omega)

/-- PROVENANCE: arithmetic never leaves its block. Two pointers into
    different objects therefore never alias, however they are computed. -/
theorem ptrAdd_blk {L : CLayout} {p q : CPtr} {n : Int} {es : Nat}
    (h : ptrAdd L p n es = some q) : q.blk = p.blk ∧ q.off = p.off + n * es := by
  unfold ptrAdd at h
  cases hL : L p.blk with
  | none => rw [hL] at h; exact absurd h (by simp)
  | some B =>
      rw [hL] at h
      dsimp only at h
      cases Classical.em (0 ≤ p.off + n * es ∧ p.off + n * es ≤ (B.lay.size : Int)) with
      | inl hc => rw [if_pos hc] at h; cases h; exact ⟨rfl, rfl⟩
      | inr hc => rw [if_neg hc] at h; exact absurd h (by simp)

/-- Arithmetic composes: `(p + a) + b = p + (a + b)` on byte elements,
    the shape of `d->basis + (lage) + i * s + off` in the device code. -/
theorem ptrAdd_add {L : CLayout} {p q : CPtr} {a b : Int}
    (h : ptrAdd L p a 1 = some q) : ptrAdd L q b 1 = ptrAdd L p (a + b) 1 := by
  obtain ⟨hb, ho⟩ := ptrAdd_blk h
  unfold ptrAdd
  rw [hb, ho]
  cases L p.blk with
  | none => rfl
  | some B =>
      have e : p.off + a * ((1 : Nat) : Int) + b * ((1 : Nat) : Int) =
          p.off + (a + b) * ((1 : Nat) : Int) := by
        simp only [Int.natCast_one, Int.mul_one]; omega
      rw [e]

/-- Progress: a result inside the object is a pointer. -/
theorem ptrAdd_progress (L : CLayout) (p : CPtr) (n : Int) (es : Nat) (B : BlkLay)
    (hB : L p.blk = some B) (h0 : 0 ≤ p.off + n * es)
    (h1 : p.off + n * es ≤ (B.lay.size : Int)) :
    ptrAdd L p n es = some ⟨p.blk, p.off + n * es⟩ := by
  unfold ptrAdd
  rw [hB]
  dsimp only
  rw [if_pos ⟨h0, h1⟩]

/-! ## 9. Stack frames and address-of -/

/-- `&x` for local `x` of frame `fr`. -/
def addrOf (fr x : Nat) : CPtr := ⟨.stk fr x, 0⟩

/-- Function entry: the listed locals of frame `fr` come alive,
    uninitialised. -/
def enterFrame (st : CSt) (fr : Nat) (xs : List Nat) : CSt where
  mem := fun b o => match b with
    | .stk f x => if f = fr ∧ x ∈ xs then .undef else st.mem b o
    | _ => st.mem b o
  live := fun b => match b with
    | .stk f x => if f = fr ∧ x ∈ xs then true else st.live b
    | _ => st.live b
  obs := st.obs

/-- Function exit: every local of frame `fr` dies. -/
def leaveFrame (st : CSt) (fr : Nat) : CSt where
  mem := st.mem
  live := fun b => match b with
    | .stk f _ => if f = fr then false else st.live b
    | _ => st.live b
  obs := st.obs

/-- A fresh local is uninitialised: reading it before a store is stuck. -/
theorem enter_uninit (L : CLayout) (st : CSt) (fr x : Nat) (xs : List Nat)
    (hx : x ∈ xs) (o : Int) (τ : CTy) :
    bLoad L (enterFrame st fr xs) ⟨.stk fr x, o⟩ τ = none := by
  apply loadUB_stuck
  apply LoadUB.uninit
  simp [enterFrame, hx]

/-- A dangling pointer: after the frame is left, every access through
    `&x` (or any pointer derived from it) is stuck. -/
theorem leave_dangling (L : CLayout) (st : CSt) (fr x : Nat) (o : Int) (τ : CTy)
    (md : AccMode) (B : BlkLay) (hB : L (.stk fr x) = some B) :
    accOk L (leaveFrame st fr) ⟨.stk fr x, o⟩ τ md = false := by
  apply accUB_not_ok
  exact .dead B hB (by simp [leaveFrame])

/-- Frames do not touch static objects. -/
theorem leaveFrame_tab (st : CSt) (fr t : Nat) :
    (leaveFrame st fr).live (.tab t) = st.live (.tab t) ∧
    (leaveFrame st fr).mem = st.mem := ⟨rfl, rfl⟩

/-! ## 10. Volatile and atomic accesses: the observation trace -/

/-- The environment's answer to a volatile read, given the history: the
    device is outside memory, as Gabbro's `Orakel` is outside the world. -/
def DevOrc := List CObs → CPtr → CTy → Int

/-- `*(volatile uintN_t *)(d->basis + off)` read: a declared register cell
    of an unsigned type in a device window. The device answers `w` bits;
    the event is appended, and memory is untouched. -/
def vLoad (L : CLayout) (orc : DevOrc) (st : CSt) (p : CPtr) (τ : CTy) : Option (Int × CSt) :=
  if accOk L st p τ .vol then
    match τ with
    | .int false w =>
        let v := cWrap w (orc st.obs p τ)
        some (v, { st with obs := .vrd p τ v :: st.obs })
    | _ => none
  else none

/-- `*(volatile uintN_t *)(d->basis + off) = v`: an event, no memory. -/
def vStore (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (v : Int) : Option CSt :=
  if accOk L st p τ .vol && valFits τ (.int v) then
    some { st with obs := .vwr p τ v :: st.obs }
  else none

/-- The order a load may name (C11 7.17.7.2p2: not `release`/`acq_rel`). -/
def COrd.loadOk : COrd → Bool
  | .release => false
  | .acqRel => false
  | _ => true

/-- The order a store may name (C11 7.17.7.1p2: not `acquire`/`acq_rel`). -/
def COrd.storeOk : COrd → Bool
  | .acquire => false
  | .acqRel => false
  | _ => true

/-- The failure order of a compare-exchange (C11 7.17.7.4p2). -/
def COrd.failOk : COrd → Bool
  | .release => false
  | .acqRel => false
  | _ => true

/-- Ordering UB: an order the operation may not name. -/
inductive OrdUB : AccMode → COrd → Prop where
  | load (o : COrd) (h : o.loadOk = false) : OrdUB .rd o
  | store (o : COrd) (h : o.storeOk = false) : OrdUB .wr o
  | casFail (o : COrd) (h : o.failOk = false) : OrdUB .atom o

/-- `atomic_load_explicit(&a, o)`: reads the cell, appends the event. -/
def aLoad (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (o : COrd) : Option (Int × CSt) :=
  if accOk L st p τ .atom && o.loadOk then
    match st.mem p.blk p.off.toNat with
    | .int v => some (v, { st with obs := .ard p o v :: st.obs })
    | _ => none
  else none

/-- `atomic_store_explicit(&a, v, o)`: writes the cell, appends the event. -/
def aStore (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (o : COrd) (v : Int) : Option CSt :=
  if accOk L st p τ .atom && o.storeOk && valFits τ (.int v) then
    some { st with mem := memUpd st.mem p.blk p.off.toNat (.int v),
                   obs := .awr p o v :: st.obs }
  else none

/-- `atomic_compare_exchange_{weak,strong}_explicit(&a, &_cx, des, os, of)`:
    success writes `des`; failure hands back the value seen (the emitted
    code then stores it into `_cx`, an ordinary stack store). The model
    is the strong form; a spurious weak failure is a `false` with the
    expected value seen, which the emitted retry loop absorbs (CUT). -/
def aCas (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (os of : COrd) (exp des : Int) :
    Option (Bool × Int × CSt) :=
  if accOk L st p τ .atom && of.failOk && valFits τ (.int des) then
    match st.mem p.blk p.off.toNat with
    | .int cur =>
        if cur = exp then
          some (true, cur, { st with mem := memUpd st.mem p.blk p.off.toNat (.int des),
                                     obs := .acas p os of cur des true :: st.obs })
        else
          some (false, cur, { st with obs := .acas p os of cur des false :: st.obs })
    | _ => none
  else none

theorem ordUB_load_stuck (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (o : COrd)
    (h : OrdUB .rd o) : aLoad L st p τ o = none := by
  cases h with
  | load _ h => unfold aLoad; simp [h]

theorem ordUB_store_stuck (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (o : COrd) (v : Int)
    (h : OrdUB .wr o) : aStore L st p τ o v = none := by
  cases h with
  | store _ h => unfold aStore; simp [h]

theorem ordUB_cas_stuck (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (os of : COrd)
    (exp des : Int) (h : OrdUB .atom of) : aCas L st p τ os of exp des = none := by
  cases h with
  | casFail _ h => unfold aCas; simp [h]

/-- A plain access to an `_Atomic` object is stuck (outside the subset). -/
theorem plain_on_atomic_stuck (L : CLayout) (st : CSt) (p : CPtr) (τ : CTy) (B : BlkLay)
    (hB : L p.blk = some B) (hk : B.kind = .atomic) : bLoad L st p τ = none := by
  apply loadUB_stuck
  exact .acc (.mode B hB (by rw [hk]; rfl))

/-- A volatile store leaves memory alone and appends exactly its event:
    volatile accesses are never merged or elided (C11 5.1.2.3p6). -/
theorem vStore_obs {L : CLayout} {st st' : CSt} {p : CPtr} {τ : CTy} {v : Int}
    (h : vStore L st p τ v = some st') :
    st'.mem = st.mem ∧ st'.live = st.live ∧ st'.obs = .vwr p τ v :: st.obs := by
  unfold vStore at h
  cases hc : (accOk L st p τ .vol && valFits τ (.int v)) with
  | false => rw [hc] at h; exact absurd h (by simp)
  | true => rw [hc] at h; cases h; exact ⟨rfl, rfl, rfl⟩

/-- A volatile load appends exactly its event and returns a value of the
    register's width. -/
theorem vLoad_obs {L : CLayout} {orc : DevOrc} {st st' : CSt} {p : CPtr} {τ : CTy} {v : Int}
    (h : vLoad L orc st p τ = some (v, st')) :
    st'.mem = st.mem ∧ st'.obs = .vrd p τ v :: st.obs := by
  unfold vLoad at h
  cases hc : accOk L st p τ .vol with
  | false => rw [hc] at h; exact absurd h (by simp)
  | true =>
      rw [if_pos hc] at h
      cases τ with
      | ptr => exact absurd h (by simp)
      | int sgn w =>
          cases sgn with
          | true => exact absurd h (by simp)
          | false =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨h1, h2⟩ := h
              subst h1; subst h2
              exact ⟨rfl, rfl⟩

/-- An atomic store is a store plus its event: its memory effect is the
    plain store's, so the refinement below covers atomic globals too. -/
theorem aStore_mem {L : CLayout} {st st' : CSt} {p : CPtr} {τ : CTy} {o : COrd} {v : Int}
    (h : aStore L st p τ o v = some st') :
    st'.mem = memUpd st.mem p.blk p.off.toNat (.int v) ∧ st'.live = st.live ∧
      st'.obs = .awr p o v :: st.obs := by
  unfold aStore at h
  cases hc : (accOk L st p τ .atom && o.storeOk && valFits τ (.int v)) with
  | false => rw [hc] at h; exact absurd h (by simp)
  | true => rw [hc] at h; cases h; exact ⟨rfl, rfl, rfl⟩

/-- `(volatile uint8_t *)(uintptr_t)a`: the handle of device `d`, defined
    only for its declared base address (C11 6.3.2.3p5 makes the
    conversion implementation-defined; the model admits exactly the
    addresses the program declares). -/
def devHandle (L : CLayout) (d : Nat) (a : Int) : Option CPtr :=
  match L (.dev d) with
  | some B => if B.kind = .mmio ∧ (B.base : Int) = a then some ⟨.dev d, 0⟩ else none
  | none => none

/-- `(uint16_t)(d->basis + k)`: a device pointer as a port number, for the
    `inb`/`outb` blocks (the only pointer-to-integer conversion emitted). -/
def portOf (L : CLayout) (p : CPtr) : Option Int :=
  match p.blk, L p.blk with
  | .dev _, some B =>
      if 0 ≤ p.off ∧ p.off < (B.lay.size : Int) then some (B.base + p.off) else none
  | _, _ => none

/-- `outb`: an event. -/
def portOut (L : CLayout) (st : CSt) (p : CPtr) (v : Int) : Option CSt :=
  match portOf L p with
  | some n => some { st with obs := .pout n v :: st.obs }
  | none => none

/-- `inb`: the environment answers 8 bits. -/
def portIn (L : CLayout) (orc : DevOrc) (st : CSt) (p : CPtr) : Option (Int × CSt) :=
  match portOf L p with
  | some n =>
      let v := cWrap .w8 (orc st.obs p (.int false .w8))
      some (v, { st with obs := .pin n v :: st.obs })
  | none => none

/-- A handle is a pointer to its window's start: every register access
    through it is `ptrAdd` from there, inside the window. -/
theorem devHandle_spec {L : CLayout} {d : Nat} {a : Int} {p : CPtr}
    (h : devHandle L d a = some p) :
    p = ⟨.dev d, 0⟩ ∧ ∃ B, L (.dev d) = some B ∧ B.kind = .mmio ∧ (B.base : Int) = a := by
  unfold devHandle at h
  cases hL : L (.dev d) with
  | none => rw [hL] at h; exact absurd h (by simp)
  | some B =>
      rw [hL] at h
      dsimp only at h
      cases Classical.em (B.kind = .mmio ∧ (B.base : Int) = a) with
      | inl hc => rw [if_pos hc] at h; cases h; exact ⟨rfl, B, rfl, hc.1, hc.2⟩
      | inr hc => rw [if_neg hc] at h; exact absurd h (by simp)

/-! ## 11. Refinement: lane 128's five forms on the block memory

The five forms keep lane 128's syntax (`CExpr`, `CStmt`) and get a
second semantics over `CSt`. A slot read or store is now a load or store
at the address the emitter computes, `t->slots[k].f` = block `tab t`,
offset `k * sizeof(T_slot) + offsetof(T_slot, f)`, with the cell type
the layout declares. The old `(table, index, field)` memory is the
PROJECTION `projMem` of the new one, and under it the two semantics make
the same steps and get stuck at the same places (`bExec_refines`). -/

/-- The program layout of the five forms: every table number is a table
    block with its record layout; nothing else exists. -/
def tabLayout (TL : Nat → RecLay) : CLayout := fun b =>
  match b with
  | .tab t => some { lay := TL t, kind := .plain, base := 0 }
  | _ => none

/-- The geometry lane 128 reads off a layout: slots per table. -/
def geomOf (TL : Nat → RecLay) : CGeom := fun t => (TL t).count

/-- The emitted address of `t->slots[k].f`. -/
def slotAt (TL : Nat → RecLay) (t k f : Nat) : CPtr :=
  ⟨.tab t, ((k * (TL t).ssize + (TL t).off f : Nat) : Int)⟩

theorem slotAt_toNat (TL : Nat → RecLay) (t k f : Nat) :
    (slotAt TL t k f).off.toNat = k * (TL t).ssize + (TL t).off f :=
  Int.toNat_natCast _

/-- Expression evaluation on the block memory: form A unchanged, form B
    a checked index and then a typed load. -/
def bEval (TL : Nat → RecLay) : CExpr → CSt → CEnv → Option Int
  | .lit v, _, _ => some v
  | .var x, _, ρ => some (ρ x)
  | .bin op sgn w l r, st, ρ =>
      match bEval TL l st ρ, bEval TL r st ρ with
      | some a, some b => cBinApply op sgn w a b
      | _, _ => none
  | .slot t i f, st, ρ =>
      match bEval TL i st ρ with
      | some k =>
          if 0 ≤ k ∧ k < ((TL t).count : Int) then
            match bLoad (tabLayout TL) st (slotAt TL t k.toNat f) ((TL t).fty f) with
            | some (.int v) => some v
            | _ => none
          else none
      | none => none

/-- The counting loop over the block state (lane 128's `cForRun`). -/
def bForRun (runBody : CSt → CEnv → Nat → Option (CSt × CEnv)) (x : Nat)
    (cur hi : Int) (st : CSt) (ρ : CEnv) (fuel : Nat) : Option (CSt × CEnv) :=
  if cur < hi then
    match fuel with
    | 0 => none
    | n + 1 =>
        match runBody st (cUpd ρ x cur) n with
        | some (st', ρ') => bForRun runBody x (cur + 1) hi st' ρ' n
        | none => none
  else some (st, cUpd ρ x cur)

/-- Statement execution on the block memory: form C is a checked index
    and a typed store `t->slots[k].f = v` at the statement's C type. -/
def bExec (TL : Nat → RecLay) : CStmt → CSt → CEnv → Nat → Option (CSt × CEnv)
  | .skip, st, ρ, _ => some (st, ρ)
  | .assign t i f sgn w e, st, ρ, _ =>
      match bEval TL i st ρ, bEval TL e st ρ with
      | some k, some v =>
          if 0 ≤ k ∧ k < ((TL t).count : Int) then
            match bStore (tabLayout TL) st (slotAt TL t k.toNat f) (.int sgn w) (.int v) with
            | some st' => some (st', ρ)
            | none => none
          else none
      | _, _ => none
  | .seq a b, st, ρ, fuel =>
      match bExec TL a st ρ fuel with
      | some (st', ρ') => bExec TL b st' ρ' fuel
      | none => none
  | .cif c t e, st, ρ, fuel =>
      match bEval TL c st ρ with
      | some v => if v ≠ 0 then bExec TL t st ρ fuel else bExec TL e st ρ fuel
      | none => none
  | .cfor x lo hi body, st, ρ, fuel =>
      bForRun (fun st ρ f => bExec TL body st ρ f) x lo hi st ρ fuel

/-- The fields an expression names exist in the layout. (Lane 128 reads
    any field number; the emitter only writes declared ones.) -/
def CExpr.fieldsOk (TL : Nat → RecLay) : CExpr → Bool
  | .lit _ => true
  | .var _ => true
  | .bin _ _ _ l r => CExpr.fieldsOk TL l && CExpr.fieldsOk TL r
  | .slot t i f => decide (f < (TL t).nf) && CExpr.fieldsOk TL i

/-- The statement's fields exist and every store names its field's
    declared C type (the emitter writes `t->slots[i].f = (T)v` at the
    type of the `typedef`). -/
def CStmt.okB (TL : Nat → RecLay) : CStmt → Bool
  | .skip => true
  | .assign t i f sgn w e =>
      decide (f < (TL t).nf) && decide ((TL t).fty f = .int sgn w) &&
        CExpr.fieldsOk TL i && CExpr.fieldsOk TL e
  | .seq a b => CStmt.okB TL a && CStmt.okB TL b
  | .cif c t e => CExpr.fieldsOk TL c && CStmt.okB TL t && CStmt.okB TL e
  | .cfor _ _ _ body => CStmt.okB TL body

/-- THE PROJECTION: lane 128's `(table, index, field)` memory is the
    integer content of the cell the layout assigns; positions the layout
    does not have read `0`. -/
def projMem (TL : Nat → RecLay) (st : CSt) : CMem := fun t k f =>
  if k < (TL t).count ∧ f < (TL t).nf then
    (st.mem (.tab t) (k * (TL t).ssize + (TL t).off f)).toInt
  else 0

/-- The invariant under which the projection is faithful: the tables
    are alive and every cell holds an integer. -/
structure Good (TL : Nat → RecLay) (st : CSt) : Prop where
  live : ∀ t, st.live (.tab t) = true
  ints : ∀ t k f, k < (TL t).count → f < (TL t).nf →
    ∃ v, st.mem (.tab t) (k * (TL t).ssize + (TL t).off f) = .int v

/-- A slot cell passes the access check. -/
theorem accOk_slot (TL : Nat → RecLay) (hwf : ∀ t, (TL t).wf = true) (st : CSt)
    (t k f : Nat) (hl : st.live (.tab t) = true) (hk : k < (TL t).count)
    (hf : f < (TL t).nf) (md : AccMode) (hmd : BKind.plain.permits md = true) :
    accOk (tabLayout TL) st (slotAt TL t k f) ((TL t).fty f) md = true := by
  unfold accOk
  show (st.live (.tab t) && BKind.plain.permits md &&
      decide (0 ≤ (slotAt TL t k f).off) &&
      decide ((TL t).cell (slotAt TL t k f).off.toNat = some ((TL t).fty f))) = true
  have h0 : 0 ≤ (slotAt TL t k f).off :=
    show 0 ≤ ((k * (TL t).ssize + (TL t).off f : Nat) : Int) by omega
  rw [slotAt_toNat, RecLay.cell_pos (hwf t) hf hk, hl, hmd]
  simp [h0]

/-- The emitted load of a slot reads its integer. -/
theorem bLoad_slot (TL : Nat → RecLay) (hwf : ∀ t, (TL t).wf = true) (st : CSt)
    (hg : Good TL st) (t k f : Nat) (hk : k < (TL t).count) (hf : f < (TL t).nf) :
    ∃ v, st.mem (.tab t) (k * (TL t).ssize + (TL t).off f) = .int v ∧
      bLoad (tabLayout TL) st (slotAt TL t k f) ((TL t).fty f) = some (.int v) := by
  obtain ⟨v, hv⟩ := hg.ints t k f hk hf
  refine ⟨v, hv, ?_⟩
  have ha := accOk_slot TL hwf st t k f (hg.live t) hk hf .rd rfl
  have hne : st.mem (slotAt TL t k f).blk (slotAt TL t k f).off.toNat ≠ .undef := by
    rw [slotAt_toNat]; show st.mem (.tab t) _ ≠ _; rw [hv]; simp
  rw [bLoad_progress _ _ _ _ ha hne, slotAt_toNat]
  exact congrArg some hv

/-- EXPRESSION REFINEMENT: on a good state, the block semantics and lane
    128's semantics on the projection evaluate every expression whose
    fields exist to the same result -- including getting stuck. -/
theorem bEval_refines (TL : Nat → RecLay) (hwf : ∀ t, (TL t).wf = true) :
    ∀ (e : CExpr) (st : CSt) (ρ : CEnv), CExpr.fieldsOk TL e = true → Good TL st →
      bEval TL e st ρ = aEval e (projMem TL st) ρ (geomOf TL) := by
  intro e
  induction e with
  | lit v => intro st ρ _ _; rfl
  | var x => intro st ρ _ _; rfl
  | bin op sgn w l r ihl ihr =>
      intro st ρ h hg
      simp only [CExpr.fieldsOk, Bool.and_eq_true] at h
      simp only [bEval, aEval, ihl st ρ h.1 hg, ihr st ρ h.2 hg]
      cases aEval l (projMem TL st) ρ (geomOf TL) <;>
        cases aEval r (projMem TL st) ρ (geomOf TL) <;> rfl
  | slot t i f ihi =>
      intro st ρ h hg
      simp only [CExpr.fieldsOk, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [bEval, aEval, ihi st ρ h.2 hg]
      cases aEval i (projMem TL st) ρ (geomOf TL) with
      | none => rfl
      | some k =>
          simp only
          by_cases hk : 0 ≤ k ∧ k < ((TL t).count : Int)
          · rw [if_pos hk, if_pos (show 0 ≤ k ∧ k < (geomOf TL t : Int) from hk)]
            have hkn : k.toNat < (TL t).count := by omega
            obtain ⟨v, hm, hl⟩ := bLoad_slot TL hwf st hg t k.toNat f hkn h.1
            rw [hl]
            simp only [projMem, if_pos (And.intro hkn h.1), hm, CVal.toInt]
          · rw [if_neg hk, if_neg (show ¬ (0 ≤ k ∧ k < (geomOf TL t : Int)) from hk)]

/-- A slot store, seen through the projection, is lane 128's store. -/
theorem projMem_store (TL : Nat → RecLay) (hwf : ∀ t, (TL t).wf = true) (st : CSt)
    (t k f : Nat) (hk : k < (TL t).count) (hf : f < (TL t).nf) (v : Int) :
    projMem TL { st with mem := memUpd st.mem (.tab t) (k * (TL t).ssize + (TL t).off f) (.int v) } =
      fun t' k' f' => if t' = t ∧ k' = k ∧ f' = f then v else projMem TL st t' k' f' := by
  funext t' k' f'
  by_cases hv : k' < (TL t').count ∧ f' < (TL t').nf
  · by_cases he : t' = t ∧ k' = k ∧ f' = f
    · obtain ⟨e1, e2, e3⟩ := he
      subst e1; subst e2; subst e3
      simp [projMem, memUpd, hv, CVal.toInt]
    · rw [if_neg he]
      simp only [projMem, if_pos hv]
      congr 1
      apply memUpd_other
      intro hc
      obtain ⟨hb, ho⟩ := hc
      cases hb
      obtain ⟨h1, h2⟩ := RecLay.pos_inj (hwf _) hv.2 hf ho
      exact he ⟨rfl, h1, h2⟩
  · have he : ¬ (t' = t ∧ k' = k ∧ f' = f) := by
      intro h
      obtain ⟨e1, e2, e3⟩ := h
      subst e1; subst e2; subst e3
      exact hv ⟨hk, hf⟩
    rw [if_neg he]
    simp only [projMem, if_neg hv]

/-- A slot store keeps the state good. -/
theorem good_store (TL : Nat → RecLay) (st : CSt) (hg : Good TL st) (b : CBlk) (o : Nat)
    (v : Int) : Good TL { st with mem := memUpd st.mem b o (.int v) } := by
  refine ⟨hg.live, ?_⟩
  intro t k f hk hf
  show ∃ w, memUpd st.mem b o (.int v) (.tab t) _ = _
  by_cases hc : (CBlk.tab t = b ∧ k * (TL t).ssize + (TL t).off f = o)
  · exact ⟨v, by simp only [memUpd]; rw [if_pos hc]⟩
  · rw [memUpd_other _ _ _ _ _ _ hc]
    exact hg.ints t k f hk hf

/-- The relation between the two outcomes: both stuck, or both finished
    with the projection, the same environment, and a good state. -/
def RelOut (TL : Nat → RecLay) : Option (CSt × CEnv) → Option (CMem × CEnv) → Prop
  | none, none => True
  | some p, some q => projMem TL p.1 = q.1 ∧ p.2 = q.2 ∧ Good TL p.1
  | _, _ => False

/-- One iteration of the block loop, unfolded. -/
theorem bForRun_succ (rb : CSt → CEnv → Nat → Option (CSt × CEnv)) (x : Nat) (cur hi : Int)
    (st : CSt) (ρ : CEnv) (n : Nat) (hlt : cur < hi) :
    bForRun rb x cur hi st ρ (n + 1) =
      match rb st (cUpd ρ x cur) n with
      | some p => bForRun rb x (cur + 1) hi p.1 p.2 n
      | none => none := by
  rw [bForRun, if_pos hlt]
  cases rb st (cUpd ρ x cur) n with
  | none => rfl
  | some p => rfl

/-- One iteration of lane 128's loop, unfolded. -/
theorem cForRun_succ (ra : CMem → CEnv → Nat → Option (CMem × CEnv)) (x : Nat) (cur hi : Int)
    (m : CMem) (ρ : CEnv) (n : Nat) (hlt : cur < hi) :
    cForRun ra x cur hi m ρ (n + 1) =
      match ra m (cUpd ρ x cur) n with
      | some p => cForRun ra x (cur + 1) hi p.1 p.2 n
      | none => none := by
  rw [cForRun, if_pos hlt]
  cases ra m (cUpd ρ x cur) n with
  | none => rfl
  | some p => rfl

/-- Loop refinement: related bodies give related loops. -/
theorem forRun_refines (TL : Nat → RecLay) (rb : CSt → CEnv → Nat → Option (CSt × CEnv))
    (ra : CMem → CEnv → Nat → Option (CMem × CEnv)) (x : Nat) (hi : Int)
    (hb : ∀ st ρ n, Good TL st → RelOut TL (rb st ρ n) (ra (projMem TL st) ρ n)) :
    ∀ fuel cur st ρ, Good TL st →
      RelOut TL (bForRun rb x cur hi st ρ fuel) (cForRun ra x cur hi (projMem TL st) ρ fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cur st ρ hg
      unfold bForRun cForRun
      by_cases hlt : cur < hi
      · rw [if_pos hlt, if_pos hlt]; trivial
      · rw [if_neg hlt, if_neg hlt]; exact ⟨rfl, rfl, hg⟩
  | succ n ih =>
      intro cur st ρ hg
      by_cases hlt : cur < hi
      · rw [bForRun_succ _ _ _ _ _ _ _ hlt, cForRun_succ _ _ _ _ _ _ _ hlt]
        have h1 := hb st (cUpd ρ x cur) n hg
        cases hr : rb st (cUpd ρ x cur) n with
        | none =>
            cases ha : ra (projMem TL st) (cUpd ρ x cur) n with
            | none => trivial
            | some q => rw [hr, ha] at h1; exact h1.elim
        | some p =>
            cases ha : ra (projMem TL st) (cUpd ρ x cur) n with
            | none => rw [hr, ha] at h1; exact h1.elim
            | some q =>
                rw [hr, ha] at h1
                obtain ⟨hp, hρ, hg'⟩ := h1
                obtain ⟨st', ρ'⟩ := p
                obtain ⟨m', ρ''⟩ := q
                simp only at hp hρ hg'
                subst hp; subst hρ
                exact ih (cur + 1) st' ρ' hg'
      · unfold bForRun cForRun
        rw [if_neg hlt, if_neg hlt]; exact ⟨rfl, rfl, hg⟩

/-- STATEMENT REFINEMENT (the old view is a projection of the new one):
    for every statement whose fields exist and whose stores name their
    declared C types, from a good state, the block semantics and lane
    128's semantics on the projection are both stuck or both finish, in
    related states. Lane 128's theorems therefore carry over. -/
theorem bExec_refines (TL : Nat → RecLay) (hwf : ∀ t, (TL t).wf = true) :
    ∀ (s : CStmt) (st : CSt) (ρ : CEnv) (fuel : Nat), CStmt.okB TL s = true → Good TL st →
      RelOut TL (bExec TL s st ρ fuel) (cExec s (projMem TL st) ρ (geomOf TL) fuel) := by
  intro s
  induction s with
  | skip => intro st ρ fuel _ hg; exact ⟨rfl, rfl, hg⟩
  | assign t i f sgn w e =>
      intro st ρ fuel h hg
      simp only [CStmt.okB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hf, hty⟩, hi⟩, he⟩ := h
      simp only [bExec, cExec, bEval_refines TL hwf i st ρ hi hg,
        bEval_refines TL hwf e st ρ he hg]
      cases aEval i (projMem TL st) ρ (geomOf TL) with
      | none => trivial
      | some k =>
          cases aEval e (projMem TL st) ρ (geomOf TL) with
          | none => trivial
          | some v =>
              simp only
              by_cases hk : 0 ≤ k ∧ k < ((TL t).count : Int)
              · rw [if_pos hk]
                have hkn : k.toNat < (TL t).count := by omega
                by_cases hv : cLo sgn w ≤ v ∧ v ≤ cHi sgn w
                · have ha := accOk_slot TL hwf st t k.toNat f (hg.live t) hkn hf .wr rfl
                  rw [hty] at ha
                  have hfit : valFits (.int sgn w) (.int v) = true := by
                    simp [valFits, hv.1, hv.2]
                  rw [bStore_progress _ _ _ _ _ ha hfit,
                    if_pos (show 0 ≤ k ∧ k < (geomOf TL t : Int) ∧ cLo sgn w ≤ v ∧
                      v ≤ cHi sgn w from ⟨hk.1, hk.2, hv.1, hv.2⟩)]
                  refine ⟨?_, rfl, ?_⟩
                  · show projMem TL { st with mem := (memUpd st.mem (.tab t)
                        (slotAt TL t k.toNat f).off.toNat (.int v)) } = _
                    rw [slotAt_toNat, projMem_store TL hwf st t k.toNat f hkn hf v]
                  · exact good_store TL st hg (.tab t) _ v
                · have hfit : valFits (.int sgn w) (.int v) = false := by
                    simp only [valFits, decide_eq_false_iff_not]; exact hv
                  rw [storeUB_stuck _ _ _ _ _ (.range hfit),
                    if_neg (show ¬ (0 ≤ k ∧ k < (geomOf TL t : Int) ∧ cLo sgn w ≤ v ∧
                      v ≤ cHi sgn w) from fun h' => hv ⟨h'.2.2.1, h'.2.2.2⟩)]
                  trivial
              · rw [if_neg hk, if_neg (show ¬ (0 ≤ k ∧ k < (geomOf TL t : Int) ∧
                    cLo sgn w ≤ v ∧ v ≤ cHi sgn w) from fun h' => hk ⟨h'.1, h'.2.1⟩)]
                trivial
  | seq a b iha ihb =>
      intro st ρ fuel h hg
      simp only [CStmt.okB, Bool.and_eq_true] at h
      have h1 := iha st ρ fuel h.1 hg
      simp only [bExec, cExec]
      cases hr : bExec TL a st ρ fuel with
      | none =>
          cases ha : cExec a (projMem TL st) ρ (geomOf TL) fuel with
          | none => trivial
          | some q => rw [hr, ha] at h1; exact h1.elim
      | some p =>
          cases ha : cExec a (projMem TL st) ρ (geomOf TL) fuel with
          | none => rw [hr, ha] at h1; exact h1.elim
          | some q =>
              rw [hr, ha] at h1
              obtain ⟨hp, hρ, hg'⟩ := h1
              obtain ⟨st', ρ'⟩ := p
              obtain ⟨m', ρ''⟩ := q
              simp only at hp hρ hg'
              subst hp; subst hρ
              exact ihb st' ρ' fuel h.2 hg'
  | cif c t e iht ihe =>
      intro st ρ fuel h hg
      simp only [CStmt.okB, Bool.and_eq_true] at h
      obtain ⟨⟨hc, ht⟩, he⟩ := h
      simp only [bExec, cExec, bEval_refines TL hwf c st ρ hc hg]
      cases aEval c (projMem TL st) ρ (geomOf TL) with
      | none => trivial
      | some v =>
          simp only
          by_cases hz : v ≠ 0
          · rw [if_pos hz, if_pos hz]; exact iht st ρ fuel ht hg
          · rw [if_neg hz, if_neg hz]; exact ihe st ρ fuel he hg
  | cfor x lo hi body ih =>
      intro st ρ fuel h hg
      simp only [CStmt.okB] at h
      exact forRun_refines TL (fun st ρ f => bExec TL body st ρ f)
        (fun m ρ f => cExec body m ρ (geomOf TL) f) x hi
        (fun st' ρ' n hg' => ih st' ρ' n h hg') fuel lo st ρ hg

/-! ### `cCorr_assignSlot` carried over to the block memory -/

/-- The emitted layout of `Konto`: `typedef struct { uint32_t stand; }
    Konto_slot; typedef struct { Konto_slot slots[NKONTO]; } Konto;`
    with `NKONTO = 2` (`beispiele/104-referenz.gab`, emitted C). -/
def kontoLay : RecLay := natLay 2 [.int false .w32]

/-- The layout computes to what a C compiler gives: the field at offset
    0, `sizeof(Konto_slot) = 4`, `sizeof(Konto) = 8`. -/
theorem kontoLay_werte :
    kontoLay.off 0 = 0 ∧ kontoLay.ssize = 4 ∧ kontoLay.size = 8 ∧
      kontoLay.fty 0 = .int false .w32 ∧ kontoLay.nf = 1 ∧ kontoLay.count = 2 := by
  decide

/-- The object with nothing in it (table numbers the program lacks). -/
def leerLay : RecLay :=
  { count := 0, nf := 0, fty := fun _ => .ptr, off := fun _ => 0, ssize := 0 }

/-- The table layouts of the reference program: table 0 is `Konto`. -/
def refTL : Nat → RecLay
  | 0 => kontoLay
  | _ + 1 => leerLay

theorem refTL_wf : ∀ t, (refTL t).wf = true := by
  intro t
  cases t with
  | zero => decide
  | succ n => rfl

/-- The block layout's geometry IS lane 128's reference geometry. -/
theorem refTL_geom : geomOf refTL = cGeomRef := by
  funext t
  cases t with
  | zero => rfl
  | succ n => rfl

/-- Memory correspondence on `refD` over the block memory: both `konto`
    cells, at offsets 0 and 4 of the table block, hold the slots. -/
def corrMemB (σ : World refD) (st : CSt) : Prop :=
  st.mem (.tab 0) 0 = .int (σ.slots () 0 ()).n ∧ st.mem (.tab 0) 4 = .int (σ.slots () 1 ()).n

/-- The block correspondence projects to lane 128's. -/
theorem corrMemB_proj (σ : World refD) (st : CSt) (h : corrMemB σ st) :
    corrMemW σ (projMem refTL st) := by
  constructor
  · show (if 0 < kontoLay.count ∧ 0 < kontoLay.nf then
        (st.mem (.tab 0) (0 * kontoLay.ssize + kontoLay.off 0)).toInt else 0) = _
    rw [if_pos (by decide)]
    show (st.mem (.tab 0) 0).toInt = _
    rw [h.1]; rfl
  · show (if 1 < kontoLay.count ∧ 0 < kontoLay.nf then
        (st.mem (.tab 0) (1 * kontoLay.ssize + kontoLay.off 0)).toInt else 0) = _
    rw [if_pos (by decide)]
    show (st.mem (.tab 0) 4).toInt = _
    rw [h.2]; rfl

/-- ... and back, on a good state (every cell holds an integer). -/
theorem corrMemB_of_proj (σ : World refD) (st : CSt) (hg : Good refTL st)
    (h : corrMemW σ (projMem refTL st)) : corrMemB σ st := by
  obtain ⟨v0, h0⟩ := hg.ints 0 0 0 (by decide) (by decide)
  obtain ⟨v1, h1⟩ := hg.ints 0 1 0 (by decide) (by decide)
  have e0 : st.mem (.tab 0) 0 = .int v0 := h0
  have e1 : st.mem (.tab 0) 4 = .int v1 := h1
  obtain ⟨p0, p1⟩ := h
  have q0 : (st.mem (.tab 0) 0).toInt = (σ.slots () 0 ()).n := by
    have := p0; revert this
    show (if 0 < kontoLay.count ∧ 0 < kontoLay.nf then
        (st.mem (.tab 0) (0 * kontoLay.ssize + kontoLay.off 0)).toInt else 0) = _ → _
    rw [if_pos (by decide)]; exact id
  have q1 : (st.mem (.tab 0) 4).toInt = (σ.slots () 1 ()).n := by
    have := p1; revert this
    show (if 1 < kontoLay.count ∧ 0 < kontoLay.nf then
        (st.mem (.tab 0) (1 * kontoLay.ssize + kontoLay.off 0)).toInt else 0) = _ → _
    rw [if_pos (by decide)]; exact id
  rw [e0] at q0; rw [e1] at q1
  exact ⟨e0.trans (congrArg CVal.int q0), e1.trans (congrArg CVal.int q1)⟩

/-- `cCorr_assignSlot` ON THE BLOCK MEMORY, derived from the old theorem
    through the refinement: the Gabbro `assignSlot` (`konto[0] := 100`)
    and the emitted store `k->slots[0].stand = 100;` -- at the emitted
    field type `uint32_t`, at offset 0 of the `Konto` block -- reach
    corresponding states from corresponding states. -/
theorem cCorr_assignSlot_blk (σ : World refD) (ρG : Env refD [.int 0 10])
    (st : CSt) (ρC : CEnv) (hg : Good refTL st) (hcorr : corrMemB σ st) :
    ∃ (σ' : World refD) (st' : CSt),
      execStmt refO 0 keinRuf refWriteStAt σ ρG = .ok σ' ρG ∧
      bExec refTL (cEmitWrite false .w32) st ρC 0 = some (st', ρC) ∧
      corrMemB σ' st' := by
  obtain ⟨σ', m', hG, hC, hW⟩ :=
    cCorr_assignSlot σ ρG (projMem refTL st) ρC false .w32 (by decide) (corrMemB_proj σ st hcorr)
  have hR := bExec_refines refTL refTL_wf (cEmitWrite false .w32) st ρC 0 (by decide) hg
  rw [refTL_geom, hC] at hR
  cases hb : bExec refTL (cEmitWrite false .w32) st ρC 0 with
  | none => rw [hb] at hR; exact hR.elim
  | some p =>
      rw [hb] at hR
      obtain ⟨hp, hρ, hg'⟩ := hR
      obtain ⟨st', ρ'⟩ := p
      simp only at hp hρ hg'
      subst hρ
      refine ⟨σ', st', hG, rfl, ?_⟩
      apply corrMemB_of_proj σ' st' hg'
      rw [hp]; exact hW

/-! ## 12. Correspondence to Gabbro's memory

Gabbro's `World` has per table, index and field a value of the declared
type, and per global one. The emitter lays each non-ghost table out as
one table block of `T_slot` records and each non-ghost global as one
scalar block (`_Atomic` when the global is `atomic`), and encodes values
as C integers. `EmitLay` carries that layout AS DATA, with the facts a
certificate would carry about it; `corrW` is the relation it induces. -/

/-- The emitter's encoding of a Gabbro value as a C integer: the number
    for ranges, `0`/`1` for `bool`, the index or the sentinel `N`
    (`T_NONE`) for `option index into T`, the case number for `reason`.
    The remaining types have no integer cell (CUTS). -/
def encOpt (n : Int) : Option (Zahl 0 (n - 1)) → Int
  | none => n
  | some z => z.n

def encW {F : Type} {sig : F → Nat} : (τ : Ty) → Val F sig τ → Int
  | .int _ _, v => Zahl.n v
  | .bool, b => if (show Bool from b) then 1 else 0
  | .opt n, o => encOpt n o
  | .grund n, i => ((show Fin n from i) : Nat)
  | _, _ => 0

/-- The C cell type holds every encoded value of the Gabbro type: the
    emitter's width choice, checked, not trusted. -/
def tyFits : Ty → CTy → Bool
  | .int lo hi, .int sgn w => decide (cLo sgn w ≤ lo) && decide (hi ≤ cHi sgn w)
  | .bool, .int sgn w => decide (cLo sgn w ≤ 0) && decide (1 ≤ cHi sgn w)
  | .opt n, .int sgn w => decide (cLo sgn w ≤ 0) && decide (0 ≤ n) && decide (n ≤ cHi sgn w)
  | .grund n, .int sgn w => decide (cLo sgn w ≤ 0) && decide ((n : Int) ≤ cHi sgn w)
  | _, _ => false

/-- A fitting cell type holds the encoded value: the store's range check
    cannot fail on an emitted store. -/
theorem encW_fits {F : Type} {sig : F → Nat} (τ : Ty) (c : CTy) (v : Val F sig τ)
    (h : tyFits τ c = true) : valFits c (.int (encW τ v)) = true := by
  cases τ with
  | int lo hi =>
      cases c with
      | ptr => exact absurd h (by simp [tyFits])
      | int sgn w =>
          simp only [tyFits, Bool.and_eq_true, decide_eq_true_eq] at h
          have h1 : lo ≤ Zahl.n v := Zahl.lo_le v
          have h2 : Zahl.n v ≤ hi := Zahl.le_hi v
          show valFits (.int sgn w) (.int (Zahl.n v)) = true
          simp only [valFits, decide_eq_true_eq]
          exact ⟨by omega, by omega⟩
  | bool =>
      cases c with
      | ptr => exact absurd h (by simp [tyFits])
      | int sgn w =>
          simp only [tyFits, Bool.and_eq_true, decide_eq_true_eq] at h
          have hb : ∀ b : Bool, valFits (.int sgn w) (.int (if b then 1 else 0)) = true := by
            intro b
            cases b <;> simp only [valFits, decide_eq_true_eq, if_true] <;>
              exact ⟨by omega, by omega⟩
          exact hb (show Bool from v)
  | opt n =>
      cases c with
      | ptr => exact absurd h (by simp [tyFits])
      | int sgn w =>
          simp only [tyFits, Bool.and_eq_true, decide_eq_true_eq] at h
          have ho : ∀ o : Option (Zahl 0 (n - 1)),
              valFits (.int sgn w) (.int (encOpt n o)) = true := by
            intro o
            cases o with
            | none => simp only [valFits, encOpt]; exact decide_eq_true ⟨by omega, by omega⟩
            | some z =>
                have := z.lo_le
                have := z.le_hi
                simp only [valFits, encOpt]; exact decide_eq_true ⟨by omega, by omega⟩
          exact ho v
  | grund n =>
      cases c with
      | ptr => exact absurd h (by simp [tyFits])
      | int sgn w =>
          simp only [tyFits, Bool.and_eq_true, decide_eq_true_eq] at h
          have hi : ∀ i : Fin n, valFits (.int sgn w) (.int ((i : Nat) : Int)) = true := by
            intro i
            have := i.isLt
            simp only [valFits, decide_eq_true_eq]; exact ⟨by omega, by omega⟩
          exact hi (show Fin n from v)
  | sum cs => exact absurd h (by cases c <;> simp [tyFits])
  | never => exact absurd h (by cases c <;> simp [tyFits])
  | fl lo hi => exact absurd h (by cases c <;> simp [tyFits])
  | fnptr s => exact absurd h (by cases c <;> simp [tyFits])
  | ptr t rw => exact absurd h (by cases c <;> simp [tyFits])

/-- The emitter's layout of a declaration, as data, with the facts a
    certificate carries about it (each checkable by `decide` on a
    concrete program, see `refEL`):
    - tables: block number `tnr t` (injective), record layout `trec t`
      (well-formed, `count` = the declared count), the block's layout
      in `lay` is that record layout, plain;
    - fields: position `fnr t f` in `T_slot` (in range, injective) whose
      C type fits the Gabbro type;
    - globals: block number `gnr g` (injective), one cell of C type
      `gty g` that fits, `_Atomic` exactly when the global is `atomic`. -/
structure EmitLay (D : Deklaration) where
  lay : CLayout
  tnr : D.Tab → Nat
  tnr_inj : ∀ t t', tnr t = tnr t' → t = t'
  trec : D.Tab → RecLay
  lay_tab : ∀ t, lay (.tab (tnr t)) = some { lay := trec t, kind := .plain, base := 0 }
  trec_wf : ∀ t, (trec t).wf = true
  trec_count : ∀ t, ((trec t).count : Int) = D.count t
  fnr : ∀ t, D.Feld t → Nat
  fnr_lt : ∀ t f, fnr t f < (trec t).nf
  fnr_inj : ∀ t f f', fnr t f = fnr t f' → f = f'
  fnr_fits : ∀ t f, tyFits (D.typ t f) ((trec t).fty (fnr t f)) = true
  gnr : D.Glob → Nat
  gnr_inj : ∀ g g', gnr g = gnr g' → g = g'
  gty : D.Glob → CTy
  lay_glob : ∀ g, lay (.glob (gnr g)) =
    some { lay := scalarRec (gty g), kind := if D.atomar g then .atomic else .plain, base := 0 }
  gty_fits : ∀ g, tyFits (D.gtyp g) (gty g) = true
  /-- **THE DEVICE WINDOWS the emitted unit declares** (`device … at mmio`):
      the C block numbers that must be MAPPED for the whole life of the unit.
      A device window is NOT memory -- `corrW`'s two clauses say nothing about
      it -- but it must be there for a register access to be defined at all,
      and *where* that fact belongs is the state relation, next to the
      liveness of every table and global. Default: no device, and then the
      relation is the one of before, character for character. -/
  devs : Nat → Bool := fun _ => false

namespace EmitLay

variable {D : Deklaration}

/-- The emitted address of `t->slots[k].f`. -/
def slotPtr (EL : EmitLay D) (t : D.Tab) (k : Int) (f : D.Feld t) : CPtr :=
  ⟨.tab (EL.tnr t), ((k.toNat * (EL.trec t).ssize + (EL.trec t).off (EL.fnr t f) : Nat) : Int)⟩

/-- The C type of field `f` (`typedef struct { … } T_slot;`). -/
def slotTy (EL : EmitLay D) (t : D.Tab) (f : D.Feld t) : CTy := (EL.trec t).fty (EL.fnr t f)

/-- The address of global `g`. -/
def globPtr (EL : EmitLay D) (g : D.Glob) : CPtr := ⟨.glob (EL.gnr g), 0⟩

theorem slotPtr_toNat (EL : EmitLay D) (t : D.Tab) (k : Int) (f : D.Feld t) :
    (EL.slotPtr t k f).off.toNat = k.toNat * (EL.trec t).ssize + (EL.trec t).off (EL.fnr t f) :=
  Int.toNat_natCast _

/-- An emitted slot address passes the access check. -/
theorem accOk_slot (EL : EmitLay D) (st : CSt) (t : D.Tab) (k : Int) (f : D.Feld t)
    (hl : st.live (.tab (EL.tnr t)) = true) (hk0 : 0 ≤ k) (hk : k < D.count t)
    (md : AccMode) (hmd : BKind.plain.permits md = true) :
    accOk EL.lay st (EL.slotPtr t k f) (EL.slotTy t f) md = true := by
  have hkn : k.toNat < (EL.trec t).count := by have := EL.trec_count t; omega
  have h0 : 0 ≤ (EL.slotPtr t k f).off :=
    show 0 ≤ ((k.toNat * (EL.trec t).ssize + (EL.trec t).off (EL.fnr t f) : Nat) : Int) by omega
  unfold accOk
  rw [show (EL.slotPtr t k f).blk = .tab (EL.tnr t) from rfl, EL.lay_tab t]
  dsimp only
  rw [slotPtr_toNat, RecLay.cell_pos (EL.trec_wf t) (EL.fnr_lt t f) hkn, hl, hmd]
  simp [h0, slotTy]

/-- The one cell of a scalar object is at offset 0. -/
theorem scalarRec_cell0 (τ : CTy) : (scalarRec τ).cell 0 = some τ := by
  unfold RecLay.cell
  rw [if_pos (show 0 < (scalarRec τ).size by
    show 0 < 1 * τ.size
    have := τ.size_pos; omega)]
  rw [Nat.zero_mod]
  rfl

/-- The address of a global passes the check in its kind's mode. -/
theorem accOk_glob (EL : EmitLay D) (st : CSt) (g : D.Glob)
    (hl : st.live (.glob (EL.gnr g)) = true) (md : AccMode)
    (hmd : (if D.atomar g then BKind.atomic else BKind.plain).permits md = true) :
    accOk EL.lay st (EL.globPtr g) (EL.gty g) md = true := by
  unfold accOk
  rw [show (EL.globPtr g).blk = .glob (EL.gnr g) from rfl, EL.lay_glob g]
  dsimp only
  rw [show (EL.globPtr g).off.toNat = 0 from rfl, scalarRec_cell0, hl, hmd]
  simp [globPtr]

end EmitLay

/-- THE RELATION between Gabbro's memory and the C block memory under
    the emitter's layout: every non-ghost table block is alive and holds,
    at the emitted address of each slot field, the encoded value of that
    slot field; every non-ghost global block is alive and holds the
    encoded global. Gabbro's trace (`spur`) and C's observation trace are
    not related here (CUTS). -/
def corrW {D : Deklaration} (EL : EmitLay D) (σ : World D) (st : CSt) : Prop :=
  (∀ t, D.geist t = false → st.live (.tab (EL.tnr t)) = true ∧
    ∀ (k : Int) (f : D.Feld t), 0 ≤ k → k < D.count t →
      st.mem (.tab (EL.tnr t)) (k.toNat * (EL.trec t).ssize + (EL.trec t).off (EL.fnr t f)) =
        .int (encW (D.typ t f) (σ.slots t k f))) ∧
  (∀ g, D.ggeist g = false → st.live (.glob (EL.gnr g)) = true ∧
    st.mem (.glob (EL.gnr g)) 0 = .int (encW (D.gtyp g) (σ.globs g))) ∧
  (∀ d, EL.devs d = true → st.live (.dev d) = true)

/-- Gabbro reads only extend the trace: the relation is unchanged. -/
theorem corrW_lese {D : Deklaration} (EL : EmitLay D) (σ : World D) (st : CSt)
    (Λ : List (Res D)) (orte : List (D.Tab ⊕ D.Glob)) :
    corrW EL (σ.lese Λ orte) st ↔ corrW EL σ st := Iff.rfl

/-- LOAD CORRESPONDENCE: the emitted load `t->slots[k].f` of a related
    state reads the encoded Gabbro slot. -/
theorem corr_leseSlot {D : Deklaration} (EL : EmitLay D) (σ : World D) (st : CSt)
    (h : corrW EL σ st) (t : D.Tab) (hgt : D.geist t = false) (k : Int) (f : D.Feld t)
    (hk0 : 0 ≤ k) (hk : k < D.count t) :
    bLoad EL.lay st (EL.slotPtr t k f) (EL.slotTy t f) =
      some (.int (encW (D.typ t f) (σ.slots t k f))) := by
  obtain ⟨hl, hc⟩ := h.1 t hgt
  have hv := hc k f hk0 hk
  have ha := EL.accOk_slot st t k f hl hk0 hk .rd rfl
  have hne : st.mem (EL.slotPtr t k f).blk (EL.slotPtr t k f).off.toNat ≠ .undef := by
    rw [EmitLay.slotPtr_toNat]; show st.mem (.tab (EL.tnr t)) _ ≠ _; rw [hv]; simp
  rw [bLoad_progress _ _ _ _ ha hne, EmitLay.slotPtr_toNat]
  exact congrArg some hv

/-- STORE CORRESPONDENCE (lane 128's single theorem, generalised to any
    table and field with the layout as data): a Gabbro `schreibSlot`
    and the emitted store `t->slots[k].f = v` preserve the relation. The
    store cannot get stuck (range from `tyFits`, cell from the layout),
    and it touches no observation. -/
theorem corr_schreibSlot {D : Deklaration} (EL : EmitLay D) (σ : World D) (st : CSt)
    (h : corrW EL σ st) (t : D.Tab) (hgt : D.geist t = false) (Λ : List (Res D)) (k : Int)
    (f : D.Feld t) (v : Wert D (D.typ t f)) (hk0 : 0 ≤ k) (hk : k < D.count t) :
    ∃ st', bStore EL.lay st (EL.slotPtr t k f) (EL.slotTy t f) (.int (encW (D.typ t f) v)) =
        some st' ∧ corrW EL (σ.schreibSlot t Λ k f v) st' ∧ st'.obs = st.obs := by
  obtain ⟨hl, -⟩ := h.1 t hgt
  have ha := EL.accOk_slot st t k f hl hk0 hk .wr rfl
  have hfit := encW_fits (D.typ t f) (EL.slotTy t f) v (EL.fnr_fits t f)
  refine ⟨_, bStore_progress _ _ _ _ _ ha hfit, ?_, rfl⟩
  rw [EmitLay.slotPtr_toNat]
  refine ⟨?_, ?_, h.2.2⟩
  · intro t' hgt'
    obtain ⟨hl', hc'⟩ := h.1 t' hgt'
    refine ⟨hl', ?_⟩
    intro k' f' hk0' hk'
    show memUpd st.mem (.tab (EL.tnr t)) (k.toNat * (EL.trec t).ssize + (EL.trec t).off (EL.fnr t f)) (.int (encW (D.typ t f) v)) (.tab (EL.tnr t')) (k'.toNat * (EL.trec t').ssize + (EL.trec t').off (EL.fnr t' f')) =
      .int (encW (D.typ t' f') ((σ.storeSlot t k f v).slots t' k' f'))
    by_cases ht : t' = t
    · subst ht
      by_cases hkf : k' = k ∧ f' = f
      · obtain ⟨e1, e2⟩ := hkf
        subst e1; subst e2
        rw [memUpd_same]
        simp [World.storeSlot]
      · rw [memUpd_other]
        · rw [hc' k' f' hk0' hk']
          by_cases hkk : k' = k
          · have hff : f' ≠ f := fun e => hkf ⟨hkk, e⟩
            subst hkk
            simp [World.storeSlot, hff]
          · simp [World.storeSlot, hkk]
        · intro hc
          obtain ⟨-, ho⟩ := hc
          obtain ⟨h1, h2⟩ := RecLay.pos_inj (EL.trec_wf t') (EL.fnr_lt t' f') (EL.fnr_lt t' f) ho
          exact hkf ⟨by omega, EL.fnr_inj t' f' f h2⟩
    · rw [memUpd_other]
      · rw [hc' k' f' hk0' hk']
        simp [World.storeSlot, ht]
      · intro hc
        obtain ⟨hb, -⟩ := hc
        injection hb with hb'
        exact ht (EL.tnr_inj _ _ hb')
  · intro g hgg
    obtain ⟨hl', hc'⟩ := h.2.1 g hgg
    refine ⟨hl', ?_⟩
    show memUpd st.mem (.tab (EL.tnr t)) (k.toNat * (EL.trec t).ssize + (EL.trec t).off (EL.fnr t f)) (.int (encW (D.typ t f) v)) (.glob (EL.gnr g)) 0 = _
    exact (memUpd_other _ _ _ _ _ _ (by intro hc; cases hc.1)).trans hc'

/-- Frame of a global store: table cells are untouched. -/
theorem corrW_tabs_of_glob {D : Deklaration} (EL : EmitLay D) (σ : World D) (st : CSt)
    (h : corrW EL σ st) (g : D.Glob) (o : Nat) (c : CVal) (σ' : World D)
    (hs : σ'.slots = σ.slots) (lv : CBlk → Bool) (hlv : ∀ t, lv (.tab t) = st.live (.tab t)) :
    ∀ t, D.geist t = false → lv (.tab (EL.tnr t)) = true ∧
      ∀ (k : Int) (f : D.Feld t), 0 ≤ k → k < D.count t →
        memUpd st.mem (.glob (EL.gnr g)) o c (.tab (EL.tnr t))
          (k.toNat * (EL.trec t).ssize + (EL.trec t).off (EL.fnr t f)) =
          .int (encW (D.typ t f) (σ'.slots t k f)) := by
  intro t hgt
  obtain ⟨hl, hc⟩ := h.1 t hgt
  refine ⟨(hlv _).trans hl, ?_⟩
  intro k f hk0 hk
  rw [hs]
  exact (memUpd_other _ _ _ _ _ _ (by intro hc; cases hc.1)).trans (hc k f hk0 hk)

/-- GLOBAL STORE CORRESPONDENCE, plain global: `schreibGlob` against the
    emitted `g = v;`. -/
theorem corr_schreibGlob {D : Deklaration} (EL : EmitLay D) (σ : World D) (st : CSt)
    (h : corrW EL σ st) (g : D.Glob) (hgg : D.ggeist g = false) (hat : D.atomar g = false)
    (Λ : List (Res D)) (v : Wert D (D.gtyp g)) :
    ∃ st', bStore EL.lay st (EL.globPtr g) (EL.gty g) (.int (encW (D.gtyp g) v)) = some st' ∧
      corrW EL (σ.schreibGlob g Λ v) st' ∧ st'.obs = st.obs := by
  obtain ⟨hl, -⟩ := h.2.1 g hgg
  have ha := EL.accOk_glob st g hl .wr (by rw [hat]; rfl)
  have hfit := encW_fits (D.gtyp g) (EL.gty g) v (EL.gty_fits g)
  refine ⟨_, bStore_progress _ _ _ _ _ ha hfit, ⟨?_, ?_, h.2.2⟩, rfl⟩
  · exact corrW_tabs_of_glob EL σ st h g 0 (.int (encW (D.gtyp g) v)) (σ.schreibGlob g Λ v) rfl _ (fun _ => rfl)
  · intro g' hgg'
    obtain ⟨hl', hc'⟩ := h.2.1 g' hgg'
    refine ⟨hl', ?_⟩
    show memUpd st.mem (.glob (EL.gnr g)) 0 (.int (encW (D.gtyp g) v)) (.glob (EL.gnr g')) 0 =
      .int (encW (D.gtyp g') ((σ.storeGlob g v).globs g'))
    by_cases he : g' = g
    · subst he
      rw [memUpd_same]
      simp [World.storeGlob]
    · rw [memUpd_other _ _ _ _ _ _ (by
        intro hc; obtain ⟨hb, -⟩ := hc; injection hb with hb'; exact he (EL.gnr_inj _ _ hb'))]
      rw [hc']
      simp [World.storeGlob, he]

/-- GLOBAL STORE CORRESPONDENCE, `atomic` global: `schreibGlob` against
    `atomic_store_explicit(&g, v, o)` -- the same memory effect, plus
    exactly one observation carrying the order. This is the handle for
    relating machine G's ordered accesses (A10) later. -/
theorem corr_schreibGlob_atomar {D : Deklaration} (EL : EmitLay D) (σ : World D) (st : CSt)
    (h : corrW EL σ st) (g : D.Glob) (hgg : D.ggeist g = false) (hat : D.atomar g = true)
    (Λ : List (Res D)) (v : Wert D (D.gtyp g)) (o : COrd) (ho : o.storeOk = true) :
    ∃ st', aStore EL.lay st (EL.globPtr g) (EL.gty g) o (encW (D.gtyp g) v) = some st' ∧
      corrW EL (σ.schreibGlob g Λ v) st' ∧
      st'.obs = .awr (EL.globPtr g) o (encW (D.gtyp g) v) :: st.obs := by
  obtain ⟨hl, -⟩ := h.2.1 g hgg
  have ha := EL.accOk_glob st g hl .atom (by rw [hat]; rfl)
  have hfit := encW_fits (D.gtyp g) (EL.gty g) v (EL.gty_fits g)
  have hs : aStore EL.lay st (EL.globPtr g) (EL.gty g) o (encW (D.gtyp g) v) =
      some { st with mem := memUpd st.mem (.glob (EL.gnr g)) 0 (.int (encW (D.gtyp g) v)),
                     obs := .awr (EL.globPtr g) o (encW (D.gtyp g) v) :: st.obs } := by
    unfold aStore
    rw [ha, ho, hfit]
    rfl
  refine ⟨_, hs, ⟨?_, ?_, h.2.2⟩, rfl⟩
  · exact corrW_tabs_of_glob EL σ st h g 0 (.int (encW (D.gtyp g) v)) (σ.schreibGlob g Λ v) rfl _ (fun _ => rfl)
  · intro g' hgg'
    obtain ⟨hl', hc'⟩ := h.2.1 g' hgg'
    refine ⟨hl', ?_⟩
    show memUpd st.mem (.glob (EL.gnr g)) 0 (.int (encW (D.gtyp g) v)) (.glob (EL.gnr g')) 0 =
      .int (encW (D.gtyp g') ((σ.storeGlob g v).globs g'))
    by_cases he : g' = g
    · subst he
      rw [memUpd_same]
      simp [World.storeGlob]
    · rw [memUpd_other _ _ _ _ _ _ (by
        intro hc; obtain ⟨hb, -⟩ := hc; injection hb with hb'; exact he (EL.gnr_inj _ _ hb'))]
      rw [hc']
      simp [World.storeGlob, he]

/-- GLOBAL LOAD CORRESPONDENCE, `atomic` global:
    `atomic_load_explicit(&g, o)` reads the encoded global and appends
    its observation. -/
theorem corr_leseGlob_atomar {D : Deklaration} (EL : EmitLay D) (σ : World D) (st : CSt)
    (h : corrW EL σ st) (g : D.Glob) (hgg : D.ggeist g = false) (hat : D.atomar g = true)
    (o : COrd) (ho : o.loadOk = true) :
    aLoad EL.lay st (EL.globPtr g) (EL.gty g) o =
      some (encW (D.gtyp g) (σ.globs g),
        { st with obs := .ard (EL.globPtr g) o (encW (D.gtyp g) (σ.globs g)) :: st.obs }) := by
  obtain ⟨hl, hc⟩ := h.2.1 g hgg
  have ha := EL.accOk_glob st g hl .atom (by rw [hat]; rfl)
  unfold aLoad
  rw [ha, ho]
  show (match st.mem (.glob (EL.gnr g)) 0 with
    | .int v => some (v, { st with obs := .ard (EL.globPtr g) o v :: st.obs })
    | _ => none) = _
  rw [hc]

/-- GLOBAL LOAD CORRESPONDENCE, plain global: the emitted read `g`. -/
theorem corr_leseGlob {D : Deklaration} (EL : EmitLay D) (σ : World D) (st : CSt)
    (h : corrW EL σ st) (g : D.Glob) (hgg : D.ggeist g = false) (hat : D.atomar g = false) :
    bLoad EL.lay st (EL.globPtr g) (EL.gty g) = some (.int (encW (D.gtyp g) (σ.globs g))) := by
  obtain ⟨hl, hc⟩ := h.2.1 g hgg
  have ha := EL.accOk_glob st g hl .rd (by rw [hat]; rfl)
  have hne : st.mem (EL.globPtr g).blk (EL.globPtr g).off.toNat ≠ .undef := by
    show st.mem (.glob (EL.gnr g)) 0 ≠ _; rw [hc]; simp
  rw [bLoad_progress _ _ _ _ ha hne]
  exact congrArg some hc

/-! ## 13. Witness on `refD`: the emitted layout of `Konto` -/

/-- The C objects of `beispiele/104-referenz.gab`: one table block, the
    object `Konto *restrict k` points to, with the emitted layout. -/
def refLay : CLayout := fun b =>
  match b with
  | .tab 0 => some { lay := kontoLay, kind := .plain, base := 0 }
  | _ => none

/-- The emitter's layout of `refD`, every certificate fact by `decide`
    or `rfl`: `Konto` is table block 0, `stand` is field 0 of
    `Konto_slot` at `uint32_t` (which holds `0 .. 100`), no globals. -/
def refEL : EmitLay refD where
  lay := refLay
  tnr := fun _ => 0
  tnr_inj := fun t t' _ => by cases t; cases t'; rfl
  trec := fun _ => kontoLay
  lay_tab := fun _ => rfl
  trec_wf := fun _ => by decide
  trec_count := fun _ => rfl
  fnr := fun _ _ => 0
  fnr_lt := fun _ _ => by decide
  fnr_inj := fun _ f f' _ => by cases f; cases f'; rfl
  fnr_fits := fun _ _ => rfl
  gnr := fun g => nomatch g
  gnr_inj := fun g => nomatch g
  gty := fun g => nomatch g
  lay_glob := fun g => nomatch g
  gty_fits := fun g => nomatch g

/-- A C state before the call: every cell `0`, every block alive, no
    observation (static storage is zero-initialised, C11 6.7.9p10). -/
def refSt0 : CSt := { mem := fun _ _ => .int 0, live := fun _ => true, obs := [] }

/-- The pre-write world of the reached run and the zero C state are
    related. -/
theorem refSt0_corr : corrW refEL (refM1B.weltVon 1) refSt0 := by
  constructor
  · intro t _
    refine ⟨rfl, ?_⟩
    intro k f hk0 hk
    have hk2 : k < 2 := hk
    cases t
    cases f
    have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with e | e <;> subst e <;> rfl
  · constructor
    · intro g
      exact nomatch g
    · intro _ _
      rfl

/-- The emitted addresses: `k->slots[0].stand` is offset 0 of the block,
    `k->slots[1].stand` offset 4. -/
theorem refEL_adressen :
    refEL.slotPtr () 0 () = ⟨.tab 0, 0⟩ ∧ refEL.slotPtr () 1 () = ⟨.tab 0, 4⟩ ∧
      refEL.slotTy () () = .int false .w32 := by
  decide

/-- WITNESS (rule 13) for the correspondence on the reference fixture.
    On the reached run's pre-write world (`refM1B`, thread 1), the Gabbro
    store `konto[0] := 100` (`refWriteStAt`) and the emitted store
    `k->slots[i].stand = 100;` at the emitted address (block of `Konto`,
    offset 0, `uint32_t`) reach related states; the emitted load
    `return k->slots[i].stand;` then reads 100; the memory moved on both
    sides (0 before, 100 after); and, as in lane 128, `einzahlen` writes
    `konto` and the reached machine step fires exactly this write. -/
theorem refKonto_zeuge :
    ∃ (σ' : World refD) (st1 : CSt),
      execStmt refO 0 keinRuf refWriteStAt (refM1B.weltVon 1) refRho7 = .ok σ' refRho7 ∧
      bStore refEL.lay refSt0 (refEL.slotPtr () 0 ()) (.int false .w32) (.int 100) = some st1 ∧
      corrW refEL σ' st1 ∧
      bLoad refEL.lay st1 (refEL.slotPtr () 0 ()) (.int false .w32) = some (.int 100) ∧
      ((refM1B.weltVon 1).slots () 0 ()).n = 0 ∧ (σ'.slots () 0 ()).n = 100 ∧
      refSt0.mem (.tab 0) 0 = .int 0 ∧ st1.mem (.tab 0) 0 = .int 100 ∧
      st1.obs = [] ∧
      (vertragVon refD refEin).schreibt () = true ∧
      RufSchrittD refP refO 0 refM1B 1 refM2B := by
  have hG : execStmt refO 0 keinRuf refWriteStAt (refM1B.weltVon 1) refRho7 =
      .ok (((refM1B.weltVon 1).lese [Res.held (D := refD) ()]
        (refIdxEin.orte ++ refHundert.orte)).schreibSlot ()
        [Res.held (D := refD) ()] 0 () refV100) refRho7 := rfl
  have h0 : corrW refEL ((refM1B.weltVon 1).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)) refSt0 :=
    (corrW_lese refEL _ refSt0 _ _).mpr refSt0_corr
  obtain ⟨st1, hs, hc, ho⟩ := corr_schreibSlot refEL _ refSt0 h0 () rfl
    [Res.held (D := refD) ()] 0 () refV100 (by decide) (by decide)
  have hl := corr_leseSlot refEL _ st1 hc () rfl 0 () (by decide) (by decide)
  have hm := (hc.1 () rfl).2 0 () (by decide) (by decide)
  refine ⟨_, st1, hG, hs, hc, ?_, rfl, rfl, rfl, ?_, ho, refEin_schreibt (), refSchrittB⟩
  · exact hl
  · exact hm

/-! ## 14. Two hard forms, expressed (design check, not yet per-form semantics)

The point of the new memory is that the ~24 hard forms can be written
down at all. Two emitted shapes, end to end, on concrete layouts:

  (a) the device register access of `beispiele/02-geraet.gab` and its
      kin: `Geraet d = (Geraet){ .basis = (volatile uint8_t *)(uintptr_t)
      BASE };` then `(*(volatile uint32_t *)(d->basis + 8)) = v;` --
      int-to-pointer at the declared base, a pointer stored in and loaded
      from a struct cell, byte pointer arithmetic, a volatile store that is
      an observation;
  (b) the out-parameter: `if (!f(&e)) …` where `f` writes `*p = v;` --
      address-of a stack local, a store through the pointer, the caller's
      read, and the dangling pointer after the frame is left. -/

/-- The window of a device with four `uint32_t` registers at 0, 4, 8, 12. -/
def geraetFenster : RecLay :=
  natLay 1 [.int false .w32, .int false .w32, .int false .w32, .int false .w32]

/-- `typedef struct { volatile uint8_t *basis; } Geraet;` as a stack
    local of frame 0 (local 0), and the device window at `0xFEE00000`. -/
def geraetLay : CLayout := fun b =>
  match b with
  | .stk 0 0 => some { lay := scalarRec .ptr, kind := .plain, base := 0 }
  | .dev 0 => some { lay := geraetFenster, kind := .mmio, base := 4276092928 }
  | _ => none

/-- The state after `Geraet d` came alive (frame 0, local 0). -/
def geraetSt0 : CSt :=
  enterFrame { mem := fun _ _ => .int 0, live := fun _ => true, obs := [] } 0 [0]

/-- (a) The device access, expressed. The handle is the window's start;
    storing it into `d.basis` and loading it back gives the same pointer
    (provenance survives memory); `+ 8` stays in the window; the volatile
    store is exactly one observation and changes no memory; `+ 17` leaves
    the window (stuck) and a 32-bit access at offset 2 hits no register
    (stuck). -/
theorem geraet_zeuge :
    devHandle geraetLay 0 4276092928 = some ⟨.dev 0, 0⟩ ∧
    ∃ st1 st2,
      bStore geraetLay geraetSt0 (addrOf 0 0) .ptr (.ptr ⟨.dev 0, 0⟩) = some st1 ∧
      bLoad geraetLay st1 (addrOf 0 0) .ptr = some (.ptr ⟨.dev 0, 0⟩) ∧
      ptrAdd geraetLay ⟨.dev 0, 0⟩ 8 1 = some ⟨.dev 0, 8⟩ ∧
      vStore geraetLay st1 ⟨.dev 0, 8⟩ (.int false .w32) 5 = some st2 ∧
      st2.obs = [.vwr ⟨.dev 0, 8⟩ (.int false .w32) 5] ∧ st2.mem = st1.mem ∧
      ptrAdd geraetLay ⟨.dev 0, 0⟩ 17 1 = none ∧
      vStore geraetLay st1 ⟨.dev 0, 2⟩ (.int false .w32) 5 = none := by
  refine ⟨by decide, _, _, rfl, ?_, by decide, rfl, rfl, rfl, by decide, ?_⟩
  · unfold bLoad
    rw [if_pos (by decide)]
    rfl
  · unfold vStore
    rw [if_neg (by decide)]

/-- The frame of a callee that takes `&e`: local 0 of frame 1, a
    `uint32_t`. -/
def outLay : CLayout := fun b =>
  match b with
  | .stk 1 0 => some { lay := scalarRec (.int false .w32), kind := .plain, base := 0 }
  | _ => none

/-- (b) The out-parameter, expressed: before the store the local is
    uninitialised (a read is stuck), `*p = 7` through `p = &e` makes the
    caller's `e` read 7, and after the frame is left `p` dangles (every
    access through it is stuck). -/
theorem ausgabe_zeuge :
    let st0 := enterFrame { mem := fun _ _ => .int 0, live := fun _ => false, obs := [] } 1 [0]
    bLoad outLay st0 (addrOf 1 0) (.int false .w32) = none ∧
    ∃ st1, bStore outLay st0 (addrOf 1 0) (.int false .w32) (.int 7) = some st1 ∧
      bLoad outLay st1 (addrOf 1 0) (.int false .w32) = some (.int 7) ∧
      bLoad outLay (leaveFrame st1 1) (addrOf 1 0) (.int false .w32) = none := by
  intro st0
  refine ⟨enter_uninit _ _ 1 0 [0] (by simp) 0 _, _, rfl, ?_, ?_⟩
  · unfold bLoad
    rw [if_pos (by decide)]
    rfl
  · apply loadUB_stuck
    exact .acc (.dead _ rfl (by simp [leaveFrame, addrOf]))

/-
CUTS: what this file does not do, by name.
- UNIONS are not expressed. The emitter writes tagged unions
  (`struct { T_marke marke; union { … } last; }`, 29 definitions in the
  measured corpus); `RecLay.disjB` forbids overlapping fields. The
  designed extension: a list of admissible types per offset, and the
  effective type recorded at each store, so reading another member than
  the last written is stuck (the never-list's "union reinterpretation
  without a tag").
- AGGREGATE VALUES are not values: `CEnv` stays lane 128's `Nat → Int`.
  A struct local whose address is taken, or an array local, is a stack
  block; by-value struct locals, compound literals `(T){ … }` and struct
  returns need aggregate values in the statement semantics (plan step 2).
- NO BYTES. Cells are typed; a store to one cell cannot change another.
  That is sound for the emitter as measured (the only pointer casts are
  `(volatile uintN_t *)` on device windows and one `(T *)(uintptr_t)0`),
  and it would be wrong for an emitter that reads a `uint32_t` through a
  `uint8_t` buffer or copies with `memcpy`: those need CompCert-style
  byte fragments.
- THE LAYOUT ABI is stated, not proved: `natLay` is the x86-64 SysV rule
  (natural alignment, tail padding); that the C compiler lays out the
  emitted `typedef`s so is the plan's named assumption "the C compiler".
  `natLay` is not proved well-formed in general; `wf` is decided per
  program (`refTL_wf`, `refEL`).
- FRAMES are numbered by the caller of `enterFrame`; nothing enforces
  fresh numbers, so re-entering a frame number revives old pointers into
  it (CompCert allocates fresh block ids). The statement semantics of
  step 2 must thread a frame counter.
- CONCURRENCY: the observation trace is one thread's. No interleaving,
  no weak-memory behaviour, no relation to machine G or A10 yet; `aCas`
  is the strong compare-exchange (a spurious weak failure is not
  modelled). The device oracle answers `w` bits; Gabbro's register types
  and `rzusage` are not related to it.
- THE CORRESPONDENCE relates memory only: Gabbro's `spur` and C's `obs`
  are not related; ghost carriers are excluded; field and global types
  must be `int`/`bool`/`opt`/`grund` (`tyFits` is false for `sum`, `fl`,
  `fnptr`, `ptr`, `never`), so a declaration with such a field has no
  `EmitLay` yet. That a `T *restrict k` parameter points to table `t`'s
  block is parameter passing, step 2.
- THE REFINEMENT needs `okB`: every store names its field's declared C
  type. Lane 128's width-generic `cCorr_assignSlot` is instantiated at the
  emitted width `uint32_t` in `cCorr_assignSlot_blk`.
- NOT MODELLED because not emitted (census): pointer comparison and
  subtraction, `void *`, `malloc`, pointer-to-pointer casts on ordinary
  memory. NOT MODELLED because they are proof exports, not semantics:
  `restrict`, `__builtin_unreachable`, `asm` bodies (the port I/O and
  syscall stubs appear only as observations). `goto` needs continuations
  in the statement semantics; it does not touch memory.
- NULL has no value: `(T *)(uintptr_t)0` has no provenance and every
  access through it is stuck. `beispiele/38-unveraenderlicher-zeiger.gab`
  emits exactly that (`static Platz * const tz = (Platz *)(uintptr_t)0;`
  then `tz->slots[i].a = 5;`), which is C UB (6.5.3.2p4) on every call:
  a finding about the emitter, reported, not fixed here.
-/

#print axioms accOk_iff
#print axioms loadUB_stuck
#print axioms storeUB_stuck
#print axioms ptrUB_stuck
#print axioms ptrAdd_blk
#print axioms ptrAdd_add
#print axioms leave_dangling
#print axioms enter_uninit
#print axioms ordUB_load_stuck
#print axioms ordUB_store_stuck
#print axioms ordUB_cas_stuck
#print axioms vStore_obs
#print axioms vLoad_obs
#print axioms aStore_mem
#print axioms devHandle_spec
#print axioms RecLay.pos_inj
#print axioms RecLay.cell_pos
#print axioms bEval_refines
#print axioms bExec_refines
#print axioms cCorr_assignSlot_blk
#print axioms encW_fits
#print axioms corr_leseSlot
#print axioms corr_schreibSlot
#print axioms corr_schreibGlob
#print axioms corr_schreibGlob_atomar
#print axioms corr_leseGlob
#print axioms corr_leseGlob_atomar
#print axioms refKonto_zeuge
#print axioms geraet_zeuge
#print axioms ausgabe_zeuge
