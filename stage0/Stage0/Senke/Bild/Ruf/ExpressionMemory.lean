module

public import Stage0.Senke.Ausdruck.Satz
public import Stage0.Senke.Bild.Mehr.Ort.MemoryReference
public import Stage0.Senke.Bild.Rand

@[expose] public section

namespace Gabbro.Stage0

open Gabbro.Grammatik Gabbro.Stage0.Senke.BildMehr Gabbro.Stage0.Senke.BildLauf Runner Runner.IR

/-- A restricted expression memory retains the exact code and lexical
    environment. The read region covers the code bytes and its frame. -/
theorem expression_pre_mask [Kern] {D : Deklaration} {L : Senke.Lay D} {Γ : Ctx}
    {memory : Mem} {fp pc : W} {K d reserved : Nat} {env : Env D Γ} {code : List II}
    {reads : W → Prop} (frameReads : ∀ byte, inSlots fp 0 K byte → reads byte)
    (codeReads : ∀ byte, pc.toNat ≤ byte.toNat → byte.toNat < pc.toNat + 16 * code.length → reads byte)
    (destination : d ≤ K) (pre : Senke.PreS L memory pc fp K d code env reserved) :
    Senke.PreS L (maskMemory reads (inSlots fp 0 K) memory) pc fp K d code env reserved := by
  let restricted := maskMemory reads (inSlots fp 0 K) memory
  have agree : MaskedAgreement reads (inSlots fp 0 K) restricted memory :=
    (maskMemory_agreement reads (inSlots fp 0 K) memory frameReads).1
  have withinFrame (index : Nat) (present : index < K) (offset : Nat) (inWord : offset < 8) :
      inSlots fp 0 K (slot fp (BitVec.ofNat 64 index) + BitVec.ofNat 64 offset) :=
    frame_slot_byte pre.frame present inWord
  obtain ⟨frames, code⟩ := maskMemory_code_frame pre.code pre.frame pre.far.1 frameReads codeReads
  refine ⟨pre.ctx, pre.small, frames, code, pre.far, ?_, trivial, Senke.wstab_true _ _⟩
  · intro ty variableAt
    have stored := pre.env ty variableAt
    refine ⟨stored.1, fun word present => ?_⟩
    have width : word < Senke.valueWords ty := by simpa only [Senke.encodeWords_length] using present
    have location := Senke.variableOffset_bound variableAt
    have slotFits : Senke.vslot variableAt reserved + word < K := by
      have frame := pre.ctx
      unfold Senke.vslot Senke.frei at *
      omega
    have sameWord (j : Nat) (inside : j < 8) :=
      agree.1 _ (frameReads _ (withinFrame _ slotFits j inside))
    change restricted.rd64 (slot fp (BitVec.ofNat 64 (Senke.vslot variableAt reserved + word))) = _
    simp only [Mem.rd64,
      Mem.all_congr (fun j inside => (sameWord j inside).2),
      Mem.le_congr (fun j inside => (sameWord j inside).1)]
    exact stored.2 word present

private theorem expression_mask_value [Kern] {D : Deklaration} {L : Senke.Lay D}
    {memory : Mem} {reads writes : W → Prop} {address : Nat} {ty : Ty} {value : Wert D ty}
    (writeReads : ∀ byte, writes byte → reads byte)
    (bound : address + 8 * Senke.valueWords ty < 2 ^ 64)
    (covered : ∀ byte : W, address ≤ byte.toNat → byte.toNat < address + 8 * Senke.valueWords ty → reads byte)
    (typed : Senke.ValueAt L memory (BitVec.ofNat 64 address) 0 ty value) :
    Senke.ValueAt L (maskMemory reads writes memory) (BitVec.ofNat 64 address) 0 ty value := by
  have agree := (maskMemory_agreement reads writes memory writeReads).1
  exact Senke.ValueAt.congr_read_bytes bound (fun byte first last => agree.1 byte (covered byte first last)) typed

/-- A physical read region containing the authorized carriers
    preserves their complete value representations in the proof memory. -/
theorem expression_world_mask [Kern] {D : Deklaration} {L : Senke.Lay D} {memory : Mem}
    {reads writes : W → Prop} {world : World D} {resources : List (Res D)}
    (writeReads : ∀ byte, writes byte → reads byte) (layout : Senke.LayIn L)
    (authorized : ∀ cell : Senke.Zelle D, cell.da L →
      Sum.elim (fun table => darf D table resources) (fun global => gdarf D global resources) cell.carrier →
      ∀ byte : W, cell.adr L ≤ byte.toNat → byte.toNat < cell.adr L + cell.bytes → reads byte)
    (values : Senke.ReadWorldAt memory L world resources) :
    Senke.ReadWorldAt (maskMemory reads writes memory) L world resources := by
  refine ⟨?_, ?_⟩
  · intro table access field index valid
    have inside := (layout.1 table field index valid).2.trans_lt layout.2.2
    exact expression_mask_value writeReads (inside.trans (by decide))
      (authorized (.elem table field index) valid access) (values.table table access field index valid)
  · intro global access
    have inside := (layout.2.1 global).2.trans_lt layout.2.2
    exact expression_mask_value writeReads (inside.trans (by decide))
      (authorized (.glob global) trivial access) (values.global global access)

/-- Every successful production expression lowering has an exact
    host-free reference. Any actual memory prefix reaches the same
    typed result when complete and cannot ask the host while incomplete. -/
theorem lowE_frameMemory [kernel : Kern] {D : Deklaration} {L : Senke.Lay D} {Λ : List (Res D)}
    {Γ : Ctx} {τ : Ty} {memory : Mem} {pc fp : W} {K d reserved top : Nat}
    {code : List II} {world initial : World D} {env : Env D Γ} {currentOld : Bool}
    (reads : W → Prop) (frameReads : ∀ byte, inSlots fp 0 K byte → reads byte)
    (codeReads : ∀ byte, pc.toNat ≤ byte.toNat → byte.toNat < pc.toNat + 16 * code.length → reads byte)
    (expression : Expr D Γ Λ τ)
    (lowered : Senke.lowE (reserved := reserved) (currentOld := currentOld) L expression d = some (code, top))
    (fits : top ≤ K) (resultFits : d + Senke.valueWords τ ≤ K)
    (pre : Senke.PreS L memory pc fp K d code env reserved)
    (valueMemory : Senke.ReadWorldAt memory L world Λ)
    (worldReads : ∀ cell : Senke.Zelle D, cell.da L →
      Sum.elim (fun table => darf D table Λ) (fun global => gdarf D global Λ) cell.carrier →
      ∀ byte : W, cell.adr L ≤ byte.toNat → byte.toNat < cell.adr L + cell.bytes → reads byte)
    (layout : Senke.LayIn L)
    (separated : fp.toNat + 8 * K ≤ L.lo) (entry : currentOld = true → initial = world) :
    let start : T := ⟨pc, fp⟩
    let target : T := ⟨pc + BitVec.ofNat 64 (16 * code.length), fp⟩
    let restricted := maskMemory reads (inSlots fp 0 K) memory
    ∃ count finish, @IRReference kernel.withoutSyscalls count start restricted target finish ∧
      ∀ {taken : Nat} {pointer : T} {actual : Mem},
        StarM taken start memory pointer actual → taken ≤ count →
        (taken = count → pointer = target ∧ Agree fp d K memory actual ∧
          Senke.ValueAt L actual fp d τ (eval initial expression world env)) ∧
        (taken < count → ∀ {control : Res T} {atControl : Mem},
          RunP (step pointer) actual control atControl → HostFreeControl reads (inSlots fp 0 K) control) := by
  intro start target restricted
  letI : Kern := kernel.withoutSyscalls
  have masked := expression_pre_mask frameReads codeReads (by omega : d ≤ K) pre
  have scope : Senke.Pre L restricted pc fp K d code env (fun m => Senke.ReadWorldAt m L world Λ) reserved :=
    ⟨masked.ctx, masked.small, masked.frame, masked.code, masked.far, masked.env,
      expression_world_mask frameReads layout worldReads valueMemory, Senke.readWorldAt_stab layout separated⟩
  obtain ⟨finish, executed, preservedWords, value⟩ :=
    Senke.lowE_ok_scoped (same := entry) initial world (fun _ h => h) layout
      expression d code top lowered fits restricted pc env scope
  obtain ⟨count, reference⟩ := IRReference.of_star executed
  obtain ⟨agree, readable, writable⟩ :=
    maskMemory_agreement reads (inSlots fp 0 K) memory frameReads
  refine ⟨count, finish, reference, ?_⟩
  intro taken pointer actual ran within
  obtain ⟨completed, remaining⟩ := IRReference.scoped_prefix (kernel := kernel) reference agree readable writable ran within
  refine ⟨?_, remaining⟩
  · intro exactCount
    obtain ⟨rfl, memoryEq, unwritten⟩ := completed exactCount
    obtain ⟨rdActual, wrActual⟩ := StarM.permissions ran
    refine ⟨rfl, ⟨rdActual, wrActual, ?_⟩, value.1, ?_⟩
    · intro byte outside
      by_cases inFrame : inSlots fp 0 K byte
      · have covered := frameReads byte inFrame
        exact (memoryEq.1 byte covered).1.symm.trans
          ((preservedWords.b byte outside).trans (agree.1 byte covered).1)
      · exact (unwritten byte inFrame).1
    · intro index present
      have indexFits : index < Senke.valueWords τ := by simpa only [Senke.encodeWords_length] using present
      have agreeWord (offset : Nat) (inWord : offset < 8) :=
        memoryEq.1 _ (frameReads _ (frame_slot_byte pre.frame (by omega : d + index < K) inWord))
      have sameRead : actual.rd64 (slot fp (BitVec.ofNat 64 (d + index))) =
          finish.rd64 (slot fp (BitVec.ofNat 64 (d + index))) := by
        simp only [Mem.rd64, Mem.all_congr (fun offset valid => (agreeWord offset valid).2.symm),
          Mem.le_congr (fun offset valid => (agreeWord offset valid).1.symm)]
      rw [sameRead]
      exact value.2 index present

/-- A body can advance its source binding at the exact completed IR
    boundary. Prefixes inside the bound expression supply the same
    footprint obligation for every typed expression. -/
theorem _root_.Gabbro.Stage0.Senke.BildLauf.BodyFrame.bind_reference [kernel : Kern] {D : Deklaration} {B : BodyFrame D}
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {bound : Expr D Γ Λ τ}
    {rest : Endblock D (vertragVon D B.f) l (τ :: Γ) Λ}
    {pc : W} {memory : Mem} {σ : World D} {env : Env D Γ} {code : List II} {top : Nat}
    (frame : B.Ok) (atStart : B.RandIR (.bind bound rest) pc memory σ env)
    (lowered : Senke.lowE (reserved := B.reserved) B.L bound (Senke.frei Γ B.reserved) = some (code, top))
    (resultFits : Senke.frei Γ B.reserved + Senke.valueWords τ ≤ B.Ks)
    (reads : W → Prop) (frameReads : ∀ byte, inSlots B.fp 0 B.Ks byte → reads byte)
    (codeReads : ∀ byte, pc.toNat ≤ byte.toNat → byte.toNat < pc.toNat + 16 * code.length → reads byte)
    (worldReads : ∀ cell : Senke.Zelle D, cell.da B.L →
      Sum.elim (fun table => darf D table Λ) (fun global => gdarf D global Λ) cell.carrier →
      ∀ byte : W, cell.adr B.L ≤ byte.toNat → byte.toNat < cell.adr B.L + cell.bytes → reads byte) :
    let target := pc + BitVec.ofNat 64 (16 * code.length)
    let observed := σ.lese Λ bound.orte
    ∃ count, ∀ {control : Res T} {current : Mem},
      SoloLauf ⟨pc, B.fp⟩ memory control current →
      HostFreeControl reads (inSlots B.fp 0 B.Ks) control ∨
      ∃ boundary : Mem, StarM count ⟨pc, B.fp⟩ memory ⟨target, B.fp⟩ boundary ∧
        SoloLauf ⟨target, B.fp⟩ boundary control current ∧
        Senke.AgreeW B.L B.fp B.lo B.K memory boundary ∧
        B.RandIR rest target boundary observed (.cons (eval observed bound observed env) env) := by
  intro target observed
  have original := atStart
  obtain ⟨all, largest, compiled, room, _, pre, _, _, _, stored, _, _⟩ := atStart
  simp only [Senke.lowEnd, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at compiled
  obtain ⟨⟨ce, te⟩, expression, ⟨tail, tailTop⟩, body, merged⟩ := compiled
  rw [lowered] at expression
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj expression)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj merged
  have floor := frame.win.lo
  have fits := frame.win.ks
  have evaluated := Senke.PreS.welt pre.left fits stored frame.win.lay (by omega)
  have ready : Senke.PreS B.L memory pc B.fp B.Ks (Senke.frei Γ B.reserved) code env B.reserved :=
    ⟨evaluated.ctx, evaluated.small, evaluated.frame, evaluated.code, evaluated.far, evaluated.env,
      trivial, Senke.wstab_true _ _⟩
  have observedMemory : Senke.ReadWorldAt memory B.L observed Λ :=
    ⟨fun t _ f k valid => stored.1 t f k valid, fun g _ => stored.2.1 g⟩
  obtain ⟨count, _, _, prefixCorrect⟩ :=
    lowE_frameMemory (world := observed) (initial := observed) reads frameReads codeReads bound lowered
      (by omega) resultFits ready
      observedMemory worldReads frame.win.lay (by omega) (fun _ => rfl)
  refine ⟨count, ?_⟩
  intro control current solo
  obtain ⟨taken, pointer, atPointer, ran, tail⟩ := solo
  rcases Nat.lt_or_ge taken count with inside | finished
  · rcases tail with ⟨rfl, rfl⟩ | part
    · exact .inl trivial
    · exact .inl ((prefixCorrect ran inside.le).2 inside part)
  · obtain ⟨atBoundary, boundary, expressionRun, later⟩ := StarM.cut ran count finished
    obtain ⟨pointerEq, memoryEffect, value⟩ := (prefixCorrect expressionRun (Nat.le_refl _)).1 rfl
    subst atBoundary
    exact .inr ⟨boundary, expressionRun, ⟨taken - count, pointer, atPointer, later, tail⟩,
      BodyFrame.finishBind frame original lowered memoryEffect value⟩

end Gabbro.Stage0
