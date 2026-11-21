module

public import Runner.Beweis.Mehr
public import Runner.IR.Seq
public import Stage0.Senke.Bild.Mehr.StoreBuffer

@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Runner.Beweis Runner.Mach

/-- The read part of an IR instruction leaves the TSO state and all other
    entries of the thread list unchanged. -/
theorem tso_read_step {layout : Lay} (before : Cfg (TSO layout) (Res T))
    {i : Nat} (inside : i < before.ths.length) {width : Nat} {address value : W}
    (resume : Ans → Res T) (loaded : rdN (before.ms.1.view i) width address = some value) :
    ProcessStep (TSO layout) actI
      ⟨before.ms, before.ths.set i (some (.ask (.rd width address) resume))⟩ []
      ⟨before.ms, before.ths.set i (some (resume (some (value, 0))))⟩ := by
  have step := ProcessStep.ask (act := actI) (i := i)
    (c := ⟨before.ms, before.ths.set i (some (.ask (.rd width address) resume))⟩)
    (List.getElem?_set_self inside) rfl rfl
    (show (TSO layout).ans before.ms i (.rd width address) (some (value, 0)) before.ms from
      ⟨rfl, 0, by rw [loaded]; rfl⟩)
    (t' := resume (some (value, 0))) rfl
  simpa only [List.set_set, Mach.lbl] using step

/-- The real runner loads an immediate, enqueues its destination store,
    and advances to the next instruction. The issuer can already read
    the written word through its own buffer. -/
theorem tso_const_prefix {layout : Lay}
    {before : Cfg (TSO layout) (Res T)} {i : Nat} {parent : T}
    {dest value pad : BitVec 32}
    (running : before.ths[i]? = some (some (.next parent)))
    (instruction : InsAt (before.ms.1.view i) parent.pc 1 dest value pad)
    (writable : Mem.all before.ms.1.m.wr (slot parent.fp (sx dest)) 8 = true) :
    ∃ after : (TSO layout).St,
      ProcessPrefix (TSO layout) actI before [] 5
        ⟨after, before.ths.set i (some (.next (nxt parent)))⟩ ∧
      after.1.m = before.ms.1.m ∧
      after.1.view i = Mem.write (before.ms.1.view i) (slot parent.fp (sx dest)) 8 (sx value).toNat := by
  have outsideTable (j : Nat) (inside : j < 8) :
      ¬ TB layout (slot parent.fp (sx dest) + BitVec.ofNat 64 j) := by
    intro touches
    obtain ⟨row, range, byte, width, address⟩ := touches
    have present : byte < (readOnlyBytes layout row).length := by
      rw [readOnlyBytes_length]
      exact width
    have readOnly := (before.ms.2.1 row range byte present).2.2
    have writeAllowed := Beweis.all_spec writable inside
    rw [address, readOnly] at writeAllowed
    cases writeAllowed
  let pending := before.ms.1.buf i ++ [(slot parent.fp (sx dest), sx value)]
  let after : (TSO layout).St := ⟨before.ms.1.setBuf i pending, by
    refine ⟨before.ms.2.1, ?_⟩
    intro thread store present
    by_cases writer : thread = i
    · subst thread
      change store ∈ (if i = i then pending else before.ms.1.buf i) at present
      rw [ite_eq_left rfl] at present
      rcases List.mem_append.mp present with old | new
      · exact before.ms.2.2 i store old
      · have same := List.mem_singleton.mp new
        subst store
        exact outsideTable
    · exact before.ms.2.2 thread store (by simpa only [TSt.setBuf, ite_eq_right writer] using present)⟩
  have answered : (TSO layout).ans before.ms i (.wr (slot parent.fp (sx dest)) (sx value))
      (some (0, 0)) after :=
    Or.inr ⟨writable, rfl, rfl⟩
  let onThread (r : Res T) : Cfg (TSO layout) (Res T) :=
    ⟨before.ms, before.ths.set i (some r)⟩
  have inside := (List.getElem?_eq_some_iff.mp running).1
  have started : ProcessStep (TSO layout) actI before [] (onThread (IR.step parent)) :=
    .priv running rfl
  have fetched : ProcessStep (TSO layout) actI (onThread (IR.step parent)) [] (onThread (op 1 parent)) := by
    have loaded : rdN (before.ms.1.view i) 1 parent.pc = some ((BitVec.ofNat 8 1).setWidth 64) := by
      simp only [rdN, instruction.op, Option.map_some]
    exact tso_read_step before inside (fun answer => opt answer fun pair =>
      op (pair.1.setWidth 8 |>.setWidth 64).toNat parent) loaded
  have immediate : ProcessStep (TSO layout) actI (onThread (op 1 parent)) []
      (onThread (ret1 parent (sx value))) := by
    have loaded : rdN (before.ms.1.view i) 4 (parent.pc + 8) = some (value.setWidth 64) := by
      simp only [rdN, instruction.f2, Option.map_some]
    simpa [op, f2, rd32, onThread] using tso_read_step before inside
      (fun answer => opt answer fun pair => ret1 parent (sx (pair.1.setWidth 32))) loaded
  have destination : ProcessStep (TSO layout) actI (onThread (ret1 parent (sx value))) []
      (onThread (wr64 (slot parent.fp (sx dest)) (sx value) (nxt parent))) := by
    have loaded : rdN (before.ms.1.view i) 4 (parent.pc + 4) = some (dest.setWidth 64) := by
      simp only [rdN, instruction.f1, Option.map_some]
    simpa [ret1, f1, rd32, onThread] using tso_read_step before inside
      (fun answer => opt answer fun pair =>
        wr64 (slot parent.fp (sx (pair.1.setWidth 32))) (sx value) (nxt parent)) loaded
  have stored : ProcessStep (TSO layout) actI
      (onThread (wr64 (slot parent.fp (sx dest)) (sx value) (nxt parent))) []
      ⟨after, before.ths.set i (some (.next (nxt parent)))⟩ := by
    have step := ProcessStep.ask (act := actI) (i := i)
      (c := onThread (wr64 (slot parent.fp (sx dest)) (sx value) (nxt parent)))
      (List.getElem?_set_self inside) rfl rfl answered (t' := .next (nxt parent)) rfl
    simpa only [onThread, List.set_set, Mach.lbl] using step
  refine ⟨after, .cons started (.cons fetched (.cons immediate (.cons destination (.cons stored (.nil _))))),
    rfl, ?_⟩
  rcases tso_store_updates_view answered with refused | accepted
  · cases refused.1
  · exact accepted.2.1

end Gabbro.Stage0.Senke.BildMehr
