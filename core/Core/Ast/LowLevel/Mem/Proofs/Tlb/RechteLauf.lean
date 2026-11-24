module

public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Rechte

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # No run lets a cell grant more than the table, outside a pending narrowing

Every instruction keeps `TlbRechteGedeckt`, so every machine state a Mem unit reaches satisfies it, for
every code and every start, with runs that fill cells at any moment and with hardware dropping cells at
any moment (`TlbRechteGedeckt.verdraengt`). The covering invariant `TlbGedeckt` is carried along: a
`map` and a `newSpace` need it to know that no cell sits on a page that is about to be mapped or on a
space that does not exist yet. -/

theorem tlbRechte_newSpace (target : ZielDaten) (tables : Nat) (s : MemState) (c : Kontext)
    {next : MemFrame} (h : (MemInstruction.newSpace tables).evaluate target s c = some next)
    (cover : (s.lokal c).TlbGedeckt) (inv : (s.lokal c).TlbRechteGedeckt) :
    next.TlbRechteGedeckt := by
  simp only [MemInstruction.evaluate] at h
  cases hr : heldMemRegion target s c tables with
  | none => simp only [hr, Option.bind_eq_bind, Option.bind_none] at h <;> cases h
  | some region =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      intro zelle mem space found
      obtain ⟨space0, found0, _⟩ := cover zelle mem
      have lt : zelle.raum < (s.lokal c).spaces.length := (List.getElem?_eq_some_iff.mp found0).1
      have found1 : (s.lokal c).spaces[zelle.raum]? = some space := by
        have appended : ((s.lokal c).spaces ++ _)[zelle.raum]? = some space := found
        rw [List.getElem?_append_left lt] at appended
        exact appended
      exact inv.bei_gleich rfl mem found1
    · cases h

theorem tlbRechte_evaluate (target : ZielDaten) (op : MemInstruction) (s : MemState)
    (c : Kontext) {next : MemFrame} (h : op.evaluate target s c = some next)
    (cover : (s.lokal c).TlbGedeckt) (inv : (s.lokal c).TlbRechteGedeckt) :
    next.TlbRechteGedeckt := by
  cases op with
  | splitRegion slot point =>
    have kept := erhaelt_splitRegion target slot point s c next h
    exact inv.aus_gleich kept.1 kept.2.1 kept.2.2
  | splitPages slot pages =>
    have kept := erhaelt_splitPages target slot pages s c next h
    exact inv.aus_gleich kept.1 kept.2.1 kept.2.2
  | mergeRegions first second =>
    have kept := erhaelt_mergeRegions target first second s c next h
    exact inv.aus_gleich kept.1 kept.2.1 kept.2.2
  | newSpace tables => exact tlbRechte_newSpace target tables s c h cover inv
  | mapSpace space virt frames rights =>
    exact tlbRechte_mapSpace target space virt frames rights s c h cover inv
  | protectSpace space virt pages rights =>
    exact tlbRechte_protectSpace target space virt pages rights s c h inv
  | unmapSpace space virt pages => exact tlbRechte_unmapSpace target space virt pages s c h inv
  | flushSpace name => exact tlbRechte_flush target name s c h inv
  | activateSpace space =>
    have kept := erhaelt_activateSpace target space s c next h
    exact inv.aus_gleich kept.1 kept.2.1 kept.2.2
  | bindToken name =>
    have kept := erhaelt_bindToken target name s c next h
    exact inv.aus_gleich kept.1 kept.2.1 kept.2.2
  | tlbFuellen core space page => exact tlbRechte_tlbFuellen target core space page s c h inv

/-- Every context's frame of a state satisfies the invariant. -/
def MemState.TlbRechteGedeckt (s : MemState) : Prop := ∀ c, (s.lokal c).TlbRechteGedeckt

theorem MemInstruction.tlbRechte_schritt (target : ZielDaten) (op : MemInstruction) (c : Kontext)
    (s : MemState) (w : PUnit.{1}) (plans : List Plan) (next : MemState)
    (step : op.step target c s w plans next) (cover : s.TlbGedeckt) (inv : s.TlbRechteGedeckt) :
    next.TlbRechteGedeckt := by
  obtain ⟨frame, evaluate, _, rfl⟩ := step
  have covered := tlbRechte_evaluate target op s c evaluate (cover c) (inv c)
  intro d
  by_cases same : d = c
  · rw [same]
    have eq : (frame.advance c s).lokal c = { frame with pc := (s.lokal c).pc + 1 } := by
      simp only [MemFrame.advance, Function.update_self]
    rw [eq]
    exact covered.aus_gleich rfl rfl rfl
  · have eq : (frame.advance c s).lokal d = s.lokal d := by
      simp only [MemFrame.advance, Function.update_of_ne same]
    rw [eq]
    exact inv d

theorem memBoot_tlbRechte (regions : List Strecke) (core : Option Nat) (c : Kontext) :
    ((memBoot regions core).lokal c).TlbRechteGedeckt := by
  apply MemFrame.TlbRechteGedeckt.leer
  unfold memBoot
  by_cases h : c = entryContext
  · simp only [h, ↓reduceIte] <;> rfl
  · simp only [h, ↓reduceIte] <;> rfl

/-- Both cache invariants hold in every state a Mem unit reaches. -/
theorem tlbInvarianten_erreichbar (k : Katalog) (code : List MemInstruction) (start : AussenStart)
    {s : MemState}
    (reach : (memProgram k code).system.IErreichbar (I.start (memProgram k code) start).2 s) :
    s.TlbGedeckt ∧ s.TlbRechteGedeckt := by
  induction reach with
  | start =>
    exact ⟨fun c => memBoot_tlbGedeckt start.regions (start.assignment 0) c,
      fun c => memBoot_tlbRechte start.regions (start.assignment 0) c⟩
  | schritt c w es _ step ih =>
    obtain ⟨op, _, ideal⟩ := step
    exact ⟨MemInstruction.tlbGedeckt_schritt k.plattform.ziel op c _ w es _ ideal ih.1,
      MemInstruction.tlbRechte_schritt k.plattform.ziel op c _ w es _ ideal ih.1 ih.2⟩

/-- **No reachable state of a memory unit holds a translation that grants more than the table, unless a
    narrowing of its page is pending.** Over every program of the unit, every fill and every drop. -/
theorem tlbRechteGedeckt_erreichbar (k : Katalog) (code : List MemInstruction) (start : AussenStart)
    {s : MemState}
    (reach : (memProgram k code).system.IErreichbar (I.start (memProgram k code) start).2 s) :
    s.TlbRechteGedeckt :=
  (tlbInvarianten_erreichbar k code start reach).2

end Gabbro.Core.Ast.LowLevel
