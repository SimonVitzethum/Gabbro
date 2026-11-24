module

public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Freigabe
public import Core.Ast.LowLevel.Mem.Proofs.Tlb.Tabelle

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

/-! # No run leaves a cached translation uncovered

Every instruction keeps the invariant, so every machine state a Mem unit reaches satisfies it, with
runs that fill cells at any moment (`tlbFuellen`) and with hardware dropping cells at any moment
(`TlbGedeckt.verdraengt`). -/

theorem tlbGedeckt_evaluate (target : ZielDaten) (op : MemInstruction) (s : MemState)
    (c : Kontext) {next : MemFrame} (h : op.evaluate target s c = some next)
    (inv : (s.lokal c).TlbGedeckt) : next.TlbGedeckt := by
  cases op with
  | splitRegion slot point =>
    exact tlbGedeckt_ohne_raeume target _ s c (erhaelt_splitRegion target slot point s c) h inv
  | splitPages slot pages =>
    exact tlbGedeckt_ohne_raeume target _ s c (erhaelt_splitPages target slot pages s c) h inv
  | mergeRegions first second =>
    exact tlbGedeckt_ohne_raeume target _ s c (erhaelt_mergeRegions target first second s c) h inv
  | newSpace tables => exact tlbGedeckt_newSpace target tables s c h inv
  | mapSpace space virt frames rights => exact tlbGedeckt_mapSpace target space virt frames rights s c h inv
  | protectSpace space virt pages rights =>
    exact tlbGedeckt_protectSpace target space virt pages rights s c h inv
  | unmapSpace space virt pages => exact tlbGedeckt_unmapSpace target space virt pages s c h inv
  | flushSpace name => exact tlbGedeckt_flush target name s c h inv
  | activateSpace space =>
    exact tlbGedeckt_ohne_raeume target _ s c (erhaelt_activateSpace target space s c) h inv
  | bindToken name =>
    exact tlbGedeckt_ohne_raeume target _ s c (erhaelt_bindToken target name s c) h inv
  | tlbFuellen core space page => exact tlbGedeckt_tlbFuellen target core space page s c h inv

/-- Every context's frame of a state satisfies the invariant. -/
def MemState.TlbGedeckt (s : MemState) : Prop := ∀ c, (s.lokal c).TlbGedeckt

theorem MemInstruction.tlbGedeckt_schritt (target : ZielDaten) (op : MemInstruction) (c : Kontext)
    (s : MemState) (w : PUnit.{1}) (plans : List Plan) (next : MemState)
    (step : op.step target c s w plans next) (inv : s.TlbGedeckt) : next.TlbGedeckt := by
  obtain ⟨frame, evaluate, _, rfl⟩ := step
  have covered := tlbGedeckt_evaluate target op s c evaluate (inv c)
  intro d
  by_cases same : d = c
  · rw [same]
    have eq : (frame.advance c s).lokal c = { frame with pc := (s.lokal c).pc + 1 } := by
      simp only [MemFrame.advance, Function.update_self]
    rw [eq]
    exact covered.aus_gleich rfl rfl
  · have eq : (frame.advance c s).lokal d = s.lokal d := by
      simp only [MemFrame.advance, Function.update_of_ne same]
    rw [eq]
    exact inv d

theorem memBoot_tlbGedeckt (regions : List Strecke) (core : Option Nat) (c : Kontext) :
    ((memBoot regions core).lokal c).TlbGedeckt := by
  apply MemFrame.TlbGedeckt.leer
  unfold memBoot
  by_cases h : c = entryContext
  · simp only [h, ↓reduceIte] <;> rfl
  · simp only [h, ↓reduceIte] <;> rfl

/-- **No reachable state of a memory unit holds a translation that points at a frame no reservation
    owns.** The statement is over every program of the unit. -/
theorem tlbGedeckt_erreichbar (k : Katalog) (code : List MemInstruction) (start : AussenStart)
    {s : MemState}
    (reach : (memProgram k code).system.IErreichbar (I.start (memProgram k code) start).2 s) :
    s.TlbGedeckt := by
  induction reach with
  | start => exact fun c => memBoot_tlbGedeckt start.regions (start.assignment 0) c
  | schritt c w es _ step ih =>
    obtain ⟨op, _, ideal⟩ := step
    exact MemInstruction.tlbGedeckt_schritt k.plattform.ziel op c _ w es _ ideal ih

end Gabbro.Core.Ast.LowLevel
