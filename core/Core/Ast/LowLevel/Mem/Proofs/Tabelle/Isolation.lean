module

public import Core.Ast.LowLevel.Mem.Proofs.Tabelle.Bindung

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel

open Katalog Maschine

private theorem map_foreign_view {target : ZielDaten} {s : MemState} {c : Kontext}
    {sp virt slot : Nat} {rights : List Speicherdienst} {kind : MemoryKind} {next : MemFrame}
    (eval : (MemInstruction.mapSpace sp virt slot rights kind).evaluate target s c = some next) :
    next.tlb = (s.lokal c).tlb ∧
      ∀ other, other ≠ sp → next.spaces[other]? = (s.lokal c).spaces[other]? := by
  simp only [MemInstruction.evaluate] at eval
  cases hs : (s.lokal c).spaces[sp]? with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none] at eval <;> cases eval
  | some space =>
    cases hr : heldMemRegion target s c slot with
    | none =>
      simp only [hs, hr, Option.bind_eq_bind, Option.bind_some, Option.bind_none] at eval
      cases eval
    | some region =>
      simp only [hs, hr, Option.bind_eq_bind, Option.bind_some] at eval
      split at eval
      · simp only [Option.pure_def, Option.some.injEq] at eval
        subst next
        exact ⟨rfl, fun other different => List.getElem?_set_ne (Ne.symm different)⟩
      · cases eval

/-- A checked `map` cannot affect the table or translation of another address space, even at
    the same virtual address. All cores keep their current cache entries. -/
def MapIsolationAussage : Prop :=
  ∀ {k : Katalog} {code : List MemInstruction} {hw : HwLauf} {t : Nat}
    {s next : MemState} {c : Kontext} {trace : SchrittSpur Nat UInt8}
    {sp virt slot : Nat} {rights : List Speicherdienst} {kind : MemoryKind},
    (memProgram k code).system.kopf s c = some (.mapSpace sp virt slot rights kind) →
    ImplSchritt memSetup (memProgram k code).system k hw t s (.kontext c (), trace) next →
    (next.lokal c).tlb = (s.lokal c).tlb ∧
    ∀ other, other ≠ sp →
      (next.lokal c).spaces[other]? = (s.lokal c).spaces[other]? ∧
      ∀ core addr right,
        uebersetze k.plattform.ziel (next.lokal c).mmuSicht core other addr right =
        uebersetze k.plattform.ziel (s.lokal c).mmuSicht core other addr right

theorem map_isolation : MapIsolationAussage := by
  intro k code hw t s next c trace sp virt slot rights kind head step
  obtain ⟨op, frame, chosen, eval, _, rfl⟩ := memKontextSchrittGenau step
  cases Option.some.inj (chosen.symm.trans head)
  obtain ⟨cache, spaces⟩ := map_foreign_view eval
  simp only [MemFrame.advance, Function.update_self]
  refine ⟨cache, fun other different => ⟨spaces other different, ?_⟩⟩
  intro core addr right
  unfold uebersetze MemFrame.mmuSicht MemFrame.tabellenSicht
  simp only [cache, spaces other different]

end Gabbro.Core.Ast.LowLevel
