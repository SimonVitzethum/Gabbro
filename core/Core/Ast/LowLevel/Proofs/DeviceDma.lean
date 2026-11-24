module

public import Core.Ast.LowLevel.DeviceLoan

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel.Device

open Katalog Maschine

def DmaAussage : Prop :=
  (∀ k (binding : Binding k) c before event after,
    DmaStep binding c before event after →
    ∃ session access,
      event = .dma binding.object.endpoint access ∧
      binding.Lent before c session ∧ session.revocation = .live ∧
      session.region.loan.erlaubt access ∧
      (after.sessions binding.object).map LoanSession.pending = some (session.pending ++ [access])) ∧
  ∀ k (binding : Binding k) c before event after session,
    before.sessions binding.object = some session → session.revocation ≠ .live →
    ¬ DmaStep binding c before event after

theorem device_dma : DmaAussage := by
  constructor
  · intro k binding c before event after step
    cases step with
    | @issue session access allowed =>
      exact ⟨session, access, rfl, allowed.1, allowed.2.1, allowed.2.2.2.2.2, by
        simp only [setSession, Function.update_self, Option.map_some]⟩
  · intro k binding c before event after session current revoked step
    cases step with
    | issue allowed =>
      have equality := Option.some.inj (current.symm.trans allowed.1.1)
      exact revoked (equality.symm ▸ allowed.2.1)

def TakeBackAussage : Prop :=
  (∀ source : TakeBackSource, source.printPieces.map Text.PrintedToken.value = source.tokens ∧
    source.resume .stuck = some source.handler) ∧
  (∀ k (binding : Binding k) c session before handle event after,
    takeBack binding c session before (.returned handle) event after →
    session.revocation = .synchronized ∧ session.pending = [] ∧
    after.sessions binding.object = none ∧ after.mappings binding.object = none ∧
    after.machine.buchung.geraet binding.object = some (c, .frei) ∧
    after.machine.leihen session.region.handle.objekt = .eigen ∧
    ¬ after.machine.rechte.Gueltig session.region.handle ∧
    after.machine.rechte.Gueltig handle) ∧
  ∀ k (binding : Binding k) c session before event after,
    takeBack binding c session before .stuck event after →
    binding.Lent after c session ∧ after.mappings binding.object = none ∧ event = none

theorem device_takeBack : TakeBackAussage := by
  refine ⟨fun _ => ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro k binding c session before handle event after step
    obtain ⟨lent, synchronized, unmapped, drained, _, _, refreshed, rfl⟩ := step
    refine ⟨synchronized, drained, ?_, unmapped, ?_, ?_, ?_, ?_⟩
    · simp only [returnRegion, setLoan, Function.update_self]
    · simp only [returnRegion, setLoan, setFrame, Function.update_self]
    · simp only [returnRegion, setLoan, Function.update_self]
    · intro old
      have previous := lent.2.2.2.2.2
      have advanced : before.machine.rechte.gen session.region.handle.objekt + 1 =
          session.region.handle.gen := by
        simpa only [returnRegion, setLoan, setFrame, Rechte.beleben, Rechte.widerrufen, eq_self, ite_true]
          using old.2
      omega
    · rw [refreshed]
      exact Rechte.ausgeben_gueltig _ _
  · intro k binding c session before event after step
    obtain ⟨lent, _, _, escaped, rfl⟩ := step
    exact ⟨lent, Function.update_self _ _ _, escaped⟩

end Gabbro.Core.Ast.LowLevel.Device
