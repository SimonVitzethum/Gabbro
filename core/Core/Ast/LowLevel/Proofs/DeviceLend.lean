module

public import Core.Ast.LowLevel.DeviceLoan

@[expose] public section

namespace Gabbro.Core.Ast.LowLevel.Device

open Katalog Maschine

def LendAussage : Prop :=
  (∀ source : LendSource, source.printPieces.map Text.PrintedToken.value = source.tokens) ∧
  ∀ k (binding : Binding k) region c before event after,
    lend binding region c before event after →
    Aussen.Ausleihen .frei region.loan (.verliehen region.loan) ∧
    Maschine.Leihe.Verleihen (Objekt := Objekt) .eigen binding.object (.verliehen binding.object) ∧
    binding.Lent after c ⟨region, .live, []⟩ ∧
    ¬ (after.machine.leihen region.handle.objekt).Zugriff ∧
    event = .geraet binding.object.endpoint (.lend region.loan)

theorem device_lend : LendAussage := by
  refine ⟨fun _ => rfl, ?_⟩
  intro k binding region c before event after step
  obtain ⟨held, _, _, _, _, _, _, rfl, rfl⟩ := step
  refine ⟨.leihen _, .eigen _, ?_, ?_, rfl⟩
  · simp only [Binding.Lent, setLoan, setFrame, Function.update_self]
    exact ⟨rfl, rfl, rfl, rfl, held.1⟩
  · simp only [setLoan, Function.update_self]
    exact id

end Gabbro.Core.Ast.LowLevel.Device
