module

public import Core.Beobachtung.Fluss.Beschriftung.Beweise.VarianteBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

theorem baueVarianteSichtAussage : BaueVarianteSichtAussage := by
  intro β pc ziel name labels cases index regel
  exact baueVarianteSicht β pc ziel name labels cases index regel

theorem optionIstBesetztSichtAussage : OptionIstBesetztSichtAussage := by
  intro β pc ziel count regel
  exact optionIstBesetztSicht β pc ziel count regel

end Gabbro.Core.Ast.Semantik
