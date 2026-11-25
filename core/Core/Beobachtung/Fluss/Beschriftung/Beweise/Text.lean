module

public import Core.Beobachtung.Fluss.Beschriftung.Text
public import Core.Beobachtung.Fluss.Beschriftung.Beweise.TextBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

theorem textLiteralSichtAussage : TextLiteralSichtAussage := by
  intro β pc ziel decoded regel
  exact textLiteralSicht β pc ziel decoded regel

theorem textConcatSichtAussage : TextConcatSichtAussage := by
  intro β pc basis a b regel
  exact textConcatSicht β pc basis a b regel

theorem textLengthSichtAussage : TextLengthSichtAussage := by
  intro β pc basis capacity regel
  exact textLengthSicht β pc basis capacity regel

end Gabbro.Core.Ast.Semantik
