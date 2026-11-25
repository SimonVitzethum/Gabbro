module

public import Core.Beobachtung.Fluss.Beschriftung.Aggregat
public import Core.Beobachtung.Fluss.Beschriftung.Beweise.AggregatBeweise

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung Katalog

theorem liesArraySichtAussage : LiesArraySichtAussage := by
  intro β pc basis element count regel
  exact liesArraySicht β pc basis element count regel

theorem liesTupelfeldSichtAussage : LiesTupelfeldSichtAussage := by
  intro β pc basis types index regel
  exact liesTupelfeldSicht β pc basis types index regel

theorem liesRecordFeldSichtAussage : LiesRecordFeldSichtAussage := by
  intro β pc basis name labels types index regel
  exact liesRecordFeldSicht β pc basis name labels types index regel

end Gabbro.Core.Ast.Semantik
