module

public import Grammatik.Kern.Syntax.Satz.Pruefung
public import Grammatik.Kern.Syntax.Satz.PruefungMessung
public import Grammatik.Kern.Syntax.Satz.PruefungAbschluss

public section
namespace Gabbro.Grammatik

theorem CheckExpansion.gate_konsumiert_zeuge :
    pruefC.duty ∈ (pruefD.signatur false).konsumiert :=
  CheckExpansion.gate_konsumiert pruef_expansion (by simp only [pruefC]; exact List.mem_singleton_self _)

theorem CheckExpansion.probe_frisch_zeuge : pruefC.probe ∉ pruefC.gates :=
  CheckExpansion.probe_frisch pruef_expansion

theorem CheckExpansion.tore_nodup_zeuge : pruefC.gates.Nodup :=
  CheckExpansion.tore_nodup pruef_expansion

theorem CheckExpansion.produziert_zeuge :
    (pruefD.signatur pruefC.probe).produziert = [pruefC.duty] :=
  CheckExpansion.produziert pruef_expansion

/-- The joint measurement-and-discharge witness (items 11/12): the true report
    covers its place, holds its floor and completes the floored fixture, while
    the negative report completes too and discharges through the same gate. -/
theorem messung_abschluss_zeuge :
    berichtDeckt ["x"] messBerichtWahr ∧ bodenHalten messBerichtWahr ∧
      CheckAbschluss pruefP pruefC1 messBerichtWahr ∧
      CheckEntladung pruefP pruefC1 messBerichtFalsch false :=
  ⟨berichtDeckt_zeuge, bodenHalten_zeuge, abschluss_wahr_zeuge,
    entladung_falsch_zeuge⟩

end Gabbro.Grammatik
