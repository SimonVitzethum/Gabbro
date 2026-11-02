module

public import Grammatik.Kern.Syntax.Satz.Pruefung

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

end Gabbro.Grammatik
