/-
  File:      core/Core/Speicher/Litmus/Katalog.lean
  Subject:   THE LITMUS CATALOGUE ROOT: one proposition joining every finished litmus group.

  Each group (SB, MP, LB, 2+2W, coherence, WRC, ISA2, RMW, RS, IRIW, SC fences) contributes its
  forbidden statement (no consistent graph shows the outcome) and its allowed statement (some
  consistent graph shows it), proved in its own file over a small finite event type or by a generic
  argument over all graphs. This root is the single pin root for those groups: the guard covers
  every `…Aussage` reachable from a root, so the group statements need no rows of their own. The
  catalogue only grows by conjunction; each extension re-measures its one row.
-/
module

public import Core.Speicher.Litmus.Iriw
public import Core.Speicher.Litmus.Isa2
public import Core.Speicher.Litmus.Kohaerenz
public import Core.Speicher.Litmus.Lb
public import Core.Speicher.Litmus.Mp
public import Core.Speicher.Litmus.Rmw
public import Core.Speicher.Litmus.Rs
public import Core.Speicher.Litmus.Sb
public import Core.Speicher.Litmus.ScFences
public import Core.Speicher.Litmus.Wrc
public import Core.Speicher.Litmus.ZweiPlusZweiW

@[expose] public section

namespace Gabbro.Core.Speicher

/-- **The litmus catalogue statement:** every finished litmus group, joined by conjunction. Later
    groups join as further conjuncts. -/
def LitmusKatalogAussage : Prop :=
  SbScVerbotenAussage ∧ SbRaErlaubtAussage ∧
  MpLitmusAussage ∧ LbLitmusAussage ∧
  ZweiPlusZweiWLitmusAussage ∧ KohaerenzLitmusAussage ∧
  WrcLitmusAussage ∧ Isa2LitmusAussage ∧
  RmwLitmusAussage ∧ RsLitmusAussage ∧ IriwLitmusAussage ∧ ScFencesLitmusAussage

/-- The catalogue holds for every joined group. Feeds: the two SB statements and the existing
    group theorems `mp_litmus`, `lb_litmus`, `zwei_plus_zwei_w_litmus`, `kohaerenz_litmus`,
    `wrc_litmus`, `isa2_litmus`, `rmw_litmus`, `rs_litmus`, `iriw_litmus`, `sc_fences_litmus`. -/
theorem litmusKatalog : LitmusKatalogAussage :=
  ⟨sb_sc_verboten_kat, sb_ra_erlaubt_kat,
    mp_litmus, lb_litmus, zwei_plus_zwei_w_litmus, kohaerenz_litmus,
    wrc_litmus, isa2_litmus, rmw_litmus, rs_litmus, iriw_litmus, sc_fences_litmus⟩

end Gabbro.Core.Speicher
