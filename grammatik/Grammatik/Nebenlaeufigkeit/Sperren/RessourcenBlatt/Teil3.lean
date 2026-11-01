module

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Syntax.Extraktion
public import Grammatik.Nebenlaeufigkeit.Sperren.RessourcenBlatt.Teil2

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-! ## CUTS
  - Green (no `sorry`, standard axioms only): `zugriff_darf_aus_gut`,
    `held_in_Λ_aus_offen` (unused, kept as a named utterance of the
    `HeldGenau` tie), `kein_schreibzugriff_ohne_sperre`, all frame lemmas
    (`lese_slots_gleich`, `storeSlot_fremd_traeger`, `storeSlot_fremd_slot`,
    `storeSlot_fremd_feld`, `storeGlob_slots_gleich`,
    `schreibBytes_fremd_traeger`), `schreibBytes_gleich_samma_traeger`
    (new in C: same-carrier byte-write case split), `blatt_slots_t_gleich`
    (fully closed in C, including the same-carrier `schreibBytes` case).
  - CUT (not in this file, recorded in MUSE-REPORT-54.md):
    `csl_ressourceninvarianteC` -- the fixed target is FALSE for
    `Stmt.axiomCall`: the oracle answer may write `t` with no `Held L`
    access event, so the leaf branch owes an underivable `hax`. A
    variant with an added no-oracle premise (rule 12) and its `_zeuge`
    (rule 13) are future work.
-/

#print axioms Gabbro.Grammatik.zugriff_darf_aus_gut
#print axioms Gabbro.Grammatik.kein_schreibzugriff_ohne_sperre
#print axioms Gabbro.Grammatik.blatt_slots_t_gleich
#print axioms Gabbro.Grammatik.schreibBytes_gleich_samma_traeger

#print axioms Gabbro.Grammatik.zugriff_darf_aus_gut
#print axioms Gabbro.Grammatik.kein_schreibzugriff_ohne_sperre

end Gabbro.Grammatik
