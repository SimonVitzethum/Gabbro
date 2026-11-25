/-
  File:      core/Core/Speicher/Litmus/Katalog.lean
  Subject:   THE LITMUS CATALOGUE ROOT: one proposition joining every finished litmus group.

  Each group (SB, MP, LB, IRIW, WRC, ISA2, 2+2W, coherence, RMW atomicity, release sequences,
  SC fences) contributes a forbidden statement (no consistent graph shows the outcome) and an
  allowed statement (some consistent and complete graph shows it), each proved in its own file
  over a small finite event type after `Core/Ziel/Korrektheit/Beweise/Iriw.lean`. This root is
  itself the single pin root with one `PinTable` row: the guard covers every `…Aussage` reachable
  from a root, so the group statements need no rows of their own. The root only grows by
  conjunction; each extension re-measures its one row. A mismatch with the literature is a model
  finding: the negation is proved and reported, never patched over.
-/
module

public import Core.Speicher.Litmus.Sb

@[expose] public section

namespace Gabbro.Core.Speicher

/-- **The litmus catalogue statement.** Today the store-buffering group: forbidden for `seq_cst`
    and allowed below it. Later groups join as further conjuncts. -/
def LitmusKatalogAussage : Prop :=
  SbScVerbotenAussage ∧ SbRaErlaubtAussage

/-- The catalogue holds for every group finished so far. Feeds: `sb_sc_verboten_kat`,
    `sb_ra_erlaubt_kat`. -/
theorem litmus_katalog : LitmusKatalogAussage :=
  ⟨sb_sc_verboten_kat, sb_ra_erlaubt_kat⟩

end Gabbro.Core.Speicher
