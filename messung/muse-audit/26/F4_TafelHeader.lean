/-
  Audit 26, finding F4 -- Erhaltung.lean: `tafel_geschlossen` (line 806)
  proves `satz_tafel` (`forall e in tafel, entschieden e`) by `decide`,
  while the file header (lines 38-43, stale) still says the table has open
  slots: "`tafel_nicht_geschlossen` proves the debt is real, and
  `vertrag_braucht_tafel` proves the contract does not hold today" and
  "`satz_tafel` and `satz_erzeugervertrag` stay SPECIFICATION". The named
  theorem `tafel_nicht_geschlossen` no longer exists. Pattern (d): the
  docstring claims MORE OPENNESS than the Lean states -- the debt proof it
  cites is gone. This demo shows the current truth: the table decides.
-/
import Grammatik.Erhaltung

open Gabbro.Grammatik

/-- F4: the table IS closed today (the stale header says it is open). -/
theorem audit26_tafel_geschlossen_holds : satz_tafel :=
  tafel_geschlossen

/-- F4: consequently the projection the old header called unprovable holds. -/
theorem audit26_vertrag_braucht_tafel_holds (gabbroSites : List Nat)
    (cert : CorrCert) (o : AliasObligation) (k : CostClaim) (paare : Nat)
    (a : Absenkung) (cAnweisungen : Nat) :
    satz_erzeugervertrag gabbroSites cert o k paare a cAnweisungen → satz_tafel :=
  vertrag_braucht_tafel gabbroSites cert o k paare a cAnweisungen

#print axioms audit26_tafel_geschlossen_holds
#print axioms audit26_vertrag_braucht_tafel_holds

/-
CUTS:
  (C1) Whether closure-by-`decide` over priced strings is ADEQUATE is the
       booked C5 question; this demo only shows header-vs-Lean drift.
-/
