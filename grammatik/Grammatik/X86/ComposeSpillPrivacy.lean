/-
  File:      Grammatik/X86/ComposeSpillPrivacy.lean
  Subject:   Composition closing: allocation spills to fresh private frame slots (lane 830).

  Producer/consumer interface closed here (all producers already accepted,
  reused by name, never re-proved):
  - Producer `SpillPrivate` (lane 343): `spillSlot`, `SpillFrisch`,
    `GetrenntK`, `spillPrivatOk`, `SpillZugelassen`, checked save/load
    equations, freshness/disjointness/commutation facts.
  - Producer `Stapel` (lane 309): `Rahmen`, `sichereWort`, `ladeWort`,
    `sichere_lade_rundreise`, permission/bound refusals and preservation.
  - Producer `TableLayout` (lane 345): `zeugenU` non-degenerate program
    (table `konto` written by `setze`) for the joint witness.
  Consumer: the token-threaded `spillPrivatSchritt` below threads one
  `Option Speicher` token through checked save then checked reload, so a
  refusal on ANY path yields `none` loudly. The closing theorem joins
  validator admission with TSO freshness (`SpillZugelassen`), checked
  save/restore round-trip (`w = v`), permission preservation and disjoint
  foreign stability. No second IR, no second evaluator, no new ISA form.
-/
import Grammatik.X86.SpillPrivate
import Grammatik.X86.TableLayout

namespace Gabbro.Grammatik.X86

/-- Token-threaded private spill step: checked save then checked reload.
    Every refusal path yields `none`; success yields the post-save token
    with the reloaded word. -/
def spillPrivatSchritt (m : Speicher) (r : Rahmen) (idx : Nat)
    (v : Wort) : Option (Speicher × Wort) :=
  match sichereWort m r idx v with
  | none => none
  | some m1 =>
    match ladeWort m1 r idx with
    | none => none
    | some w => some (m1, w)

/- CUTS:
    - Skeleton only: closing theorem, refusals and joint witness follow.
    - OPEN (not claimed): SCFG-side application waits for the accepted 287
      interface (owner 287, reviewer 303), never invented here; W store/read
      bridges wait for accepted 567/570 interfaces (owners 573, 574);
      extended decoder path is lane 575's, not assumed here; no aligned
      multi-byte atomicity beyond byte-extensional commutation; no LOCK RMW;
      no source-to-target simulation; no cost, fairness or timing claim.
-/

#print axioms spillPrivatSchritt

end Gabbro.Grammatik.X86
