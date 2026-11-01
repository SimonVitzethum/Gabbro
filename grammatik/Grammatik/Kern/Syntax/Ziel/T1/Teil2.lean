module

public import Grammatik.Nebenlaeufigkeit.Allgemein.Wettlauf
public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
public import Grammatik.Logik.Vertraege.Komposition
public import Grammatik.Nebenlaeufigkeit.Allgemein.Geteilt.Teil2
public import Grammatik.Kern.Semantik.Fristlauf
public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Semantik.MaschinenKette
public import Grammatik.Kern.Syntax.Extraktion
public import Grammatik.Kern.Syntax.Ziel.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration} {V : Vertrag D}

/-! ## 7. Invariant-form discharge: no per-run interference proof (y02, 2026-09-11)

    The auditor's finding behind `InterferenzAllgemein.lean` §20: the §6
    discharge (`ziel_seqLogic_aus_spec`, bound to `stabil_from_spec`)
    books `hFree : InterferenceFree` as user OWN-LOGIC -- a per-run
    non-interference proof over every foreign step. For the covered class
    -- contract assertions in invariant (resource-invariant) form -- §20
    derives that check by construction (`interferenceFree_of_invariantForm`
    over `invErhalt_aus_Kontext`), and `stabil_from_spec_invariantForm`
    closes it to the last world with `hForm` in place of `hFree`. The
    theorem below is the Ziel-level binder §20 booked as remainder: same
    conclusion as `ziel_seqLogic_aus_spec`, with the FORM check owed
    instead of the per-run check. Non-invariant assertions over shared
    carriers still owe `hFree` exactly as §6 books it. -/

/-- L2-invariant discharge (y02): the invariant-form shape that fills
    `ziel_nutzer_last`'s sequential-logic slot without a per-run
    interference proof -- `hForm` (OWN-LOGIC: exhibit, per thread, the
    carrier whose invariant the contract conjunction coincides with) plus
    the unchanged `hInv` context premise. Proved by
    `stabil_from_spec_invariantForm` (`InterferenzAllgemein.lean`, §20). -/
theorem ziel_seqLogic_aus_spec_invariantForm (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (Pre Post : D.Fn → World D → Prop)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f))
        (SpecQ Pre Post Nb J f))
    (hSpec : ∀ (f : Faden), f ∈ J.faeden → SpecTriple Pre Post Nb J f)
    (hForm : InvariantForm Nb J I (SpecQ Pre Post Nb J))
    (σ : World D) (hletzte : J.welten.getLast? = some σ)
    (f : Faden) (hf : f ∈ J.faeden) :
    SpecQ Pre Post Nb J f σ :=
  stabil_from_spec_invariantForm Nb J I Pre Post hInv hDeck hAb hSpec hForm σ hletzte f hf

#print axioms Gabbro.Grammatik.ziel_seqLogic_aus_spec_invariantForm


end Gabbro.Grammatik
