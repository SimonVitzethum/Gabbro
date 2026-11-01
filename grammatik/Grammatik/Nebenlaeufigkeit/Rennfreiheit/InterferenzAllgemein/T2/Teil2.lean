module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T1
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T2.Teil1

@[expose] public section


/-! ## 19. Sequential contracts as triples: the Owicki-Gries bind (P15 to shape)

    `owickiGries_stabil` (§18) consumes abstract assertions `Q` with sequential
    validity (`SeqTriple`) plus interference freedom (`InterferenceFree`). This
    section binds that shape to CONTRACT-shaped obligations, without importing
    them: `QRequires`/`QEnsures` live downstream in `Extraktion.lean`, which
    already imports THIS file -- importing them here would be circular (and
    `Interferenz.lean` (S1) books exactly this cut: contracts as abstract `Q`,
    substitution downstream). So the triple below is stated over explicit
    `Pre`/`Post` predicates (`D.Fn → World D → Prop`), and the remainder names
    precisely where each premise is discharged.

    Covered fragment (named): the HEAD-VALID CONTRACT CONJUNCTION -- for one
    thread `f` running `J.code f`, the assertion
    `SpecQ Pre Post f σ := Pre (J.code f) σ ∧ Post (J.code f) σ`, valid at the
    chain head (`requiresHead`/`ensuresHead`), preserved by its own steps
    (`requiresEigen`/`ensuresEigen`, the sequential-logic side), and preserved
    by every foreign step (`InterferenceFree`, the Owicki-Gries check).
    `seqTriple_from_spec` folds the triple into `SeqTriple`;
    `stabil_from_spec` closes it to the last world via `owickiGries_stabil`.

    Honest remainder:
    (R1) The instantiation `Pre := QRequires P`, `Post := QEnsures P`
    (`Extraktion.lean`) happens downstream, where the import direction allows
    it -- not here.
    (R2) `hAb` (frame-locality of the conjunction) stays a premise; downstream
    it is `haengtAb_vertrag_gesamt` once both footprints lie in the signature
    frame (the checker's footprint duty).
    (R3) `hFree` (interference freedom) stays a premise; it IS the
    Owicki-Gries check, discharged per program by the verifier (own logic).
    (R4) `requiresEigen`/`ensuresEigen` are carried, not derived from `exec`
    (G7 carries over: own-step preservation is assumed, not executed).
    (R5) `Ziel.lean`'s `hSeqLogic` premise (`ziel_nutzer_last`) still needs
    rewriting to consume `stabil_from_spec` -- owned by the proof architect
    (`Ziel.lean` is not touched here).
-/

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The contract conjunction for one thread: `Pre` (requires-side) and `Post`
    (ensures-side) over the function that thread runs. This is the covered
    fragment -- the head-valid contract conjunction -- as an assertion. -/
def SpecQ (Pre Post : D.Fn → World D → Prop)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) :
    Faden → World D → Prop :=
  fun f σ => Pre (J.code f) σ ∧ Post (J.code f) σ

/-- A sequential contract triple for one thread `f`: both sides valid at the
    chain head and both preserved by its own steps. The MINIMAL spec-triple
    predicate: exactly the `SeqTriple` obligations under contract names, so
    that `seqTriple_from_spec` is a folding, not a claim. -/
structure SpecTriple (Pre Post : D.Fn → World D → Prop)
    (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb) (f : Faden) : Prop where
  /-- The requires-side holds at the chain head (caller obligation at entry). -/
  requiresHead : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Pre (J.code f) σ₀
  /-- The ensures-side holds at the chain head (sequential proof concludes). -/
  ensuresHead : ∀ σ₀ : World D, J.welten[0]? = some σ₀ → Post (J.code f) σ₀
  /-- Own steps preserve the requires-side. -/
  requiresEigen : ∀ (k : Nat) (vor nach : World D),
    J.schrittFaden[k]? = some f → J.welten[k]? = some vor →
      J.welten[k + 1]? = some nach → (Pre (J.code f) vor ↔ Pre (J.code f) nach)
  /-- Own steps preserve the ensures-side. -/
  ensuresEigen : ∀ (k : Nat) (vor nach : World D),
    J.schrittFaden[k]? = some f → J.welten[k]? = some vor →
      J.welten[k + 1]? = some nach → (Post (J.code f) vor ↔ Post (J.code f) nach)

/-- The triple folds into `SeqTriple` over the conjunction: head validity
    pairs up, own-step preservation meets under `and_congr`. -/
theorem seqTriple_from_spec (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := D) Nb)
    (Pre Post : D.Fn → World D → Prop) (f : Faden)
    (h : SpecTriple Pre Post Nb J f) :
    SeqTriple Nb J (SpecQ Pre Post Nb J) f := by
  refine ⟨?_, ?_⟩
  · intro σ₀ h₀
    show Pre (J.code f) σ₀ ∧ Post (J.code f) σ₀
    exact ⟨h.requiresHead σ₀ h₀, h.ensuresHead σ₀ h₀⟩
  · intro k vor nach hkg hkv hkn
    show (Pre (J.code f) vor ∧ Post (J.code f) vor) ↔
      (Pre (J.code f) nach ∧ Post (J.code f) nach)
    exact and_congr (h.requiresEigen k vor nach hkg hkv hkn)
      (h.ensuresEigen k vor nach hkg hkv hkn)


end Gabbro.Grammatik
