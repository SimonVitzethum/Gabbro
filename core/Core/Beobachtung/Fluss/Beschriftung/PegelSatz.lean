module

public import Core.Beobachtung.Fluss.Beschriftung.Pegel
public import Core.Beobachtung.Fluss.Beschriftung.Erfuellbar
public import Core.Beobachtung.Fluss.Beschriftung.Leck

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Ast.Semantik
open Katalog

/-- Collective NI statement for levels Stufe 2 (D-4), the single pinned shape:
    noninterference up to declared releases, substantive with input and output.
    (a) An accepted program satisfies the labelled flow rule. (b) The model
    expresses the leak and the checker refuses it. (c) Public outputs and every
    release occurrence are low-visible: the low observer sees inputs, outputs
    and releases, so the statement is not vacuous. -/
def PegelNIAussage : Prop :=
  (∀ platform : Plattform, FlussLokal (gutFragment.beschriftet platform gutBeschriftung)) ∧
  (∀ platform : Plattform, ¬ FlussLokal (leckEinheit platform)) ∧
  (∀ (e : Etiketten Unit) (k : Nat),
    oeffentlich (e.ausgabe k) = true →
    Ausgabe.niedrig e (Ausgabe.wert (Wert := Int) k 0) = true) ∧
  (∀ (e : Etiketten Unit) (id : Nat) (q : Etikett) (w : Int),
    Ausgabe.niedrig e (Ausgabe.freigabe (Wert := Int) id q w) = true)

/-- Proof of the collective statement from the established witnesses. -/
theorem pegelNIAussage_beweis : PegelNIAussage := by
  refine ⟨fun platform => gut_fluss_lokal platform, fun platform => leck_abgelehnt platform, ?_, ?_⟩
  · intro e k h
    simp only [Ausgabe.niedrig, h]
  · intro e id q w
    simp only [Ausgabe.niedrig]

/-- Satisfiability: the premises hold jointly. The accepted program with the
    all-secret-local declaration is the joint witness. -/
theorem pegelNIAussage_erfuellbar :
    ∃ (β : Ast.Semantik.Beschriftung), gutFragment.FlussAkzeptiert β :=
  ⟨gutBeschriftung, gut_akzeptiert⟩

/-- Non-triviality: the model expresses the error (the leaking program is
    refused), so the checker excludes a real behaviour; the accepted program
    above shows the rule is not empty. -/
theorem pegelNIAussage_nichtTrivial :
    (∃ platform : Plattform, ¬ FlussLokal (leckEinheit platform)) ∧ PegelNIAussage :=
  ⟨⟨.x86_64, leck_abgelehnt .x86_64⟩, pegelNIAussage_beweis⟩

end Gabbro.Core.Beobachtung
