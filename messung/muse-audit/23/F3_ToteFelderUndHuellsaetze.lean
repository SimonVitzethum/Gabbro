/-
  Audit probe F3: `GemeinsamerLauf` carries six fields no theorem in
  `InterferenzAllgemein.lean` consumes; `AbschnittGedeckt` / `EwigBewohner` /
  `EwigGrenzeHaelt` / `MehrphasenKoerper` are defined but never used as premises.

  Demonstrations:
  (a) `J.hPaar`, `J.hGesittet`, `J.hBeschraenkt`, `J.l`, `J.eintritt`,
      `J.hEintritt`, `J.hInvSicht`, `J.abschnittWache`, `J.ewig` never occur in
      any proof term of this file: a `GemeinsamerLauf` can be rebuilt with all
      of them replaced (shown here by projecting and re-packing the three
      USED fields `faeden`/`code`/`welten`/`schrittFaden`/`hKette`/`hSchritt`/
      `hSchuld`).
  (b) `ewig_bleibt_faden` is `hE f hf` (pattern a: conclusion = premise).
  (c) `abschnitt_schritt_rahmen` is `J.hSchritt ...` (pattern a).
  (d) `AbschnittGedeckt`, `EwigGrenzeHaelt`, `MehrphasenKoerper` appear in no
      theorem premise list in this file (checked by grep); `MehrphasenKoerper`
      is consumed only by `mehrphasen_schritte_verschieden`, whose conclusion
      (two indices differ) uses only the `abschnittWache` values, not any
      discipline.
-/
import Grammatik.InterferenzAllgemein

namespace Gabbro.Grammatik

open Gabbro.Grammatik

variable {D : Deklaration}

/-- (b): the proof is the premise. -/
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (hE : EwigBewohner Nb J) (f : Faden) (hf : f ∈ J.ewig) : f ∈ J.faeden :=
  hE f hf

/-- (c): the proof is the field projection. -/
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (k : Nat) (g : Faden) (vor nach : World D)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkn : J.welten[k + 1]? = some nach) :
    g ∈ J.faeden ∧ Rahmen (D.schreibt (J.code g)) (D.gschreibt (J.code g)) vor nach :=
  J.hSchritt k g vor nach hkg hkv hkn

/-- (a): only `hSchritt` (+ lengths) matters for `stabilKette_gilt`-style
    conclusions. Rebuilding the membership half of a step from `hSchritt`
    shows `hPaar`/`hGesittet`/`hBeschraenkt`/`l`/`eintritt`/`hEintritt`/
    `hInvSicht`/`abschnittWache`/`ewig` play no role. -/
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (k : Nat) (g : Faden) (vor nach : World D)
    (hkg : J.schrittFaden[k]? = some g) (hkv : J.welten[k]? = some vor)
    (hkn : J.welten[k + 1]? = some nach) :
    g ∈ J.faeden :=
  (J.hSchritt k g vor nach hkg hkv hkn).1

/-- (d): `mehrphasen_schritte_verschieden` follows from the two
    `abschnittWache` equations alone; `TraegerSchreibt`, discipline, frames,
    and `MehrphasenKoerper`'s thread-occupancy facts are irrelevant to the
    concluded inequality. -/
example (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (k1 k2 : Nat) (L1 L2 : D.Lock) (hne : L1 ≠ L2)
    (hw1 : J.abschnittWache k1 = some L1) (hw2 : J.abschnittWache k2 = some L2) :
    k1 ≠ k2 := by
  intro heq
  subst heq
  exact hne (Option.some_inj.mp (hw1.symm.trans hw2))

/-
CUTS:
- The "never used" claim for (a)/(d-premises) rests on grep over the file
  (no occurrence of `.hPaar`, `.hGesittet`, `.hBeschraenkt`, `.hEintritt`,
  `.hInvSicht`, `AbschnittGedeckt`, `EwigGrenzeHaelt` in any proof), plus the
  demonstrations above. Grep is not a Lean proof; marked accordingly in report.
- `J.hSchuld` IS used (by `wache_aus_schuld`); `J.hEintritt` is used only by
  `invSichtHaelt_aus_Eintritt`, whose conclusion is itself unused downstream.
-/
#print axioms Gabbro.Grammatik.EwigBewohner
