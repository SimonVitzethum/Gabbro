module

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Kern.Syntax.Extraktion
public import Grammatik.Kern.Semantik.MaschinenKette.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

theorem serialLink_zeuge_tabelle (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (run : Lauf D) (t₀ : D.Tab) (L : D.Lock)
    (hGuardT : Sum.inl L ∈ D.braucht t₀)
    (hCov : ∀ (g : Faden), g ∈ J.faeden →
      TraegerSchreibt (J.code g) (.inl t₀) = true → ∃ i : D.Inv, t₀ ∈ D.traeger i)
    (hwit : ∀ (k : Nat) (g : Faden), J.schrittFaden[k]? = some g →
      TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λ : List (Res D)) (h : List D.Lock),
        run[j]? = some (Schritt.mk g (.zugriff t₀ w Λ h))) :
    SerialLink Nb J run t₀ ∧
      ∀ (g : Faden), g ∈ J.faeden → TraegerSchreibt (J.code g) (.inl t₀) = true →
        L ∈ D.haelt (J.code g) := by
  constructor
  · intro k g hkg hW
    exact hwit k g hkg hW
  · intro g hg hW
    exact wache_aus_schuld Nb J t₀ L hGuardT g hg hW (hCov g hg hW)


end Gabbro.Grammatik
