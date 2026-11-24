/-
  File:      core/Core/Ziel/Korrektheit/Beweise/Graphmaschine.lean
  Subject:   THE PROOF of `GraphmaschineAequivalentAussage`: a finite graph is produced by a run of the
             graph machine exactly when it is consistent, complete and orders each thread by program order.
             The missing inverse embedding `Einbettung.symm` is proved here; it transports consistency and
             completeness from the reachable machine state back to the graph that state produces.
-/
module

public import Core.Ziel.Korrektheit.Speicher

@[expose] public section

namespace Gabbro.Core.Speicher.Graph.Einbettung

variable {E F Ort Wert : Type} {H : Graph F Ort Wert} {G : Graph E Ort Wert} {g : F → E}

/-- The inverse of a bijective embedding is again an embedding. Feeds: `rightInverse_surjInv`,
    `injective_surjInv`; each field of `h` is transported along `g (surjInv hg.2 x) = x`. -/
theorem symm (h : Einbettung H G g) (hg : Function.Bijective g) :
    Einbettung G H (Function.surjInv hg.2) where
  inj := Function.injective_surjInv hg.2
  lab := fun a => by
    have hri := Function.rightInverse_surjInv hg.2
    have h1 := h.lab (Function.surjInv hg.2 a)
    rw [hri a] at h1
    exact h1.symm
  po := fun a b => by
    have hri := Function.rightInverse_surjInv hg.2
    have h1 := h.po (Function.surjInv hg.2 a) (Function.surjInv hg.2 b)
    rw [hri a, hri b] at h1
    exact h1.symm
  rf := fun a b => by
    have hri := Function.rightInverse_surjInv hg.2
    have h1 := h.rf (Function.surjInv hg.2 a) (Function.surjInv hg.2 b)
    rw [hri a, hri b] at h1
    exact h1.symm
  mo := fun a b => by
    have hri := Function.rightInverse_surjInv hg.2
    have h1 := h.mo (Function.surjInv hg.2 a) (Function.surjInv hg.2 b)
    rw [hri a, hri b] at h1
    exact h1.symm

end Gabbro.Core.Speicher.Graph.Einbettung

namespace Gabbro.Core.Ziel.Korrektheit

open Gabbro.Core

/-- THE GRAPH MACHINE IS CORRECT AND COMPLETE against the axiomatic model, as the pinned equivalence.
    Feeds: `Zustand.erreichbar_gut`, `Zustand.erreichbar_faden`, `Zustand.erzeugt`, `Einbettung.symm`,
    `Einbettung.konsistent`, `Einbettung.vollstaendig`. Proof sketch: the backward half is `erzeugt`; the
    forward half transports soundness back along the inverse of the bijective embedding of `Erzeugt` and
    reads the thread order from `erreichbar_faden`. -/
theorem graphmaschine_aequivalent : GraphmaschineAequivalentAussage := by
  intro E F Ort Wert instE G th
  letI : Finite E := instE
  constructor
  · rintro ⟨Z, hZ, e, hbij, hf, heinb⟩
    have hgut := Speicher.Zustand.erreichbar_gut hZ
    have hsymm : Speicher.Graph.Einbettung G Z.graph (Function.surjInv hbij.2) := heinb.symm hbij
    refine ⟨hsymm.konsistent hgut.1,
      hsymm.vollstaendig (Function.leftInverse_surjInv hbij).surjective hgut.2, ?_⟩
    intro a b hab hne
    obtain ⟨ia, hia⟩ := hbij.2 a
    obtain ⟨ib, hib⟩ := hbij.2 b
    have hka : (Z.ev[ia.1]'ia.2).kontext = th a := by
      rw [← hia]
      exact hf ia
    have hkb : (Z.ev[ib.1]'ib.2).kontext = th b := by
      rw [← hib]
      exact hf ib
    have hctx : (Z.ev[ia.1]'ia.2).kontext = (Z.ev[ib.1]'ib.2).kontext := by
      rw [hka, hkb, hab]
    have hidx : ia.1 ≠ ib.1 := by
      intro hval
      apply hne
      calc
        a = e ia := hia.symm
        _ = e ib := by rw [Fin.ext hval]
        _ = b := hib
    rcases lt_or_gt_of_ne hidx with hlt | hgt
    · have hpo : Z.po ia.1 ib.1 :=
        Speicher.Zustand.erreichbar_faden hZ ia.1 ib.1 ia.2 ib.2 hctx hlt
      exact Or.inl (by
        rw [← hia, ← hib]
        exact (heinb.po ia ib).1 hpo)
    · have hpo : Z.po ib.1 ia.1 :=
        Speicher.Zustand.erreichbar_faden hZ ib.1 ia.1 ib.2 ia.2 hctx.symm hgt
      exact Or.inr (by
        rw [← hib, ← hia]
        exact (heinb.po ib ia).1 hpo)
  · rintro ⟨hk, hv, htot⟩
    exact Speicher.Zustand.erzeugt G th hk hv htot

end Gabbro.Core.Ziel.Korrektheit
