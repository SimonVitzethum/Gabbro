/-
  File:      core/Core/Aussen/Geraet.lean
  Subject:   DEVICE TYPESTATES (PERFECT-MODEL §4, step M10): linear device authority with
             `lend`/`take back` states; DMA addresses are capabilities of lent regions only,
             never integers. A DMA access outside the currently lent region is not permitted
             (`dma_ausserhalb_verweigert`).
-/
module

public import Core.Katalog.Geraet

@[expose] public section

namespace Gabbro.Core.Aussen

open Gabbro.Core.Katalog

/-- **Linear device authority**: a device region is either free or lent to one outside
    object. There is no copy and no second loan. -/
inductive Vollmacht where
  | frei
  | verliehen (darlehen : Leihe)

/-- Lending: only a free region is lent. -/
inductive Ausleihen : Vollmacht → Leihe → Vollmacht → Prop
  | leihen (l : Leihe) : Ausleihen .frei l (.verliehen l)

/-- Taking back: only from the object it was lent to, back to free. -/
inductive Zuruecknehmen : Vollmacht → Leihe → Vollmacht → Prop
  | zurueck (l : Leihe) : Zuruecknehmen (.verliehen l) l .frei

/-- A lent region cannot be lent again: authority is linear. -/
theorem kein_doppeltes_ausleihen (l l' : Leihe) (v : Vollmacht)
    (h : Ausleihen (.verliehen l) l' v) : False := by
  cases h

/-- Taking back names the same loan that was lent. -/
theorem zurueck_gleich (l l' : Leihe) (h : Zuruecknehmen (.verliehen l) l' .frei) :
    l = l' := by
  cases h
  rfl

/-- A region is lent and taken back. -/
theorem ausleihen_zurueck (l : Leihe) :
    Ausleihen .frei l (.verliehen l) ∧ Zuruecknehmen (.verliehen l) l .frei :=
  ⟨.leihen l, .zurueck l⟩

/-- **A DMA access needs the lent region**: permission holds only for the loan the
    current phase lends. -/
theorem dma_braucht_leihe (d : GeraeteDaten) (phase : GeraetePhase) (darlehen : Leihe)
    (zugriff : DmaZugriff) (h : dma d phase darlehen zugriff) :
    phase = .lending darlehen ∧ darlehen.erlaubt zugriff :=
  let ⟨_, hphase, herlaubt⟩ :=
    (h : d.dma = true ∧ phase = .lending darlehen ∧ darlehen.erlaubt zugriff)
  ⟨hphase, herlaubt⟩

/-- **A DMA access outside the currently lent region is not permitted. Any access the
    current loan does not allow — a foreign token, a missing direction, an overrun —
    has no permission, in no phase. -/
theorem dma_ausserhalb_verweigert (d : GeraeteDaten) (phase : GeraetePhase)
    (darlehen : Leihe) (zugriff : DmaZugriff)
    (ausserhalb : ∀ l, phase = .lending l → ¬ l.erlaubt zugriff) :
    ¬ dma d phase darlehen zugriff := by
  intro h
  let ⟨_, hphase, herlaubt⟩ :=
    (h : d.dma = true ∧ phase = .lending darlehen ∧ darlehen.erlaubt zugriff)
  exact ausserhalb darlehen hphase herlaubt

/-- Satisfiability: the virtio window lends a page-aligned region and permits a read
    inside it. -/
theorem geraet_erfuellbar :
    ∃ (d : GeraeteDaten) (z : ZielDaten) (darlehen : Leihe) (zugriff : DmaZugriff),
      GeraeteUebergang d z .ready (.lend darlehen) (.lending darlehen) ∧
        dma d (.lending darlehen) darlehen zugriff := by
  have seitenOk : (⟨0, 4096⟩ : Strecke).seiten (Plattform.x86_64.ziel) := by
    simp only [Strecke.seiten, ZielDaten.seitengranule, Plattform.ziel, Nat.reducePow]
    exact ⟨by omega, by omega, trivial, trivial⟩
  have erlaubtOk : (⟨7, ⟨0, 4096⟩, true, true⟩ : Leihe).erlaubt
      (DmaZugriff.read 7 0 1) := by
    refine ⟨rfl, rfl, by omega, by omega⟩
  exact ⟨Plattform.virtio .x86_64, Plattform.x86_64.ziel, ⟨7, ⟨0, 4096⟩, true, true⟩,
    DmaZugriff.read 7 0 1, .lend rfl seitenOk, ⟨rfl, rfl, erlaubtOk⟩⟩

end Gabbro.Core.Aussen
