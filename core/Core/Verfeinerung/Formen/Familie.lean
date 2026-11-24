module

public import Core.Ast.Semantik.Pflichten
public import Core.Ast.Semantik.Runtime.Klasse.Klasse
public import Core.Verfeinerung.Formpflichten

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Annahme Katalog

/-- The groups of frame-level proofs of the local instructions. The machine obligations are proved once
    per effect class (`klassenSim`); what depends on the data an instruction moves in its frame (its
    non-interference) is proved per group. -/
inductive LokalFamilie where
  | skalar
  | kontrollfluss
  | aufrufSchleife
  | aggregat
  | variante
  | text

/-- Classify executing instructions into their frame-level proof groups. Surface forms that elaborate to
    the same instruction share its obligation. A new instruction must be classified. -/
def Befehl.familie : Befehl → LokalFamilie
  | .literal .. | .binaer .. | .wahrheitswert .. | .lesen .. | .negativ ..
  | .negieren .. | .verneinen .. | .teilen .. | .vergleichen .. => .skalar
  | .binden .. | .springeWenn .. | .zuweisen .. | .zurueck .. | .springe ..
  | .blockEnde .. | .bindeWert .. | .starte .. | .ende | .bindeRegion .. => .kontrollfluss
  | .definiere .. | .rufe .. | .rueckVoid | .pruefeMass .. | .setzePasszahl ..
  | .whileTest .. | .forAnfang .. | .forTest .. | .forNaechster .. | .zurueckSprung .. => .aufrufSchleife
  | .baueArray .. | .liesArray .. | .baueTupel .. | .liesTupelfeld .. | .bindeTupel ..
  | .definiereRecord .. | .baueRecord .. | .liesRecordFeld .. | .setzeRecordFeld .. => .aggregat
  | .definiereVariante .. | .baueVariante .. | .waehleVariante ..
  | .definiereTraeger .. | .optionIstBesetzt .. | .definiereEffektgruppe .. | .waehleUmgebung .. => .variante
  | .textLiteral .. | .textConcat .. | .textIndex .. | .substring .. | .textLength .. => .text

/-- **Simulation, once per class.** An instruction of the class has one linearisation point: its ideal and
    its implementation step are one relation, and it takes no private step. Both must hold throughout every
    fragment using an instruction of the class. -/
def KlassenSim (k : Wirkungsklasse) : Prop :=
  ∀ (p : Fragment) (platform : Plattform) (b : Befehl), b.klasse = k →
    I.RegelSimulation (p.einheit platform) b

/-- The simulation duty of the class `lokal`. -/
def LokalSimAussage : Prop := KlassenSim .lokal

/-- The simulation duty of the class `ruf`. -/
def RufSimAussage : Prop := KlassenSim .ruf

/-- Both frame-only classes satisfy it, by the same argument: the rule of the instruction is its own
    ideal rule. -/
theorem klassenSim (k : Wirkungsklasse) : KlassenSim k := by
  intro p platform b _
  exact ⟨I.RegelSimSchritt.aus_gleicher_regel rfl (fun _ _ _ _ _ step => step),
    I.RegelStotterSchranke.null rfl⟩

/-- **The class contract of the frame-only classes.** Every instruction, whatever its group, has these
    machine obligations from its class alone: locality, determinacy, progress, composability, state
    match and simulation. The instruction pays its class assignment; the proofs are the generic ones
    over its rule. -/
theorem Befehl.klassenvertrag (p : Fragment) (platform : Plattform) (b : Befehl) :
    RegelLokal (p.einheit platform) b ∧ Ideal.RegelBestimmt b.regel ∧
      Ideal.RegelFortschritt (p.einheit platform).system b ∧
      I.RegelKomponierbar (p.einheit platform).einrichtung (p.einheit platform).system b ∧
      I.RegelAbgleich (p.einheit platform) b ∧ I.RegelSimulation (p.einheit platform) b :=
  ⟨b.lokal (p.einheit platform) rfl, b.bestimmt, b.fortschritt p, b.komponierbar p platform,
    b.abgleich p platform, klassenSim b.klasse p platform b rfl⟩

end Gabbro.Core.Ast.Semantik
