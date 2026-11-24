module

public import Core.Ast.Semantik.Pflichten
public import Core.Ast.Semantik.Runtime.Klasse.Pflichten
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

/-- **Every instruction is a form of its class, embedded in the unit of every fragment**: the unit
    reads its rule from the instruction's step form and memory through the elaborated model. The class
    theorems (`klassenSim`, `klassenLokal`, `klassenFortschritt`) therefore apply to it without a premise. -/
theorem Befehl.eingebettet (p : Fragment) (platform : Plattform) (b : Befehl) :
    b.form.Eingebettet (p.einheit platform) b :=
  ⟨rfl, rfl, rfl⟩

/-- **Simulation of an instruction, from its class.** -/
theorem Befehl.simulation (p : Fragment) (platform : Plattform) (b : Befehl) :
    I.RegelSimulation (p.einheit platform) b :=
  (klassenSim b.klasse Befehl (p.einheit platform) b b.form rfl (b.eingebettet p platform) rfl rfl).1

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
    b.abgleich p platform, b.simulation p platform⟩

end Gabbro.Core.Ast.Semantik
