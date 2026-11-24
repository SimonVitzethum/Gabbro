module

public import Core.Ast.Semantik.Pflichten
public import Core.Verfeinerung.Formpflichten

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

inductive SimFamilie where
  | skalar
  | kontrollfluss
  | aufrufSchleife
  | aggregat
  | variante
  | text

/-- Classify executing instructions. Surface forms that elaborate to the same
    instruction share its obligation. A new instruction must be classified. -/
def Befehl.simFamilie : Befehl → SimFamilie
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

/-- Both the step match and the per-head bound must hold throughout every
    fragment using an instruction of this family. -/
def SimFamilie.Pflicht (familie : SimFamilie) : Prop :=
  ∀ (p : Fragment) (platform : Plattform) (b : Befehl), b.simFamilie = familie →
    I.RegelSimulation (p.einheit platform) b

end Gabbro.Core.Ast.Semantik
