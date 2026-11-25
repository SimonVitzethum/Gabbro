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
  | zugriff

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
  | .zugriff .. | .faden .. => .zugriff
  | .maskiere .. | .prioritaet .. | .sendeUnterbrechung .. | .leiteLeitung .. => .kontrollfluss

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

/-- An instruction that is not in the family of access instructions is frame-only. -/
theorem Befehl.privat_von_familie {b : Befehl} (h : b.familie ≠ .zugriff) : b.Privat :=
  b.privat_von_kein_zugriff (fun form eq => h (by subst eq; rfl)) (fun form eq => h (by subst eq; rfl))

/-- A frame-only instruction is not in the family of the access instructions. -/
theorem Befehl.privat_ne_zugriff {b : Befehl} (h : b.Privat) : b.familie ≠ .zugriff := by
  intro hf
  cases b with
  | zugriff z => exact absurd rfl (Befehl.privat_ne_zugriff_klasse _ h z)
  | faden z => exact absurd rfl (Befehl.privat_ne_faden_klasse _ h z)
  | _ => cases hf

/-- **Locality of every instruction, from its class.** -/
theorem Befehl.regelLokal (p : Fragment) (platform : Plattform) (b : Befehl) :
    RegelLokal (p.einheit platform) b :=
  klassenLokal b.klasse Befehl (p.einheit platform) b b.form rfl (b.eingebettet p platform)

/-- **Progress of every instruction, from its class**: the class rule is total. -/
theorem Befehl.regelFortschritt (p : Fragment) (platform : Plattform) (b : Befehl) :
    Ideal.RegelFortschritt (p.einheit platform).system b :=
  klassenFortschritt b.klasse Befehl (p.einheit platform) b b.form rfl (b.eingebettet p platform)

/-- **The class contract of the frame-only classes.** Every frame-only instruction has these
    machine obligations from its class alone: locality, determinacy, progress, composability, state
    match and simulation. The instruction pays its class assignment; the proofs are the generic ones
    over its rule. The access classes have locality, progress, state match and simulation for every
    instruction (`Befehl.regelLokal`, `Befehl.regelFortschritt`, `Befehl.abgleich`, `Befehl.simulation`); their
    determinacy and composability are the open statements of `Atom/Aussagen`. -/
theorem Befehl.klassenvertrag (p : Fragment) (platform : Plattform) (b : Befehl) (h : b.Privat) :
    RegelLokal (p.einheit platform) b ∧ Ideal.RegelBestimmt b.regel ∧
      Ideal.RegelFortschritt (p.einheit platform).system b ∧
      I.RegelKomponierbar (p.einheit platform).einrichtung (p.einheit platform).system b ∧
      I.RegelAbgleich (p.einheit platform) b ∧ I.RegelSimulation (p.einheit platform) b :=
  ⟨b.lokal (p.einheit platform) rfl h, b.bestimmt h, b.fortschritt p h, b.komponierbar p platform h,
    b.abgleich p platform, b.simulation p platform⟩

end Gabbro.Core.Ast.Semantik
