module
public meta import Lean

open Lean

namespace Gabbro.Core.Waechter

/-- Regel S allow-list of `(structure, field)` pairs whose Prop-valued field the review has tied to a
    model definition. Each entry carries a one-line justification naming the binding definition
    (file paths relative to `core/`, with the line of the binding construction). A field with no such
    entry is reported by `strukturPropInfos`; a field that is really free (user input, open obligation)
    is never listed here — it stays a finding and is documented in the review report. -/
public meta def strukturPropErlaubt : Array (Name × Name) := #[
  -- Rahmen: R₀ (Ziel/Korrektheit/Instanz.lean:67) belegt alle Prop-Felder mit gepinnten realen Definitionen.
  (`Gabbro.Core.Ziel.Rahmen, `Akzeptiert),
  (`Gabbro.Core.Ziel.Rahmen, `Bestimmt),
  (`Gabbro.Core.Ziel.Rahmen, `Bezeichnet),
  (`Gabbro.Core.Ziel.Rahmen, `enthaelt),
  (`Gabbro.Core.Ziel.Rahmen, `FairLaeufe),
  (`Gabbro.Core.Ziel.Rahmen, `Fortschritt),
  (`Gabbro.Core.Ziel.Rahmen, `GleicheNiedrigeUmgebung),
  (`Gabbro.Core.Ziel.Rahmen, `GleichePolitik),
  (`Gabbro.Core.Ziel.Rahmen, `Haengt),
  (`Gabbro.Core.Ziel.Rahmen, `Hardware),
  (`Gabbro.Core.Ziel.Rahmen, `IdealFortschritt),
  (`Gabbro.Core.Ziel.Rahmen, `IdealLaeufe),
  (`Gabbro.Core.Ziel.Rahmen, `ImSchranken),
  (`Gabbro.Core.Ziel.Rahmen, `KatalogWohlgeformt),
  (`Gabbro.Core.Ziel.Rahmen, `Laeufe),
  (`Gabbro.Core.Ziel.Rahmen, `NiedrigAequiv),
  (`Gabbro.Core.Ziel.Rahmen, `NiedrigGleich),
  (`Gabbro.Core.Ziel.Rahmen, `realisiert),
  (`Gabbro.Core.Ziel.Rahmen, `Sim),
  (`Gabbro.Core.Ziel.Rahmen, `WohlgeformterText),
  (`Gabbro.Core.Ziel.Rahmen, `ZielFX),
  (`Gabbro.Core.Ziel.Rahmen, `ZulStart),
  -- Sicherheit: S₀ (Ziel/Korrektheit/Instanz.lean:113) belegt alle vier Felder mit den Sicherheitssätzen.
  (`Gabbro.Core.Ziel.Sicherheit, `InvariantenErhalten),
  (`Gabbro.Core.Ziel.Sicherheit, `Rennfrei),
  (`Gabbro.Core.Ziel.Sicherheit, `Speichersicher),
  (`Gabbro.Core.Ziel.Sicherheit, `ToctouFrei),
  -- FormBeleg: beleg (Ziel/Korrektheit/Beweise/BegleitZusammensetzung.lean:81) belegt beide Felder.
  (`Gabbro.Core.Ziel.Korrektheit.FormBeleg, `enthaelt),
  (`Gabbro.Core.Ziel.Korrektheit.FormBeleg, `realisiert),
  -- ProtokollGut: fuehrtSchrittAus_erhaelt (Ziel/Korrektheit/Beweise/ProtokollSchritt.lean:137) erhält alle Felder je Schritt.
  (`Gabbro.Core.Ziel.Korrektheit.ProtokollGut, `speicher),
  (`Gabbro.Core.Ziel.Korrektheit.ProtokollGut, `sperren),
  (`Gabbro.Core.Ziel.Korrektheit.ProtokollGut, `verbrauch),
  -- Wohlgeformt: einschraenken_wf (Speicher/Praefix.lean) erhält jedes Feld unter Präfixeinschränkung.
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `mo_irrefl),
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `mo_ort),
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `mo_schreibt),
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `mo_total),
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `mo_trans),
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `po_irrefl),
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `po_trans),
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `rf_eindeutig),
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `rf_liest),
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `rf_ort),
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `rf_schreibt),
  (`Gabbro.Core.Speicher.Graph.Wohlgeformt, `rf_wert),
  -- Konsistent: einschraenken_konsistent (Speicher/Praefix.lean) erhält jedes Feld unter Präfixeinschränkung.
  (`Gabbro.Core.Speicher.Graph.Konsistent, `atomar),
  (`Gabbro.Core.Speicher.Graph.Konsistent, `hb_irrefl),
  (`Gabbro.Core.Speicher.Graph.Konsistent, `kohaerent),
  (`Gabbro.Core.Speicher.Graph.Konsistent, `liest_vorher),
  (`Gabbro.Core.Speicher.Graph.Konsistent, `ohneLB),
  (`Gabbro.Core.Speicher.Graph.Konsistent, `psc),
  (`Gabbro.Core.Speicher.Graph.Konsistent, `wf),
  -- Graph: sbGraph (Speicher/Trennung.lean:93) belegt alle Relationen mit den SB-Litmus-Definitionen.
  (`Gabbro.Core.Speicher.Graph, `mo),
  (`Gabbro.Core.Speicher.Graph, `po),
  (`Gabbro.Core.Speicher.Graph, `rf),
  -- Einbettung: einschraenken_einbettung (Speicher/Einbettung.lean:38) konstruiert jedes Feld aus der Restriktion.
  (`Gabbro.Core.Speicher.Graph.Einbettung, `inj),
  (`Gabbro.Core.Speicher.Graph.Einbettung, `lab),
  (`Gabbro.Core.Speicher.Graph.Einbettung, `mo),
  (`Gabbro.Core.Speicher.Graph.Einbettung, `po),
  (`Gabbro.Core.Speicher.Graph.Einbettung, `rf),
  -- Zustand: Zustand.senke (Speicher/Anhaengen.lean:44) definiert alle Relationen aus Anhang plus Vorgänger.
  (`Gabbro.Core.Speicher.Zustand, `mo),
  (`Gabbro.Core.Speicher.Zustand, `po),
  (`Gabbro.Core.Speicher.Zustand, `rf),
  -- Zustand.Schritt: Zustand.senke_schritt (Speicher/Anhaengen.lean:306) belegt jedes Feld aus der senke-Formel.
  (`Gabbro.Core.Speicher.Zustand.Schritt, `ev),
  (`Gabbro.Core.Speicher.Zustand.Schritt, `konsistent),
  (`Gabbro.Core.Speicher.Zustand.Schritt, `mo_alt),
  (`Gabbro.Core.Speicher.Zustand.Schritt, `po_alt),
  (`Gabbro.Core.Speicher.Zustand.Schritt, `po_ende),
  (`Gabbro.Core.Speicher.Zustand.Schritt, `po_faden),
  (`Gabbro.Core.Speicher.Zustand.Schritt, `rf_alt),
  (`Gabbro.Core.Speicher.Zustand.Schritt, `rf_ende),
  (`Gabbro.Core.Speicher.Zustand.Schritt, `vollstaendig),
  -- Zustandsrahmen: Befehl.vollzug (Ast/Semantik/Pflichten.lean:39) belegt alle Felder mit rfl im Framebeweis.
  (`Gabbro.Core.Maschine.Zustandsrahmen, `antworten),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `epoche),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `erzeuger),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `fragen),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `geliefert),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `graph),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `initial),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `kerne),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `leitung),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `persistenz),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `software),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `sperren),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `verbraucht),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `verlauf),
  (`Gabbro.Core.Maschine.Zustandsrahmen, `verworfen),
  -- Einrichtung: einrichtung (Ast/Semantik/Elaborierung.lean:259) belegt bedingung mit False, invariant mit True.
  (`Gabbro.Core.Maschine.Einrichtung, `bedingung),
  (`Gabbro.Core.Maschine.Einrichtung, `invariant),
  -- Regel: Befehl.regel (Ast/Semantik/Runtime/Regeln.lean:26) belegt beide Felder mit der elaborierten Regel.
  (`Gabbro.Core.Maschine.Regel, `ideal),
  (`Gabbro.Core.Maschine.Regel, `impl),
  -- System: system (Ast/Semantik/Runtime/Regeln.lean:143) belegt beide Felder mit dem elaborierten System.
  (`Gabbro.Core.Maschine.System, `blockiert),
  (`Gabbro.Core.Maschine.System, `fertig),
  -- Kommutation: Befehl.kommutation (Ast/Semantik/Pflichten.lean:92) belegt beide Felder durch False-Elim.
  (`Gabbro.Core.Maschine.Kommutation, `nach_links),
  (`Gabbro.Core.Maschine.Kommutation, `vor_rechts),
  -- Quellklauseln: Quellklauseln.leer (Maschine/Quelltabellen.lean:43) belegt alle Felder mit leeren Tabellen.
  (`Gabbro.Core.Maschine.Quellklauseln, `invariant),
  (`Gabbro.Core.Maschine.Quellklauseln, `sicher),
  (`Gabbro.Core.Maschine.Quellklauseln, `voraus),
  -- Quelltabellen: Fragment.tabellen (Ast/Semantik/Elaborierung.lean:277) belegt guard aus der Elaboration.
  (`Gabbro.Core.Maschine.Quelltabellen, `guard),
  -- Einheit: Fragment.einheit (Ast/Semantik/Elaborierung.lean:296) belegt lokalerBezug mit Eq.
  (`Gabbro.Core.Maschine.Einheit, `lokalerBezug),
  -- Zeitlauf: Zeitlauf.existiert (Maschine/Zeitlauf.lean:93) konstruiert jeden Lauf mit takt-Beweis.
  (`Gabbro.Core.Maschine.Zeitlauf, `takt),
  -- AussenBezug: ProtokollBezug.aussen (Verfeinerung/Protokoll.lean:22) erhält fragen/antworten/verbraucht per rfl.
  (`Gabbro.Core.Maschine.I.AussenBezug, `antworten),
  (`Gabbro.Core.Maschine.I.AussenBezug, `fragen),
  (`Gabbro.Core.Maschine.I.AussenBezug, `verbraucht),
  -- AussenBezug: aussen_ankunft (Ideal/Replay.lean:61) erhält verlauf über den Ankunftsbeweis.
  (`Gabbro.Core.Maschine.I.AussenBezug, `verlauf),
  -- AussenBezug: aussen_absturz (Ideal/Absturz.lean:16) erhält epoche/verworfen über den Wiederanlauf.
  (`Gabbro.Core.Maschine.I.AussenBezug, `epoche),
  (`Gabbro.Core.Maschine.I.AussenBezug, `verworfen),
  -- Laufabgleich: laufabgleich (Verfeinerung/Maschine.lean:208) konstruiert alle Felder aus dem Laufbild.
  (`Gabbro.Core.Maschine.I.Laufabgleich, `belegt),
  (`Gabbro.Core.Maschine.I.Laufabgleich, `frei),
  (`Gabbro.Core.Maschine.I.Laufabgleich, `hardware),
  (`Gabbro.Core.Maschine.I.Laufabgleich, `spur),
  (`Gabbro.Core.Maschine.I.Laufabgleich, `start),
  (`Gabbro.Core.Maschine.I.Laufabgleich, `zustand),
  -- RegelSimulation: aus_gleicher_regel (Verfeinerung/Formpflichten.lean:79) belegt schritt pro Klasse.
  (`Gabbro.Core.Maschine.I.RegelSimulation, `schritt),
  -- RegelSimulation: RegelStotterSchranke.null (Verfeinerung/Formpflichten.lean:51) belegt stottern per Induktion.
  (`Gabbro.Core.Maschine.I.RegelSimulation, `stottern),
  -- SCOrdnung: sc_ordnung_im_lauf (Verfeinerung/Speicherordnung.lean:138) wählt die Ordnung per linearer Erweiterung.
  (`Gabbro.Core.Maschine.I.SCOrdnung, `irreflexiv),
  (`Gabbro.Core.Maschine.I.SCOrdnung, `total),
  -- Hardware: Umgebung.referenz_hardware (Katalog/Erfuellbar.lean) belegt alle Felder mit der Referenzumgebung.
  (`Gabbro.Core.Katalog.Hardware, `abi),
  (`Gabbro.Core.Katalog.Hardware, `antwort),
  (`Gabbro.Core.Katalog.Hardware, `dma),
  (`Gabbro.Core.Katalog.Hardware, `float),
  (`Gabbro.Core.Katalog.Hardware, `interrupts),
  (`Gabbro.Core.Katalog.Hardware, `katalog),
  (`Gabbro.Core.Katalog.Hardware, `kerne),
  (`Gabbro.Core.Katalog.Hardware, `lader),
  (`Gabbro.Core.Katalog.Hardware, `mmu),
  (`Gabbro.Core.Katalog.Hardware, `pages),
  (`Gabbro.Core.Katalog.Hardware, `persistence),
  (`Gabbro.Core.Katalog.Hardware, `ziel),
  -- FairLaeufe: Umgebung.referenz_fair (Katalog/Erfuellbar.lean) belegt alle Felder mit dem Referenzangebot.
  (`Gabbro.Core.Katalog.FairLaeufe, `auslieferung),
  (`Gabbro.Core.Katalog.FairLaeufe, `cycles),
  (`Gabbro.Core.Katalog.FairLaeufe, `gueltig),
  (`Gabbro.Core.Katalog.FairLaeufe, `hardware),
  (`Gabbro.Core.Katalog.FairLaeufe, `interrupts),
  (`Gabbro.Core.Katalog.FairLaeufe, `kerne),
  (`Gabbro.Core.Katalog.FairLaeufe, `medium),
  (`Gabbro.Core.Katalog.FairLaeufe, `politik),
  (`Gabbro.Core.Katalog.FairLaeufe, `zeit),
  -- Umgebung: Umgebung.referenz (Katalog/Erfuellbar.lean:21) belegt beide Felder mit der Katalogzeile.
  (`Gabbro.Core.Katalog.Umgebung, `medium),
  (`Gabbro.Core.Katalog.Umgebung, `pages),
  -- GuardVerwendung: kanonischeVerwendung (Annahme/Waechter.lean:55) ist die einzige Instanz im Modell.
  (`Gabbro.Core.Annahme.GuardVerwendung, `bedarf),
  -- KlauselTabelle: kanonischeKlauseln (Annahme/Klauseln.lean:34) belegt alle Felder aus der Elaboration.
  (`Gabbro.Core.Annahme.KlauselTabelle, `invariant),
  (`Gabbro.Core.Annahme.KlauselTabelle, `sicher),
  (`Gabbro.Core.Annahme.KlauselTabelle, `voraus),
  -- SchrankenLokal: schrankenLokal_leer (Annahme/Schranken.lean:177) belegt alle Felder mit Leer-Bounds.
  (`Gabbro.Core.Annahme.SchrankenLokal, `bezug),
  (`Gabbro.Core.Annahme.SchrankenLokal, `protokoll),
  (`Gabbro.Core.Annahme.SchrankenLokal, `regel),
  (`Gabbro.Core.Annahme.SchrankenLokal, `start),
  -- ZulassungsRegel: zulassung_m2 (Aussen/Zulassung.lean:69) belegt alle Felder mit den Zulassungslemmas.
  (`Gabbro.Core.Aussen.ZulassungsRegel, `fehlerkanal),
  (`Gabbro.Core.Aussen.ZulassungsRegel, `griffbindung),
  (`Gabbro.Core.Aussen.ZulassungsRegel, `namen_nur_griff),
  -- SchrittSicherheit: Befehl.sicher (Ast/Semantik/Runtime/Sicherheit.lean:17) belegt alle Felder pro Form.
  (`Gabbro.Core.Sicherheit.SchrittSicherheit, `invarianten),
  (`Gabbro.Core.Sicherheit.SchrittSicherheit, `register),
  (`Gabbro.Core.Sicherheit.SchrittSicherheit, `rennen),
  (`Gabbro.Core.Sicherheit.SchrittSicherheit, `speicher),
  (`Gabbro.Core.Sicherheit.SchrittSicherheit, `sperrwechsel),
  (`Gabbro.Core.Sicherheit.SchrittSicherheit, `toctou),
  -- Buchung: Buchung.leer (Maschine/Buchung.lean:48) belegt alle Felder mit False als Default.
  (`Gabbro.Core.Sicherheit.Buchung, `aussengriff),
  (`Gabbro.Core.Sicherheit.Buchung, `haelt),
  (`Gabbro.Core.Sicherheit.Buchung, `schreibt),
  -- Invariante: sicherheitsEinheit_invarianten (Ast/Semantik/Runtime/UnitInvarianten.lean:74) bindet gilt per Elaboration.
  (`Gabbro.Core.Sicherheit.Invariante, `gilt),
  -- Grammar: tokenGrammar (Text/Syntax.lean:17) belegt beide Felder mit der Token-Grammatik.
  (`Gabbro.Core.Text.Grammar, `production),
  (`Gabbro.Core.Text.Grammar, `root),
  -- PrintedToken: PrintedToken.unquoted (Text/Printing.lean:118) belegt alle Felder aus dem Lexem.
  (`Gabbro.Core.Text.PrintedToken, `headNotSpace),
  (`Gabbro.Core.Text.PrintedToken, `reads),
  (`Gabbro.Core.Text.PrintedToken, `separated),
  -- Syntax: Category.syntax (Ast/Grammar.lean:68) belegt beide Felder mit Kategorie-Lesern.
  (`Gabbro.Core.Text.Syntax, `reads),
  (`Gabbro.Core.Text.Syntax, `unique),
  -- UnquotedStart: UnquotedStart.ofCodepoint (Text/Printing.lean:18) belegt alle Felder per Codepoint-Schranke.
  (`Gabbro.Core.Text.UnquotedStart, `nonchar),
  (`Gabbro.Core.Text.UnquotedStart, `nonslash),
  (`Gabbro.Core.Text.UnquotedStart, `nonspace),
  (`Gabbro.Core.Text.UnquotedStart, `nonstring),
  -- Address: Instruction.evaluate (Ast/LowLevel/Meaning.lean:139) belegt beide Felder aus der gehaltenen Region.
  (`Gabbro.Core.Ast.LowLevel.Address, `fits),
  (`Gabbro.Core.Ast.LowLevel.Address, `spaceWidth),
  -- Binding: selectedDevice (Ast/LowLevel/Proofs/DeviceSatisfiability.lean:13) belegt beide Felder mit virtio.
  (`Gabbro.Core.Ast.LowLevel.Device.Binding, `described),
  (`Gabbro.Core.Ast.LowLevel.Device.Binding, `selected),
  -- ReadRange: registerReadElse_erfuellbar (Ast/LowLevel/Proofs/DeviceSatisfiability.lean:67) belegt ordered.
  (`Gabbro.Core.Ast.LowLevel.Device.ReadRange, `ordered),
  -- RegisterTransition: registerTransition_erfuellbar (Ast/LowLevel/Proofs/DeviceSatisfiability.lean:76) belegt alle Felder.
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterTransition, `freeAfter),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterTransition, `freeBefore),
  (`Gabbro.Core.Ast.LowLevel.Device.RegisterTransition, `rule),
  -- AddressValue: RegionSatisfiability.lean:106 belegt fits mit konkreter Instanz aus dem Regions-Erzeuger.
  (`Gabbro.Core.Ast.AddressValue, `fits),
  -- Zahl: Zahl.literal (Ast/Semantik/Arithmetik.lean:15) belegt beide Schranken per Reflexivität.
  (`Gabbro.Core.Ast.Zahl, `oben),
  (`Gabbro.Core.Ast.Zahl, `unten),
  -- TableDeclaration: TableProofs.lean:194 belegt beide Felder mit der leeren Tabelleninstanz.
  (`Gabbro.Core.Ast.TableDeclaration, `distinct),
  (`Gabbro.Core.Ast.TableDeclaration, `valid),
  -- TextValue: TextValue.literal (Ast/TextValue/Bytes.lean:20) belegt bound per Reflexivität.
  (`Gabbro.Core.Ast.TextValue, `bound),
  -- RegistryStatements: Quellform.statements (Ast/Semantik/Quellform.lean:138) belegt alle Felder je Quellform.
  (`Gabbro.Core.Waechter.RegistryStatements, `acceptanceRule),
  (`Gabbro.Core.Waechter.RegistryStatements, `idealRule),
  (`Gabbro.Core.Waechter.RegistryStatements, `implementationRule),
  (`Gabbro.Core.Waechter.RegistryStatements, `jointlySatisfiable),
  (`Gabbro.Core.Waechter.RegistryStatements, `preservation),
  (`Gabbro.Core.Waechter.RegistryStatements, `unitsAndCommutation),
  -- Vergleich: vergleichslauf (Beobachtung/Projektion.lean:72) plus Selbstvergleich (Fluss/Erfuellbar.lean:50).
  (`Gabbro.Core.Beobachtung.Vergleich, `links),
  (`Gabbro.Core.Beobachtung.Vergleich, `politik),
  (`Gabbro.Core.Beobachtung.Vergleich, `rechts),
  (`Gabbro.Core.Beobachtung.Vergleich, `start),
  (`Gabbro.Core.Beobachtung.Vergleich, `umgebung),
  -- Hebebuendel: buendelUnterZulStart (Beobachtung/Wahrscheinlichkeit/Hebung/BuendelUnterZulStart.lean:134) belegt alle Felder.
  (`Gabbro.Core.Beobachtung.Hebebuendel, `istWMass),
  (`Gabbro.Core.Beobachtung.Hebebuendel, `massErhalt),
  (`Gabbro.Core.Beobachtung.Hebebuendel, `replayFolgtScheduler),
  (`Gabbro.Core.Beobachtung.Hebebuendel, `replayKausal),
  (`Gabbro.Core.Beobachtung.Hebebuendel, `replayZiehungen),
  (`Gabbro.Core.Beobachtung.Hebebuendel, `replayZulaessig),
  -- RessourcenPflichten: hosted_pflichten (Beobachtung/SchrankenB9B21Erfuellbar.lean:43) belegt alle Felder.
  (`Gabbro.Core.Beobachtung.RessourcenPflichten, `protokoll),
  (`Gabbro.Core.Beobachtung.RessourcenPflichten, `regel),
  (`Gabbro.Core.Beobachtung.RessourcenPflichten, `start),
  -- DurchlaufPflichten: pflichten_leer (Beobachtung/SchrankenBeweise/Durchlauf.lean:261) belegt alle Felder vakuos.
  (`Gabbro.Core.Beobachtung.DurchlaufPflichten, `protokoll),
  (`Gabbro.Core.Beobachtung.DurchlaufPflichten, `regel),
  (`Gabbro.Core.Beobachtung.DurchlaufPflichten, `start),
  -- Zufallsquelle: muenzQuelle (Beobachtung/Wahrscheinlichkeit/Quelle.lean:51) belegt pos mit 0 < 2.
  (`Gabbro.Core.Beobachtung.Zufallsquelle, `pos),
  -- ArrayIndexArgs: ArrayIndexProofs.lean:175 belegt beide Felder mit 0 ≤ 0 und oberer Schranke.
  (`Gabbro.Core.Ast.Surface.ArrayIndexArgs, `lower),
  (`Gabbro.Core.Ast.Surface.ArrayIndexArgs, `upper),
  -- ArrayValueArgs: ArrayValueProofs.lean:177 belegt beide Felder mit dem Leer-Literal-Zeugen.
  (`Gabbro.Core.Ast.Surface.ArrayValueArgs, `fits),
  (`Gabbro.Core.Ast.Surface.ArrayValueArgs, `principal),
  -- AssignArgs: BatchSurface.lean:37 belegt alle Felder mit dem assignVar-Zeugen.
  (`Gabbro.Core.Ast.Surface.AssignArgs, `fits),
  (`Gabbro.Core.Ast.Surface.AssignArgs, `visible),
  (`Gabbro.Core.Ast.Surface.AssignArgs, `writable),
  -- AssignFieldArgs: AssignFieldProofs.lean:237 belegt alle Felder mit dem Erfuellbar-Zeugen.
  (`Gabbro.Core.Ast.Surface.AssignFieldArgs, `fits),
  (`Gabbro.Core.Ast.Surface.AssignFieldArgs, `visible),
  (`Gabbro.Core.Ast.Surface.AssignFieldArgs, `writable),
  (`Gabbro.Core.Ast.Surface.AssignFieldArgs, `written),
  -- BindDirectArgs: SurfaceForms.lean:144 belegt beide Felder mit dem bindDirect-Zeugen.
  (`Gabbro.Core.Ast.Surface.BindDirectArgs, `ordinary),
  (`Gabbro.Core.Ast.Surface.BindDirectArgs, `valid),
  -- BoundedWhileArgs: SurfaceForms.lean:181 belegt beide Felder mit dem boundedWhile-Zeugen.
  (`Gabbro.Core.Ast.Surface.BoundedWhileArgs, `nonnegative),
  (`Gabbro.Core.Ast.Surface.BoundedWhileArgs, `staticBound),
  -- ConstantArgs: SurfaceForms.lean:290 belegt alle Felder mit dem constant-Zeugen.
  (`Gabbro.Core.Ast.Surface.ConstantArgs, `fits),
  (`Gabbro.Core.Ast.Surface.ConstantArgs, `ordinary),
  (`Gabbro.Core.Ast.Surface.ConstantArgs, `staticValue),
  (`Gabbro.Core.Ast.Surface.ConstantArgs, `valid),
  -- DivisionArgs: Expression/Surface.lean:267 belegt nonzero mit dem Divisions-Zeugen.
  (`Gabbro.Core.Ast.Surface.DivisionArgs, `nonzero),
  -- ForRangeArgs: SurfaceForms.lean:222 belegt beide Felder mit dem forRange-Zeugen.
  (`Gabbro.Core.Ast.Surface.ForRangeArgs, `ordinary),
  (`Gabbro.Core.Ast.Surface.ForRangeArgs, `staticBounds),
  -- FunctionArgs: SurfaceForms.lean:333 belegt alle Felder mit dem function-Zeugen.
  (`Gabbro.Core.Ast.Surface.FunctionArgs, `distinct),
  (`Gabbro.Core.Ast.Surface.FunctionArgs, `ordinary),
  (`Gabbro.Core.Ast.Surface.FunctionArgs, `returns),
  (`Gabbro.Core.Ast.Surface.FunctionArgs, `valid),
  -- LetArgs: Surface.lean:143 belegt ordinary mit dem letValue-Zeugen.
  (`Gabbro.Core.Ast.Surface.LetArgs, `ordinary),
  -- MutableLocalArgs: SurfaceForms.lean:71 belegt alle Felder mit dem mutableLocal-Zeugen.
  (`Gabbro.Core.Ast.Surface.MutableLocalArgs, `fits),
  (`Gabbro.Core.Ast.Surface.MutableLocalArgs, `ordinary),
  (`Gabbro.Core.Ast.Surface.MutableLocalArgs, `valid),
  -- MutableValueArgs: MutableValueProofs.lean:97 belegt ordinary mit dem Ableitungs-Zeugen.
  (`Gabbro.Core.Ast.Surface.MutableValueArgs, `ordinary),
  -- RecordDeclArgs: RecordDeclProofs.lean:102 belegt beide Felder mit dem leeren Record-Zeugen.
  (`Gabbro.Core.Ast.Surface.RecordDeclArgs, `distinct),
  (`Gabbro.Core.Ast.Surface.RecordDeclArgs, `valid),
  -- RecordFieldArgs: RecordFieldProofs.lean:246 belegt written mit dem Singleton-Record-Zeugen.
  (`Gabbro.Core.Ast.Surface.RecordFieldArgs, `written),
  -- RecordValueArgs: ConstructionProofs.lean:184 belegt fits mit dem Beispiel-Record-Wert.
  (`Gabbro.Core.Ast.Surface.RecordValueArgs, `fits),
  -- DirectCall: SurfaceForms.lean:101 belegt ordinary mit dem directCall-Zeugen.
  (`Gabbro.Core.Ast.DirectCall, `ordinary),
  -- EffectClause: GroupProofs.lean:448 belegt checked mit dem Klausel-Beweis aus der Auflösung.
  (`Gabbro.Core.Ast.EffectClause, `checked),
  -- EffectGroupDeclaration: GroupProofs.lean:422 belegt checked mit dem Gruppen-Beweis aus der Auflösung.
  (`Gabbro.Core.Ast.EffectGroupDeclaration, `checked),
  -- Parameter: CarrierIndexProofs.lean:217 belegt beide Felder mit dem Index-Parameter-Zeugen.
  (`Gabbro.Core.Ast.Parameter, `ordinary),
  (`Gabbro.Core.Ast.Parameter, `valid),
  -- ReturnArgs: BatchSurface.lean:62 belegt fits mit dem returnValue-Zeugen.
  (`Gabbro.Core.Ast.Surface.ReturnArgs, `fits),
  -- ReturnVoidArgs: ProgramObligations.lean:95 belegt declared mit dem returnVoid-Zeugen.
  (`Gabbro.Core.Ast.Surface.ReturnVoidArgs, `declared),
  -- Rule: Surface.lean:40 belegt production mit jeder konkreten Produktion.
  (`Gabbro.Core.Ast.Surface.Rule, `production),
  -- Rule.Entry: Surface.lean:53 belegt alle Felder mit dem literalen Eintrag als Muster.
  (`Gabbro.Core.Ast.Surface.Rule.Entry, `erfuellbar),
  (`Gabbro.Core.Ast.Surface.Rule.Entry, `prints),
  (`Gabbro.Core.Ast.Surface.Rule.Entry, `reads),
  -- TaggedDeclArgs: TaggedDeclProofs.lean:146 belegt beide Felder mit dem Ableitungs-Zeugen.
  (`Gabbro.Core.Ast.Surface.TaggedDeclArgs, `distinct),
  (`Gabbro.Core.Ast.Surface.TaggedDeclArgs, `valid),
  -- TupleBindArgs: TupleBindProofs.lean:151 belegt checked mit dem Tupelbindungs-Zeugen.
  (`Gabbro.Core.Ast.Surface.TupleBindArgs, `checked),
  -- VariableArgs: LeafObligations.lean:153 belegt beide Felder mit dem Variablen-Zeugen.
  (`Gabbro.Core.Ast.Surface.VariableArgs, `ordinary),
  (`Gabbro.Core.Ast.Surface.VariableArgs, `visible),
  -- VariantValueArgs: VariantValueProofs.lean:210 belegt alle Felder mit dem Varianten-Zeugen.
  (`Gabbro.Core.Ast.Surface.VariantValueArgs, `available),
  (`Gabbro.Core.Ast.Surface.VariantValueArgs, `ordinary),
  (`Gabbro.Core.Ast.Surface.VariantValueArgs, `written),
  -- RecordArguments: ConstructionProofs.lean:191 belegt alle Felder mit dem Beispiel-Record.
  (`Gabbro.Core.Ast.RecordArguments, `arity),
  (`Gabbro.Core.Ast.RecordArguments, `distinct),
  (`Gabbro.Core.Ast.RecordArguments, `label),
  -- RecordRef: ConstructionProofs.lean:187 belegt alle Felder mit der Beispiel-Referenz.
  (`Gabbro.Core.Ast.RecordRef, `distinct),
  (`Gabbro.Core.Ast.RecordRef, `ordinary),
  (`Gabbro.Core.Ast.RecordRef, `shape),
  (`Gabbro.Core.Ast.RecordRef, `spelled),
  (`Gabbro.Core.Ast.RecordRef, `visible),
  -- VariantRef: VariantValueProofs.lean:206 belegt alle Felder mit der Beispiel-Referenz.
  (`Gabbro.Core.Ast.VariantRef, `distinct),
  (`Gabbro.Core.Ast.VariantRef, `shape),
  (`Gabbro.Core.Ast.VariantRef, `spelled),
  (`Gabbro.Core.Ast.VariantRef, `visible),
  -- OptionLetArgs: ConstructProofs.lean:285 belegt beide Felder mit dem Options-Zeugen.
  (`Gabbro.Core.Ast.Semantik.OptionLetArgs, `ordinary),
  (`Gabbro.Core.Ast.Semantik.OptionLetArgs, `resolved),
  -- OptionReturnArgs: ConstructProofs.lean:310 belegt declared mit dem Options-Rückgabe-Zeugen.
  (`Gabbro.Core.Ast.Semantik.OptionReturnArgs, `declared),
  -- OptionTestArgs: TestProofs.lean:269 belegt beide Felder mit dem Options-Test-Zeugen.
  (`Gabbro.Core.Ast.Semantik.OptionTestArgs, `ordinary),
  (`Gabbro.Core.Ast.Semantik.OptionTestArgs, `visible),
  -- Quellform: Default-Beweis in der Struktur (Ast/Semantik/Quellform.lean:23) belegt privat für jede Form.
  (`Gabbro.Core.Ast.Semantik.Quellform, `privat),
  -- RegionEntryArgs: RegionSatisfiability.lean:37 belegt alle Felder mit dem Regions-Eintrags-Zeugen.
  (`Gabbro.Core.Ast.Semantik.RegionEntryArgs, `entryName),
  (`Gabbro.Core.Ast.Semantik.RegionEntryArgs, `ordinary),
  (`Gabbro.Core.Ast.Semantik.RegionEntryArgs, `ordinaryRegion),
  -- Eingebettet: Befehl.eingebettet (Verfeinerung/Formen/Familie.lean:44) belegt alle Felder mit rfl.
  (`Gabbro.Core.Ast.Semantik.Schrittform.Eingebettet, `griff),
  (`Gabbro.Core.Ast.Semantik.Schrittform.Eingebettet, `objekt),
  (`Gabbro.Core.Ast.Semantik.Schrittform.Eingebettet, `regel)]

end Gabbro.Core.Waechter
