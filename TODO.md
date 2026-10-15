# Offen — was dem Projekt noch fehlt

*Stand 2026-10-15, am Code gemessen. Enthält NUR Offenes aus fünf Gebieten:
LLVM-Backend, Lean-Modell, Prüfer, Übersetzungsvalidierung, Heap. IDs (`Oxx`) sind
stabil — Kommentare im Baum, die `OFFEN Oxx` nennen, meinen diese Abschnitte
(`TODO.md` selbst ist gelöscht, Historie in Git). Geschlossenes und
Entferntes steht im Anhang, je mit einer Zeile Grund.*

## 1. Heap — unbegrenzt, aber mit Grenzen

- **A (Freiliste als Muster) — gebaut.** `beispiele/27-freiliste.gab`,
  `58-freiliste-zwei-formen.gab`: belegen/ablegen über `naechst`-Kette, keine
  Sprachänderung. Typisierte Fächer haben keine Fragmentierung (ein Elementtyp
  je Halde) — frei heißt ein Belegt-Bit je Slot.
- **B (unbegrenzt mit Abtastung) — Kern gebaut 2026-10-15, `free` offen.**
  Gebaut: `druckfrage P unter B` an der Arena (SYNTAX.md §9.1) schaltet die
  UNBEGRENZTE Form ein (ohne sie ist ohne `max` die Decke `hi` — statisch).
  Der Erzeuger reserviert einmal Adressraum (`mmap(PROT_NONE)`, kein RAM),
  committet je 1 MiB bei Bedarf (`mprotect`) und fragt VOR jedem Commit die
  nullstellige Frage `P` nach freien Bytes; unter der Nutzer-Schwelle `B`
  (z.B. `unter 1048576` — 1 MiB) läuft der `else`-Zweig (OOM-Pfad). EIN Ruf
  je MiB, null im Schnellpfad (`bereit >= bedarf` fragt gar nicht) — Abtasten
  kostet keine Performance. Freistehend misst `P` selbst (kein Systemruf im
  Erzeuger). Prüfer: `N584` (Frage nennt nichts), `N585` (falsche Form,
  keine fällige Schwelle); Erzeuger: drittes sanktioniertes `inttoptr`
  (Laufzeit-Basis); Beispiel `1160`, Proben `gift/1436`–`1438`, LLVM-Test
  `abtastung_vor_commit`. Offen: `free` mit linearer Fähigkeit
  (Use-after-free — Nähe O37: nichts gibt eine Region frei), Lean-Form
  für Freigabe/Generationen.
- **C (Rückgabe an den Kern) — offen, nach B.** Leere Chunks per `madvise`
  zurückgeben; Nutzer-Tor wie bei B, kein Erzeuger-Wissen über das System.

## 2. Lean-Modell

- **O1-Rest (Pflichten jenseits der Maschine).** L50/L52 trägt das Bein `folge`,
  L24 die Invarianten-Beine, L34 steht als Existenz mit Zeuge. Offen: der Name
  von `breaking` im G-Rest (Markenschicht + Re-Beweis aller satzweisen Sätze),
  die Block-Wiederherstellungspflicht in (b), Axiom-/Register-Ereignisse im
  Ruf-Log, pfadsensitives `ende` (je Rückgabestelle), ein Ordnungsfeld in
  `Einheit` vom Exporteur gefüllt.
- **O4 (`cdt_wohlgeformt` bei freiem Slot).** Wartet auf O5 (Geschwister-Konsistenz);
  `delete_leaf` gilt nur bedingt, `revoke` erbt die Bedingung.
- **O5 (Geschwister-Konsistenz als Tabellen-Invarianten-Demand).** Indexieren
  DURCH die Option (`slots[s.next_sibling]`) blockiert; `requires` je Rufstelle
  ist Ersatz, kein Supply-once.
- **O6 (DEMAND 3 als schrankenloser Rangzeuge).** Geht für die Widerlegung;
  die Beweis-Richtung (`unsat`) über der Rangform plus vier ungezogene
  Erreichbarkeits-Zeilen bleiben bei der Demand.
- **O14 (Arena-Ketten: zwei Statement-Formen ohne Form).** Spezifikation und
  Exporteur haben die Form; zwei Statement-Gestalten schließen keine Kette.
- **O19-Rest (Handler und Kerne).** `Einheit` nennt keinen Handler, G hat keine
  Kerne (`kern`, `H`, Rufgraphen, Maskendisziplin sind Hypothesen des Beins);
  C realisiert kein Maskieren (nichts für die Validierungskette);
  Re-Entry und Handler-auf-Handler draußen; `H102` feuert nur auf `via idt`.
- **O20 (Arenen unter Nebenläufigkeit).** Generationen und Commit-Decke nehmen
  einen Kontrollfaden und einmal betretene Wurzeln an.
- **O21 (`child` ohne Modell).** Der Kind-Faden existiert im Prüfer; sein Code
  zwischen Torruf und Region ist für das Kind ungeprüft.
- **O23 (Tor-Vorbedingungen nicht im Ziel).** NUL-Pfad und Rahmenlänge sind
  benannt, nicht modelliert.
- **O24 (Strings geprüft, nicht dargestellt).** NUL, `max`-Decke, Aggregate.
- **O27 (Programme ohne Lean-Urteil).** Neu gemessen 2026-10-15: **138 von 166**
  `beispiele/*.gab` exportieren kein G-Programm (`gabbro lean-g` verweigert,
  meist `LG004`). Größter gezählter Brocken.
- **O28-Rest (Verbund).** Spec-Diff ohne unabhängige Review-Runde; keine
  semantische Äquivalenz/Verfeinerung bei Verträgen (Normalform-Bäume);
  kein Zertifikat für verlinkte Programme; C-Linkschritt ist Sache der
  Validierung (§5).
- **O37 (Regionen in G).** Keine Byte-Zeiger im Modell (`Ty.ptr` ist
  Träger-Fähigkeit); nichts gibt eine Region frei (kein Eigentums-Schluss
  am Tor-Parameter); Gabbro-Rümpfe reichen keine Ausdehnung weiter
  (nur fremde `ensures … <= lenof(result)` trägt).

## 3. Prüfer

- **O11 (hüterlose Invariante).** Eine `table`/`group`-Invariante, die keine
  Funktion `maintains`, wird von NICHTS gebucht (`N275`–`N277` prüfen nur
  verankerte).
- **Alias (Entscheidung ausstehend).** Zwei Zeiger auf ein Objekt bleiben
  ununterscheidbar (M3, Sperren-Rest). Schließen heißt: `own` an Rufgrenzen
  prüfen oder 113 Zeilen Zeremonie schreiben — Richtungsentscheidung, kein Bau.
- **O26-Rest (fremde Sperrprimitive).** Eigene Primitive geprüft (`N481`–`N483`);
  fremde bleiben angenommen (schwaches Gedächtnis nimmt acquire/release an).

## 4. LLVM-Backend

Volltabelle in `dokumente/LLVM-MODELLSTAND.md` §5. Kurzform:

- **O22 (`start` läuft sequentiell).** Senkt als direkte Rufe — keine echten
  Fäden. Schärfste Kante: läuft, aber nicht nebenläufig.
- **`entries` (12 Stellen).** Hardware-Dispatch ohne Modell — benannt verweigert.
- **Stapel-Tore + `child` (12).** `clone`-Trampolin fehlt.
- **`publish` mit Nutzlast (11).** OFFEN O25 — vom Zielsatz nicht gedeckt.
- **Geteilte Sperren (3), Bibliotheksrufe (3).** Eigenes Primitiv / Nutzlast-Modell fehlt.
- **O40-Rest (Emitter-Namen).** Prüfer-Hälfte gebaut (`N042`); modulqualifizierte
  Namen fehlen beiden Emittern (LLVM mangelt `m_` nur bei Kollision).

## 5. Übersetzungsvalidierung — kommt VIEL später

Voraussetzungskette, in dieser Reihenfolge; nichts davon ist O27-Arbeit:

- **Vollständiges Lean-Modell einer CPU.** Ohne es keine Verfeinerung —
  das ist der lange Pol (ARM-PLAN: Sail-Arm plus Mehrkern-Modell), nicht O27.
- **Und mehr:** Brücke je Zugriff (Ziel → W/GX-Simulation pro Zugriff),
  Tor- + Eintritts-Lemmata je Ziel (rohe Anweisung, `_start` mit Stapel,
  Zustand, Austritt/`never`), O28-Linkschluss, O26-fremde Ordnungen.
- **Automatisch für alle Programme.** Kein Schritt je Programm von Hand —
  deshalb ist die Kette teurer als O27, nicht billiger: O27 erweitert die
  Urteil-Menge Programm für Programm, die Validierung muss danach für ALLE
  ohne Zutun laufen.

## Anhang — geschlossen oder entfernt (ID → Grund)

O2 zurückgezogen (Falsifikatoren ohne Schwelle); O3 gebaut; O7 gebaut;
O8 gebaut (Lane 167); O9 gebaut; O12 Einzelprogramm, kein Modellfall;
O13 gebaut; O15/O16 bepreist und ABGELEHNT (null Korpusnutzen);
O18 gebaut (F10); O25 geschlossen (Rely IST das Ziel, `gabbro_ziel`);
O10 Messschicht, kein Gebietsgegenstand; O29 außerhalb des Umfangs (Simon);
O30 überholt (Rust-Backend + Lean-Validator statt Selbsthosting);
O31 gebaut (Reste: Build/Hardware, nicht Gebietsgegenstand);
O32 Hardware/Laufzeit, kein Gebietsgegenstand; O33 Prozessbuchhaltung;
O34/O35/O36/O38 gebaut; O39 Kernelmodul-Welt (Zählung: `N574`–`N577` gebaut,
Unload-Fenster Hardware).
