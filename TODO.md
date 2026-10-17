# Offen — was dem Projekt noch fehlt

*Updated 2026-10-17 for memory, stack, `own`/alias separation and model-based LLVM coverage. Enthält NUR Offenes aus fünf Gebieten:
LLVM-Backend, Lean-Modell, Prüfer, Übersetzungsvalidierung, Heap. IDs (`Oxx`) sind
stabil — Kommentare im Baum, die `OFFEN Oxx` nennen, meinen diese Abschnitte
(Historie in Git). Geschlossenes und
Entferntes steht im Anhang, je mit einer Zeile Grund.*

## 1. Heap and stack (updated 2026-10-17)

- **Built:** pressure-sampled unbounded arenas, slot release, external free-list
  links supporting small elements, per-chunk live counts and physical return of
  empty anonymous payload pages. Whole-arena reset clears counts and returns
  used payload pages. Virtual reservations/access rights and the committed
  prefix stay intact; best-effort page discard requires no decommit bitmap.
- **Built:** all direct/compatible indirect recursive cycles use a loop
  dispatcher and explicit growable continuation storage. Pure tail cycles keep
  their jump-only path. Continuation chunks are released on unwind; allocation
  failure is an explicit trap. This avoids recursion-dependent native stack
  growth, not the need for RAM to store non-tail continuations.
- **Built:** checked static range zeroing and optional whole-page return through
  declared program bindings; guarded per-invocation thread stacks, group spawn
  before join, kernel-exit completion and stack unmapping after join.
- **Still open:** `free` across function boundaries, aliases outside the tracked
  ownership discipline, complete `ArenaForm`/`DynForm` export and the G form of
  the newer memory statements. No checker refusal or source obligation was
  relaxed. CPU/final-byte refinement remains section 5 work.
- **Evidence:** `dokumente/LLVM-BACKEND.md`. Coverage is the actual Lean
  constructor/field register, checked by
  `python3 instrumente/pruefe-llvm-modelldeckung.py`; examples never define it.

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
- **O27 (source forms without complete G export).** The source-to-G exporter
  remains partial, notably float, byte-pointer/string and dynamic-arena forms.
  A working LLVM lowering is not a Lean judgment. Track the constructor/field
  boundaries in `dokumente/llvm-modelldeckung.tsv`, not counts of examples.
- **O28-Rest (Verbund).** Spec-Diff ohne unabhängige Review-Runde; keine
  semantische Äquivalenz/Verfeinerung bei Verträgen (Normalform-Bäume);
  kein Zertifikat für verlinkte Programme; C-Linkschritt ist Sache der
  Validierung (§5).
- **O37 (Regionen in G).** Keine Byte-Zeiger im Modell (`Ty.ptr` ist
  Träger-Fähigkeit); nichts gibt eine Region frei (kein Eigentums-Schluss
  am Tor-Parameter); Gabbro-Rümpfe reichen keine Ausdehnung weiter
  (nur fremde `ensures … <= lenof(result)` trägt).

## 3. Prüfer

- **Wächter-Reste (vier Wächter seit 2026-10-17).** `bruecke/` wird nicht gemessen (sein `lake build`
  scheitert am fehlenden `mathlib`-Eintrag); der baumweite `gabbro prove`-Lauf und der E1-Vergleich
  (Pflichten-Manifest) hängen in keinem Wächter; der Mutationslauf über den Prüfer ist ersatzlos
  gestrichen; 8 600 deutsche Kommentarzeilen im Prüfer sind nicht bewacht. Details:
  `dokumente/WERKZEUGKASTEN.md`.

- **O11 (hüterlose Invariante).** Eine `table`/`group`-Invariante, die keine
  Funktion `maintains`, wird von NICHTS gebucht (`N275`–`N277` prüfen nur
  verankerte).
- **Alias / `own` (gebaut 2026-10-17, Reste offen).** `R014` (Fehler) und `R015`
  (Hinweis) trennen Zeigerwurzeln an Rufgrenzen; Lean hat `ParamGetrennt` und
  `ObjGetrennt` (Objekte unterhalb einer Tabelle) samt Brücke zu `R014`; LLVM setzt
  `noalias` an interne schreibbare Zeigerparameter. Papier: `dokumente/A1-OWN-PAPER.md`.
  Offen: Records über Byte-Puffern (Bereichsobjekte im Modell, `LG005`/`LG001`);
  die vier Brücken-Hypothesen (`ParamVerschieden`, `RechteOk`, `HerkunftTreu`,
  `FrischNeu` nur für den Modell-Allokator) und der `let`-Lauf des Prüfers in Lean;
  `R004`/`R007` als Sonderfälle von `R014`; Mutationslauf (gestrichen mit den 80 Wächtern, kein Ersatz);
  `noalias` ist kein Lean-Urteil (O27).
- **O26-Rest (fremde Sperrprimitive).** Eigene Primitive geprüft (`N481`–`N483`);
  fremde bleiben angenommen (schwaches Gedächtnis nimmt acquire/release an).

## 4. LLVM-Backend

Volltabelle in `dokumente/LLVM-BACKEND.md` §5. Kurzform:

- **O22 — group execution and stack lifecycle built 2026-10-17.** Every
  invocation owns a guarded mapping and completion word. All roots start before
  any join; kernel `clear_child_tid` ends the join after actual exit, then the
  mapping is released. Trampoline assembly is confined to the stack switch.
  Runtime syscall numbers still belong to the Linux profile; OS-neutral
  bindings/profiles and the target-to-GX proof remain open.
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
