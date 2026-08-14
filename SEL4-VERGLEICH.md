# Was eine seL4-Verifikation NEBEN dem Logikbeweis braucht — und was Gabbro dafuer hat

**2026-08-14.** Gabbros Zusage lautet „alles ausser dem Logikbeweis faellt durch Konstruktion".
**Dann muss man wissen, was „alles ausser" bei seL4 wirklich ist** — sonst vergleicht man einen
Entwurf mit einer Vorstellung.

> **Vorbehalt, und er gilt fuer die ganze Datei:** die seL4-Angaben sind **aus dem Gedaechtnis**.
> Der Ordner hat dieselbe Klasse schon einmal gebraucht (die 20:1-Aufteilung) und sie wurde
> bestaetigt — **das ist kein Beleg fuer diese hier.** Wo eine Zahl steht, steht sie als
> Groessenordnung.

---

## Die sechs Posten neben der Logik

| # | Posten | was er bei seL4 ist | was Gabbro dafuer hat |
|---|---|---|---|
| **1** | **Maschinenmodell** | ein eigenes Modell in Isabelle: Register, Speicher, MMU; nicht Modelliertes ist **axiomatisiert** | die **Axiomschicht**, ~130 Namen fuer zwei Architekturen, **ratschenfaehig** und im Erzeugnis. `port` hat sie gerade um 70 Fundstellen entlastet |
| **2** | **C-Semantik** | ein **C-Parser** samt Formalisierung eines C-Ausschnitts (Simpl/AutoCorres) — ein Teilprojekt fuer sich | **nichts Gleichwertiges.** Gabbro ersetzt es durch „eine Emission, syntaxgesteuert, nicht optimierend" — **und diese Entsprechung ist behauptet**, nicht formalisiert |
| **3** | **Die Annahmenliste** | ausdruecklich gefuehrt: Assembler unbewiesen, Bootcode zunaechst aussen vor, Hardware wie modelliert, DMA eingeschraenkt, **verifizierte Konfiguration einkernig** | **das Pflichtenmanifest** — dieselbe Sache, aber **maschinenlesbar, mit Klassen und Ratsche ueber Namen**. Hier ist Gabbro nicht schlechter, sondern schaerfer |
| **4** | **Binaerverifikation** | Uebersetzungsvalidierung C ⟶ Maschinencode (graph-refine/SydTV), damit der Uebersetzer nicht der Riss ist. **Assembler und volatile sind ausgenommen** | **steht unter „Spaeter"**, ist aber **ermoeglicht** — derselbe Zeugnispruefer liefert benannten C-Ausschnitt und erhaltene Funktionsgrenzen. **Nur laege der ganze `device`-Zweig ausserhalb** |
| **5** | **Eigenschaften ueber der Korrektheit** | Integritaet, Vertraulichkeit, Autoritaetsbeschraenkung — **eigene Saetze mit eigenen Spezifikationen** | nicht adressiert. Gabbro liefert die Huelle, **nicht die Sicherheitsaussage darueber** |
| **6** | **Der Unterhalt** | **der Posten, den niemand mitzaehlt** — s. u. |

---

## Posten 6: der Unterhalt, und hier liegt Gabbros staerkstes Argument

**Die eigentlichen Kosten einer Gold-Verifikation sind nicht der erste Beweis, sondern dass er
gepflegt werden muss.** Jede Kerneländerung bricht Beweise; die Beweisbasis (Groessenordnung
200 000 Zeilen) ist ein **dauerhafter** Posten, kein einmaliger. Deshalb ist verifizierter Code in
der Praxis Code, den man **nicht mehr gern anfasst**.

> **Gabbros Antwort darauf ist strukturell und wurde bisher nirgends ausgesprochen:**
> **faellt Klempnerei durch Konstruktion, kann eine Codeaenderung sie nicht brechen.** Ein neuer
> Index, eine neue Subtraktion, eine neue Sperrnahme erzeugen **keine** neue Beweisarbeit — sie
> uebersetzen oder nicht. **Der Unterhaltsaufwand skaliert mit dem LOGIK-Anteil, nicht mit der
> Codegroesse.**

**Das ist die eine Achse, auf der Gabbro seL4 nicht nachbaut, sondern schlaegt** — und sie steht
und faellt mit derselben ungezaehlten Zahl: **wie gross ist der Logik-Anteil wirklich?**

---

## Wo Gabbro schlechter ist, ohne Beschoenigung

1. **Keine C-Semantik.** seL4 hat eine Formalisierung; Gabbro hat eine **Zusage ueber die eigene
   Absenkung**. Das ist Posten 2, und er ist der groesste Rueckstand.
2. **Kein Beweis ueber den Pruefer.** seL4s Beweise laufen in Isabelle, dessen Kern klein und
   geprueft ist. Gabbros Pruefer ist **unverifiziertes Rust**, und alles haengt an ihm.
3. **Keine Sicherheitsaussagen.** Integritaet und Informationsfluss sind bei seL4 **eigene
   Saetze**; Gabbro liefert sie nicht und behauptet es auch nicht.
4. **Reife.** seL4s Kette ist gefahren, mehrfach, auf echter Hardware. Gabbro hat keine Zeile
   Uebersetzer.

---

## Was der Vergleich fuer die harten Zusagen sagt

[`HARTE-ZUSAGEN.md`](HARTE-ZUSAGEN.md) macht Induktion automatisch statt heuristisch — das
adressiert **den Beweisteil**, also genau den Posten, den seL4 mit 200 000 Zeilen bezahlt.

**Der Vergleich zeigt aber, dass das die kleinere Haelfte ist:** von den sechs Posten neben der
Logik beruehrt die Schrittzusage **einen** (den Beweisaufwand ueber deklarierten Strukturen).
**Posten 2 und 5 bleiben unberuehrt, Posten 4 steht unter „Spaeter", Posten 3 ist gut geloest,
Posten 1 ist zur Haelfte da.**

- [ ] **Die ehrliche Folge fuer den Plan:** die naechste Arbeit ist **nicht** eine weitere
      Verschaerfung der Beweisautomatik, sondern **Posten 2** — was heisst „welches C", und wie
      wird die Absenkung von einer Zusage zu einer pruefbaren Aussage? Das steht in
      [`BEWEISER.md`](BEWEISER.md) als L4 und ist der einzige Posten, an dem Gabbro **strukturell**
      hinter seL4 zurueckliegt statt nur an Reife.
