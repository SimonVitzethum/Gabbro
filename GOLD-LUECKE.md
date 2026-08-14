# Was Gabbro fuer GOLD fehlt — ausser dem Logikbeweis und der Ausdruckskraft

**2026-08-14.** Zwei Posten sind ausdruecklich **nicht** gemeint: der **Logikbeweis** (den schreibt
der Programmierer, in jeder Sprache) und die **Ausdruckskraft** (dass alle Programme, vor allem
Caprock, hineinpassen — das ist der laufende Rueckstand, s. `FERTIG.md` A3/A5/A6/A7).

**Was bleibt, wenn man beides wegnimmt?** Die Antwort ist unbequem und kurz:

> **Gabbro erzeugt Beweispflichten. Es gibt nichts, was sie erfuellt, und nichts, WORUEBER sie
> sprechen.**

Eine Beweispflicht braucht dreierlei: eine **Sprache**, ein **Modell**, in dem sie einen Sinn hat,
und einen **Beweiser**. Gabbro hat die Sprache — halb. Modell und Beweiser hat es gar nicht.

---

## L1 — Ein MASCHINENMODELL. **Entworfen am 2026-08-14** ([`MODELL.md`](MODELL.md)): 106 Axiome, ~130 Namen — und die 20 arch-neutralen Familien stehen bereits in `caprock-hal/*/cpu.rs`

### Die urspruengliche Fassung der Luecke

`axiom write_cr3(p: Pa) effects { writes tlb, writes active_table }` nennt eine **Wirkung auf einen
Zustand, den es nicht gibt.** Es gibt keinen `tlb`, keine `active_table`, keinen Maschinenzustand —
nur ein Wort in einer Wirkungsliste.

**Damit ist heute nicht sagbar, was ein privilegierter Befehl TUT**, nur dass er etwas anfasst. Ein
Gold-Beweis ueber einem Kernel ist aber im Kern ein Beweis **ueber Maschinenzustaenden**: „nach
`write_cr3(p)` uebersetzt jeder Zugriff nach der Tabelle bei `p`".

| | |
|---|---|
| **Was fehlt** | ein Zustandsraum (Register, TLB, Seitentabellen, Geraetezustand) und je Axiom eine **Uebergangsfunktion** darauf |
| **Warum es nicht „Logik" ist** | der Programmierer beweist ueber *seinem* Programm; das Maschinenmodell ist **unter** ihm und fuer alle Programme dasselbe |
| **Groessenordnung** | seL4 hat dafuer ein eigenes Modell in Isabelle. **Das ist kein Nebenposten, das ist ein Teilprojekt** |

---

## L2 — Ein SPEICHERMODELL. **Entschieden: RC11 ohne SC** — und die Wahl ist weniger tragend als hier unterstellt, weil Caprock nur RMW-Atomizitaet und Kohaerenz je Adresse beansprucht ([`MODELL.md`](MODELL.md))

### Die urspruengliche Fassung der Luecke

`atomic X : bool publishes { Y } release;` ist heute eine **Schreibweise ohne Bedeutung.** Was
`release` formal heisst — welche vorherigen Schreibvorgaenge fuer welchen `acquire` sichtbar werden
—, steht nirgends.

**Ohne Speichermodell ist ueber einen nebenlaeufigen Kernel nichts zu beweisen.** Und Caprock ist
nebenlaeufig: **2 231 `Ordering::`-Fundstellen**, davon 872 in einer einzigen Datei.

> **Das ist der Posten, den seL4 UMGANGEN hat**, nicht geloest — der seL4-Beweis ist im Kern
> sequenziell. Wer einen nebenlaeufigen Kernel gold beweisen will, betritt Gebiet, das auch die
> Vorbilder nicht betreten haben.

---

## L3 — **ENTSCHIEDEN 2026-08-14** ([`BEWEISER.md`](BEWEISER.md)): drei Arten Pflichten, Schablonen nach Isabelle, Programmpflichten ueber einen **Zertifikatspruefer**. **Und die Decke: Gold im seL4-Sinn ist auf diesem Weg nicht erreichbar**

### Die urspruengliche Fassung der Luecke

Der Typpruefer erledigt **Klempnerei**. Die **Logik**-Pflichten — `ensures`, `maintains`,
`invariant` — erzeugt Gabbro und **niemand entlaedt sie**.

Frueher stand dafuer „ein vorhandener Beweiser" (Verus/GNATprove/Frama-C). **Mit der Entscheidung
„Ausgabe ist C + iasm, Gabbro prueft selbst" ist dieser Weg zu** — und kein Ersatz benannt.

- [ ] **Zu entscheiden, und es ist eine Richtungsentscheidung:** eigener SMT-Anschluss (Z3/CVC5
      hinter `pred`), oder Ausgabe der Pflichten in ein vorhandenes System (Why3, Isabelle), oder
      doch eine zweite Emission. **Jede Antwort kostet etwas anderes**, und heute steht keine da.

---

## L4 — **ENTSCHIEDEN 2026-08-14**: es sind **drei** Absenkungen, nicht eine; Deckungszeugnis je Lauf; und der unbenannte Riss ist **welches C** ([`BEWEISER.md`](BEWEISER.md))

### Die urspruengliche Fassung der Luecke

„Syntaxgesteuert und nicht optimierend" ist die Bedingung, unter der die Verfeinerung billig wird.
**Nichts prueft sie.** Der Beweis liegt auf der Quelle, ausgeliefert wird das C — dass beide
dasselbe tun, ist **unbewiesen**, und genau diese Luecke schliesst seL4 mit Binaerverifikation
(eigenes Projekt, steht unter „Spaeter").

---

## L5 — Die eigene TCB ist nicht benennbar

Die Annahmenmenge im Erzeugnis („bewiesen unter A1…An") deckt die **Hardware**. Sie deckt **nicht**:

| | unverifiziert |
|---|---|
| der Gabbro-Typpruefer | ja |
| die Absenkung nach C | ja |
| die **Geistertheorie-Schablonen** (dort lebt die strukturelle Induktion) | ja |
| die Axiomschicht | ja, und sie ist die groesste Flaeche |

**Fuer Gold muss man sagen koennen, worauf man vertraut hat.** Heute kann man es fuer die Hardware
und fuer nichts sonst.

---

## L6 — Der ANFANG fehlt

Ein Beweis beginnt in einem Zustand. **Welcher Zustand gilt, bevor der erste Gabbro-Code laeuft?**
Die Bootphase ist als Marke da (`BootPhase`, linear, `boot_end` bildet `.boot` ab) — aber was
**gilt**, wenn sie verbraucht wird, steht nirgends. seL4 hat dafuer einen eigenen Initialisierungs-
beweis.

---

## Was ausdruecklich NICHT auf dieser Liste steht

* **Lebendigkeit und Fortschritt** — kein Mechanismus adressiert sie, und das ist eine
  ausgesprochene Grenze, kein Rueckstand.
* **Der Logikbeweis** — er ist der Punkt der Uebung, nicht ein Mangel.
* **Die Ausdruckskraft** — sie ist der laufende Rueckstand (19 haengende Klempnerei-Pflichten,
  kein Fragment im Ordner), aber sie war ausgenommen.

---

## Die ehrliche Bilanz

**Vier der sechs Posten (L1, L2, L3, L6) sind jeweils ein Teilprojekt**, kein offener Punkt. L2 ist
zusaetzlich einer, den die Vorbilder nicht geloest, sondern **umgangen** haben.

> **Damit ist die Frage „was fehlt fuer Gold" heute nicht mit einer Liste von Konstrukten zu
> beantworten.** Die Sprache kann die Pflichten **aufstellen**; sie hat weder das Modell, in dem
> sie einen Sinn haben, noch das Werkzeug, das sie entlaedt.
>
> **Das ist keine Widerlegung** — Gabbros Zusage war nie, den Beweis zu fuehren. Es ist die
> Feststellung, dass zwischen „erzeugt gute Beweispflichten" und „Gold" **nicht die letzte Meile
> liegt, sondern der Weg**.

- [ ] **Der billigste Schritt dagegen ist L3, und er ist eine Entscheidung, keine Arbeit:** wohin
      gehen die Logik-Pflichten? Solange das offen ist, ist jede weitere Grammatikregel eine Zeile
      fuer einen Empfaenger, den es nicht gibt.


---

## Was die Luecken KOSTEN — die Rechnung, zusammengezogen (2026-08-14)

**Die Frage ist nicht, ob es Luecken gibt, sondern in welcher Waehrung sie bezahlt werden.** Es
gibt genau zwei, und der Unterschied ist der ganze Entwurf:

| Waehrung | heisst | Beispiel |
|---|---|---|
| **Reichweite** | der Satz gilt **relativ zu benannten Annahmen**. Man weiss, was man bewiesen hat, und woran es haengt | „speichersicher **unter A1…An**" |
| **Gueltigkeit** | man weiss **nicht**, was man bewiesen hat, weil die Annahme unbenannt ist | ein `unsafe`-Block mit einem Kommentar |

> **Gabbros Entwurf besteht im Kern darin, jede Luecke von der zweiten Waehrung in die erste zu
> ueberfuehren.** Deshalb steht die Annahmenmenge **im Erzeugnis** und nicht in einer Fussnote.

### Die vier Luecken, einzeln beziffert

| Luecke | kostet | Zahl |
|---|---|---|
| **Axiomschicht** | Reichweite | **~130 Namen** fuer zwei Architekturen (A1–A25 gezaehlt, plus MSRs, CPUID-Blaetter, Geraeteannahmen). **Ratsche: darf nur fallen** — und `port` hat sie gerade um **70 Fundstellen** entlastet |
| **Speichermodell** | Reichweite | **2 Annahmen** (`c11_release_acquire_x86`/`_aarch64`), je mit Litmus-Falsifikator (MP/SB/LB) |
| **Vertrauensbasis der Werkzeuge** | Reichweite | **4 Posten**: Pruefer, Absenkung, **eine** `iasm`-Emissionsstelle, N Geistertheorie-Schablonen. Alle benannt, keiner geschaetzt |
| **Naht CPU ↔ Geraet** | Reichweite, **aber ohne Vorbild** | die Geraeteseite ist `assume` + Sonde, die **Verbindung** hat kein mechanisiertes Modell. Fuer die MMU gibt es Vorarbeit, fuer DMA nicht |
| **Lebendigkeit (D8)** | Reichweite | jede Fortschrittsaussage ist ein `progress`-**assume** mit Falsifikator (der Watchdog). **96 Endlosschleifen** gemessen; wieviele eine Fortschrittsaussage brauchen, ist ungezaehlt |
| **Funktionale Korrektheit ausserhalb der Struktur-Induktion** | **unbekannt** | **das ist die einzige Luecke ohne Zahl** — und genau sie ist die offene Messung |

### Der Satz, den ein fertiger Caprock-Beweis am Ende traegt

```
speichersicher    unter A1…An            n ≈ 130, gemessen, ratschenfaehig
rennfrei          unter c11_*            2, mit Litmus-Sonden
funktional offen  an O1…Ok               k UNBEKANNT
```

> **Die Kosten aller Luecken zusammen sind: `n` ist gross, aber gezaehlt und fallend — und `k` ist
> ungezaehlt.** Das ist die ganze Rechnung. **`k` zu kennen, ist der billigste Schritt, der den
> Ordner noch bewegt**, und er ist derselbe wie der Falsifikator der L3-Entscheidung: **die 17
> gemessenen Logik-Pflichten einordnen** in *durch Konstruktion · durch erzeugtes Induktionsschema ·
> von Hand*.

**Was die dritte Spalte kostet, laesst sich vorab sagen:** ein Rumpf, der von Hand bewiesen werden
muss, kostet nach der eigenen Messung **5 : 1** auf seinem Anteil. Bei 5 % des Kernels sind das
+0,25 auf die Kennzahl, bei 10 % +0,5. **Ein einziger unerwarteter Fall dort ist deshalb teurer als
alle 130 Axiome zusammen** — die kosten Reichweite, er kostet Arbeit.
