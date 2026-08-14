# Gabbro — die Beweisarchitektur

**Was bewiesen wird, wovon es spricht, wer es entlaedt, und wohin es abgesenkt wird.**
Zusammengezogen am 2026-08-14 aus sechs Einzeldateien — Text unveraendert.

---


---

# Das Kriterium — nur Logik

## Das Kriterium: **nur Logik beweisen, sonst nichts**

**2026-08-13.** Bis hierher war das Ziel eine **Zahl** (0,5 : 1). Sie ist ein Stellvertreter, und
Stellvertreter sind in diesem Projekt eine bezahlte Falle. Das eigentliche Kriterium ist eine
**Art**, nicht eine Menge:

> **Wer ein Gabbro-Programm beweist, beweist die LOGIK seines Programms — und sonst nichts.**
> Alles Uebrige faellt durch Konstruktion.

**Selbst 2 : 1 waere gut, wenn die gezaehlten Zeilen Logik sind.** Und 0,5 : 1 waere ein
Misserfolg, wenn darin Bereichspruefungen von Hand stecken. **Die Zahl wird damit vom Ziel zur
Diagnose.**

---

### Die Trennlinie, und sie muss scharf sein

> **Eine Pflicht ist KLEMPNEREI, wenn ihre Aussage nur die MASCHINE erwaehnt.
> Sie ist LOGIK, wenn sie die SACHE erwaehnt.**

| **Klempnerei — muss durch Konstruktion fallen** | **Logik — die schreibt man, in jeder Sprache** |
|---|---|
| ein Index liegt im Bereich | „der Baum bleibt ein Baum" |
| kein Ueber-/Unterlauf | „der Refcount ist die Zahl der Verweise" |
| kein Alias, keine Ausleihverletzung | „die Nachricht kam beim richtigen Thread an" |
| Rahmenbedingung: was **nicht** angefasst wird | „nach `revoke` hat `s` keine Abkoemmlinge" |
| die Sperre wird gehalten, die Ordnung stimmt | „ein erschoepfter Thread laeuft nicht" |
| kein Datenrennen | „die Faerbung trennt die Mandanten" |
| die Schleife endet, weil die Menge endlich ist | die Schleife endet, weil **der Algorithmus** fortschreitet |
| die Verfeinerung Quelle ↔ C | — |
| die Wohlgeformtheit einer Datenstruktur nach einer **erzeugten** Mutation | die **Formulierung** der Invariante |

**Der Grenzfall ist die Terminierung**, und die Regel entscheidet ihn: „endet, weil ueber eine
endliche Menge gelaufen wird" nennt nur die Maschine — **Klempnerei**. „Endet, weil der Scheduler
Fortschritt macht" nennt die Sache — **Logik**, und sie gehoert hingeschrieben.

---

### Was das mit den vorhandenen Messungen macht

**Die Zahlen bleiben, ihre Lesart aendert sich** — und beide Messungen sind daraufhin **noch nicht
aufgeschluesselt**. Das ist der naechste Papierschritt, nicht eine Behauptung:

| Messung | Zahl | **offen: welcher Anteil ist Logik?** |
|---|---|---|
| `delete_leaf` (Pruefer) | 3,6–6 : 1 ausgeschrieben | Kettenendlichkeit und Indexgrenzen sind **Klempnerei** und muessten fallen; `child_points_back` und `refcount_matches` sind **Formulierungen von Invarianten**, also Logik |
| `Endpoint::call` (Entwerfer) | 1,8–2,3 : 1 | `msg_copied` ist **Logik** und war an nichts gebunden (G2); die fehlende `locks`-Wirkung (G3) ist **Klempnerei**, die gar nicht haette anfallen duerfen |

- [ ] **Beide Messungen nach Logik/Klempnerei aufschluesseln.** Erst dann sagen sie etwas ueber das
      Kriterium. **Eine Zahl ohne diese Aufteilung ist ab jetzt kein Messwert.**

---

### Die Abbruchbedingung wird schaerfer, nicht weicher

Bisher: *„ueber 3 : 1"* — eine Zahl, messbar erst mit Uebersetzer.

**Jetzt:** *„es bleibt eine **benannte** Klempnerei-Pflicht, die der Programmierer von Hand
erledigen muss."*

Das ist **auf Papier je Konstrukt pruefbar** und damit ungleich billiger. Jede solche Stelle ist
entweder ein fehlendes Konstrukt oder das Ende der These.

**Zwei stehen heute schon da, beide aus den Papiertests:**

1. **`self.queues[p]` nach `31 - leading_zeros()`** (`caprock-sched/src/lib.rs:1996`) braucht die
   Datenstruktur-Invariante, um die Indexpflicht zu erledigen. **Reine Klempnerei** — und heute
   nicht durch Konstruktion gedeckt. Entweder M1 traegt sie, oder das Kriterium ist an dieser
   Stelle verletzt.
2. **Die Verfeinerung**, wenn die Absenkung nicht flach genug ist. Sie erwaehnt nie die Sache und
   ist damit per Definition Klempnerei — jedes Verfeinerungslemma ist ein Verstoss.

---

### Warum das Kriterium besser ist als die Zahl

* **Es ist per Konstrukt entscheidbar**, ohne Uebersetzer und ohne Korpus.
* **Es kann nicht durch kurze falsche Zusagen geschoent werden** — der Fund aus
  [`MESSUNGEN.md`](MESSUNGEN.md) verliert seine Wirkung, weil nicht mehr die **Menge**
  zaehlt, sondern die **Art**. Ein falsches `ensures` ist Logik, die falsch ist; es macht die Zahl
  nicht besser.
* **Es sagt, was Gabbro ist**, in einem Satz, den man widerlegen kann: *alles ausser der Logik
  faellt durch Konstruktion.* Wer eine Klempnerei-Pflicht findet, die haengen bleibt, hat den Satz
  an dieser Stelle widerlegt — und zugleich gesagt, welches Konstrukt fehlt.
* **Es macht die Zahl ehrlich:** 2 : 1 aus lauter Logik ist ein Erfolg. 0,5 : 1 mit
  handgeschriebenen Bereichspruefungen ist keiner.

---

### Was es nicht heisst

* **Die Trennlinie ist eine Entscheidung, kein Naturgesetz.** „Nennt nur die Maschine" ist scharf
  genug fuer die Faelle oben und wird an einem Grenzfall streiten muessen. **Der Streitfall gehoert
  dann hierher, nicht in eine Fussnote.**
* **Es ersetzt die Messung nicht, es ordnet sie.** Ohne Aufschluesselung bleibt jede Zahl das, was
  sie vorher war: ein Stellvertreter.


---

# Die Luecken zwischen Beweispflicht und Gold

## Was Gabbro fuer GOLD fehlt — ausser dem Logikbeweis und der Ausdruckskraft

**2026-08-14.** Zwei Posten sind ausdruecklich **nicht** gemeint: der **Logikbeweis** (den schreibt
der Programmierer, in jeder Sprache) und die **Ausdruckskraft** (dass alle Programme, vor allem
Caprock, hineinpassen — das ist der laufende Rueckstand, s. `PLAN.md` A3/A5/A6/A7).

**Was bleibt, wenn man beides wegnimmt?** Die Antwort ist unbequem und kurz:

> **Gabbro erzeugt Beweispflichten. Es gibt nichts, was sie erfuellt, und nichts, WORUEBER sie
> sprechen.**

Eine Beweispflicht braucht dreierlei: eine **Sprache**, ein **Modell**, in dem sie einen Sinn hat,
und einen **Beweiser**. Gabbro hat die Sprache — halb. Modell und Beweiser hat es gar nicht.

---

### L1 — Ein MASCHINENMODELL. **Entworfen am 2026-08-14** ([`BEWEIS.md`](BEWEIS.md)): 106 Axiome, ~130 Namen — und die 20 arch-neutralen Familien stehen bereits in `caprock-hal/*/cpu.rs`

#### Die urspruengliche Fassung der Luecke

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

### L2 — Ein SPEICHERMODELL. **Entschieden: RC11 ohne SC** — und die Wahl ist weniger tragend als hier unterstellt, weil Caprock nur RMW-Atomizitaet und Kohaerenz je Adresse beansprucht ([`BEWEIS.md`](BEWEIS.md))

#### Die urspruengliche Fassung der Luecke

`atomic X : bool publishes { Y } release;` ist heute eine **Schreibweise ohne Bedeutung.** Was
`release` formal heisst — welche vorherigen Schreibvorgaenge fuer welchen `acquire` sichtbar werden
—, steht nirgends.

**Ohne Speichermodell ist ueber einen nebenlaeufigen Kernel nichts zu beweisen.** Und Caprock ist
nebenlaeufig: **2 231 `Ordering::`-Fundstellen**, davon 872 in einer einzigen Datei.

> **Das ist der Posten, den seL4 UMGANGEN hat**, nicht geloest — der seL4-Beweis ist im Kern
> sequenziell. Wer einen nebenlaeufigen Kernel gold beweisen will, betritt Gebiet, das auch die
> Vorbilder nicht betreten haben.

---

### L3 — **ENTSCHIEDEN 2026-08-14** ([`BEWEIS.md`](BEWEIS.md)): drei Arten Pflichten, Schablonen nach Isabelle, Programmpflichten ueber einen **Zertifikatspruefer**. **Und die Decke: Gold im seL4-Sinn ist auf diesem Weg nicht erreichbar**

#### Die urspruengliche Fassung der Luecke

Der Typpruefer erledigt **Klempnerei**. Die **Logik**-Pflichten — `ensures`, `maintains`,
`invariant` — erzeugt Gabbro und **niemand entlaedt sie**.

Frueher stand dafuer „ein vorhandener Beweiser" (Verus/GNATprove/Frama-C). **Mit der Entscheidung
„Ausgabe ist C + iasm, Gabbro prueft selbst" ist dieser Weg zu** — und kein Ersatz benannt.

- [ ] **Zu entscheiden, und es ist eine Richtungsentscheidung:** eigener SMT-Anschluss (Z3/CVC5
      hinter `pred`), oder Ausgabe der Pflichten in ein vorhandenes System (Why3, Isabelle), oder
      doch eine zweite Emission. **Jede Antwort kostet etwas anderes**, und heute steht keine da.

---

### L4 — **ENTSCHIEDEN 2026-08-14**: es sind **drei** Absenkungen, nicht eine; Deckungszeugnis je Lauf; und der unbenannte Riss ist **welches C** ([`BEWEIS.md`](BEWEIS.md))

#### Die urspruengliche Fassung der Luecke

„Syntaxgesteuert und nicht optimierend" ist die Bedingung, unter der die Verfeinerung billig wird.
**Nichts prueft sie.** Der Beweis liegt auf der Quelle, ausgeliefert wird das C — dass beide
dasselbe tun, ist **unbewiesen**, und genau diese Luecke schliesst seL4 mit Binaerverifikation
(eigenes Projekt, steht unter „Spaeter").

---

### L5 — Die eigene TCB ist nicht benennbar

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

### L6 — Der ANFANG fehlt

Ein Beweis beginnt in einem Zustand. **Welcher Zustand gilt, bevor der erste Gabbro-Code laeuft?**
Die Bootphase ist als Marke da (`BootPhase`, linear, `boot_end` bildet `.boot` ab) — aber was
**gilt**, wenn sie verbraucht wird, steht nirgends. seL4 hat dafuer einen eigenen Initialisierungs-
beweis.

---

### Was ausdruecklich NICHT auf dieser Liste steht

* **Lebendigkeit und Fortschritt** — kein Mechanismus adressiert sie, und das ist eine
  ausgesprochene Grenze, kein Rueckstand.
* **Der Logikbeweis** — er ist der Punkt der Uebung, nicht ein Mangel.
* **Die Ausdruckskraft** — sie ist der laufende Rueckstand (19 haengende Klempnerei-Pflichten,
  kein Fragment im Ordner), aber sie war ausgenommen.

---

### Die ehrliche Bilanz

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

### Was die Luecken KOSTEN — die Rechnung, zusammengezogen (2026-08-14)

**Die Frage ist nicht, ob es Luecken gibt, sondern in welcher Waehrung sie bezahlt werden.** Es
gibt genau zwei, und der Unterschied ist der ganze Entwurf:

| Waehrung | heisst | Beispiel |
|---|---|---|
| **Reichweite** | der Satz gilt **relativ zu benannten Annahmen**. Man weiss, was man bewiesen hat, und woran es haengt | „speichersicher **unter A1…An**" |
| **Gueltigkeit** | man weiss **nicht**, was man bewiesen hat, weil die Annahme unbenannt ist | ein `unsafe`-Block mit einem Kommentar |

> **Gabbros Entwurf besteht im Kern darin, jede Luecke von der zweiten Waehrung in die erste zu
> ueberfuehren.** Deshalb steht die Annahmenmenge **im Erzeugnis** und nicht in einer Fussnote.

#### Die vier Luecken, einzeln beziffert

| Luecke | kostet | Zahl |
|---|---|---|
| **Axiomschicht** | Reichweite | **~130 Namen** fuer zwei Architekturen (A1–A25 gezaehlt, plus MSRs, CPUID-Blaetter, Geraeteannahmen). **Ratsche: darf nur fallen** — und `port` hat sie gerade um **70 Fundstellen** entlastet |
| **Speichermodell** | Reichweite | **2 Annahmen** (`c11_release_acquire_x86`/`_aarch64`), je mit Litmus-Falsifikator (MP/SB/LB) |
| **Vertrauensbasis der Werkzeuge** | Reichweite | **4 Posten**: Pruefer, Absenkung, **eine** `iasm`-Emissionsstelle, N Geistertheorie-Schablonen. Alle benannt, keiner geschaetzt |
| **Naht CPU ↔ Geraet** | Reichweite, **aber ohne Vorbild** | die Geraeteseite ist `assume` + Sonde, die **Verbindung** hat kein mechanisiertes Modell. Fuer die MMU gibt es Vorarbeit, fuer DMA nicht |
| **Lebendigkeit (D8)** | Reichweite | jede Fortschrittsaussage ist ein `progress`-**assume** mit Falsifikator (der Watchdog). **96 Endlosschleifen** gemessen; wieviele eine Fortschrittsaussage brauchen, ist ungezaehlt |
| **Funktionale Korrektheit ausserhalb der Struktur-Induktion** | **unbekannt** | **das ist die einzige Luecke ohne Zahl** — und genau sie ist die offene Messung |

#### Der Satz, den ein fertiger Caprock-Beweis am Ende traegt

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


---

# L1 und L2 — Maschinenmodell und Speichermodell

## L1 und L2 — Maschinenmodell und Speichermodell, entworfen und gemessen

**2026-08-14.** Die zwei schwersten Posten aus [`BEWEIS.md`](BEWEIS.md). Tragende Zahlen
nachgeprueft.

---

### L1 — Die Axiomzahl: **106**, und der schoenste Fund war schon da

| | |
|---|---|
| Axiome, je Register und Breite gezaehlt | **106** — x86_64 40, aarch64 58, MMIO-Zugriff 8 |
| konservativ (parametrisiert) | **65** |
| davon **reine Lesungen** | **30 (28 %)** — sie aendern keinen Zustand und sind der billige Teil |
| dazu Kontrollfluss-Primitive, Geraeteannahmen | ~8 + ~25 |
| **Die Annahmenmenge A1…An eines Zwei-Architektur-Kernels** | **rund 130 Namen** |

**Damit hat „speichersicher unter A1…An" erstmals einen Inhalt.** 130 ist gross genug, um eine
Ratsche zu rechtfertigen, und klein genug, um sie zu fuehren.

#### Zwei Korrekturen an meiner Vorabmessung, beide gegen mich

* **168 `asm!` waren nie 168 Fundstellen** — es sind Aufrufe **plus** `global_asm!` **plus**
  Doc-Erwaehnungen. *(Nachgezaehlt: 150 + 15; die Abweichung zur Agentenzahl ist ein anderes
  Suchmuster, nicht ein anderer Befund.)*
* **Von 129 volatilen Zugriffen sind nur 61 Geraete-MMIO.** Die anderen 68 sind Marken und
  `packed`-Strukturen im normalen RAM. **Ich hatte volatile mit Geraet gleichgesetzt.**

#### Der Fund: die Axiomschicht steht schon im Baum, nur ohne Namen

> **Der arch-neutrale Durchschnitt sind ~20 Familien** — aus zwei unabhaengigen Richtungen
> hergeleitet (Absenkungsklassen und Schnittmenge beider Architekturen).
> **Nachgeprueft, und es sind exakt 20:** `caprock-hal/src/x86_64/cpu.rs` hat 27 oeffentliche
> Funktionen, `aarch64/cpu.rs` hat 20, **die Schnittmenge ist 20** — namensgleich:
> `local_irq_save/restore/enable/disable`, `dsb_sy`, `isb`, `csdb`, `csv2`, `csv3`,
> `speculation_barrier`, `array_index_nospec`, `sb_supported`, `core_id`, `mpidr_affinity`,
> `current_el`, `halt`, `wfi`, `irqs_freigegeben`, `hypervisor_present`, `sync_code_range`.

**Caprock hat die Axiomabstraktion gebaut, ohne sie so zu nennen.** Das ist der billigste denkbare
Anfang fuer L1: die Schnittstelle existiert, es fehlen die Uebergangsfunktionen dahinter.

---

### L2 — RC11 ohne die SC-Achse. Und die Wahl ist weniger tragend als gedacht

**Kein Modell erfunden.** Gewaehlt: **RC11 ohne SC**, mit Ownership-Transfer (RSL/FSL/iRC11) als
Oberflaeche — **der Programmierer sieht RC11 nie**, er schreibt `publishes`.

**Die Begruendung ist gemessen, nicht gewaehlt:**

| | |
|---|---|
| `Ordering::SeqCst` im ganzen Baum | **0** — nachgezaehlt |
| `compare_exchange` | 11 |
| nichttriviale lock-freie Algorithmen | 3 |
| Seqlock, RCU, `AtomicPtr`-CAS | **keine** |
| Anteil der Ordnungsangaben in **Selbsttestcode** | **70 %** |

*Promising* faellt, weil sein Alleinstellungsmerkmal (out-of-thin-air) in Caprock kein Gegenstueck
hat; „Rusts Modell" ist kein dritter Kandidat, sondern C11 mit anderer Syntax.

> **Die schaerfere Fassung, und sie relativiert L2 selbst:** was Caprock **beansprucht**, ist
> **RMW-Atomizitaet plus Kohaerenz je Adresse** — und die ist in **allen drei** Modellen identisch.
> Jede Dekker-foermige Stelle im Baum kollabiert darauf. **Die Modellwahl ist damit deutlich
> weniger tragend, als die Luecke unterstellt hat.**

---

### Was NICHT abgedeckt ist

**Die Naht CPU ↔ Geraet ist Forschung**, und der Grund ist differenziert statt pauschal:

| Seite | Stand |
|---|---|
| CPU | **mechanisch** — Ueberapproximation plus voller Zaun |
| Geraet | **benannte Annahme mit Falsifikator** — das kann Gabbro |
| **die Verbindung** | **kein mechanisiertes Vorbild.** Fuer die MMU gibt es Vorarbeit (Syeda & Klein), fuer DMA-Geraete nicht |

**W^X bleibt unformulierbar**, und die Ursache ist dieselbe wie bekannt: **ein PTE ist Zeiger und
Bitfeld zugleich.** Neu ist die Folge — **der TLB-Entwurf haengt daran.** Damit ist das
PTE-Konstrukt kein offener Punkt mehr, sondern ein **Blocker mit Grund**.

---

### Der schwaechste Teil — vom Entwerfer selbst benannt, und es ist das Hausmuster

> **„Der Maschinenzustand ist die Menge der linearen Geisterwerte."**

Wahr fuer Zustand, den ein Kern **haelt**. Stillschweigend erweitert auf **den** Maschinenzustand —
**exakt der Zug, den `HISTORIE.md` als Muster fuehrt**, diesmal von einem Agenten an sich selbst
gefunden. `vspace_wx_ok` ist **eine** gemessene Gegeninstanz, und **wie viele es sonst gibt, ist
nicht gezaehlt**.

- [ ] **Diese Zahl entscheidet, ob L1 ein Entwurf ist oder eine Skizze.** Sie ist billig zu
      erheben und steht als naechster Schritt.

Nachrangig, aber lehrreich: **die erste eigene Axiomzaehlung lag bei 75 statt 106 — 29 % zu klein,
und alle Auslassungen in dieselbe Richtung.** Eine Zaehlung, deren Fehler ein Vorzeichen haben, ist
keine Zaehlung.

---

### Grammatik

**Ein neues Wort** (`result`), vier Produktionen, **kein neuer Mechanismus** — und `result` war
unabhaengig schon noetig: ohne es kann **keine** Funktion mit Rueckgabewert in `ensures` ueber ihn
zusichern. **Die sieben Domaenen halten** — bezahlt mit W^X.


---

# L3 und L4 — Beweiser und Entsprechung

## L3 und L4 — der Beweiser und die Entsprechung. **Und die Decke ist benannt**

**2026-08-14.** Die Auftragsfrage lautete: fallen die sieben Quantorendomaenen bei Schachtelung 2
in eine **entscheidbare** Theorie? Das waere der staerkste Befund des ganzen Ordners gewesen.

> **Gefahren. Antwort: nein.** Und der Grund ist nicht die Domaenenliste.

---

### Warum es nicht entscheidbar ist — vier Gruende, jeder fuer sich hinreichend

1. **Die sieben sind in Wahrheit drei Klassen**, und die Zaehlung war schief: eine verschwindet
   zur Uebersetzungszeit (`fields of`), vier sind endlich indiziert, **zwei sind transitive
   Huelle** — dazu `reaches … via`, das **dasselbe** ist wie `chain(…) in`, nur als Praedikat
   geschrieben. **Die Erreichbarkeitsklasse ist drei von acht Konstrukten, nicht eine von sieben.**
2. **Das array property fragment ist einschlaegig und bricht genau hier:** quantifizierte Indizes
   duerfen **nur direkt** gelesen werden, `a[b[i]]` ist verboten. **Caprocks CDT ist ein
   Zeigergeflecht, als Indizes kodiert** — also durchgaengig `a[b[i]]`.
3. **Die drei tragenden Invarianten von `space.rs` liegen in DREI verschiedenen Theorien:**
   `cdt_wellformed` (transitive Huelle), `child_points_back` (geschachtelte Lesezugriffe),
   `refcount_matches` (Kardinalitaet). **Keine bekannte Kombination enthaelt alle drei plus
   Bitvektoren.**
4. **Die Schranke „Schachtelung hoechstens zwei" haelt nicht.** Sie gilt ueber dem **Quelltext**,
   nicht ueber der **Formel**: `maintains` setzt eine `spec fn` mit eigenem `forall` in ein
   `ensures` mit `forall`, und `spec fn` darf `spec fn` rufen — verboten ist nur Rekursion.
   **Auf Papier pruefbar, heute nirgends geprueft.**

**Und darueber steht ein Posten, den der Ordner schon gemessen hat:** das Nachordnungslemma aus
[`MESSUNGEN.md`](MESSUNGEN.md) ist **strukturelle Induktion**, und **kein SMT-Loeser fuehrt
Induktion**. Damit war die Richtung entschieden, bevor die Frage gestellt war.

**Ein konstruktiver Gegenbefund, und er ist der wertvollste Teil:** die Beweisflaeche ist nicht die
Domaenenliste, sondern die **Kodierung**. Modelliert man `parent`/`first_child` als **unaere
Funktionen auf einer abstrakten Sorte** statt als Array-Indizes, wandert die Invariantenfamilie in
die Erreichbarkeitstheorie. **Zur Laufzeit bleibt es ein Array — die Logik sieht nie einen Index.**
*(Ungeprueft: der Schluss stammt vom Entwerfer, und `refcount_matches` faellt sicher nicht hinein.)*

---

### L3 — Die Pflichten sind nicht EINE Art, sondern DREI

**Der Ordner hat sie als eine behandelt.** Sobald man trennt, verschwindet der Hauptgrund fuer ein
Beweiser-Frontend.

| Stufe | Pflicht | wohin |
|---|---|---|
| **1** | **Schablonen** (Geistertheorie, Nachordnungslemma) — endlich viele, haengen am **Konstrukt**, nicht am Programm | **Isabelle, einmal, ausserhalb des Bauvorgangs.** Der **einzige** Posten, der die Vertrauensbasis **verkleinert** — heute heisst die Schablone „vertrauenskritischste Komponente, geprueft vom unverifizierten Kern" |
| **2** | **Programmpflichten** | eigener VC-Erzeuger → Z3/cvc5 — **aber im Vertrauen steht ein Zertifikatspruefer in sicherem Rust, nicht der Loeser** |
| **3** | die Leiter **bewiesen · geprueft · geschuldet** | **null neue Woerter** — sie besteht aus `invariant … runs online\|offline`, `check` und der Annahmenmenge |

**Fail-closed, nachgeschlagen:** cvc5s Alethe deckt nur Teile, LFSC druckt **`trust steps`** — ein
Zertifikat mit `trust step` gilt **nicht als bewiesen**. Bei Fehlschlag bricht der Bau **immer** ab,
mit **unterscheidbaren** Ausgaengen (`widerlegt` ≠ `unklar` — Caprocks Falle woertlich), Zeitschranken
in **Ressourcen statt Wanduhr** (D13), Loeserversion im Fingerabdruck.

**Harte Regel: die Leiter gilt ausschliesslich fuer Logik.** Eine ungeloeste Klempnerei-Pflicht hat
**genau eine Sprosse und keinen Ausgang.**

#### Die Decke, und sie gehoert in Zeile 1 des Ordners

> **Programm-spezifische Induktion ist damit ausgeschlossen** — ein Anwender kann keine Schablone
> schreiben. Die Decke ist **Sicherheitshuelle plus deklarierte Invarianten aus einer endlichen
> Schablonenbibliothek.**

#### BERICHTIGUNG (2026-08-14, wenige Stunden spaeter): „unmoeglich" war falsch. Es ist VERBOTEN

Die Fassung oben schrieb „fuer immer ausgeschlossen" und „Gold ist auf diesem Weg nicht
erreichbar". **Nachgelesen: Induktion scheitert an drei Zeilen, und alle drei stehen in der Liste
„Was es absichtlich nicht gibt"** (`SYNTAX.md`:585):

> *benutzerdefinierte Quantorendomaenen · Rekursion in `spec fn` · handgeschriebene Lemmata*

**Das sind Entwurfsentscheidungen, keine Saetze.** Wer sie zuruecknimmt, kann Induktion ausdruecken —
und landet bei Verus oder F\*, was die Linie ausdruecklich vermeiden wollte. **Der Unterschied
zwischen „unmoeglich" und „von uns verboten" ist genau der Zug, den `HISTORIE.md` als Hausmuster
fuehrt** — ein Satz, der wahr waere, haette man den Geltungsbereich nicht erweitert.

#### Und es gibt einen dritten Weg, den niemand betrachtet hat

Die Fassung oben setzt gleich: *Schablonen haengen am **Konstrukt*** ⟹ *endlich viele* ⟹ *nichts
Programmspezifisches*. **Der mittlere Schritt stimmt nicht.**

> **Ein Induktionsschema muss nicht fest sein — es kann aus der DEKLARATION DES ANWENDERS erzeugt
> werden.**

Eine `table` mit `parent`/`first_child`/`next_sibling` **deklariert einen Wald**. Das
Strukturinduktionsprinzip darueber folgt aus der Deklaration — **genauso wie im Zuschnitt (c) die
Mutationen daraus folgen.** Der Anwender schreibt **kein** Lemma und **keine** rekursive `spec fn`
und bekommt trotzdem Induktion **ueber seine eigene Struktur**.

**Das ist keine Erfindung:** Isabelle und Coq leiten das Induktionsprinzip seit jeher aus der
Datentypdeklaration ab. Neu waere nur, es auf eine **deklarierte** Tabelle anzuwenden statt auf
einen Datentyp.

**Und es traefe den gemessenen Fall:** das Nachordnungslemma aus [`MESSUNGEN.md`](MESSUNGEN.md)
ist strukturelle Induktion **ueber genau den deklarierten Baum**.

#### Wo die Schwierigkeit dann wirklich sitzt — und sie ist echt

**Eine `table` ist kein induktiver Datentyp, sondern ein veraenderliches Feld.** „Ist ein Wald" ist
eine **Invariante**, kein Typ — also gilt das Induktionsprinzip nur, **solange die Invariante
haelt**, und die will man gerade beweisen. Die Standardaufloesung ist eine Induktion ueber ein
**wohlfundiertes Mass** (etwa die Zahl der Abkoemmlinge) mit der Invariante als **Voraussetzung**.

**Machbar, bekannt — und genau dort sitzt die Arbeit.**

**EINGETRAGEN 2026-08-14:** `by induction over <domain>` steht in der Grammatik — **ein** neues
Wort (`over` wird wiederverwendet), zwei Produktionen, kein Lemma. Damit lautet die Decke:
**Sicherheitshuelle + deklarierte Invarianten + induktive Eigenschaften ueber DEKLARIERTEN
Strukturen.**

- [ ] **Zu pruefen, und es ist billig:** reicht ein aus der `table`-Deklaration erzeugtes
      Induktionsschema fuer die 17 gemessenen Logik-Pflichten? **Diese Frage ersetzt die Behauptung
      „unmoeglich" durch eine Messung** — und sie ist dieselbe, die als Falsifikator der
      L3-Entscheidung ohnehin ansteht.

#### Was auch danach draussen bleibt

* **Induktion ueber eine beliebige benutzerdefinierte rekursive Funktion** — die gibt es nicht,
  und das bleibt so.
* **Induktion ueber Programmablaeufe** (Lebendigkeit) — ausgesprochene Grenze, unabhaengig davon.
* **Und der Vorbehalt gegen den dritten Weg selbst:** dass das erzeugte Schema die Pflichten
  wirklich entlaedt, ist **ungeprueft**. Bis dahin ist er ein Entwurf, keine Loesung.

**Zur Verwerfung der zweiten Emission:** sie haelt, **aber der Grund im Ordner ist zu breit.** Er
trifft eine zweite **Code**emission (man zahlt L4 zweimal) und traegt **nicht** gegen ein
**Pflichten**-Frontend wie Why3. Why3 faellt aus einem anderen Grund: sein Nutzen ist der manuelle
Rueckfall — *„ein Ordner mit einem Rueckfall hat kein Tor."*

---

### L4 — „Die Absenkung" gibt es nicht, es sind drei

| | Teil | ist „syntaxgesteuert, nicht optimierend" … |
|---|---|---|
| **(a)** | flacher Kern | **wahr** |
| **(b)** | Bibliotheksemissionen (`format`, `table`, `device`) | **gegenstandslos** — eine Deklaration wird zu einem Algorithmus, es gibt keine Quellstruktur |
| **(c)** | Assembler | **nicht anwendbar** |

**Die Bedingung ist ausgerechnet fuer den Teil formuliert, der am wenigsten Zeilen erzeugt.**

* **„Nicht optimierend" wird pruefbar als Bijektion zwischen Auswertungsstellen** — und **das geht
  nur, weil E2 und E3 schon entschieden sind** (Zuweisung ist kein Ausdruck, nichts ist implizit).
  Ohne sie waere es semantisch und damit unentscheidbar. **Das ist die staerkste Begruendung fuer
  E2/E3, und sie stand nirgends im Ordner.**
* **(a):** Deckungszeugnis je Uebersetzungslauf, nachgerechnet von einem **eigenen** Programm mit
  eigener Regeltabelle — die `checkfat.py`-Lehre. **Abnahme ist die Mutationsliste, nicht die
  Existenz des Pruefers.**
* **(b):** ein **Deuter im Uebersetzer** statt der Handschrift, Differenztest gegen den Beschreiber.
  **Preis, heute nirgends genannt: die Bibliotheksschicht wird zweimal gebaut.**

#### Der unbenannte Riss: **welches C?**

„Ausgabe ist C" — **ohne benannten Ausschnitt und benannte Uebersetzeroptionen ist die Entsprechung
nicht unbewiesen, sondern UNFORMULIERBAR.** Vier Stellen, an denen Gabbros eigener Entwurf auf
undefiniertes Verhalten trifft: `restrict`, vorzeichenbehafteter Ueberlauf, `tagged` → Union,
volatile. **Die Menge gehoert ins Erzeugnis, neben A1…An.**

#### Binaerverifikation: **ermoeglicht, und billiger als gedacht**

Sie braucht benannten C-Ausschnitt und erhaltene Funktionsgrenzen — **beides liefert derselbe
Zeugnispruefer. Eine Eigenschaft, zwei Kaeufe.** Und **Monomorphisierung verbaut sie nicht** — damit
ist der Widerspruchskandidat aus [`PLAN.md`](PLAN.md) entlastet.

> **Aber:** seL4 nimmt Assembler **und volatile Zugriffe** aus. **Damit laege der ganze
> `device`/`mmio`-Zweig ebenfalls draussen — genau der Teil mit den meisten getoeteten Fallen.**

---

### Der Inline-Assembler: **„eine Emissionsstelle statt 161" ist heute FALSCH**

L4 gilt dort nicht — Assembler wird **nicht abgesenkt, sondern eingesetzt**. Pruefbar ist nur die
**Schnittstelle**, und **die ist heute nicht einmal sagbar**: `prim fn` hat **keinen `abi`-Block**;
`arch` gibt es, die Registerbelegung nicht.

**Die Flaeche schrumpft also nicht — sie wandert in eine Deklaration ohne Inhalt.**

Die minimale Fassung ist entworfen (`abi`-Block, **vier neue Woerter**); drei der vier Bedingungen
fallen aus **D2** und **M1**, also nicht beim Programmierer. Die billigere Zwei-Wort-Fassung ist
geprueft und **verworfen** — `reserved` hiesse dann zweierlei, Caprocks teuerste Fallenklasse.
**Fuer den Block gilt Zaehlbarkeit, nicht Korrektheit:** ein Axiom eigener Klasse **„Emission"**
(nicht „Hardware"), plus baubare Falsifikatoren — **drei von vier laufen in Caprock schon.**
**Der Block bekommt keinen Beweis, aber `check`.**

- [ ] **Noch nicht in der Grammatik.** Die vier Woerter stehen nicht im Wortschatz, die zwei
      Produktionen nicht in der EBNF, `./pruefe-syntax.sh` ist nicht dagegen gefahren. **Bis dahin
      ist der `abi`-Teil eine Skizze, keine Regel** — und seine Begruendung ist **schwaecher als
      bei jedem anderen Konstrukt**: ein Sprachbefund, keine bezahlte Falle.

---

### Der schwaechste Teil — vom Entwerfer benannt, und er trifft

1. **Die L3-Entscheidung ruht auf n = 1** (`revoke` → Nachordnungslemma) — **in einem Ordner, der
   genau diesen Fehler zweimal gemessen hat.** Der Falsifikator steht dabei und kostet einen Tag:
   die **17 gemessenen Logik-Pflichten** einordnen in *SMT-entscheidbar / braucht Schablone /
   braucht **programm-spezifische** Induktion*. **Ein einziger Fall in der dritten Spalte widerlegt
   die Entscheidung.**
2. **Das Deckungszeugnis prueft STRUKTUR, und es gibt kein Argument, dass Struktur Bedeutung
   impliziert.** Dazwischen liegt eine handgeschriebene, handgeglaubte Tabelle
   *Gabbro-Operation → C-Operation → Bedingung*, geschaetzt **40–60 Eintraege** — **A8 um eine
   Groessenordnung skaliert, und der einzige Posten ohne Instrument.**
3. **Drei Literaturbehauptungen aus dem Gedaechtnis**; der Satz „bei Funktionskodierung faellt
   Caprocks Invariantenfamilie in ein entscheidbares Fragment" ist **ein Schluss, ungeprueft**.


---

# Posten 2 — welches C

## Posten 2 — WELCHES C, und wie die Absenkung von einer Zusage zu einer Aussage wird

**2026-08-14.** Der einzige Posten, an dem Gabbro **strukturell** hinter seL4 zurueckliegt
([`BEWEIS.md`](BEWEIS.md)). seL4 loest ihn durch **Formalisierung** eines
C-Ausschnitts (Parser, Simpl/AutoCorres) — ein Teilprojekt.

**Gabbro loest ihn anders, und der Unterschied ist die ganze Antwort:**

> **seL4 formalisiert C. Gabbro emittiert so wenig C, dass dessen Semantik eine ENDLICHE TABELLE
> ist.** Was nie emittiert wird, braucht keine Semantik.

---

### 1. Die Zielsprache ist nicht „C", sondern eine geschlossene Formenliste

Der Emittent kennt **eine C-Form je Konstrukt** (Festlegung §14.1). Damit ist die Zielsprache
**aufzaehlbar**, und sie ist klein:

```
Deklarationen   static, extern, typedef-freie Struct-/Union-Definition, enum-freie Konstanten
Typen           uint{8,16,32,64}_t, int{8,16,32,64}_t, _Bool, T*, T[N], struct, union
Anweisungen     Zuweisung, if/else, switch (erschoepfend, ohne default), for (Zaehlschleife),
                return, goto NUR als erzeugter Schleifenausgang, Aufruf
Ausdruecke      Literal, Bezeichner, Feldzugriff, Index, unaeres !/-, binaeres
                + - * / % & | ^ << >> == != < <= > >=, Aufruf, EXPLIZITER Cast
Sonstiges       volatile-Zugriff, _Atomic mit benannter Ordnung, _Noreturn, restrict,
                Inline-Assembler an genau einer Emissionsstelle
```

**Was NIE emittiert wird** — und damit ohne Semantikbedarf ist: Praeprozessor ausser `#if` aus
`when`; `void*`; Zeigerarithmetik; `union`-Umdeutung ohne Marke; Komma-Operator; Zuweisung im
Ausdruck; `?:`; verschachtelte Zuweisung; implizite Umwandlung; variadische Funktionen; `longjmp`;
VLA; Bitfelder (Gabbro macht sie selbst mit Maske und Schiebung); `const`-Verwerfung.

- [ ] **Die Liste ist zu zaehlen und zu ratschen**, wie die Axiomschicht. Waechst sie, um ein
      Emissionsproblem zu loesen, ist das dieselbe Bewegung wie eine wachsende Axiomschicht.

---

### 2. Das UB-Inventar — jede Klasse, und wodurch sie stirbt

**Die Beweise leben in Gabbro. Die Gefahr ist, dass die EMISSION sie durch Cs eigene Regeln
entwertet.** Deshalb ist die Liste nicht „welches UB kann Gabbro-Code haben" (keines), sondern
**„welches UB kann das erzeugte C haben"**:

| # | UB-Klasse in C | stirbt durch | Restrisiko |
|---|---|---|---|
| 1 | **vorzeichenbehafteter Ueberlauf** | M1 beweist die Schranke — **aber C weiss das nicht.** Emission nutzt vorzeichenlose Typen, wo moeglich; sonst `-fwrapv` als Guertel | keins, wenn beides steht |
| 2 | **Zugriff ausserhalb** | M1/M4 im Quelltyp; die Emission erzeugt **keine** Zeigerarithmetik | keins |
| 3 | **Division/Rest durch null** | M1: der Nenner-Bereich schliesst 0 aus | keins |
| 4 | **Schieben um ≥ Breite** | M1 beschraenkt den Schiebebetrag | keins |
| 5 | **striktes Aliasing** | **kein Cast zwischen Zeigertypen wird je emittiert**; `-fno-strict-aliasing` als Guertel | keins |
| 6 | **Auswertungsreihenfolge / Sequenzpunkte** | **E2**: Zuweisung ist kein Ausdruck, je Anweisung eine Wirkung. **Die ganze Klasse entfaellt** | keins |
| 7 | **implizite Umwandlung / Ganzzahl-Promotion** | **E3** im Quelltext; die Emission setzt **ueberall explizite Casts** | keins, aber **mechanisch zu pruefen** |
| 8 | **uninitialisiertes Lesen** | E3: nichts ist implizit, jede Deklaration hat einen Wert | keins |
| 9 | **Nullzeiger** | Gabbro hat kein `null`; `option` ist `tagged` | **nur am `extern`-Rand** |
| 10 | **`union`-Umdeutung** | `tagged` schreibt und liest **ueber die Marke**; C11 erlaubt das Lesen eines anderen Glieds ausdruecklich | Fuellbytes bleiben unspezifiziert — **nie gelesen** |
| 11 | **`restrict` falsch** | aus `effects` erzeugt. **Ist `effects` falsch, ist das C-UB** — ein **Beweis-Export in Cs Regeln** | **echter Vertrauenstransfer, benannt** |
| 12 | **`volatile`-Semantik** | schwach spezifiziert; MMIO-Praxis. **seL4 nimmt genau das aus** | **Axiom, benannt** (A12/A17) |

> **Zwei Zeilen tragen echtes Restrisiko, und beide sind benannt statt gedeckt:** `restrict` (11)
> exportiert eine Gabbro-Zusage in Cs UB-Regeln, und `volatile` (12) ist ohnehin Axiom. **Alles
> Uebrige stirbt an einer Regel, die aus einem anderen Grund schon dasteht** — E2 und E3 zahlen
> hier zum zweiten Mal.

---

### 3. Die Uebersetzeroptionen sind Teil des Artefakts, nicht der Umgebung

```
-std=c11 -ffreestanding -fno-builtin
-fwrapv -fno-strict-aliasing -fno-delete-null-pointer-checks
-fno-common -fno-stack-protector
```

**Sie gehoeren ins Erzeugnis, neben A1…An** — und mit **Fingerabdruck**. Die Lehre steht im
Register: *„`cargo build` laeuft durch" ist kein Beleg, solange niemand die KONFIGURATION bindet*
(`CAPROCK_FLAGS_FP`). Eine Absenkung, deren Gueltigkeit an Optionen haengt, die niemand festhaelt,
ist eine Zusage ueber eine fremde Maschine.

- [ ] **Fail-closed:** uebersetzt jemand das erzeugte C **ohne** die genannten Optionen, muss es
      **brechen**, nicht stiller anders bedeuten. Mechanismus: eine erzeugte
      `_Static_assert`-Praeambel, die `__OPTIMIZE__`-unabhaengige Merkmale prueft, plus der
      Fingerabdruck im Abbild.

---

### 4. Wie die Absenkung von einer Zusage zu einer AUSSAGE wird

**„Syntaxgesteuert und nicht optimierend" ist heute Prosa.** Pruefbar wird es als **Bijektion
zwischen Auswertungsstellen** — und **das geht nur, weil E2 und E3 schon entschieden sind**: ohne
sie waere die Frage semantisch und damit unentscheidbar.

Der Emittent gibt je Uebersetzungslauf ein **Deckungszeugnis** aus:

```
site  gabbro:space.gb:412:9   ->  c:space.c:1187:5   form ASSIGN_INDEX
site  gabbro:space.gb:413:5   ->  c:space.c:1188:5   form CALL
form  ASSIGN_INDEX  =  "<lhs>[<idx>] = <rhs>;"        aus Regel R17
```

Ein **unabhaengiges** Programm mit **eigener** Formentabelle rechnet nach:

1. **Vollstaendigkeit** — jede Gabbro-Auswertungsstelle kommt **genau einmal** vor.
2. **Reihenfolge** — die C-Stellen stehen in derselben Ordnung.
3. **Geschlossenheit** — jede C-Form steht in der Liste aus §1.
4. **Keine Zusatzwirkung** — das C enthaelt keine Auswertungsstelle ohne Gabbro-Urbild.

**Die `checkfat.py`-Lehre gilt woertlich:** der Nachrechner ist **ein zweites Programm mit
eigenem Muster**, nicht derselbe Code zweimal gerufen. **Und die Abnahme ist die Mutationsliste,
nicht die Existenz des Pruefers** — eine absichtlich verschobene Auswertungsstelle muss auffallen.

---

### 5. Was das erreicht — und was ausdruecklich nicht

**Erreicht:**

* **Die Zielsprache ist benannt und geschlossen**, damit ist die Entsprechung ueberhaupt
  formulierbar — vorher war sie das nicht.
* **Zehn von zwoelf UB-Klassen sterben an vorhandenen Regeln**, nicht an neuen.
* **Die Absenkung wird je Lauf nachgerechnet**, von einem zweiten Programm.
* **Binaerverifikation bleibt moeglich** und wird sogar leichter: benannter Ausschnitt und
  erhaltene Funktionsgrenzen sind genau das, was sie verlangt.

**Nicht erreicht, und der Unterschied zu seL4 bleibt:**

* **Das ist KEINE formale C-Semantik.** Es ist eine **Verkleinerung der Flaeche plus eine
  strukturelle Nachrechnung.** Was die zwoelf Formen *bedeuten*, steht in einer Tabelle, die ein
  Mensch geschrieben hat — **40–60 Eintraege, handgeglaubt** (so schon in
  [`BEWEIS.md`](BEWEIS.md) benannt).
* **Struktur impliziert nicht Bedeutung.** Das Zeugnis zeigt, dass die Stellen **einander
  entsprechen** — nicht, dass die C-Form dasselbe **tut**. Die Luecke dazwischen ist genau die
  Tabelle, und sie ist der **einzige Posten des ganzen Ordners ohne Instrument**.
* **`restrict` und `volatile` bleiben Vertrauen**, benannt im Manifest.

### Das Instrument, das es doch gibt — Zeugenpaare

**„Der einzige Posten ohne Instrument" war falsch.** Das Werkzeug liegt im eigenen Kasten:
**jeder Tabelleneintrag bekommt ein ausfuehrbares Zeugenpaar** — ein Gabbro-Fragment, das erwartete
C, das erwartete Verhalten —, durch den **echten** C-Uebersetzer gefahren und verglichen. Damit ist
die Tabelle **pruefbar statt handvertraut**, und ein Eintrag ohne Zeugenpaar ist unvollstaendig.

### `restrict` wird eine bepreiste Option, kein Standardexport

`restrict` exportiert eine Gabbro-Zusage in Cs UB-Regeln (Zeile 11 des Inventars). **Deshalb wird
es standardmaessig NICHT emittiert** — nur dort, wo der Differenz-Benchmark es verlangt. Die
Kostenwahrheit misst ohnehin gegen Handschrift; **der UB-Transfer wird also genau da bezahlt, wo er
messbar etwas kauft**, und nirgends sonst.

### Der Gleichtaktfehler des Deckungszeugnisses, benannt

Zwei Programme mit **eigenen** Formentabellen sind N-Versionen — **aber beide Tabellen stammen aus
demselben Spezifikationstext.** Ein Fehler *im Text* steht in beiden. **Der Gleichtaktfehler bleibt
und ist damit ein benannter Posten**, kein geschlossener; die Zeugenpaare oben sind das einzige,
was gegen ihn hilft, weil sie gegen den **Uebersetzer** messen statt gegen eine zweite Lesart.

- [ ] **Der naechste Schritt ist die Formentabelle selbst** — 40–60 Eintraege, je *Gabbro-Operation
      → C-Form → Bedingung*. Sie ist klein genug, um sie zu schreiben, und gross genug, um sie zu
      **zaehlen und zu ratschen**. **Erst wenn sie steht, ist Posten 2 von „unformulierbar" auf
      „benannt" gerueckt** — und mehr behauptet dieser Entwurf nicht.


---

# Was seL4 neben der Logik braucht

## Was eine seL4-Verifikation NEBEN dem Logikbeweis braucht — und was Gabbro dafuer hat

**2026-08-14.** Gabbros Zusage lautet „alles ausser dem Logikbeweis faellt durch Konstruktion".
**Dann muss man wissen, was „alles ausser" bei seL4 wirklich ist** — sonst vergleicht man einen
Entwurf mit einer Vorstellung.

> **Vorbehalt, und er gilt fuer die ganze Datei:** die seL4-Angaben sind **aus dem Gedaechtnis**.
> Der Ordner hat dieselbe Klasse schon einmal gebraucht (die 20:1-Aufteilung) und sie wurde
> bestaetigt — **das ist kein Beleg fuer diese hier.** Wo eine Zahl steht, steht sie als
> Groessenordnung.

---

### Die sechs Posten neben der Logik

| # | Posten | was er bei seL4 ist | was Gabbro dafuer hat |
|---|---|---|---|
| **1** | **Maschinenmodell** | ein eigenes Modell in Isabelle: Register, Speicher, MMU; nicht Modelliertes ist **axiomatisiert** | die **Axiomschicht**, ~130 Namen fuer zwei Architekturen, **ratschenfaehig** und im Erzeugnis. `port` hat sie gerade um 70 Fundstellen entlastet |
| **2** | **C-Semantik** | ein **C-Parser** samt Formalisierung eines C-Ausschnitts (Simpl/AutoCorres) — ein Teilprojekt fuer sich | **nichts Gleichwertiges.** Gabbro ersetzt es durch „eine Emission, syntaxgesteuert, nicht optimierend" — **und diese Entsprechung ist behauptet**, nicht formalisiert |
| **3** | **Die Annahmenliste** | ausdruecklich gefuehrt: Assembler unbewiesen, Bootcode zunaechst aussen vor, Hardware wie modelliert, DMA eingeschraenkt, **verifizierte Konfiguration einkernig** | **das Pflichtenmanifest** — dieselbe Sache, aber **maschinenlesbar, mit Klassen und Ratsche ueber Namen**. Hier ist Gabbro nicht schlechter, sondern schaerfer |
| **4** | **Binaerverifikation** | Uebersetzungsvalidierung C ⟶ Maschinencode (graph-refine/SydTV), damit der Uebersetzer nicht der Riss ist. **Assembler und volatile sind ausgenommen** | **steht unter „Spaeter"**, ist aber **ermoeglicht** — derselbe Zeugnispruefer liefert benannten C-Ausschnitt und erhaltene Funktionsgrenzen. **Nur laege der ganze `device`-Zweig ausserhalb** |
| **5** | **Eigenschaften ueber der Korrektheit** | Integritaet, Vertraulichkeit, Autoritaetsbeschraenkung — **eigene Saetze mit eigenen Spezifikationen** | nicht adressiert. Gabbro liefert die Huelle, **nicht die Sicherheitsaussage darueber** |
| **6** | **Der Unterhalt** | **der Posten, den niemand mitzaehlt** — s. u. |

---

### Posten 6: der Unterhalt, und hier liegt Gabbros staerkstes Argument

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

#### Die stille Vorbedingung — und sie ist messbar

**„Klempnerei kann nicht brechen" gilt nur, solange die Aenderung INNERHALB der Konstrukte
bleibt.** Eine Aenderung, die ein **neues Konstrukt** braucht, bricht keine Beweise — **sie bricht
die Sprache.** Und dann ersetzt **Sprachunterhalt** den Beweisunterhalt, nur mit einem anderen
Namen.

**Die eigene Geschichte zeigt, dass der Preis real ist:** elf Klempnerei-Klassen wurden zwoelf;
`keeping` wurde `mirrors`; `transition` wurde `transset`; `forever` bekam `leaves` — alles binnen
Tagen.

> **Die Wette lautet, dass der Wortschatz konvergiert, und sie ist MESSBAR:** *neue Konstrukte je
> ausgeschriebenem Fragment muessen fallen.* **Die vier fehlenden Bereichsfragmente — Scheduler,
> MMU, Lader, Parser — sind genau das Messgeraet dafuer**, und deshalb sind sie nicht nur eine
> Abdeckungsluecke, sondern die Probe auf das staerkste Produktargument des Ordners.

---

### Wo Gabbro schlechter ist, ohne Beschoenigung

1. **Keine C-Semantik.** seL4 hat eine Formalisierung; Gabbro hat eine **Zusage ueber die eigene
   Absenkung**. Das ist Posten 2, und er ist der groesste Rueckstand.
2. **Kein Beweis ueber den Pruefer.** seL4s Beweise laufen in Isabelle, dessen Kern klein und
   geprueft ist. Gabbros Pruefer ist **unverifiziertes Rust**, und alles haengt an ihm.
3. **Keine Sicherheitsaussagen.** Integritaet und Informationsfluss sind bei seL4 **eigene
   Saetze**; Gabbro liefert sie nicht und behauptet es auch nicht.
4. **Reife.** seL4s Kette ist gefahren, mehrfach, auf echter Hardware. Gabbro hat keine Zeile
   Uebersetzer.

---

### Was der Vergleich fuer die harten Zusagen sagt

[`SPRACHE.md`](SPRACHE.md) macht Induktion automatisch statt heuristisch — das
adressiert **den Beweisteil**, also genau den Posten, den seL4 mit 200 000 Zeilen bezahlt.

**Der Vergleich zeigt aber, dass das die kleinere Haelfte ist:** von den sechs Posten neben der
Logik beruehrt die Schrittzusage **einen** (den Beweisaufwand ueber deklarierten Strukturen).
**Posten 2 und 5 bleiben unberuehrt, Posten 4 steht unter „Spaeter", Posten 3 ist gut geloest,
Posten 1 ist zur Haelfte da.**

- [ ] **Die ehrliche Folge fuer den Plan:** die naechste Arbeit ist **nicht** eine weitere
      Verschaerfung der Beweisautomatik, sondern **Posten 2** — was heisst „welches C", und wie
      wird die Absenkung von einer Zusage zu einer pruefbaren Aussage? Das steht in
      [`BEWEIS.md`](BEWEIS.md) als L4 und ist der einzige Posten, an dem Gabbro **strukturell**
      hinter seL4 zurueckliegt statt nur an Reife.


---

# Die Leistung des erzeugten C — was gemessen ist (nichts) und was folgt

**2026-08-14.** Der Ordner hat dazu eine **Tabelle mit Behauptungen** (Festlegung §14.2) und
**keine Messung**. Hier steht, was daraus folgt, getrennt nach Richtung — und der Posten, den die
Tabelle **nicht** nennt.

## Wo es schneller sein sollte als der heutige Rust-Kernel

| | Grund | Zahl |
|---|---|---|
| **Bereichspruefungen** | Rust prueft **jede** Indizierung, ausser LLVM kann sie wegoptimieren. **Caprock umgeht das nirgends** — nachgezaehlt: **0** `get_unchecked`, **0** `unreachable_unchecked`, **0** `assert_unchecked`. Gabbro **beweist** und emittiert **keine** | **1 398** variable Indizierungen im Baum |
| **`accumulates`** | Zelle je Kern plus Merge beim Lesen statt CAS-Schleife | gemessen an `sync:572–592` **strikt besser als das Original**, das dort zusaetzlich eine hingenommene Rennstelle hat |
| **`transition`/`mirrors`** | **ein** Store mit konstanter Maske statt Lesen-Aendern-Schreiben | je Geraeteuebergang |
| **Geister, Vertraege, `check`** | verschwinden vor der Codeerzeugung; `check` uebersetzt nur unter `when TESTBUILD` | **0 Bytes** |

## Wo es gleich sein sollte

Bereichstypen → nackter C-Typ · `tagged`+`match` → Union mit Marke, `switch` · `traverse` → `for`
ohne Bound-Checks · `format`-Leser → Zugriffe **nach einer** Laengenpruefung · `lock`/`locks` → die
vorhandene Primitive.

## Wo es LANGSAMER sein wird — und die Tabelle nennt es nicht

### 1. Die Schleifenschranken kosten einen Zaehler, den es vorher nicht gab

`retry`/`forever` verlangen `bounded N ops`. **Eine Warteschleife, die heute ohne Zaehler spinnt,
bekommt einen** — Inkrement und Vergleich je Durchgang. Bei einer umkaempften Sperre ist das
messbar. Gemessen: **96 `spin_loop`-Hinweise** im Baum, **2** rohe `loop {` allein in
`caprock-sync`.

- [ ] **Abhilfe, entwerfbar und noch nicht entworfen:** die Schranke muss nicht **je Durchgang**
      geprueft werden. Ist sie eine **Watchdog**-Schranke (und das ist sie, denn `progress` traegt
      die Terminierung), genuegt eine Pruefung **alle 2^k Durchgaenge** — Kosten fallen auf
      ~1/2^k, die Zusage bleibt „bricht nach hoechstens N + 2^k". **Das gehoert entschieden, bevor
      der erste Benchmark laeuft**, sonst misst er ein Konstrukt, das niemand so bauen wuerde.

### 2. `restrict` ist jetzt standardmaessig AUS

Der UB-Transfer wird nur bezahlt, wo der Differenz-Benchmark ihn verlangt. **Der Preis dafuer ist
konservativerer C-Code an genau den Stellen**, wo Handschrift `restrict` gesetzt haette — und das
sind die kopierenden Pfade, also die heissen.

### 3. Der strukturelle Posten: **flach absenken und schnell sein stehen in Spannung**

**„Syntaxgesteuert, nicht optimierend" ist die Bedingung, unter der die Verfeinerung billig wird**
(M-Gold-2) — und sie heisst: **der Emittent restrukturiert nicht.** Wo ein Mensch eine Schleife
verschmolzen, eine Berechnung hochgezogen oder eine Staerke reduziert haette, emittiert Gabbro die
naive Form und **verlaesst sich auf den C-Uebersetzer**.

> **Der Ordner hat diese Spannung bisher nur auf der Korrektheitsseite bepreist.** Auf der
> Leistungsseite ist sie ungepreist: **die Absenkung ist eine Wette darauf, dass LLVM/GCC die
> Form, die Gabbro erzeugt, gut behandelt.** Ob das stimmt, weiss niemand — es haengt an der
> Formentabelle, die noch nicht geschrieben ist.

## Was es entscheidet — und es ist nicht diese Datei

**Der Differenz-Benchmark je Modul** (P3/P5-Tor): erzeugtes C gegen handgeschriebenes, Ausloesung
bei „erzeugt langsamer als Handschrift plus Messrauschen". **Bis dahin ist jede Zahl hier eine
Erwartung.**

**Die ehrliche Zusammenfassung in einem Satz:** *In den Zaehl- und Zugriffspfaden sollte das
erzeugte C schneller sein als der heutige Rust-Kernel, weil 1 398 Bereichspruefungen entfallen; in
den Wartepfaden zunaechst langsamer, bis die Schrankenpruefung amortisiert ist; und ueber alles
haengt eine ungepreiste Wette auf den C-Uebersetzer.*
