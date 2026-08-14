# L3 und L4 — der Beweiser und die Entsprechung. **Und die Decke ist benannt**

**2026-08-14.** Die Auftragsfrage lautete: fallen die sieben Quantorendomaenen bei Schachtelung 2
in eine **entscheidbare** Theorie? Das waere der staerkste Befund des ganzen Ordners gewesen.

> **Gefahren. Antwort: nein.** Und der Grund ist nicht die Domaenenliste.

---

## Warum es nicht entscheidbar ist — vier Gruende, jeder fuer sich hinreichend

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
[`P0-1-REVOKE.md`](P0-1-REVOKE.md) ist **strukturelle Induktion**, und **kein SMT-Loeser fuehrt
Induktion**. Damit war die Richtung entschieden, bevor die Frage gestellt war.

**Ein konstruktiver Gegenbefund, und er ist der wertvollste Teil:** die Beweisflaeche ist nicht die
Domaenenliste, sondern die **Kodierung**. Modelliert man `parent`/`first_child` als **unaere
Funktionen auf einer abstrakten Sorte** statt als Array-Indizes, wandert die Invariantenfamilie in
die Erreichbarkeitstheorie. **Zur Laufzeit bleibt es ein Array — die Logik sieht nie einen Index.**
*(Ungeprueft: der Schluss stammt vom Entwerfer, und `refcount_matches` faellt sicher nicht hinein.)*

---

## L3 — Die Pflichten sind nicht EINE Art, sondern DREI

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

### Die Decke, und sie gehoert in Zeile 1 des Ordners

> **Programm-spezifische Induktion ist damit ausgeschlossen** — ein Anwender kann keine Schablone
> schreiben. Die Decke ist **Sicherheitshuelle plus deklarierte Invarianten aus einer endlichen
> Schablonenbibliothek.**

### BERICHTIGUNG (2026-08-14, wenige Stunden spaeter): „unmoeglich" war falsch. Es ist VERBOTEN

Die Fassung oben schrieb „fuer immer ausgeschlossen" und „Gold ist auf diesem Weg nicht
erreichbar". **Nachgelesen: Induktion scheitert an drei Zeilen, und alle drei stehen in der Liste
„Was es absichtlich nicht gibt"** (`SYNTAX.md`:585):

> *benutzerdefinierte Quantorendomaenen · Rekursion in `spec fn` · handgeschriebene Lemmata*

**Das sind Entwurfsentscheidungen, keine Saetze.** Wer sie zuruecknimmt, kann Induktion ausdruecken —
und landet bei Verus oder F\*, was die Linie ausdruecklich vermeiden wollte. **Der Unterschied
zwischen „unmoeglich" und „von uns verboten" ist genau der Zug, den `HISTORIE.md` als Hausmuster
fuehrt** — ein Satz, der wahr waere, haette man den Geltungsbereich nicht erweitert.

### Und es gibt einen dritten Weg, den niemand betrachtet hat

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

**Und es traefe den gemessenen Fall:** das Nachordnungslemma aus [`P0-1-REVOKE.md`](P0-1-REVOKE.md)
ist strukturelle Induktion **ueber genau den deklarierten Baum**.

### Wo die Schwierigkeit dann wirklich sitzt — und sie ist echt

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

### Was auch danach draussen bleibt

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

## L4 — „Die Absenkung" gibt es nicht, es sind drei

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

### Der unbenannte Riss: **welches C?**

„Ausgabe ist C" — **ohne benannten Ausschnitt und benannte Uebersetzeroptionen ist die Entsprechung
nicht unbewiesen, sondern UNFORMULIERBAR.** Vier Stellen, an denen Gabbros eigener Entwurf auf
undefiniertes Verhalten trifft: `restrict`, vorzeichenbehafteter Ueberlauf, `tagged` → Union,
volatile. **Die Menge gehoert ins Erzeugnis, neben A1…An.**

### Binaerverifikation: **ermoeglicht, und billiger als gedacht**

Sie braucht benannten C-Ausschnitt und erhaltene Funktionsgrenzen — **beides liefert derselbe
Zeugnispruefer. Eine Eigenschaft, zwei Kaeufe.** Und **Monomorphisierung verbaut sie nicht** — damit
ist der Widerspruchskandidat aus [`FERTIG.md`](FERTIG.md) entlastet.

> **Aber:** seL4 nimmt Assembler **und volatile Zugriffe** aus. **Damit laege der ganze
> `device`/`mmio`-Zweig ebenfalls draussen — genau der Teil mit den meisten getoeteten Fallen.**

---

## Der Inline-Assembler: **„eine Emissionsstelle statt 161" ist heute FALSCH**

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

## Der schwaechste Teil — vom Entwerfer benannt, und er trifft

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
