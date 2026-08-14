# Posten 2 — WELCHES C, und wie die Absenkung von einer Zusage zu einer Aussage wird

**2026-08-14.** Der einzige Posten, an dem Gabbro **strukturell** hinter seL4 zurueckliegt
([`SEL4-VERGLEICH.md`](SEL4-VERGLEICH.md)). seL4 loest ihn durch **Formalisierung** eines
C-Ausschnitts (Parser, Simpl/AutoCorres) — ein Teilprojekt.

**Gabbro loest ihn anders, und der Unterschied ist die ganze Antwort:**

> **seL4 formalisiert C. Gabbro emittiert so wenig C, dass dessen Semantik eine ENDLICHE TABELLE
> ist.** Was nie emittiert wird, braucht keine Semantik.

---

## 1. Die Zielsprache ist nicht „C", sondern eine geschlossene Formenliste

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

## 2. Das UB-Inventar — jede Klasse, und wodurch sie stirbt

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

## 3. Die Uebersetzeroptionen sind Teil des Artefakts, nicht der Umgebung

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

## 4. Wie die Absenkung von einer Zusage zu einer AUSSAGE wird

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

## 5. Was das erreicht — und was ausdruecklich nicht

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
  [`BEWEISER.md`](BEWEISER.md) benannt).
* **Struktur impliziert nicht Bedeutung.** Das Zeugnis zeigt, dass die Stellen **einander
  entsprechen** — nicht, dass die C-Form dasselbe **tut**. Die Luecke dazwischen ist genau die
  Tabelle, und sie ist der **einzige Posten des ganzen Ordners ohne Instrument**.
* **`restrict` und `volatile` bleiben Vertrauen**, benannt im Manifest.

- [ ] **Der naechste Schritt ist die Formentabelle selbst** — 40–60 Eintraege, je *Gabbro-Operation
      → C-Form → Bedingung*. Sie ist klein genug, um sie zu schreiben, und gross genug, um sie zu
      **zaehlen und zu ratschen**. **Erst wenn sie steht, ist Posten 2 von „unformulierbar" auf
      „benannt" gerueckt** — und mehr behauptet dieser Entwurf nicht.
