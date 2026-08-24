# Die Paarungsform — wie ein `impl fn` sagt, welches `spec fn` es verfeinert

*Gemessen und entschieden am 2026-08-24. Jede Zahl nennt den Befehl, der sie nachrechnet.*

> **Der Befund zuerst, weil er die Reihenfolge umdreht:** `TODO.md` führte *„Die Kopfform von
> P6 hat NULL Fundstellen: kein einziges `spec fn`/`impl fn`-Paar im Korpus"* als **Korpuslücke**.
> Sie ist keine. **Es gibt keine Form**, in der ein `impl fn` sagt, welches `spec fn` es
> verfeinert — weder ein Wort noch eine Produktion.

```bash
grep -rn 'refines\|verfeinert' dokumente/SYNTAX.md crates/gabbro-syntax/src/kw.rs
#   (keine Ausgabe)
```

`spec` und `impl` sind **Qualifizierer an `fndecl`** ([`SYNTAX.md`](../dokumente/SYNTAX.md):659),
sonst nichts. *Ein Korpuseintrag hätte also gar nicht geschrieben werden können.*

---

## 1. Der Bestand

```bash
# spec/impl je Name, über beispiele/, messung/ und arbeitsprotokoll/messungen/
python3 - <<'PY'
import re,glob,collections
spec=collections.defaultdict(list); impl=collections.defaultdict(list)
for f in glob.glob('beispiele/*.gab')+glob.glob('messung/*/*.gab')+glob.glob('arbeitsprotokoll/messungen/*.gab'):
    for z in open(f):
        m=re.match(r'\s*(?:pub\s+)?(spec|impl) fn (\w+)',z)
        if m: (spec if m.group(1)=='spec' else impl)[m.group(2)].append(f)
print(len(spec), sum(map(len,spec.values())), len(impl), sum(map(len,impl.values())),
      sorted(set(spec)&set(impl)))
PY
```

| | |
|---|---:|
| `spec fn` | **8** in **4** Namen |
| `impl fn` | **236** in **178** Namen |
| **gleicher Name als `spec` UND `impl`** | **0** |

**Die letzte Zeile entscheidet mit.** Fünf Dateien führen beides nebeneinander
(`01-tabelle.gab`, `09-ohne-zeiger.gab`, `kapraum.gab`, `F01`, `F03`) — dort ist `spec fn`
**überall ein Prädikathelfer** in `requires`/`ensures`, nie die Spezifikation, gegen die ein
Rumpf steht. *Das Verhältnis 8 : 236 ist keine Nachlässigkeit; es ist die Rolle, die `spec fn`
heute hat.*

---

## 2. Die drei Formen, beide Seiten je Form

### (a) Paarung über den NAMEN — `spec fn f` und `impl fn f` paaren sich

| | |
|---|---|
| **dafür** | **null Grammatik, null Wortschatz.** Nur eine Passregel. Die billigste Form, die es gibt |
| **dagegen** | **eine Umbenennung erzeugt oder vernichtet eine Beweispflicht, still.** Das ist wörtlich die *stille Semantikänderung*, gegen die `kernel/build.rs` in Caprock vierzig Zeilen führt. Und `spec fn` hat heute eine andere Rolle: aus einem Prädikathelfer, der zufällig heißt wie ein Rumpf, würde eine Verfeinerungspflicht |

### (b) Ein neues Wort — `impl fn f(…) refines g`

| | |
|---|---|
| **dafür** | **ein Wort, eine Aufgabe.** Greppbar, explizit, und die Pflicht entsteht, weil jemand sie hingeschrieben hat — nicht, weil zwei Namen zusammenfallen |
| **dagegen** | **ein Wort kostet.** Der Wortschatz ist geschlossen: Eintrag in `kw.rs`, Zeile in der Tafel von `SYNTAX.md`, und `pruefe-wortschatz.py`, `tests/wortschatz.rs` sowie die Terminalzählung ziehen mit. *„A new word is a language change and needs an entry here"* |

### (c) Eine Klausel, die `spec` wiederverwendet — `impl fn f(…) spec g`

| | |
|---|---|
| **dafür** | **kein neues Wort.** Und es gibt einen Präzedenzfall in derselben Produktion: «C3a» `or <reason>` steht in der Signatur und trägt den Vermerk *„Kein neues Wort: `or` steht schon im Wortschatz"* |
| **dagegen** | **`spec` bekäme zwei Aufgaben** — Qualifizierer vor `fn`, Klausel nach der Signatur. Mehrdeutig ist es nicht (verschiedene Parserzustände), aber es ist genau die Form, für die dieser Ordner schon einen offenen Posten führt: *„«P6» heißt ZWEIERLEI, und beide Register sind in Gebrauch"* ([`TODO.md`](../TODO.md):533) |

---

## 3. Die Entscheidung: **(b)**, das neue Wort

**Der Grund ist die Traglast, nicht der Preis.** Eine Verfeinerungspflicht ist die stärkste
Aussage, die diese Sprache über einen Rumpf machen kann — sie ist die Aussage, an der die
Kennzahl `0,5 : 1` hängt. *Eine Aussage dieser Stärke darf weder aus einem Zusammenfallen von
Namen entstehen (a) noch aus einem Wort, das nebenher etwas anderes tut (c).*

> **Der Preis des geschlossenen Wortschatzes ist der Punkt, nicht das Hindernis.** Er macht
> eine Sprachänderung sichtbar und zählbar. Wer ihn umgeht, indem er ein vorhandenes Wort
> doppelt belegt, hat die Änderung nicht vermieden — nur ihre Buchung.

**Und (a) bleibt zusätzlich verboten, nicht nur ungewählt:** solange `refines` nicht dasteht,
paart sich nichts. Ein `spec fn` und ein `impl fn` gleichen Namens bleiben zwei Funktionen.
*Sonst hätte die Entscheidung für (b) eine Hintertür.*

### Die Form

```ebnf
fndecl = [ "pub" ] [ "spec" | "const" | "impl" | … ] "fn" ident "(" [ params ] ")"
         [ "->" typeexpr ] [ "or" ident ]
         [ "refines" path ]                     (* NEU -- nur an einem `impl fn` *)
         [ "requires" predlist ] …
```

`refines` steht **vor** `requires`, weil die Spezifikation die Vorbedingungen mitbringt und
ein Leser sie kennen muss, bevor er die eigenen liest.

### Was das Wort kostet, genau

| Ort | |
|---|---|
| `crates/gabbro-syntax/src/kw.rs` | ein Eintrag in der Makrotafel, Klasse `res` |
| `dokumente/SYNTAX.md` | ein Wort in der Zeile `Vertraege`, plus die Produktion |
| `pruefe-syntax.sh` · `tests/wortschatz.rs` | ziehen **automatisch** nach, sobald beide Tafeln es führen — sie halten sie gegeneinander |

---

## 4. Was diese Entscheidung NICHT kauft

**Eine Form ist keine Pflicht.** Sobald `refines` steht und eine Korpusdatei es benutzt, stellt
sich die Frage, die P6 schon gemessen hat: **kann `refinement.rs` das Ziel SCHLIESSEN?** Der
Erzeuger schreibt ein Ziel nur dort, wo jede Hypothese ohne eine Semantik eines Gabbro-Rumpfs
verfügbar ist — und `messung/P6.md` misst, dass **16 der 23 wirklich offenen Pflichten** genau
daran hängen.

> **Beide Ausgänge sind Ertrag, und deshalb ist dieser Schritt vor dem teuren richtig:**
>
> | | |
> |---|---|
> | P6 **schließt** das Ziel | die Kennzahl bekommt ihren ersten `W`-Datenpunkt; `unbekannt, > 0,5` wird eine Zahl |
> | P6 **sagt ab, mit Namen** | die Absage benennt, was eine Rumpfsemantik liefern müsste — der Arbeitsauftrag für den teuren Posten, gemessen statt geschätzt |

*Was dieser Schritt ausdrücklich nicht behauptet:* dass eine Verfeinerungspflicht schon
**bewiesen** wird. Er stellt her, dass eine **entstehen** kann. Solange keine entstanden ist,
bleibt die Kennzahl zurückgezogen, und das steht so in `README.md`.

---

## 5. Gebaut und gefahren, am selben Tag — **P6 sagt ab, und die Absage ist der Ertrag**

**Die Kette steht von der Form bis zum Beweiser.** `refines` ist ein Wort, `M130`/`M131`/`M132`
halten die drei Wohlgeformtheiten, `pflichten.rs` führt die fünfte Pflichtart `R`, und
`refinement.rs` schreibt sie als Isabelle-Text:

```bash
./target/debug/gabbro pflichten beispiele/50-verfeinerung.gab
  R  Refinement of a specification (1)
       freigeben :: refines ist_frei
  == 1 obligations: 1 refinement, 0 preservation, 0 postcondition, 0 foreign, 0 precondition ==

./target/debug/gabbro pflichten --isabelle beispiele/50-verfeinerung.gab
  @duty 1  beispiele/50-verfeinerung.gab  total 1  goals 0  refused 1
  body-effect (1): speaks about the world AFTER a body ran, and there is no Isabelle
                   semantics of a Gabbro body
    duty_1  R  freigeben :: refines ist_frei
```

> **Das ist Ausgang (b) aus §4, und er war der wahrscheinlichere.** Was er kauft, ist nicht
> die Zahl, sondern ihre **Adresse**: die erste `W`-förmige Pflicht dieses Ordners existiert,
> sie ist gezählt, sie geht durch den Kanal — und sie bleibt an **genau einem** benannten
> Posten hängen. *Vorher war „die Rumpfsemantik fehlt" ein Satz über 16 `K`-Pflichten; jetzt
> ist er an einer Verfeinerungspflicht gemessen.*

**Und was das NICHT heißt:** die Kennzahl bleibt zurückgezogen. Eine Pflicht, die **entsteht**
und **abgesagt** wird, liefert keine Beweiszeile — sie liefert die Gewissheit, dass zwischen
heute und der ersten Beweiszeile **eine** Sache steht und nicht mehrere. *Das ist eine Aussage
über die Entfernung, nicht über die Ankunft.*

### Zwei Funde, die beim Bauen abgefallen sind

| | |
|---|---|
| **`M111` liest nicht durch eine `spec fn`** | Der erste Entwurf der Korpusdatei trug `ensures ist_frei(p)` und fiel: *„it names neither `result` nor a place the function writes"*. Ein `spec fn`-Aufruf im `ensures` nennt seinen Ort nicht selbst. **In dieser Datei war die Doppelung ohnehin falsch** (`refines` sagt es schon, W7) — aber die Regel trifft jeden, der eine Nachbedingung über eine Spezifikation ausdrücken will. *Gebucht, nicht behoben* |
| **die Bilanzzeile ging nicht auf** | Die erste Fassung meldete `1 obligations: 0 preservation, 0 postcondition, 0 foreign, 0 precondition`. **Eine Bilanz, die nicht aufgeht, ist die Klasse, gegen die `zaehle-p6.py` gebaut ist** — und sie entstand an genau dem Tag, an dem eine neue Art dazukam. Behoben, und ein `debug_assert_eq!` steht jetzt daneben |

### Der Preis, gemessen

| | vorher | heute |
|---|---:|---:|
| Wortschatz (EBNF-Terminale) | 216 | **217** |
| Absagekennungen | 210 | **213** |
| saubere Beispiele | 49 | **50** |
| Giftproben | 252 | **255** |
| Mutationsanker | 283 | **286** |
| Emission | 49 von 49 | **50 von 50** |

*Drei Regeln, drei Giftproben, drei Anker* — keine der drei steht ohne Messung da.
