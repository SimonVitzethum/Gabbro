# `result-in-ensures` trug zwei Fälle — und keiner davon war der, den der Name nennt

> Gemessen am 2026-08-30. **Der W24-Vorlauf hat den Posten zur Hälfte umgedreht.** Der
> Auftrag lautete, zwei Fälle zu trennen, von denen einer *„ein Tor entfernt"* sei. Gemessen
> ist: **das Tor steht seit dem 28. offen**, der Name beschreibt einen Fall, der in diesem
> Kanal überhaupt nicht mehr absagt — und was unter ihm gebucht wurde, war ein anderer.

---

## 1. W24 zuerst — beide Formen durch den UNVERÄNDERTEN Prüfer

**W24 sagt: schreib die naheliegende Form hin und miss, woran sie fällt.** Zwei Formen,
dieselbe Routine, ein Zeichen Unterschied.

### 1.1 Form A — `result` im `ensures`, Rumpf ohne `result`

```gabbro
module t {
type Kopf = { eintritt : u64, };
impl fn lies(k : ptr<normal, r> Kopf) -> u64
    ensures  result == k.eintritt
    effects  { reads k }
    costs    <= 8 ops
{ return k.eintritt; }
}
```

```
gabbro pflichten --lean a-ensures.gab
    @duty 1  a-ensures.gab  total 1  goals 1  refused 0
    -- Nothing was refused in this unit.

    theorem duty_1 (ρ : Env) (s : State)
        : ∃ s' v, finalState (exec ρ body_duty_1 s) = some s'
            ∧ finalValue (exec ρ body_duty_1 s) = some v
            ∧ eval { s' with local' := bindLocal s'.local' "result" v } post_duty_1
                = some (.bool true) := by
```

**Null Absagen.** Der Fall, den das Etikett `result-in-ensures` nennt und dessen Erklärtext
*„one gate away, not far"* verspricht, **erzeugt ein ZIEL**. Das Tor ist gebaut: `finalValue`
liefert den Wert, `bindLocal` bindet ihn unter dem Namen `result`, bevor die Nachbedingung
ausgewertet wird. *Der Satz daneben hat sein eigenes Tor überlebt.*

### 1.2 Form B — `result` im RUMPF

```gabbro
{ let x = result; return k.eintritt; }
```

```
gabbro pflichten --lean b-rumpf.gab
    @duty 1  b-rumpf.gab  total 1  goals 0  refused 1
    result-in-ensures (1): `result` in an `ensures` -- one gate away, not far
```

**Hier steht die Absage, und beide Hälften ihres Textes sind falsch.** `result` stand nicht in
einem `ensures`, sondern im Rumpf; und es ist nicht ein Tor entfernt, sondern **nie zu bauen**
— im Rumpf hat noch nichts zurückgegeben, also benennt das Wort nichts. `result` ist ein
reserviertes Wort, so dass auch kein `let` und kein Parameter es gebunden haben kann.

> *Wer das Zeugnis liest, sucht die fehlende Wertform und findet einen Programmfehler unter
> ihrem Etikett.*

### 1.3 Und der Prüfer nimmt Form B an

```
gabbro pruefe b-rumpf.gab
    b-rumpf.gab: 3 Items, 0 Fehler, 0 Hinweise
```

**Ein `result` im Rumpf ist heute kein Fehler des Prüfers**, nur eine Absage des Rumpfkanals.
Das ist ein eigener Befund und steht als solcher in `TODO.md`; er wurde hier NICHT geheilt,
weil er ein Pass ist und kein Etikett (§4).

---

## 2. Es waren nicht zwei Stellen, sondern drei — und ein `bool` hat zwei Zustände

Der Auslöser ist eine Zeile in `expr_term`, und was sie entschied, hing an `c.allow_result`:

```rust
ExprArt::Ergebnis => {
    if !c.allow_result { return Err(LeanReason::Result); }
    ...
}
```

`allow_result` ist ein `bool`. Der Kanal hat aber **drei** Orte, an denen das Wort auftreten
kann, und zwei davon sagen ab — aus entgegengesetzten Gründen:

| Ort | `allow_result` | was dort geschah | ist es ein Tor? |
|---|---|---|---|
| **Rumpf** des Pflichtenkanals (Anweisung oder Schleifeninvariante) | `false` | `result-in-ensures` | **nein — nie zu bauen** |
| **Nachbedingung** des Pflichtenkanals | `true` | Ziel, kein Wort | **gebaut, seit dem 28.** |
| **Klausel** des Ausfuhrdatums (`gabbro lean`) | `false` | `result-in-ensures` | **nein — absichtlich** |

Die dritte Zeile ist mitgemessen worden:

```
gabbro lean a-ensures.gab
    /-- `lies` -- what it PROMISES: … (dropped, and a caller is not wrong):
        ensures #1 (result-in-ensures) -/
```

**Dort ist der Name richtig** — es IST ein `ensures` — und die Absage ist eine Entscheidung,
keine Lücke: das Ausfuhrdatum verspricht bewusst weniger, weil ein Rufer das Ergebnis an
seiner eigenen Rufstelle liest. *Ein Versprechen weniger macht das Ziel eines Rufers
schwerer, nie falsch.*

Damit standen unter **einem** Namen ein Programmfehler und eine bewusste Zurückhaltung —
und der Erklärtext beschrieb den dritten Fall, der gar nicht mehr absagt.

---

## 3. Was gebaut wurde

**Der `bool` ist ein Dreizustand geworden**, und die Unterscheidung sitzt jetzt an der
STELLE, nicht am Kanal:

```rust
enum ResultSite { Body, Contract, Bound }

ExprArt::Ergebnis => match c.result_site {
    ResultSite::Body     => Err(LeanReason::ResultInBody),
    ResultSite::Contract => Err(LeanReason::Result),
    ResultSite::Bound    => { c.uses_result = true; Ok("(.name \"result\")".into()) }
},
```

*Warum an der Stelle und nicht am Kanal:* auch das Ausfuhrdatum übersetzt zuerst einen Rumpf.
Ein `result` dort ist derselbe Programmfehler wie im Pflichtenkanal, und ein Feld, das nur
sagte „welches Werkzeug läuft", hätte ihn wieder unter dem falschen Namen gebucht. Beide
Kanäle beginnen deshalb auf `Body` und wechseln, wenn sie die Klauseln erreichen.

| | Etikett | Satz daneben |
|---|---|---|
| Rumpf | **`result-in-body`** | *„`result` in a BODY, where it names nothing — a program error, not a gap"* |
| Klausel | `result-in-ensures` | *„the export datum drops it; the goal channel CARRIES it"* |

**Der zweite Satz ist mitgeändert worden, und das war nicht Kosmetik:** *„one gate away, not
far"* war seit dem 28. unwahr, ganz gleich unter welchem Namen er stand.

### 3.1 `zaehle-lean.py` führt `result-in-ensures` nicht mehr

Das Werkzeug zählt den **Pflichtenkanal**, und dorthin kann das Etikett seit dem 28. nicht
mehr gelangen: die Nachbedingung bindet `result`, die Klausel-Stelle gehört dem Ausfuhrdatum.
Eine Zeile, die immer `0` läse, sagte, der Kanal schulde etwas, das er nicht schuldet.

**Dieselbe Bewegung wie bei `division-or-bits`**, und der Grund steht dort schon im Werkzeug.
`result-in-body` steht an seiner Stelle.

---

## 4. Was NICHT gebaut wurde

* **Kein Pass, der `result` im Rumpf zurückweist.** Gemessen ist, dass `gabbro pruefe` die
  Form annimmt (§1.3) — das ist ein Befund und ein Kandidat, aber ein Pass ist Arbeit an der
  Sprache und nicht am Zeugnis, und der Bedarf ist **eine erfundene Probe, kein Korpusfund**:
  keine der 93 `.gab`-Dateien schreibt `result` in einen Rumpf. *Regel A — kein Konstrukt
  ohne gemessenen Bedarf.* Der Punkt steht in `TODO.md`.
* **Kein Tor für die Klausel-Absage des Ausfuhrdatums.** Sie ist die konservative Richtung
  und mit Grund gewählt; sie zu schließen hieße, einem Rufer ein Versprechen zu geben, das er
  an seiner eigenen Rufstelle schon hat.
* **Keine Zahl des Kanals hat sich bewegt.** 75/9/66 vor und nach dem Bau — der Korpus
  schreibt `result` in keinen Rumpf, also war die Zeile schon vorher `0`. **Das ist die
  ehrliche Auskunft über den Wert dieses Postens: er kauft kein Ziel, er heilt ein Etikett.**

---

## 5. Die zwei Mutationen

Beide sitzen auf demselben `match`-Arm und beschädigen Verschiedenes. **Ihre Namen stehen
hier und nicht in einem Quellkommentar** — `ohne`, `auch` und `im` sind Funktionswörter der
Englisch-Ratsche, und ein Mutationsname in einem Kommentar von `instrumente/` bricht sie
(einmal an diesem Tag geschehen, §6).

| Mutation | was sie wiederherstellt | wer fällt |
|---|---|---|
| `lean-ergebnis-auch-im-rumpf` | `result` wird auch im Rumpf übersetzt — das Datum sagt danach, der Rumpf lese einen Namen, den niemand bindet | `lean_ergebnis_bleibt_im_rumpf_abgesagt` |
| **`lean-ergebnis-rumpf-unter-klauselnamen`** *(neu)* | die Absage bleibt stehen und heißt wieder `result-in-ensures` — **genau der Zustand von heute früh** | `lean_ergebnis_bleibt_im_rumpf_abgesagt` |

Die erste musste **umgehängt** werden: ihr Anker war die alte `if !c.allow_result`-Zeile, die
es nicht mehr gibt. *Ein Anker, der ins Leere zeigt, fällt bei `--anker` sofort auf — der
Katalog ist gegen genau diesen Fall gebaut.*

> **Beide sind von Hand gesetzt, gebaut und gezählt worden**, und nicht nur über `--anker`
> geprüft. `--anker` sagt NICHT, ob der mutierte Baum übersetzt; zweimal an diesem Tag ist
> eine Mutation still als `ungueltig` aus dem Nenner gefallen. Gemessen, je Mutation:
> **übersetzt, und genau eine Probe von 234 fällt** — mit `--no-fail-fast` über alle
> fünfzehn Sammlungen nachgesehen, damit keine spätere Sammlung übersehen wird.

---

## 6. Gemessen, nachher

| | vorher | nachher |
|---|---:|---:|
| Absagegründe in `lean.rs` | 31 | **32** |
| Zeilen in `GRUENDE` (`zaehle-lean.py`) | 31 | **31** *(einer getauscht)* |
| `result-in-ensures` im Pflichtenkanal | 0 | **0** *(nicht mehr erreichbar)* |
| `result-in-body` im Pflichtenkanal | — | 0 |
| Pflichten · Ziele · Absagen | 75 · 9 · 66 | **75 · 9 · 66** |
| Proben | 233 | **234** |
| Mutationsanker | 345 | **346** |

**Und ein Wächter kam ROT an, bevor irgendetwas geändert war.** `pruefe-englisch.py` meldete
am unveränderten `master` **1080 deutsche Kommentarzeilen in `instrumente/`, gebucht 1072** —
`b4f6eae` hatte acht deutsche Zeilen in `mutiere-pruefer.py` hinterlassen, ohne die Marke zu
bewegen. *Eine Ratsche, die man hebt, ist keine mehr*, also sind die acht **übersetzt** worden
statt die Marke gezogen: `instrumente/` trägt englische Kommentare (CLAUDE.md), der Stand
steht wieder bei genau 1072, und die neunte Zeile fiel auf, weil sie einen Mutationsnamen mit
`ohne` zitierte. **Der Wächter hat seinen eigenen Gegenstand gefunden.**
