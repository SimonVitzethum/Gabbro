# Drei Regeln des Rumpfkanals waren unbewacht — gefunden beim ersten vollen Lauf über die Vereinigung

*Schritt 6 des autonomen Plans, 2026-08-30. **Der Befund gehört der Zusammenführung, nicht
einer Bahn** — er war in keiner der beiden sichtbar, und zwar aus einem Grund, der sich
benennen lässt.*

---

## 0. Warum keine Bahn ihn sehen konnte

Bahn B hat acht Mutationen für den Rumpfkanal geschrieben und ihre Abnahme mit
**„335 von 335 Ankern"** gemeldet. Das ist wahr und es ist etwas anderes als eine Quote:

> **`--anker` prüft, ob der Ankertext im Prüfer steht. Er fährt keine einzige Mutation.**

Ein Anker, der greift, sagt: *diese Zeile gibt es noch.* Er sagt nicht: *und eine Probe fällt,
wenn sie sich ändert.* Zwischen beiden liegen zehn Minuten Rechenzeit, und deshalb steht der
volle Lauf im Plan an genau einer Stelle — **in Schritt 6, über dem vereinigten Stand.**

*Beide Bahnen waren einzeln grün. Das war kein Irrtum und keine Nachlässigkeit; es war die
Reichweite des Werkzeugs, das sie benutzt haben.*

---

## 1. Der Lauf

```
./instrumente/mutiere-pruefer.py          10 min 10 s Wanduhr, 29 min CPU (Faktor 2,9)
== 337 von 339 gueltigen Mutationen gefangen (99 %) ==
   Pruefer 213 · Code 86 · Annotation 38 · Schablone 3
   !! UEBERLEBT  lean-optionswert-ist-wieder-ein-ruf
   !! UEBERLEBT  lean-ergebnis-auch-im-rumpf
   ?? ungueltig  lean-ergebnis-ohne-wert
```

**Alle drei Auffälligkeiten stammen aus denselben acht Mutationen** — aus dem Rumpfkanal, den
Bahn B gebaut hat. Der Prüferteil des Katalogs, gewachsen über Wochen, hat keine einzige
Überlebende.

*Das ist keine Bilanz gegen Bahn B, sondern eine über Katalogalter: Mutationen, die noch nie
gefahren wurden, sind Vermutungen über Deckung. Die 213 des Prüfers sind gefahrene.*

---

## 2. Die erste Lücke — **eine Regel an zwei Armen, eine Probe an einem**

`is_option_value` steht in `lean.rs` an **zwei** Stellen: im `Let`-Arm (`:830`) und im
`Return`-Arm (`:1033`). Die Probe `lean_optionswert_ist_kein_ruf` liest
`return Some(i);` — also **nur den zweiten**.

Die Mutation beschädigt den ersten. `let n = Some(i);` läuft danach in `call_parts`, und der
Rumpf wird ganz abgesagt.

> **Zwei Arme, eine Regel, eine Probe.** Die Regel kann an einem Arm ausfallen, ohne dass
> irgendein Test fällt.

**Geheilt:** `lean_optionswert_im_let_ist_kein_ruf`. Von Hand nachgemessen — ohne Fix
ÜBERLEBT, mit Fix GEFANGEN. Gemessen wird der Text des Datums:

```
(.bindName "n" (.someOf (.name "i")))     erwartet
bodies 1, refused 0                        die Bilanzzeile dazu
```

---

## 3. Die zweite Lücke — **eine Probe, die ihren Namen trug und nicht ihren Gegenstand**

`lean_ergebnis_bleibt_im_rumpf_abgesagt` heißt so, seit sie geschrieben wurde. Ihr Programm
**nennt `result` in keinem Rumpf.** Sie las eine Nachbedingung *ohne* `result` und sicherte zu,
dass daraus kein `finalValue`-Ziel wird.

Das ist eine wahre Aussage über etwas anderes. Die Regel, nach der die Probe heißt — *`result`
im Rumpf wird bei Namen abgesagt* — konnte gelöscht werden, und sie blieb grün.

> **Dieselbe Klasse wie die `bank`-Zusicherung vom 2026-08-28**, die über der GANZEN Ausgabe
> stand und die der Schreiber allein erfüllte. *Ein Wächter, der neben seinem Gegenstand
> steht, liest sich wie Deckung.* `W16`, zum zweiten Mal in drei Tagen.

**Geheilt:** die Probe bekommt eine erste Hälfte, die `result` wirklich in einen Rumpf schreibt.
Gemessen gegen den unveränderten Prüfer, bevor irgendetwas repariert wurde (`W24`-Vorlauf):

```
gabbro pflichten --lean r.gab
    @duty 1  r.gab  total 1  goals 0  refused 1
    result-in-ensures (1): `result` in an `ensures` -- one gate away, not far
```

**Und ein kleiner Nebenbefund, unrepariert gebucht:** die Absage heißt
`result-in-ensures`, auch wenn `result` im **Rumpf** stand. *Der Name der Absage nennt den
häufigen Fall, nicht den vorliegenden* — ein Leser des Zeugnisses sucht an der falschen Stelle.
Kein Bau, eine Zeile; steht in `TODO.md`.

> **REPARIERT noch am selben Tag, und der Nebenbefund war größer als er aussah**
> (`messung/ERGEBNIS-ZWEI-NAMEN.md`). Der Rumpffall heißt seit dem 2026-08-30
> **`result-in-body`**; der Erklärtext oben — ~~*„one gate away, not far"*~~ — beschrieb
> weder ihn noch den anderen Fall, sondern einen dritten, **dessen Tor seit dem 28. offen
> steht**. Der Zeilenblock hier bleibt so stehen, wie er gemessen wurde.

---

## 4. Die dritte — **eine ungültige Mutation ist eine geschrumpfte Grundgesamtheit**

`lean-ergebnis-ohne-wert` wurde als `ungueltig` gebucht. Der Grund war ein Escape:

```
    "        \\<and> True \<and> finalValue …"      EIN Backslash -- kein Rust-Escape
```

Der mutierte Baum übersetzte nicht, und der Lauf zählte die Mutation aus dem Nenner heraus.
**337 von 339 liest sich besser als 337 von 340, und der Unterschied war ein Tippfehler.**

> *Eine gelöschte Mutation verkleinert den Nenner und liest sich wie Deckung* — dieselbe
> Bewegung, gegen die der Katalog seine Ankerprüfung hat, nur eine Ebene höher.

**Nach der Reparatur des Escapes übersetzte sie — und ÜBERLEBTE.** Und das war zu Recht so:

> **`True ∧ X` ist `X`. Eine Mutation, die eine Tautologie einfügt, beschädigt nichts.**
> Eine Überlebende darüber ist eine Aussage über die Mutation, nicht über den Prüfer.

**Neu entworfen:** statt der Tautologie steht dort jetzt eine Wiederholung des ERSTEN
Konjunkts. `v` ist danach unter dem Existenzquantor ungebunden, und das Ziel sagt *„es gibt
IRGENDEINEN Wert, für den die Zusage gilt"* statt *„der Rumpf hat einen erzeugt, und für den
gilt sie"* — genau die Verwässerung, die der Eintrag beschreibt.
`lean_ergebnis_verlangt_dass_ein_wert_entstand` fängt sie. Von Hand nachgemessen.

---

## 5. Was das NICHT heißt

**Die Quote ist keine Deckungsaussage über den Rumpfkanal.** Sie misst den Prüfer; über die
Annotationsemission sagt sie, was ihre eigene Flächentabelle sagt — 38 Mutationen, und mehr
nicht. *Eine Fläche mit 0 Mutationen ist nicht gedeckt, sondern unbeschädigbar.*

**Und die drei Namen stehen hier, nicht im Quelltext.** Sie tragen deutsche Funktionswörter
(`ist`, `ein`, `auch`, `im`), und die Englisch-Ratsche zählt sie auch mitten in einem
englischen Satz. *Zum zweiten Mal in drei Tagen hat ein Kommentar über eine Mutation die
Ratsche gebrochen, die er beschreibt* — die Namen gehören darum in dieses Dokument:

| Mutation | Fläche | Zustand vorher | Zustand nachher |
|---|---|---|---|
| `lean-optionswert-ist-wieder-ein-ruf` | annotation | ÜBERLEBT | gefangen |
| `lean-ergebnis-auch-im-rumpf` | annotation | ÜBERLEBT | gefangen |
| `lean-ergebnis-ohne-wert` | annotation | ungültig → überlebt | gefangen |
