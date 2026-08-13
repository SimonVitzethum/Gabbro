# P0.1 — `revoke` auf Papier. Ergebnis: BEDINGT, und die Bedingung ist ein fehlendes Konstrukt

**Gefahren am 2026-08-13**, gegen `crates/caprock-cap/src/space.rs:619` (echter Code, nicht
Skizze). Der Ausgang war weder das vorbereitete Ja noch das vorbereitete Nein.

---

## Was zu zeigen war

`revoke(s)` löscht den ganzen Teilbaum unter `s`. Drei Pflichten:

| | Pflicht |
|---|---|
| **T** | **Terminierung** |
| **N** | **Nachbedingung:** danach hat `s` keine Abkömmlinge |
| **I** | **Invariantenerhaltung:** `cdt_wellformed` und Kettenendlichkeit gelten weiter |

Der echte Code ist eine äussere Schleife („solange `s` ein Kind hat: zum Blatt absteigen, Blatt
löschen") mit **zwei** Schrittgrenzen und einem gezählten Abbruch, wenn der Teilbaum nicht
baumförmig ist.

---

## Erster Versuch: als `traverse`. **Scheitert, und zwar sauber**

```gabbro
traverse victims over subtree(s) by unvisited touches writes slots { delete(it); }
```

**Geht nicht.** `by unvisited` setzt eine **stabile** Menge voraus — der Fortschritt ist „noch nicht
besucht", und die besuchte Menge wächst gegen eine feste Grundmenge. `revoke` **verkleinert die
Menge, über die es läuft**. Eine Traversierung, die ihre eigene Grundmenge mutiert, ist mit
`over`/`by` nicht beschreibbar.

**Damit ist die Vorhersage aus `PLAN.md` bestätigt: `revoke` passt nicht in die vorhandenen
Konstrukte.**

## Zweiter Versuch: als `loop … variant`. **Geht, kostet aber einen HANDBEWEIS**

```gabbro
loop { let leaf = descend_to_leaf(s); delete_leaf(leaf); } variant descendants(s)
```

`variant descendants(s)` ist schreibbar. Dass er **streng fällt**, ist es nicht: dafür braucht es
*„`delete_leaf(l)` mit `l ∈ descendants(s)` verkleinert `descendants(s)` um genau 1"* — ein Lemma,
das jemand hinschreibt. **Das ist genau der Ausgang, der 0,5 : 1 ausser Reichweite bringt.**

---

## Dritter Versuch: ein Konstrukt, das FEHLT — und dann fällt alles heraus

```gabbro
traverse victims over subtree(s) by consuming touches writes slots
{ delete_leaf(it); }        -- `it : linear Member(subtree(s))`
```

**`by consuming`**: die Laufvariable ist ein **linearer Zugehörigkeitszeuge**, und der Rumpf **muss**
ihn verbrauchen. Wer ihn nicht verbraucht, übersetzt nicht — M2, ohne Sonderregel.

| Pflicht | wie sie fällt |
|---|---|
| **T** | die Menge ist durch `NSLOTS` beschränkt (M1) und schrumpft je Runde um mindestens eins, weil ein linearer Zeuge verbraucht wird. **Kein Variant, kein Lemma** |
| **N** | die Schleife endet, wenn die Menge leer ist — die Nachbedingung **ist** die Abbruchbedingung, nicht eine zusätzliche Aussage |
| **I** | `delete_leaf` ist eine **erzeugte** Operation des `table`-Konstrukts (Zuschnitt (c)). Der Erzeuger zeigt **einmal**, dass das Aushängen eines Blattes `child_points_back` und Kettenendlichkeit erhält — über der Deklaration, nicht je Aufrufstelle |

**Und ein vierter Posten fällt weg, der im echten Code Zeilen kostet:** der Zweig „Teilbaum ist
nicht baumförmig" wird **unerreichbar**. `subtree(s)` ist nur definiert, wenn die Invariante gilt;
gilt sie, gibt es den Zyklus nicht. Die zwei Schrittgrenzen, der `note_overrun`, der `break` —
alles Folgen davon, dass die Invariante im Rust-Code **nicht** getragen wird.

---

## Das Ergebnis, in drei Sätzen

1. **`revoke` ist ausdrückbar — aber nicht in den Konstrukten, die `SYNTAX.md` heute nennt.**
   Es fehlt genau eines: **die verbrauchende Traversierung**.
2. **Mit ihr sind T, N und I durch Konstruktion erledigt.** Kein Variant, kein Lemma, kein
   Schleifeninvariant von Hand — für **diesen** Rumpf.
3. **Sie ist nicht gratis:** `over subtree(s)` muss lineare Zugehörigkeitszeugen liefern. Die kommen
   aus einer **erzeugten Geistertheorie** je deklarierter Struktur.

---

## Der Nebenbefund ist wichtiger als das Ergebnis: die ZÄHLREGEL ist kaputt

Die Geistertheorie hat **keine Laufzeitwirkung**. Nach der Zählregel aus `PLAN.md` — *Spezifikation
ist, was der Übersetzer vor der Codeerzeugung löscht* — zählt sie damit **in den Zähler**.

> **Dann verschlechtert der Gold-Mechanismus die Kennzahl, je besser er wirkt.** Zuschnitt (c)
> erzeugt mehr Geistercode, also mehr „Spezifikation", also ein schlechteres Verhältnis — während
> die Arbeit, die ein Mensch leistet, sinkt.

Das ist dieselbe Klasse wie „ein Zähler, der VERSUCHE zählt, beantwortet die Frage nach der WIRKUNG
nicht". Die Regel muss lauten:

> **Spezifikation ist, was ein MENSCH schreibt und was der Übersetzer vor der Codeerzeugung löscht.**
> Erzeugter Geistercode ist weder Spezifikation noch Code — er ist **Ausgabe**.

**Gefunden hat das der Papiertest, nicht das Gegenlesen** — und er hat einen halben Tag gekostet
statt der Wochen, die eine Messung am Übersetzer gekostet hätte.

---

## Was das NICHT zeigt

* **Ein Rumpf ist kein Kernel.** `revoke` fällt heraus, weil seine Nachbedingung *„die Menge ist
  leer"* ist — eine Aussage über **Zugehörigkeit**, und Zugehörigkeit ist genau das, was ein
  linearer Zeuge trägt. Der IPC-Fastpath hat eine Nachbedingung über **Werten** (die Nachricht kam
  an, die Antwortpflicht liegt beim richtigen Thread). **Nichts hier zeigt, dass die auch fällt.**
* **Die 10 %-Annahme bleibt unbelegt.** Sie trägt die ganze bedingte Ja-Antwort und ist die am
  wenigsten gestützte Zahl des Ordners — gemessen sind **68,8 % algorithmischer Rest**.
* **Zuschnitt (c) ist damit erstmals empirisch gestützt**, nicht nur vom Ziel gefordert: ohne
  erzeugtes `delete_leaf` fällt Pflicht **I** auf einen Handbeweis zurück.

---

## Was daraus folgt

- [ ] **`by consuming` in `SYNTAX.md` aufnehmen** — mit der Geistertheorie, die es verlangt, und
      der offenen Frage, welche `over`-Mengen Zeugen liefern können.
- [ ] **Die Zählregel in `PLAN.md` berichtigen** (Mensch-geschrieben, nicht bloss gelöscht).
- [ ] **P0.4 (neu): denselben Test am IPC-Fastpath.** Er ist der Fall, für den `revoke` nichts
      aussagt — und er entscheidet die 10 %-Annahme, nicht dieser hier.
