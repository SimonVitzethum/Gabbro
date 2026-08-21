# Die Handproben zu «B8» (`fnptr`)

**Belege, auf die sich [`../FNPTR.md`](../FNPTR.md) beruft** — sie stehen hier im Baum und
nicht in einem Arbeitsverzeichnis, weil *ein Bericht, der sich auf eine Datei beruft, die es
nicht mehr gibt, eine Zahl ohne Fundstellenliste in neuer Form ist.*

| Datei | was sie zeigt |
|---|---|
| `p1.gab` … `p7.gab` | die vier Hälften einzeln, jede vor ihrem Bau: Erzeuger, Ruf über einen Ort, Absenkung, Vertrag |
| `p8.gab` | **der unbebuchte Fund**: `fn(…)` lag auf `Typ::Unbekannt` und war mit allem verträglich — `let x : u32`, `: bool` und `: ptr<…> Treiber` aus **demselben** `t->bereit`, **null Typfehler in einer Datei** |
| `h1.gab`, `h2.gab` | die Gegenrichtung: dieselbe Gestalt, korrekt geschrieben |

Nachrechnen, je Datei:

```
cargo run -q --bin gabbro -- pruefe messung/fnptr-proben/p8.gab
```

> **Und was hier NICHT steht:** diese Proben sind keine Giftproben. Sie tragen keine
> `-- erwartet:`-Zeile, kein Wächter fährt sie, und `mutiere-pruefer.py` kennt sie nicht.
> *Sie sind der Beleg eines Berichts, nicht Teil der Deckung* — wer sie mit dem Giftkorpus
> verwechselt, zählt eine Deckung, die es nicht gibt.
