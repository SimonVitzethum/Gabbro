# `N035`, `M124`, `N029` — drei Absagen an Fragmenten, und alle drei sind RICHTIG

*Gemessen am 2026-08-31, Bahn P, Posten P-b/P-c/P-d. Je Posten ein W24-Vorlauf: die Form
hinschreiben, durch den **unveränderten** Prüfer laufen lassen, und erst danach entscheiden.*

> **Das Ergebnis in einer Zeile:** kein Konstrukt gebaut, drei Buchungen berichtigt — und der
> teuerste Beleg kommt von außen, aus `caprock-messbasis`. *Eine benannte Absage ist ein
> Ergebnis; drei sind eine Arbeitsliste, die kürzer geworden ist.*

| | Posten | gebucht als | gemessen |
|---|---|---|---|
| **P-b** | `N035` — der Funktionszeigervertrag | „Stufe 7, zu bauen" | **gebaut, gelesen und bewacht** — seit dem 2026-08-21 |
| **P-c** | `M124` — ein Grundwert kann hier nicht stehen | „ein echtes Loch" | **richtige Absage.** Die Vorlage draußen benutzt eine `const`, keinen Grund |
| **P-d** | `N029` — ein fehlbarer Ruf ohne `let … else` | „der Preis der Entscheidung *kein `?`*" | **schärfer:** der Ruf ist die unbezahlte zweite Hälfte von «B29», und **jede** Fehlerweitergabe kostet dieselben zwei eingefrorenen Zeilen |

---

# P-b — `N035`: der Vertrag ist Pflicht, und er wird GELESEN

## Was der Prüfer heute tut — sechs Sonden

| Sonde | was drinsteht | was der Prüfer sagt |
|---|---|---|
| `ohne_vertrag` | `hol : fn(u32) -> u32,` | **`N035`** — *declares no `effects` and no `costs`* |
| `mit_vertrag` | `+ effects { pure } costs <= 3 ops` | **0 Fehler** |
| `ruf_kosten` | Ruf hindurch, Rufer sagt `<= 1 ops` zu | **`K001`** — *the body costs **3*** |
| `ruf_kosten_gross` | derselbe Ruf, `<= 99 ops` | **0 Fehler** |
| `ruf_wirkung` | Zeiger verspricht `writes p.slots`, Rufer nennt nur `reads o` | **`E008`** — *calls something with `writes t.slots` but names no `writes` effect* |
| `ruf_wirkung_erklaert` | derselbe Ruf, Rufer nennt `writes t.slots` | **0 Fehler** |

**Beide Hälften des Vertrags haben einen Leser**, und das ist die Frage, auf die es ankommt —
nicht, ob die Klausel parst. Die `3` in `the body costs 3` ist die Zahl vom Zeigertyp und von
nirgendwo sonst; ohne sie stünde dort `0`.

> **Und die Rufform ist `o.hol(7)`, nicht `(o.hol)(7)`.** Die Klammerschreibung des Rust-Originals
> (`(t.senden)(b)`) fällt an `P001` — `call = ( path | place ) "(" … ")"` nimmt den Ort
> direkt. *Das ist keine Lücke, das ist die Grammatik; C lässt beide Schreibungen zu, Gabbro
> eine.*

## Ist die Fläche bewacht? — gemessen, nicht angenommen

Die Kostenhälfte von Hand mutiert (`kosten.rs::ruf`, `Some(n) => …Zahl(n)` nach `Zahl(0)`),
gebaut, ganze Sammlung gefahren: **genau eine Probe fällt**, `jedes_gift_faellt_mit_seinem_code`
über `beispiele/gift/246-indirekter-ruf-sprengt-kosten.gab`. Die Wirkungshälfte trägt
`gift/242-indirekter-ruf-verliert-huelle.gab`, die Pflicht selbst `gift/240`, und im
Mutationskatalog stehen alle drei seit dem 2026-08-21:
`indirekter-ruf-kostet-null`, `huelle-verliert-indirekten-ruf`, `fnzeiger-ohne-vertrag-geht-durch`.

**Damit ist P-b kein Bauposten, sondern eine veraltete Buchung.** `TODO.md`:2855 führt ihn
bereits als *„GEBAUT am 2026-08-21"*; `dokumente/PLAN-VOLLSTAENDIGKEIT.md` §7 nicht.

## Und die fünf `N035` in `F03` bleiben

Sie sind die **beabsichtigte** Antwort. `messung/fragmente/README.md` sagt es wörtlich:

> *„Ein eingefrorener Korpus kann unter einer neuen Absage veralten — und das ist keine
> Regression, sondern der Preis dafür, dass der Maßstab nicht mitwandert."*

Der Vertrag müsste **in die fünf Zeilen selbst**, vor das Komma (so schreibt es
`beispiele/49-dispatch-tabelle.gab`). Aus fünf Zeilen würden fünfzehn — *ein Umschreiben und
keine Ergänzung*, und die Ordnerregel lässt nur Ergänzungen zu.

---

# P-c — `M124`: die Vorlage draußen benutzt eine `const`, keinen Grund

## Die Form, kleinstmöglich

```gabbro
reason R { Ok = 0 "gut"  Voll = 9 "voll"  exhaustive }
extern fn setz(w : u64) effects { pure } costs <= 2 ops;
impl fn f() effects { pure } costs <= 4 ops { setz(R::Voll); }
```

→ **`M124`: a reason value cannot stand here.** Die Absage nennt selbst alle vier Türen
(`return` mit `or R`, Gegenstand eines `match`, `==`/`!=`, und ein Argument an einem Parameter,
dessen Typ **genau dieser Grund** ist).

Dieselbe Absicht in drei anderen Formen, **alle 0 Fehler**:

| | Form | |
|---|---|---|
| die Konstante | `const ERR_VOLL : u64 = 9;` … `setz(ERR_VOLL);` | geht durch |
| die vierte Tür | `extern fn melde(g : R)` … `melde(R::Voll);` | geht durch |
| beides nebeneinander | Grund als KANAL, Zahl als `const` | geht durch |

## Der Bedarf, außen gemessen (Regel B) — und er zeigt in die andere Richtung

`F03`:164/186/193 schreiben `set_reg(f, SYSNO_RESULT, IpcResult::ErrQuiescing)` — einen
Grundwert an einen `u64`-Parameter. **In dem Code, aus dem der Ausschnitt geschnitten ist, gibt
es an dieser Stelle keinen Aufzählungstyp:**

```rust
// caprock-messbasis, crates/caprock-abi/src/lib.rs:188
pub mod result {
    pub const OK: u64 = 0;
    pub const ERR_BADCAP: u64 = 1;
    …
    pub const ERR_QUIESCING: u64 = 8;
    pub const ERR_EP_FULL: u64 = 9;
}
```

und der Kanal daneben ist ein `Option<u64>`, kein Fehlertyp:

```rust
// crates/caprock-ipc/src/lib.rs:401
pub fn gate_new_transaction(&self) -> Option<u64> {
    if !self.used { Some(result::ERR_BADCAP) } else if self.quiescing { Some(result::ERR_QUIESCING) } else { None }
}
```

**Null Stellen im ganzen Baum projizieren eine Aufzählung auf eine Zahl.** Was der Ausschnitt
braucht, ist eine benannte `u64`-Konstante — und die hat Gabbro.

## Der Beleg, der die Frage schließt: die zwei Zahlenräume sind schon auseinandergelaufen

| Name | `reason IpcResult` (eingefroren, 2026-08-14) | ABI (`caprock-abi`, heute) |
|---|---|---|
| `Ok` | 0 | 0 |
| **`ErrBadCap`** | **2** | **1** |
| `ErrQuiescing` | 8 | 8 |
| `ErrEpFull` | 9 | 9 |

**Eine von vier Zahlen stimmt nicht**, und sie steht seit siebzehn Tagen so da, ohne dass
irgendwer es bemerkt hätte — *weil niemand die Zahl eines `reason` als ABI-Zahl liest.*

> **Genau das wäre der Ertrag einer „Zahlprojektion" gewesen:** `F03` hätte übersetzt und
> `2` ins Ergebnisregister geschrieben, wo das ABI `1` sagt. **Eine Projektion hätte aus zwei
> getrennten Zahlenräumen einen gemacht — und der falsche wäre gefahren.** *Die Zahl in einer
> `reason`-Zeile ist für den BERICHT da; sobald sie eine ABI-Zahl wird, gibt es zwei Register
> über derselben Sache (W7), und heute weichen sie ab.*

**Entschieden: `M124` ist eine richtige Absage.** Die Buchung *„`M124` ist ein echtes Loch (ein
Grundwert kann hier nicht stehen)"* fällt; was `F03` fehlt, sind vier `const`-Zeilen — und die
zu ergänzen hieße, drei Ausschnittzeilen umzuschreiben, also bleibt der Fehler stehen und
gehört ab heute dem BERICHT und nicht Gabbro.

---

# P-d — `N029`: nicht der Preis von „kein `?`", sondern die zweite Hälfte von «B29»

## Die Form GIBT es, und sie ist gemessen

`F01`:355 in die vorhandene Form gedreht, zwei Fassungen, unveränderter Prüfer:

| | was geändert wurde | was übrigbleibt |
|---|---|---|
| **a** | nur `let ok = delete_leaf(…) else (e) { }` | **`S002`** *the `else` branch of `let ok = …` falls through* — richtig: ein `else` muss enden |
| **b** | dazu `or Fehler` an `revoke` und `return Fehler::Buchfuehrung;` im `else` | **`K001`**, und sonst nichts |

```
[K001] `revoke` promises <= 16452480 ops, the body costs 16532736
```

**Die Differenz ist `80 256`** — und das ist `NSLOTS`, die Schranke der Domäne
`descendants of c.slots[s]`. *Das `let … else` kostet genau eine op, einmal je Durchgang.*

## Damit ist die Rechnung aufgemacht: es sind ZWEI eingefrorene Zeilen

| Zeile | steht in `FRAGMENTE.md` | müsste werden |
|---|---|---|
| `:337` `delete_leaf(c, o, a, rf, victim);` | ja | `let ok = … else (e) { return Fehler::Buchfuehrung; }` |
| `:328` `costs <= 16452480 ops` | ja | `costs <= 16532736 ops` |

Eine Zeile käme hinzu (`or Fehler` an `revoke`) — das wäre nach der Ordnerregel erlaubt. **Die
beiden anderen sind Umschreibungen, und die Regel lässt sie nicht zu.**

> **`F01` bleibt, wie es ist.** Es „so zu schreiben, dass es die Sprache benutzt, die es
> gibt", hieße hier, zwei Zeilen des Berichts zu erfinden — und der Bericht ist der Maßstab,
> gegen den gemessen wird.

## Und die Buchung wird schärfer, nicht nur berichtigt

Gebucht war: *„kein Sprachloch, sondern der Preis der Entscheidung «kein `?`»"*. **Das trifft
nicht.** Mit einem `?` stünde dort `delete_leaf(c, o, a, rf, victim)?;` — **auch eine geänderte
Zeile**, und die Kostenzahl bewegte sich genauso, denn die Weitergabe ist dieselbe Arbeit. *Es
gibt keine Fehlerweitergabe, die diese Zeile unverändert lässt; die einzige Sprache, in der sie
stehen bleibt, ist eine, die den Grund fallen lässt* — und genau dagegen steht `N029`.

**Der wirkliche Grund liegt eine Ebene tiefer, und er steht im eingefrorenen Bericht selbst.**
Im Original kann `delete_leaf` überhaupt nicht scheitern:

```rust
// caprock-messbasis, crates/caprock-cap/src/space.rs:1062
fn delete_leaf(&mut self, alloc: &mut PhysAllocator, slot: usize, rf: &mut Finalized<'_>) {
    …
    self.objects[obj].refcount -= 1;      // ungeprueft, kein Rueckgabewert, kein Kanal
}
```

Fehlbar wird sie erst durch «B29» — `FRAGMENTE.md`:268, den geprüften `narrow`, der die
ungeprüfte Subtraktion ersetzt:

```gabbro
narrow o.slots[obj].refcount to 1 .. 80255 else {
    return Fehler::Buchfuehrung;
}
```

> **Beide Hälften dieser einen Entscheidung stehen im selben eingefrorenen Bericht, und sie
> widersprechen einander.** Wer eine Gerufene fehlbar macht, muss es an jeder Rufstelle sagen —
> in jeder Sprache. `:268` hat es getan, `:337` nicht. *`N029` meldet nicht eine fehlende
> Sprachform, sondern eine unbezahlte Rechnung.*

---

# Was NICHT gebaut wurde, und warum

| | | |
|---|---|---|
| **keine Zahlprojektion für `reason`** | Regel B: null Fundstellen draußen, und die zwei Zahlenräume weichen heute schon ab (P-c) |
| **keine Lockerung von `M124`** | dieselbe Messung — die vierte Tür deckt den gemessenen Fall (`melde(R::Voll)` an `melde(g : R)`), der ABI-Fall braucht eine `const` |
| **kein Umschreiben von `F03`/`F01`** | die Ordnerregel lässt nur ERGÄNZUNGEN zu; beides wären Umschreibungen eingefrorener Zeilen |
| **nichts an `N035`** | die Regel ist gebaut, beide Hälften haben einen Leser, drei Giftproben und drei Mutationen stehen darauf |
