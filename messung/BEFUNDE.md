# Drei Stücke echter Code in Gabbro — und was dabei herausfiel

> **Der Gegenstand dieser Messung ist nicht der Code, sondern die Sprache.** Geschrieben
> wurden ein virtio-net-Treiber und zwei Stücke Caprock; gemessen wird, was Gabbro dabei
> *sagen* kann, was es *findet* und wo es *schweigt, wo es reden müsste*.
>
> Gemessen am **2026-08-20** gegen `../caprock-messbasis`, Zweig `arch/x86_64`,
> schreibgeschützt.

## Was geschrieben wurde

| Datei | Gegenstand | Bestand | Gabbro |
|---|---|---|---|
| [`treiber/virtio-net.gab`](treiber/virtio-net.gab) | virtio-net: Handshake, zwei Ringe, ARP | `caprock-virtio` 997 Z. | 269 Z. |
| [`caprock/kapraum.gab`](caprock/kapraum.gab) | Kapabilitätsraum, `revoke` | `caprock-cap/space.rs` 1188 Z. | 150 Z. |
| [`caprock/planer.gab`](caprock/planer.gab) | die sechs Blockiergründe | `caprock-sched` `BlockReasons` | 115 Z. |

Alle drei: **0 Fehler, 0 Hinweise**, erzeugen C, und das C übersetzt unter
`cc -std=c11 -Wall -Wextra -Werror -O2`.

*Die Zeilenzahlen sind kein Ertrag.* Der Bestand trägt Dinge, die hier gar nicht vorkommen
(PCI-Enumeration, Slab-Verwaltung, Statistik). Was zählt, ist, **welche Zeilen verschwinden
und warum**.

---

## 1. `revoke` — zwei geschachtelte begrenzte Schleifen werden eine Zeile

Der Bestand (`space.rs`:619-658, 41 Zeilen) schreibt:

```rust
let limit = self.cdt_step_limit();
let mut ops = 0usize;
while let Some(child) = self.slots[slot].mdb.first_child {
    let (leaf, steps) = match descend_to_leaf(self.slots.as_slice(), child, limit) {
        Ok(v) => v,
        Err(()) => { self.note_overrun(); break; }
    };
    self.note_walk(steps);
    self.delete_leaf(alloc, leaf, rf);
    ops += 1;
    if ops > limit { self.note_overrun(); break; }
}
```

Daneben steht der Kommentar, der beide Schranken erklärt: *„**Beide** Schleifen sind
begrenzt (B-5.5), und zwar aus verschiedenen Gründen."*

In Gabbro:

```gabbro
traverse opfer over descendants of c.slots[s] by consuming
    touches reads c.slots, consumes c.slots, writes c.slots, writes o.slots
{
    blatt_loeschen(c, o, opfer);
}
```

Was **nicht** dasteht und nicht dastehen muss:

* `cdt_step_limit()` — die Schranke fällt aus `count NSLOTS`
* `ops`, `steps` — der Kostenpass zählt, und `costs <= 831488 ops` wird nachgerechnet
* `descend_to_leaf` — das ist die Laufform von `by consuming`
* `note_overrun()` zweimal — die Wohlfundiertheit ist Invariante der Tabelle
* `requires ist_blatt` von Hand herstellen — die Nachordnung liefert es

**Und die Kante steht jetzt an der Tabelle.** `space.rs` führt vier Felder (`parent`,
`first_child`, `next_sibling`, `prev_sibling`) und sagt an keiner Stelle, welches
`descend_to_leaf` läuft — das steht im Rumpf, an einer Stelle. `tree { parent elter, child
erstes_kind, sibling naechstes }` sagt es einmal, und `D006`–`D008` halten es gegen den Slot.

---

## 2. Die sechs Blockiergründe — „unformulierbar" wird ein Typfehler

`caprock-sched` führt sechs Bits in einem `u8` und **vierzig Zeilen Prosa**, die erklären,
warum jeder Grund sein eigenes Bit braucht:

> *In der Menge ist genau das **unformulierbar**: `resume` entfernt `PAUSE`, `unpark` entfernt
> `PARK`, `unblock` entfernt `IPC` — keiner von ihnen entfernt `HANDLER`.*

„Unformulierbar" ist dort eine **Konvention**. In Gabbro sind es sechs
`linear ghost type`-Zeugen, und der falsche Wecker übersetzt nicht.

**Kosten zur Laufzeit: null.** Das erzeugte C ist

```c
void resume(Faeden *restrict f, uint32_t t) { … }
```

— der Zeuge ist gelöscht, und im Erzeugnis steht keine Zeile davon.

---

## Und fünf Befunde, die das Schreiben gefunden hat

*Alle fünf sind am selben Tag gefallen, und keiner kam aus dem Entwurf.*

### B1 · Die Gegenseite der Paarung ist das GERÄT, und Gabbro sucht sie in Software

`V001` verlangte an `AVAIL_IDX = i publishes { … }` eine Gegenseite: *„nothing awaits this
payload ON THIS ATOMIC"*. **Die Regel ist richtig und ihre Prämisse gilt hier nicht** — wer
den avail-Index liest, ist die Netzkarte, und ihr `awaits` steht in Silizium.

Heute schreibbar ist es nur als **Funktion**, also steht das Gerätemodell im Erzeugnis. *Das
Modell wird Code.* Offen.

### B2 · Der Paarungspass liest `check`-Rümpfe nicht

Der erste Versuch schrieb die Gerätegegenseite als **Probe** — der richtige Ort, denn eine
falsifizierbare Aussage über Hardware IST eine Probe. `V001` fiel trotzdem:
`paarung::pass` läuft über `ItemArt::Funktion` und sonst nichts.

**Dieselbe Klasse wie am selben Tag bei M1**, das über `beispiele/06` meldete *„this file has
no function body"*, während im `can_fail` gerechnet wurde. Ein `check`-Rumpf hat mehrere
Pässe, die ihn nicht lesen. Offen.

### B3 · Ein `format` hatte nur Leser — **geschlossen**

`SPRACHE.md`:355 sagt seit jeher *„Generates: reader, writer"* zu. Der Schreiber fehlte, und
`r.ethertyp = 2054;` wurde `EthArp_ethertyp(r) = 2054;` — **eine Zuweisung an einen
Funktionsaufruf, bei null Fehlern im Prüfer.**

Gefunden vom ersten Treiber, der nicht aus dem Entwurf kam: ein virtio-net muss einen
ARP-Rahmen **stellen**. Ein Bitfeld-Schreiber ist ein Lese-Ändere-Schreib-Zug auf dem ganzen
Wort; mit `scale K` gibt es **keinen** Schreiber, denn der Rückweg wäre eine Division und ob
ein Wert ohne Rest teilbar ist, sagt die Deklaration nicht.

### B4 · Die Geistlöschung ließ `return m;` stehen — **geschlossen**

Die Löschung nahm Parameter und Rückgabetyp und ließ die Anweisung stehen:
`void stufe_anerkennen(Gemein *g) { … return m; }` — ein Name, den die Signatur gerade
gelöscht hatte.

*Nie aufgefallen, weil keine `impl fn` im Korpus einen Geist zurückgibt:* `beispiele/22`
führt die ganze Bootstrecke als `extern fn`, also Prototypen, also keine Rümpfe. **Drei von
vier Stellen der Löschung waren gebaut**, und die vierte hat kein Beispiel je ausgelöst.

### B5 · Am Ruf wird der BEREICH gehalten und der NAME nicht — **geschlossen (`N030`)**

Der schwerste. `resume(w : WartetIpc)`, das den IPC-Zeugen an `pause_grund_weg` weiterreicht,
ging mit **null Fehlern** durch. Ebenso zwei `opaque type` über demselben Träger, ebenso
`u32` an einem `bool`-Parameter.

M1 hält den Bereich scharf — `nimm_klein(4000)` fällt an `M101`. Was fehlte, ist die
**nominale** Gleichheit: `Typ` ist ein Bereichsmodell, und zwei Namen über demselben Träger
sind darin dasselbe.

> **Das ist genau die Eigenschaft, für die `SPRACHE.md` diesen Fall als Musterbeispiel
> führt:** *„Lost wakeup | Z24 (ein Bit für vier Gründe) | **M2**: der Wecker verbraucht
> **genau seinen** Grund."* Die Zusage stand seit Monaten da, und kein Pass hat sie gehalten.

`N030` vergleicht **`opaque`, `linear`, `ghost`, `tagged`** — bei allen vieren ist die
Nichtaustauschbarkeit der ganze Zweck. Ein Bereichsalias bleibt durchsichtig; ihn nominal zu
nehmen wäre eine Sprachänderung und keine Lücke.

*Null Fehlalarme über 38 saubere Beispiele und 197 Giftdateien.* Zwei neue Giftproben
(`198`, `199`) und eine Mutation halten die Regel.

---

## Was der Treiber NICHT sagen konnte

Ehrlich, und ohne Umweg:

* **Der avail-Index ist kein Gabbro-`atomic`.** Er liegt im DMA-Puffer, und `atomic` ist eine
  Deklaration auf oberster Ebene. Der Treiber hier führt ihn als eigenes `atomic` neben dem
  Ring — für das erzeugte C ist das richtig, für die Wirklichkeit ist es eine Näherung.
* **`at dma` sagt nicht, welche Barriere.** Das ist als Axiomschicht gebucht, seit Monaten,
  und diese Messung bestätigt es an einem echten Treiber: `Transport::new` im Bestand nimmt
  einen Funktionszeiger, weil `fence(SeqCst)` auf aarch64 `dmb ish` wäre und Device-Memory
  nicht in dieser Domäne liegt.
* **Zwei Warteschlangen mit verschiedenem `queue_notify_off`** — die Zahl kommt aus einem
  Register, und der Treiber müsste sie je Queue getrennt halten. Das geht, aber nichts in der
  Sprache verhindert, dass jemand eine für beide nimmt. *Der Bestand nennt es den Fehlerfall,
  der bei einem Einqueue-Gerät strukturell nicht auffällt.*
