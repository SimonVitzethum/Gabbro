# `narrow` gemessen — der gefaehrlichste offene Punkt geht gut aus

**2026-08-14.** Offener Punkt 1 in [`SYNTAX.md`](SYNTAX.md) lautete: *`narrow` verwandelt eine
Beweispflicht in eine Laufzeitpruefung. Kommt er haeufig vor, ist das Kriterium verletzt — Klempnerei
bliebe beim Programmierer, nur in anderer Form.* **Gemessen an 65 001 Zeilen Caprock.**

*(Die drei Agenten, die das breiter pruefen sollten, sind am Sitzungslimit gescheitert. Das hier ist
die Messung von Hand — schmaler, aber gefahren.)*

---

## Woher Indizes ihre Schranke nehmen — drei Dateien, 268 Fundstellen

| Datei | Fundstellen | **Schranke aus dem Typ moeglich** (`index into …`) | Feld | fremd/sonstiges |
|---|---|---|---|---|
| `caprock-cap/src/space.rs` (Tabelle) | 86 | **75,6 %** | 2,3 % | 22,1 % |
| `caprock-sched/src/lib.rs` (algorithmisch) | 156 | **94,9 %** | 2,6 % | 2,6 % |
| `kernel/src/threads/mod.rs` | 25 | 0 % | — | 100 % (konstante Felder wie `FP_PATTERN[id]`) |

> **Die Auswahlverzerrung, gegen die ich geprueft habe, ist nicht eingetreten.** Ich erwartete, dass
> `index into` nur in Tabellendateien traegt und im **algorithmischen** Code versagt. Gemessen ist
> es umgekehrt: der Scheduler liegt bei **94,9 %**, hoeher als der Cap-Space.

---

## Die harte Klasse: **4 Fundstellen in 65 001 Zeilen**

Flusssensitiv — der Bereich folgt aus einer **vorher geprueften Bedingung**, nicht aus dem Typ:

| | |
|---|---|
| `caprock-sched/src/lib.rs:1996` | `(31 - self.bitmap.leading_zeros())` |
| `crates/caprock-hal/src/cache_decode.rs:68` | `63 - n.leading_zeros()` |
| `kernel/src/colors.rs:864` | `u64::BITS - (n - 1).leading_zeros()` |
| `kernel/src/colors.rs:1052` | `n_lines.trailing_zeros()` |

**Alle vier sind dieselbe Redewendung: eine Bitposition aus einem Wort.** Und alle vier stehen
hinter einer Nullpruefung — `dequeue_highest` hat zwei Zeilen darueber
`if self.bitmap == 0 { return None; }`.

---

## Damit wird die Aussage ueber M1 praeziser — und schwaecher als befuerchtet

Der Entwerfer meldete: *„M1 heisst Bereichstyp und ist ein Loeser."* Das stimmt, **aber nicht in der
Allgemeinheit, in der es klingt.** Was M1 wirklich braucht:

> **Genau eine Flussregel: eine geprueste Bedingung verengt den Bereich der geprueften Groesse im
> Zweig danach.** Nach `if x == 0 { return }` ist `x : u64 in 1..`.

Das ist die billigste Form von Flusssensitivitaet und in jedem Bereichspruefer Stand der Technik.
**Was M1 NICHT braucht, ist allgemeine Inferenz.** Und mit dieser einen Regel plus einem
eingebauten `highest_bit(x: u64 in 1..) -> u32 in 0..63` traegt die Signatur den Bereich —
**alle vier Stellen sind damit ohne `narrow` schreibbar.**

- [ ] **Aus dem gefaehrlichsten offenen Punkt wird eine Entwurfsentscheidung:** M1 bekommt die
      Verengung an geprueften Bedingungen, und die Bitzaehl-Intrinsics kommen mit Vertrag statt roh.
      **`narrow` bleibt im Entwurf, aber als Notausgang fuer den Einzelfall — nicht als
      Regelfall.**

---

## Was diese Messung NICHT zeigt — sonst ist es Ueberschreibung Nr. 15

* **Der Klassierer ist eine Heuristik ueber `x[y]`-Mustern.** Er sieht **keine** Indizes, die aus
  Arithmetik oder aus einem Schleifenzaehler stammen. Die 1 398 variablen Indizierungen im ganzen
  Baum sind damit **nicht** klassifiziert, nur 268 davon.
* **„Schranke aus dem Typ moeglich" ist eine Aussage ueber die DEKLARATION, kein Beweis.** Sie
  setzt voraus, dass die Tabelle ihre Felder als `option index into slot` fuehrt. Dass das geht, ist
  Entwurf; dass es traegt, ist ungeprueft.
* **Die zweite Kandidatenklasse ist ungemessen:** 25 `-=` und 69 `a - b` auf potenziell
  vorzeichenlosen Groessen. Ein Unterlauf nach einer Pruefung ist dieselbe Form wie die vier oben —
  **wieviele davon flusssensitiv sind, weiss ich nicht.**
* **Drei Dateien sind keine Erhebung.** `programs/` ist praktisch ungemessen (eine einzige
  Fundstelle im geprueften Userspace-Modul).

- [ ] **Die 69 Subtraktionen klassifizieren.** Das ist die naechste billige Messung und die
      einzige, die das Ergebnis noch kippen kann.
