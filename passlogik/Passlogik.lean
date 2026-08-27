/-
  Passlogik -- eine Lean-4-Formalisierung der Pruefer- und Emissionslogik von Gabbro.

  **Abgeleitet aus der SPEZIFIKATION, nicht aus der Rust-Implementierung.** Keine Zeile
  unter `crates/**/*.rs` ist beim Schreiben dieser Dateien gelesen worden; die Quellen
  stehen je Datei im Kopf. *Der Wert dieser Arbeit liegt darin, dass das Modell dem Rust
  WIDERSPRECHEN kann -- wer den Rust abschreibt, vernichtet genau das.*

  Kein `mathlib`. `TODO.md`: "Der Prueferalgorithmus -- Bereichsverbaende, Wirkungshuellen
  ueber dem Aufrufgraphen, Rangordnung, Linearitaet -- ist endliche Mathematik ohne
  `mathlib`-Tiefe."

  | Datei              | Gegenstand                                      |
  |--------------------|-------------------------------------------------|
  | `Bereich.lean`     | M1, V1-V3 -- der Bereichsverband                |
  | `Wirkung.lean`     | `E005`/`E008` -- Wirkungshuelle, lokale Regel   |
  | `Kosten.lean`      | `K001`/`K002` -- Kosten als obere Schranke      |
  | `Rang.lean`        | `H006` -- Rangordnung, keine Verklemmung        |
  | `Terminierung.lean`| M4 -- die Schleifenformen und ihre Masse        |
  | `Linear.lean`      | M2 -- genau einmal je Pfad                      |
  | `Phasen.lean`      | `O001`-`O006` -- `advances` laeuft vorwaerts    |
-/
import Passlogik.Bereich
import Passlogik.Wirkung
import Passlogik.Kosten
import Passlogik.Rang
import Passlogik.Terminierung
import Passlogik.Linear
import Passlogik.Phasen
