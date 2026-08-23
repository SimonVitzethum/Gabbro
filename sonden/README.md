# `sonden/` — der Ort, an dem ein `falsifier` ein Programm werden kann

*Angelegt 2026-08-21. Vorher gab es ihn nicht, und das war der Befund.*

```bash
./instrumente/pruefe-sonden.sh [--runden N]
```

## Der Befund, mit dem das anfängt

[`messung/AXIOMSCHICHT.md`](../messung/AXIOMSCHICHT.md) §3, gemessen am 2026-08-21:

> **27 Annahmen nennen eine Sonde, 26 verschiedene Namen — und NULL davon existieren als
> Programm.**
>
> Ein `falsifier sonde_xyz`, dessen Sonde nirgends existiert, ist eine Zusicherung über das
> **Ausbleiben einer Widerlegung** — dieselbe Klasse wie `R15` und `W10`.

Der Abschnitt endete mit einem Satz, der kein Werkzeug hatte: *„es gibt im ganzen Ordner
keinen Ort, an dem eine Sonde stünde, kein Verzeichnis, keinen Läufer, keine Buchung über
ihren Lauf."*

**Dies ist der Ort. Er hat heute genau EINE Sonde**, und das ist Absicht: *eine Sonde, die
läuft, ist mehr wert als siebenundzwanzig, die benannt sind.*

## Warum eine Sonde nicht in Gabbro steht

`namen.rs`:1548 hält es seit dem 2026-08-19 fest: *„`expects` names an EXTERNAL probe, like
`assume … falsifier`: it does not stand in Gabbro because it RUNS."* Eine Sonde **gehört**
nicht in den Baum der geprüften Programme — sie gehört daneben, und genau das fehlte.

## Der Vertrag

| Rücklaufwert | heisst |
|---:|---|
| **0** | **nicht widerlegt in diesem Lauf** — *und das ist ALLES, was es heisst* |
| **1** | **WIDERLEGT**, oder die Sonde hat sich selbst als blind erwiesen |
| **77** | hier nicht lauffähig — kein Gerät, kein Recht, ein Kern |

**Die dritte Stufe ist die, die die Grammatik nicht hat.** `SYNTAX.md`:1211 nennt genau
diese Unterscheidung: *„Three classes, and the third does not exist syntactically: falsified
(probe ran and held), not falsifiable (with a reason), not run."* Sie existiert jetzt als
**Rücklaufwert** — das ist der ganze Unterschied zwischen einer benannten und einer
gelaufenen Sonde.

Dazu, je Sonde:

* **Erste Ausgabezeile:** `sonde <name> :: <annahme>` — die Zuordnung, die ein Mensch liest.
  *Der Läufer prüft NICHT, dass eine Sonde die Annahme trifft, die sie im Namen führt.*
* **Die Arbeitsmenge in der Ausgabe.** Ein grüner Lauf ohne Zahl daneben ist von einem
  leeren nicht zu unterscheiden (`W17`).
* **Eine eigene Empfindlichkeitsprobe.** Siehe unten — sie ist die Forderung, an der die
  meisten Sonden scheitern werden, und sie ist die wichtigste.

## Die Forderung, die eine Sonde von einem grünen Haken unterscheidet

> **Eine Sonde, die nichts findet, hat zwei mögliche Gründe: es war nichts da, oder sie kann
> nicht sehen.** Wer die beiden nicht trennt, hat keine Messung, sondern eine Beruhigung.

`sonde_release_sichtbarkeit` trennt sie mit einer **positiven Kontrolle**: einem dritten Arm,
in dem der Schreiber die Flagge absichtlich VOR der Nutzlast setzt. Dieser Arm **muss**
fallen — er verspricht das Fenster im Programm selbst, keine Umordnung nötig. *Fällt er
nicht, ist der Detektor blind, und die Sonde endet mit 1 über sich selbst.*

```
arm 3  flag BEFORE load  -- positive control, MUST fall
       observations 204693       violations 3079
```

**Gemessen 2026-08-21** auf dem Arbeitsrechner (20 Kerne): der Kontrollarm fiel 3 079-mal
bei 1,5 Mio. Runden, der Release-Arm null-mal. Die zweite Zahl ist erwartet und sagt nichts —
x86 ist für diese Form nahe an sequentieller Konsistenz.

## Die Widerlegbarkeit hat eine RICHTUNG, und die Buchung sah nur eine

`messung/AXIOMSCHICHT.md` führt `release_stellt_sichtbarkeit_her` als **nicht
falsifizierbar**, mit diesem Grund:

> *„das Speichermodell ist nicht durch Ausführung widerlegbar — eine erfolgreiche Probe zeigt
> nur, dass die Umordnung diesmal ausblieb"*

**Der Satz ist wahr, und er ist ein Argument über die GRÜNE Richtung.** Falsifizierbarkeit
ist die rote. *Eine einzige Beobachtung einer sichtbaren Flagge über einer veralteten
Nutzlast tötet die Annahme endgültig*, mit ausgedrucktem Zeugen; keine Zahl grüner Läufe
stützt sie je.

> **Das ist kein Formfehler in der Buchung, sondern eine Verwechslung von zwei Richtungen —
> und sie kostet genau das, was hier neu ist: den Ort.** Solange die Annahme als „nicht
> falsifizierbar" steht, ist der Gedanke, eine Sonde für sie zu schreiben, wegdefiniert.

**Vorschlag, nicht ausgeführt** (die Datei gehört diesem Lauf nicht): die Zeile in
`beispiele/` von `unfalsifiable "…"` auf `falsifier sonde_release_sichtbarkeit` umzustellen
und den Grund dorthin zu verschieben, wo er hingehört — in die **Auswertung** des grünen
Laufs, die die Sonde selbst druckt. Die sechs nicht falsifizierbaren würden damit **fünf**.

## Was hier NICHT stehen darf

* **Keine Sonde, deren grüner Lauf als Bestätigung gelesen werden kann.** Wer keine
  Empfindlichkeitsprobe hat, hat keine Sonde.
* **Keine ANALOGIE.** Eine Sonde für `masks_irq_schuetzt_wie_eine_sperre`, die statt
  Interrupts POSIX-Signale maskiert, misst POSIX. *Ein grüner Lauf einer Analogie ist die
  schmeichelhafte Richtung.*
* **Keine Sonde, die den Prüfer ausführt.** Was der Prüfer entscheidet, messen die
  Giftproben und der Mutationslauf. Eine Sonde misst die **Umgebung**.

## Warum genau eine — und was die 26 benannten bräuchten

Die Einzelaufstellung steht in [`messung/RACE.md`](../messung/RACE.md) §5; sie ist eine
**Einschätzung je Name, keine Messung**, und das steht dort neben der Tabelle.

| was die Sonde bräuchte | von 26 | Beispiele |
|---|---:|---|
| **Ring 0** | **9** | `sonde_cr0`, `sonde_cr3`, `sonde_cr4`, `sonde_efer`, `sonde_invlpg`, `sonde_tlb_nach_cr3`, `sonde_pf_bei_p0`, `sonde_gastausbruch`, `sonde_irq_maskiert` |
| **ein GERÄT** | **9** | `sonde_vtd_srtp`, `sonde_vtd_te`, `sonde_virtio_avail`, `sonde_deskriptor_zu_frueh`, `sonde_dma_ohne_barriere`, `sonde_geraet_antwortet`, `sonde_karte_antwortet`, `sonde_zaehlwerk_antwortet`, `sonde_zeitgeber_tickt` |
| **einen Mechanismus, den der Erzeuger nicht erzeugt** | **4** | `sonde_leser_holt_ab`, `sonde_quelle_endet`, `sonde_eingabe_endet`, `sonde_leser_noch_drin` |
| **nichts — läuft im Userland** | **4** | `sonde_mxcsr_rne`, `sonde_keine_ueberbreite`, `sonde_tsc`, `sonde_rdtscp` |

> **Vier von 26 könnten hier heute laufen, und gebaut ist KEINE von ihnen.** Die eine Sonde,
> die dasteht, gehört zu **keinem** der 26 Namen — sie gehört zu einer Annahme, die der
> Ordner als *nicht falsifizierbar* führt. **Der Zähler `0 von 27` aus `AXIOMSCHICHT.md` §3
> steht damit unverändert.**

*Das ist kein Versehen, sondern die Wahl.* `sonde_mxcsr_rne` wäre billiger gewesen und hätte
den Zähler auf `1 von 27` gebracht — und nichts über Rennen gesagt. Die gebaute Sonde steht
an der Annahme, auf der die **Paarung** ruht, also an der Klasse, um die dieser Lauf ging;
und sie hat dabei einen Befund über die BUCHUNG mitgebracht, den die billigere nicht gehabt
hätte (siehe oben, die Richtung der Widerlegbarkeit).

**Und der Name `sonde_release_sichtbarkeit` steht in keiner `falsifier`-Zeile** — es gibt
diese Sonde als Programm und nicht als Deklaration, also genau umgekehrt zu den 26. *Bis die
Zeile in `beispiele/` steht, ist sie eine Sonde ohne Verpflichtung*, und `N024` (*„a probe
belongs to exactly ONE obligation"*) hat nichts, woran es sie hielte.
