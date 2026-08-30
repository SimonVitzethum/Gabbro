# Die neun Suchschritte in `Table_Ops_Erhaltung.thy` — benannt, mit Vorschlag je Stelle

> ## EINGESETZT und GEBAUT, 2026-08-30 abends — alle neun
>
> **Der Satz darunter („kein Schritt hiervon steht in der Theorie") galt bis zu diesem
> Kasten und gilt nicht mehr.** Er bleibt stehen, weil er der Grund war: das Dokument
> wurde als Vorschlag geschrieben, weil `isabelle build` fehlte. *Ein Bericht wird nicht
> nachträglich richtig gemacht; was sich geändert hat, gehört daneben.*
>
> **Isabelle läuft lokal** — der 3-GB-Wachhund greift auf diesem Rechner nicht (31 GB,
> 20 Kerne). Fünfzehn Theorien in 12–20 s, Rücklauf 0.
>
> **Jede der neun Stellen wurde EINZELN gebaut**, in einer Kopie
> (`cp -r beweise $S/b`, `isabelle build -D . -o threads=4`), in dieser Reihenfolge:
>
> | # | Zeile | Vorschlag | Bau |
> |---|---|---|---|
> | 9 | 411 | `umhaengen_erhaelt[OF assms(1) assms(3) assms(4)] .` | grün |
> | 6 | 377 | `mp[OF umhaengen_ausserhalb[OF elter_da] nicht_drunter]` | grün |
> | 8 | 394 | `mp[OF umhaengen_durch_s s_neu]` | grün |
> | 1 | 281 | ausgeschriebener Widerspruch, Annahme auf `nu` benannt | grün |
> | 2 | 292 | derselbe Block | grün |
> | 3 | 293 | Kontraposition über `ueber.hoeher[OF aufstieg(1) aufstieg(2) this]` | grün |
> | 4 | 294 | `mp[OF aufstieg(4)]` | grün |
> | 5 | 348 | `mp[OF aufstieg(4) s_da]` | grün |
> | 7 | 393 | `wf[unfolded wohlgeformt_def, rule_format]` + `simp` | grün |
>
> **Neun von neun beim ersten Versuch, kein Rückfall gebraucht.** Auch die beiden
> Stellen, die dieses Dokument selbst als unsicher ausgewiesen hat, hielten:
>
> * **Die `aufstieg(n)`-Indizes waren richtig geraten** — das Dokument nannte sie
>   ausdrücklich als „der einzige Teil, der ohne Isabelle geraten ist" und stellte sie
>   unter Vorbehalt. Sie stimmten. *Der Vorbehalt war trotzdem richtig: er hat das
>   Raten als Raten ausgewiesen, statt es als Wissen zu verkaufen.*
> * **Stelle 7 brauchte den `auto`-Rückfall NICHT.** Sie trug die niedrigste
>   Zuversicht der Tabelle, und `rule_format` traf die Form.
>
> **Ergebnis:** `./instrumente/zaehle-theorien.py` meldet **31 eingefrorene
> Suchergebnisse gegen die Marke 31** — `metis 3, blast 28, smt 0`, ALL PASS.
> `MARKE_EINGEFROREN = 31` steht unverändert, und `pruefe-beweise.sh` ist grün
> (15 Theorien, 15 Dateien).
>
> Die sechs älteren `blast` der Datei (174, 187, 189, 214, 226, 228) sind unangetastet,
> wie unten vorgesehen.

**Stand 2026-08-30. Kein Schritt hiervon steht in der Theorie.** `isabelle build` war
an diesem Tag nicht erreichbar (`ki-pc-fisch-101` antwortet nicht, Sprunghost
`172.30.0.4` tot), und ein Isar-Schritt, den niemand gebaut hat, macht aus einer roten
Ratsche eine grüne Lüge. *Dieses Dokument ist der Vorschlag, nicht die Reparatur.*

## Der Stand

`./instrumente/zaehle-theorien.py` (lokal, rein zählend):

```
== Suche: 0 Suchbefehle, 40 eingefrorene Suchergebnisse ==
   eingefroren  metis 3, blast 37, smt 0   (Marke 31)
== THEORIEN: 40 eingefrorene Suchergebnisse gegen die Marke 31 ==
```

Neun über der Marke. Verteilung über alle fünfzehn Theorien:

| Datei | Zahl |
|---|---|
| **`Table_Ops_Erhaltung.thy`** | **15** |
| `Restrict_Alleinzugriff.thy` | 5 |
| `Consuming.thy` | 4 |
| `Table_Indexschranke.thy`, `Table_Absenkung.thy`, `Device_Konstruktor.thy` | je 3 |
| `Gruppe_Erhaltung.thy`, `Accumulates_Monoid.thy` | je 2 |
| `Verbund_Konstruktor.thy`, `Table_Induktion.thy`, `Format_Roundtrip.thy` | je 1 |

Summe 40. **Der Befund des Auftrags stimmt:** die neun liegen in einer Datei, und
zwar sämtlich im `umhaengen`-Beweis (`relabel`) vom 2026-08-28 — Zeilen 234–411.
Die sechs älteren `blast` derselben Datei (174, 187, 189, 214, 226, 228) gehören zu
`einfuegen` und `blatt_loeschen` und bleiben unangetastet.

**Marke 31 fällt nicht an, wenn diese neun verschwinden:** 40 − 9 = 31. Die Ratsche
wird gehalten, nicht gezogen.

## Was der Wächter zählt — und was nicht

`metis`, `blast`, `smt`. **`auto`, `simp`, `force`, `fastforce`, `rule` zählt er
nicht.** Das ist kein Schlupfloch, sondern der Gegenstand: die Marke steht seit dem
2026-08-17, weil *ein* `metis` und *ein* `blast` zusammen 21 Minuten und 11 GB
gekostet haben. Ein `rule`-Schritt mit benannter Instanz sucht überhaupt nicht.

*Trotzdem gilt: ein `blast`, das durch ein `auto` ersetzt wird, ist nur dann besser
geworden, wenn `auto` es auch schließt.* Darum steht unten je Stelle die
`rule`/`OF`-Form zuerst — sie ersetzt Suche durch Rechnung — und `auto` nur als
Rückfall.

## Die neun Stellen

### 1 + 2 — Zeile 281 und 292, identisch

```isabelle
then have ne: "y \<noteq> s" using ueber.hier by blast
```

Zu zeigen: aus `\<not> ueber \<sigma> y s` folgt `y \<noteq> s`. Der Grund ist
`ueber.hier : ueber \<sigma> s s` — wäre `y = s`, stünde die Kette da.

```isabelle
have ne: "y \<noteq> s"
proof
  assume "y = s"
  then have "ueber \<sigma> y s" by (simp add: ueber.hier)
  with nu show False ..
qed
```

*Zeile 281 liegt im `wurzel`-Fall, wo die Annahme unbenannt ist* (`assume "\<not> ueber
\<sigma> y s"`); sie braucht zuerst einen Namen, dann ist der Block wörtlich derselbe.

### 3 — Zeile 293

```isabelle
have "\<not> ueber \<sigma> q s" using nu aufstieg ueber.hoeher by blast
```

Die Kontraposition von `ueber.hoeher`: läge `s` über `q`, läge es auch über `y`.

```isabelle
have "\<not> ueber \<sigma> q s"
proof
  assume "ueber \<sigma> q s"
  from ueber.hoeher[OF aufstieg(1) aufstieg(2) this] have "ueber \<sigma> y s" .
  with nu show False ..
qed
```

### 4 — Zeile 294

```isabelle
then have q_da: "erreicht (umhaengen \<sigma> s p) q" using aufstieg by blast
```

Reiner Modus ponens auf die Induktionsvoraussetzung
(`\<not> ueber \<sigma> q s \<longrightarrow> erreicht (umhaengen \<sigma> s p) q`).

```isabelle
then have q_da: "erreicht (umhaengen \<sigma> s p) q" by (rule mp[OF aufstieg(4)])
```

### 5 — Zeile 348 (`umhaengen_durch_s`)

```isabelle
have "erreicht (umhaengen \<sigma> s p) q" using s_da aufstieg by blast
```

Dieselbe Form, andere Voraussetzung: die IH lautet hier
`erreicht (umhaengen \<sigma> s p) s \<longrightarrow> erreicht (umhaengen \<sigma> s p) q`, und `s_da` ist ihre
Prämisse.

```isabelle
have "erreicht (umhaengen \<sigma> s p) q" by (rule mp[OF aufstieg(4) s_da])
```

### 6 — Zeile 377 (`umhaengen_erhaelt`)

```isabelle
have p_neu: "erreicht (umhaengen \<sigma> s p) p"
  using elter_da nicht_drunter umhaengen_ausserhalb by blast
```

`umhaengen_ausserhalb` nimmt `erreicht \<sigma> x` und liefert eine Implikation; beide
Hälften stehen benannt da.

```isabelle
have p_neu: "erreicht (umhaengen \<sigma> s p) p"
  by (rule mp[OF umhaengen_ausserhalb[OF elter_da] nicht_drunter])
```

### 7 — Zeile 393

```isabelle
then have "erreicht \<sigma> x" using wf unfolding wohlgeformt_def by blast
```

`wohlgeformt_def` ist ein `\<forall>s sl. \<sigma> s = Some sl \<longrightarrow> erreicht \<sigma> s`; gebraucht wird die
eine Instanz bei `x`.

```isabelle
then have "erreicht \<sigma> x"
  using wf[unfolded wohlgeformt_def, rule_format] by simp
```

*Rückfall, falls `rule_format` die Form nicht trifft:* `by auto` statt `by blast` —
derselbe Schritt, ohne den Zähler.

### 8 — Zeile 394

```isabelle
then show ?thesis using s_neu umhaengen_durch_s by blast
```

```isabelle
then show ?thesis by (rule mp[OF umhaengen_durch_s s_neu])
```

### 9 — Zeile 411 (`umhaengen_erhaelt_am_belegten_platz`)

```isabelle
using assms umhaengen_erhaelt by blast
```

**Die klarste der neun.** Das Korollar führt vier Annahmen, der Satz braucht drei;
`assms(2)` (`\<sigma> s = Some sl`) ist genau die entbehrliche, über die der `text`-Block
darüber redet. Die Instanz lässt sich hinschreiben:

```isabelle
using umhaengen_erhaelt[OF assms(1) assms(3) assms(4)] .
```

## Vertrauen, ehrlich

| Stelle | Zuversicht | Grund |
|---|---|---|
| 9 (411) | **hoch** | reine Instanziierung, keine Suche, kein Unifikationsschritt |
| 6 (377), 8 (394) | **hoch** | `OF`/`mp`-Kette über benannten Lemmas |
| 1–3 (281, 292, 293) | **mittel** | ausgeschriebener Widerspruch; hängt am Namen der Annahme im jeweiligen Fall |
| 4, 5 (294, 348) | **mittel** | `aufstieg(4)` unterstellt, dass die IH die vierte Tatsache des Falles ist — **das ist am Bau abzulesen, nicht zu raten** |
| 7 (393) | **niedriger** | `rule_format` auf einem zweifach gebundenen `\<forall>`; hier ist `auto` der wahrscheinlichere Ausgang |

**Die Indizes in `aufstieg(n)` sind der einzige Teil, der ohne Isabelle geraten
ist.** Wer das baut, liest sie mit `print_cases` ab und korrigiert sie; an der
Struktur des Vorschlags ändert das nichts.

## Was hier NICHT vorgeschlagen wird

* **Die Marke zu ziehen.** Sie darf fallen, nicht steigen. Neun Suchschritte von
  gestern sind kein Grund, eine Schranke von vorgestern zu verschieben — genau das
  Muster wurde am 2026-08-17 zweimal abgelehnt.
* **Die sechs älteren `blast` derselben Datei anzufassen.** Sie liegen unter der
  Marke, sie sind nicht der Rückstand, und ein Beweis, der ohne Not umgeschrieben
  wird, ist ein Beweis, der ohne Not neu gebaut werden muss.
* **`sledgehammer` laufen zu lassen.** Verboten (`0 Suchbefehle`), und ohne Server
  ohnehin nicht zu haben.
