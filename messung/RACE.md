# Die Klasse **Rennen**, je Rennform aufgeschlüsselt — und wo die Grenze wirklich läuft

*Stand 2026-08-23. Jede Zahl unten nennt den Befehl, der sie nachrechnet (Hausordnung 6).
Gebaut und gemessen auf `ki-pc-fisch-101:gabbro-m`; lokal reicht der Speicher nicht.*

```bash
rsync -rlpgoD --delete --exclude 'target/' --exclude '__pycache__/' --exclude '.claude/' \
      ./ ki-pc-fisch-101:gabbro-m/
ssh ki-pc-fisch-101 'cd gabbro-m && export PATH=$HOME/.cargo/bin:$PATH && cargo build -q --bin gabbro'
```

> **Der Satz, der bis heute fehlte, und er ist der Ertrag dieses Laufs:**
>
> **Von 28 unterschiedenen Rennformen tragen 21 auf einer REGEL, 2 auf der AXIOMSCHICHT, 1
> auf beidem — und 4 trägt gar nichts.** *Die Klasse hängt nicht an der Axiomschicht: sie
> hängt an ihr an genau drei Stellen, und an drei weiteren an etwas anderem — dem **Alias**,
> der im Ordner bis heute keine Zahl hatte.*
>
> **Und der Nachsatz ist der unangenehmere:** von den drei Annahmen, die die Klasse wirklich
> trägt, kann **keine** heute eine laufende Sonde bekommen. §5.4.

`README.md` führt *Rennen* als hängend mit dem Grund *„an der Axiomschicht". Das ist für
`publishes`/`awaits` richtig und für den Rest der Klasse zu bequem.* Die Aufschlüsselung
unten ist der Beleg.

---

## 1. Die Tafel: 28 Rennformen, 24 mit einem Träger und 4 ohne

**Was eine „Rennform" ist:** eine unterscheidbare Art, wie zwei nebenläufige Zugriffe auf
denselben Ort einander in die Quere kommen können — oder wie ein Mechanismus, der das
verhindern soll, ins Leere greift. Die Liste ist aus den **Konstrukten der Sprache**
abgeleitet (`lock`, `rcu`, `atomic`, `entry`, `accumulates`, `dma`, `ptr`), nicht aus einer
Literaturliste. *Sie ist damit vollständig gegenüber dem, was Gabbro AUSSPRECHEN kann, und
sagt nichts über das, was es nicht ausspricht.*

Legende: **Regel** = ein Pass sagt ab · **Axiom** = eine `assume`-Zeile trägt es ·
**nichts** = kein Pass, keine Annahme.

| # | Rennform | getragen von | woran es sonst hängt |
|---:|---|---|---|
| 1 | Zugriff auf einen `protects`-Platz ohne die Sperre | **Regel** `H007` | — |
| 2 | Schreiben unter GETEILTER Nahme | **Regel** `H001` | — |
| 3 | `shared` genommen ohne `shared held`-Zahl | **Regel** `H002` | — |
| 4 | Hochstufung: exklusiv innerhalb geteilt (Selbstverklemmung) | **Regel** `H003` | — |
| 5 | `shared held` erklärt, nie geteilt genommen | **Regel** `H004` *(Hinweis)* | *keine Giftprobe* |
| 6 | Geteilter Block ruft eine exklusive `requires Held(…)` | **Regel** `H005` | — |
| 7 | Rangumkehr im eigenen Rumpf (Verklemmung) | **Regel** `H006` | unvollständige Hülle → **schweigt** (R16) |
| 8 | Rangumkehr ÜBER die Aufrufgrenze | **Regel** `H012` ⚠ | dito, und s. §1.1 |
| 9 | Ein `rank`, den niemand ausrechnen kann | **Regel** `H014` | — |
| 10 | Ein Sperrname, den keine Deklaration erklärt | **Regel** `H016` | — |
| 11 | `locks L` deklariert, nirgends eingelöst (Papiersperre) | **Regel** `H011` ⚠ | s. §1.1 |
| 12 | Deklarierte Sperre, nirgends genommen | **Regel** `H008` *(Hinweis)* | *keine Giftprobe* |
| 13 | RCU-Lesen ausserhalb `observes` | **Regel** `H009` | — |
| 14 | RCU-Schreiben ohne Schreibersperre | **Regel** `H010` | — |
| 15 | Rückgabe im EIGENEN Lesebereich | **Regel** `H011` ⚠ | s. §1.1 |
| 16 | Rückgabe ohne Schreibersperre | **Regel** `H012` ⚠ | s. §1.1 |
| 17 | Die GNADENFRIST selbst | **Axiom** | `H015` verlangt die Annahme, stellt sie nicht her |
| 18 | Ein Domänenname, den keine Deklaration erklärt | **Regel** `H017` *(neu, 2026-08-23)* | — |
| 19 | Verwaiste Paarungshälfte (`awaits` ohne `publishes`, und umgekehrt) | **Regel** `V001`/`V002` | **global statt transitiv** — s. §4 |
| 20 | `relaxed`/ordnungslos mit Nutzlast | **Regel** `V004`/`V005` | nur auf der PUBLISH-Seite |
| 21 | Nutzlast nach dem `publishes` geschrieben / vor dem `awaits` gelesen | **Regel** `V006`/`V007` | `V007` steigt nicht ab |
| 22 | Die SICHTBARKEIT von release/acquire | **Axiom** | **kein Pass kann es** — s. §5 |
| 23 | Ein `entry` schreibt Geteiltes, das nichts als geteilt erklärt | **Regel** `H013` + **Axiom** `ein_kern` | auf diesem Korpus **0 Bisse** |
| 24 | Ein maskierender Träger, den ein Eintritt ohne `nested masked` erreicht | **Regel** `H101` | — |

### Und die vier, die **nichts** trägt

| # | Rennform | Stand |
|---:|---|---|
| **A1** | **Zwei Zeiger auf dasselbe Objekt, syntaktisch derselbe Ort** — `zwei(r, r)` | **nichts**, ausser bei `own` (`R004`) |
| **A2** | **Zwei Zeiger auf dasselbe Objekt, verschiedene Namen** — `w = kopfworte_von(k)` | **nichts** |
| **A3** | **Die EREIGNISHÄLFTE**: ein Schreiben durch den einen Namen entwertet den anderen nicht | **nichts** |
| **A4** | Ein atomares RMW als eigene Wechselseitigkeit (`atomic_long_inc_not_zero`) | **nicht AUSSPRECHBAR** — `atomic` ist ein Item, kein Slotfeld (`FRAGMENTE.md`, K2-F2) |

**Das ist die eigentliche Korrektur an der Buchung.** *Rennen* hängt an der Axiomschicht bei
**Nr. 17 und 22** und teilweise bei **23**. Bei **A1–A3** hängt es am Alias — und das ist
keine Aussage über das Speichermodell, sondern eine über Zeiger. Die Zahlen dazu stehen in §3.

```bash
# Die Tafel ist von Hand geführt. Was sie mechanisch stützt:
ssh ki-pc-fisch-101 'cd gabbro-m && export PATH=$HOME/.cargo/bin:$PATH && ./target/debug/gabbro paesse --je-satz' | grep -A3 sperren
head -1 beispiele/gift/*.gab | grep -oE 'erwartet: [HVR][0-9]+' | sort | uniq -c
```

### 1.1 Vier Zeilen der Tafel stehen auf **zwei Kennungen, die je zwei Regeln tragen**

`H011` und `H012` werden in `geteilt.rs` an **je zwei Stellen mit völlig verschiedenen
Regeln** vergeben:

```bash
ssh ki-pc-fisch-101 'cd gabbro-m && export PATH=$HOME/.cargo/bin:$PATH && \
  ./instrumente/pruefe-vergabe.py --liste' | grep -A3 'H01[12]'
# H011  Aehnlichkeit 0.45   2 Probe(n)
#      geteilt.rs:384   ` ` declares ` ` but never takes it
#      geteilt.rs:1396  ` ` reclaims while ` ` stands in `observes`
# H012  Aehnlichkeit 0.27   2 Probe(n)
#      geteilt.rs:1166  (die Rangordnung ueber die Aufrufgrenze)
#      geteilt.rs:1416  ` ` reclaims without holding the writer lock of ` `
```

**Beide sind unter den 14 gebuchten Kandidaten** und damit kein neuer Befund — *aber der
Preis fällt in dieser Klasse an, und deshalb steht er hier:* die Giftproben prüfen auf
Kennungen. `gift/103` erwartet `H011` für die Rückgabe im Lesebereich, `gift/141` erwartet
`H011` für die nie genommene Sperre. **Fällt eine der beiden Regeln aus, bleibt die Probe
grün, weil die andere dieselbe Kennung schreibt.** Vier Zeilen der Tafel — 8, 11, 15, 16 —
stehen damit auf einer Deckungsaussage, die weniger sagt, als sie liest.

*Das ist nicht gebaut worden: eine Kennung umzuhängen berührt vier Giftproben, das
Passregister und den Korpustest, und die Ratsche `pruefe-vergabe.py` 14/41 hätte es nicht
gemerkt.* Vorschlag steht in der Übergabe.

Giftproben je Regel, gemessen: `H001` 1 · `H002` 1 · `H003` 1 · `H005` 1 · `H006` 2 ·
`H007` 1 · `H009` 1 · `H010` 1 · `H011` 2 · `H012` 2 · `H013` 2 · `H014` 1 · `H015` 1 ·
`H016` 1 · **`H017` 2** · `H101` 1 · `V001` 1 · `V002` 1 · `V004` 1 · `V005` 1 · `V006` 2 ·
`V007` 1 · `V008` 1. **`H004` und `H008` haben keine — beide sind Hinweise bzw. `H004` ist
eine Absage, die niemand misst**, und das steht so im Passregister.

---

## 2. Das Loch, das heute geschlossen ist: `H017`

**Handprobe VOR dem Bau**, an einer Datei, die seit dem 2026-08-21 im Ordner steht:

```bash
ssh ki-pc-fisch-101 'cd gabbro-m && export PATH=$HOME/.cargo/bin:$PATH && \
  ./target/debug/gabbro pruefe messung/abi-proben/unbekannte-domaene.gab'
# messung/abi-proben/unbekannte-domaene.gab: 4 Items, 0 Fehler, 0 Hinweise
```

**Dieselbe Gestalt wie `H016`, ein Konstrukt weiter** — und der Grund, warum sie hier
schlimmer ist, war vorher nicht aufgeschrieben:

> Der RCU-Wächter (`rcu_schutz`, Träger von `H009`, `H010`, `H011`, `H012`, `H015`) wird
> **überhaupt nur aufgerufen, wenn die Einheit mindestens eine Domäne deklariert.** Eine
> Datei ohne `rcu`, die `observes X { … }` schreibt, betritt ihn nie.

Zwei Gestalten, zwei Giftproben, und die zweite ist die gefährlichere:

| Probe | Lage | vor `H017` |
|---|---|---|
| `gift/271-observes-ohne-domaene.gab` | keine `rcu`-Deklaration in der Einheit | **0 Fehler** — der Wächter läuft nicht |
| `gift/272-observes-tippfehler-in-der-domaene.gab` | `BACCT` deklariert, `observes BACT` geschrieben | **`H009` und `H007`** — abgesagt an der falschen Stelle |

**Die zweite ist der Grund, warum die Regel nicht bloss Kosmetik ist.** Ein Tippfehler im
Domänennamen fiel vorher als *„`Konten.slots` gehört zur RCU-Domäne `BACCT`, und `lesen`
steht nicht in `observes`"* — **zwei Zeilen unter einem `observes BACT`.** *Der Leser sieht
einen geschützten Zugriff, der Pass sieht einen ungeschützten, und die Absage redet über die
falsche Sache.*

```bash
ssh ki-pc-fisch-101 'cd gabbro-m && export PATH=$HOME/.cargo/bin:$PATH && \
  ./target/debug/gabbro pruefe beispiele/gift/271-observes-ohne-domaene.gab \
                               beispiele/gift/272-observes-tippfehler-in-der-domaene.gab'
# 271: [H017] this `observes` names `NIEDADOM`, and no `rcu` declaration explains it
# 272: [H017] `BACT` … + [H007] + [H009]  -- die drei nebeneinander sind der Befund
```

Zwei Mutationen, beide gefangen, **und jede von einer ANDEREN Probe** (`cargo test` auf
`gabbro-m`, je einzeln gesetzt und byteweise zurückgenommen):

| Mutation | beschädigt | gefangen von |
|---|---|---|
| `domaene-ohne-deklaration-geht-durch` | `H017` fällt ganz aus | `gift/271` |
| `domaenenprobe-steigt-nicht-ab` | nur der oberste Anweisungsrand wird abgesucht | `gift/272` |

*Deshalb steht `observes` in `272` in einem `if`-Zweig:* eine Probe mit beiden `observes` auf
oberster Ebene hätte die zweite Mutation überleben lassen, und die Deckungsaussage hätte
gestimmt, ohne zu stimmen.

### Was `H017` NICHT prüft

* **nicht, dass die Domäne die richtige ist.** Wer `observes BACCT` schreibt, wo `BQUOTA`
  gemeint war, und beide sind deklariert, kommt durch. Das fängt `H009` — aber nur, wenn der
  Ort zu einer *anderen* deklarierten Domäne gehört.
* **nicht an der Bibliotheksgrenze**, und dort kann es heute nichts: `abi.rs` trägt
  **kein** `rcu`-Item in ein `.gabi` (`messung/ABI.md` §5 führt `rcu` unter den 14
  ungemessenen Item-Arten). Es gibt keinen Weg, eine Domäne zu importieren, also nichts
  auszunehmen. **Wenn `rcu` die Grenze überquert, ist diese Regel die Stelle, an der die
  Ausnahme steht** — `H016` zeigt die Form.
* **null Bisse auf dem Korpus und auf den Fragmenten.**
  ```bash
  ssh … './target/debug/gabbro fragmente dokumente/FRAGMENTE.md' | grep -c H017   # 0
  ```
  `FRAGMENTE.md`:1969 trägt ein `observes TASKLIST` ohne Deklaration — es steht dort als
  **freier Block**, nicht in einem Rumpf, und die Regel läuft über Funktionsrümpfe. *Der
  Beleg ist damit Gift, nicht Korpus* — dieselbe Lage wie bei `H013` und `H101`.

### Die Nachbarn derselben Gestalt, gemessen

`messung/ABI.md` §6.1 nannte drei offene Ausprägungen: `rcu`, `entry`, `group`. Zwei sind
jetzt erledigt oder waren es schon:

| Konstrukt | Handprobe | Befund |
|---|---|---|
| `rcu` | `messung/race-proben/` | **geschlossen** durch `H017` |
| `entry … dispatch nirgends` | `messung/race-proben/eintritt-nirgends.gab` | **war nie offen** — `N018` fällt: *„`dispatch eintr::nirgends` of `syscall` names no declared function"* |
| `group G over { A, NIEDATAB }` | `messung/race-proben/gruppe-unbekannter-traeger.gab` | **offen** — der unerklärte Träger bleibt still; abgesagt wurde `U007` über etwas anderes |

*Der `group`-Fall ist nicht gebaut worden: er gehört der Klasse **Verbindungs-Invariante**,
nicht Rennen, und ein Bau darin wäre ein Eingriff in einen Pass, um den dieser Lauf nicht
ging.* Er ist in der Übergabe als Posten formuliert.

---

## 3. Die Aliasfläche — gemessen, nicht analysiert

**`m3.rs` sagt es über sich selbst, seit es geschrieben ist:** *„Er ist kein
Alias-Analysator. Zwei `ptr<normal, rw>` auf dasselbe Objekt bleiben ununterscheidbar."*
Der Satz ist ehrlich und er ist **keine Zahl**. Eine Aliasanalyse ist der grösste
Einzeleingriff der offenen Liste, und die Entscheidung dazu ist nicht gefallen.

> **Eine gemessene Fläche macht die spätere Entscheidung möglich; eine gebaute Analyse ohne
> Entscheidung ist Vertrauensfläche.**

Gebaut ist deshalb ein **Zähler**, kein Pass: `gabbro alias` (`crates/gabbro-check/src/alias.rs`).
Er sagt nichts ab und kann es nicht.

```bash
ssh ki-pc-fisch-101 'cd gabbro-m && export PATH=$HOME/.cargo/bin:$PATH && \
  ./target/debug/gabbro alias --summe beispiele/*.gab messung/netz/*.gab \
                              messung/treiber/*.gab messung/caprock/*.gab'
```

```
# TOTAL over 53 units

functions: 213   ·   with at least one pointer parameter: 86

S1  signatures with >= 2 pointer parameters        10   (writable: 9)
S2  call sites passing >= 2 pointer arguments       3   (writable: 2)
S3  ... of those with two arguments of one root     0   (writable: 0)
S4  re-views `fn(ptr A) -> ptr B`                   2   (taken at 0 sites)
S5  bodies writing through one, reading another     5
```

**Fünf Schichten, jede echt enger als die darüber — und zwei obere Schranken gegen zwei
untere.** *Nur eine der beiden Richtungen zu drucken hiesse, den Leser wählen zu lassen.*

| | zählt | Richtung des Fehlers |
|---|---|---|
| **S1** | Funktionen mit ≥ 2 Zeigerparametern | **über**zählt: zwei Zeiger können auf Verschiedenes zeigen |
| **S2** | Rufstellen mit ≥ 2 Zeigerargumenten | **über**zählt, derselbe Grund |
| **S3** | davon: zwei Argumente mit derselben Wurzel | **unter**zählt (W10) |
| **S4** | Umdeutungen `fn(ptr A) -> ptr B` — die Alias-FABRIKEN | **unter**zählt |
| **S5** | S1-Rümpfe, deren `effects` durch den einen schreiben und durch den anderen lesen | überzählt innerhalb S1 |

Die fünf Fundstellen von **S5**, einzeln ausgedruckt statt geglaubt:

```
S5  beispiel::zeuge::aufloesen                writes {z} · reads {k}
S5  beispiel::handschlag::uebertragen_lassen  writes {k, r} · reads {r}
S5  netz::udp_echo::echo_beantworten          writes {k} · reads {e, w}
S5  caprock::kapraum::blatt_loeschen          writes {c, o} · reads {c}
S5  caprock::kapraum::einsammeln              writes {c, o} · reads {c}
S4  netz::udp_echo::kopfworte_von             ptr<…> IpKopf -> ptr<…> Kopfworte
S4  netz::udp_echo::udpkopf_von               ptr<…> IpKopf -> ptr<…> UdpKopf
```

### Die drei Zahlen, die die Entscheidung tragen

**(a) `S3 = 0` auf dem sauberen Korpus.** Der syntaktisch definite Alias — derselbe Name
zweimal an einem Ruf — **kommt im Korpus nicht vor.** Auf dem Giftkorpus kommt er genau
einmal vor, und das ist `gift/165`, die Probe für `R004`.

```bash
ssh … './target/debug/gabbro alias --summe beispiele/gift/*.gab' | head -9
# S3  in gift::eigen::ruft: gift::eigen::zwei(q, q) -- two pointer arguments share a root
```

> **Und daraus fällt ein Befund, den die Aufgabe nicht erwartet hat:** die Erkennung, die
> `R004` an zwei `own`-Parametern leistet, **ist genau S3**. Der Unterschied ist eine
> einzige Bedingung — `R004` verlangt `Recht::Eigen`, S3 nicht. *Die A1-Hälfte zu schliessen
> braucht keine Aliasanalyse, sondern das Streichen einer Rechteprüfung in `m3.rs`.*
>
> **Sie ist trotzdem nicht gebaut worden, und der Grund ist die Zahl: `S3 = 0`.** Regel A —
> kein Konstrukt ohne ein Programm, das es gebraucht hat. *Eine gemessene Null ist ein
> Ergebnis.* Der einzige Beleg wäre `messung/race-proben/zwei-zeiger-ein-objekt.gab`, und
> das ist eine Datei, die für diesen Zweck geschrieben wurde — **ein Bedarf, den ich selbst
> erfunden habe, ist kein Bedarf** (W3/R7).

Die Probe steht trotzdem im Ordner, weil sie den Zustand belegt:

```bash
ssh … './target/debug/gabbro pruefe messung/race-proben/zwei-zeiger-ein-objekt.gab'
# 4 Items, 0 Fehler, 0 Hinweise      <- `verschraenken(r, r)` auf zwei `ptr<normal, rw>`
ssh … './target/debug/gabbro alias  messung/race-proben/zwei-zeiger-ein-objekt.gab'
# S3  ... 1   (writable: 1)
```

**(b) `S4 = 2`, an 0 Stellen genommen.** Die zwei Umdeutungen des Korpus stehen beide in
`udp-echo.gab` und werden **in derselben Datei nie gerufen**. *Der Alias entsteht dort nicht
durch einen Ruf, sondern durch die SIGNATUR* — `echo_beantworten` bekommt `k` und `w`
nebeneinander von aussen gereicht, und `kopfworte_von` steht daneben als die Erklärung, was
`w` ist.

**(c) `S5 = 5`, davon `1` mit echtem RFC-Belang.** Der Fall aus der Aufgabe, nachgerechnet:

```bash
ssh … './target/debug/gabbro pruefe messung/netz/udp-echo.gab'
# messung/netz/udp-echo.gab: 25 Items, 0 Fehler, 0 Hinweise
```

`echo_beantworten(e, k, w, meine_ip)` liest die IPv4-Prüfsumme über `w : ptr<normal, r>
Kopfworte` (via `kopf_gueltig` → `kopfsumme` → `summe_1071`) und schreibt danach `k.quelle`,
`k.ziel` und `k.ttl` über `k : ptr<normal, rw> IpKopf` — **dieselben zwanzig Bytes**, und
`kopfworte_von` sagt es. RFC 791 §3.1 verlangt die Prüfsumme danach neu gerechnet.
**0 Fehler, 0 Hinweise.**

> ***Die Rechtehälfte stimmt dort; es fehlt die EREIGNISHÄLFTE.*** `w` trägt `r`, `k` trägt
> `rw`, jeder Zugriff ist im Recht. Was fehlt, ist eine Aussage der Form *„ein Schreiben
> durch `k` entwertet, was durch `w` gelesen wurde"* — und die ist **keine Rechteprüfung und
> keine Aliasanalyse**, sondern dieselbe Bauart wie `V006` an der Paarung: eine
> **Reihenfolge** zwischen zwei benannten Stellen.

**Die Fläche dafür ist S5 = 5**, und sie ist klein genug, dass eine Regel darüber messbar
wäre — und gross genug, dass sie nicht null ist. *Das ist die Zahl, die die Entscheidung
möglich macht; getroffen ist sie hier nicht.*

### Was KEINE der fünf Schichten sieht

Ein Alias über einen **Tabellenindex**, über eine **ganzzahlige Adresse** oder in einem Rufer
zwei Rahmen weiter oben hinterlässt in keiner dieser Zahlen eine Spur. `udp-echo` steht in S4
und S5, **weil `kopfworte_von` als Funktion hingeschrieben ist**; wäre dieselbe Umdeutung
durch Adressarithmetik gemacht, wäre jede Zahl hier um eins kleiner und am Programm hätte
sich nichts geändert. **Alle fünf zählen, was die QUELLE SAGT.**

---

## 4. Was die Paarung wirklich trägt — und wo sie schwächer ist, als sie liest

Die Rennformen 19–21 stehen auf `V001`–`V008`. Der Vorbehalt aus dem Passregister ist für
die Rennklasse zentral genug, um hier zu stehen:

> **Der Modulkopf sagt TRANSITIV, der Code nimmt die GLOBALE Menge.** Beide Mengen werden
> über **alle** Funktionen des Baums vereinigt; der Aufrufgraph steuert nur ein
> Unvollständigkeitsmerkmal bei. **Ein `publishes` in Modul A paart mit einem `awaits` in
> Modul B ohne jede Aufrufbeziehung.**

Die wahre Aussage lautet: *irgendwo in dieser Übersetzungseinheit gibt es ein Gegenstück.*
Das ist grob in die sichere Richtung — es meldet **weniger** Waisen — und **weit schwächer,
als es sich liest.** Für Rennform 19 heisst das konkret: *ein `awaits`, dessen `publishes` auf
einem Pfad steht, den dieser Leser nie erreicht, gilt als gepaart.*

Fläche im Korpus: **52 `publishes`-Zeilen gegen 20 `awaits`-Zeilen, 16 `atomic`-Deklarationen**
(`grep -hc` über `beispiele/*.gab`).

---

## 5. Die Axiomschicht: was von der Klasse WIRKLICH auf ihr ruht

**Drei Rennformen, und nur drei.**

| Rennform | Annahme | Klasse |
|---|---|---|
| 17 — die Gnadenfrist | `gnadenfrist_ist_abgelaufen` (A9) | falsifizierbar, Sonde `sonde_leser_noch_drin` **benannt** |
| 22 — release/acquire-Sichtbarkeit | `release_stellt_sichtbarkeit_her` (A21) | **als nicht falsifizierbar gebucht** — s. unten |
| 23 — Ausnahmen an `entry` | `ein_kern` | falsifizierbar, keine Sonde benannt |

Dazu **`sperrabdruck_haelt_fremde_kerne_fern` (A22)** — sie trägt keine Rennform der Tafel,
sondern den Beweis in `Gruppe_Erhaltung.thy`, und ist ebenfalls als nicht falsifizierbar
gebucht.

```bash
ssh ki-pc-fisch-101 'cd gabbro-m && export PATH=$HOME/.cargo/bin:$PATH && \
  ./target/debug/gabbro annahmen beispiele/*.gab' | tail -1
# -- 33 Annahmen
```

### 5.1 Die Aufgabe hatte hier eine Prämisse, und sie ist falsch

Der Auftrag nannte *„`A10` (die `release`/`acquire`-Sichtbarkeit) … eine [der 27 benannten
Sonden]"*. **Gemessen ist sie das nicht:** `release_stellt_sichtbarkeit_her` steht unter den
**sechs nicht falsifizierbaren**, also unter denen, die gar keine Sonde nennen. *Der Zähler
„0 von 27" wird von dieser Annahme nicht berührt.*

### 5.2 Und die Buchung selbst hält nicht — die Widerlegbarkeit hat eine RICHTUNG

`messung/AXIOMSCHICHT.md` gibt als Grund:

> *„das Speichermodell ist nicht durch Ausführung widerlegbar — eine erfolgreiche Probe zeigt
> nur, dass die Umordnung diesmal ausblieb"*

**Der Satz ist wahr, und er ist ein Argument über die GRÜNE Richtung.** Falsifizierbarkeit
ist die rote. *Eine einzige Beobachtung einer sichtbaren Flagge über einer veralteten
Nutzlast tötet die Annahme endgültig*, mit ausgedrucktem Zeugen; keine Zahl grüner Läufe
stützt sie je. **Solange sie als „nicht falsifizierbar" steht, ist der Gedanke, eine Sonde
für sie zu schreiben, wegdefiniert** — und genau das war bis heute der Fall.

### 5.3 Der ORT für Sonden — gebaut, für genau eine

```bash
./instrumente/pruefe-sonden.sh [--runden N]     # laeuft lokal: ein `cc` auf einer Datei
```

`sonden/` gibt es seit heute; `sonden/README.md` sagt, was dort stehen darf. Der Vertrag ist
**der dritte Zustand als Rücklaufwert** — genau die Stufe, die `SYNTAX.md`:1211 als
grammatisch nicht existierend benennt:

```
0    nicht widerlegt in diesem Lauf   -- und das ist ALLES, was es heisst
1    WIDERLEGT, oder die Sonde hat sich selbst als blind erwiesen
77   hier nicht lauffaehig
```

**Gemessen 2026-08-23 auf dem Arbeitsrechner (20 Kerne), 1,5 Mio. Runden je Arm:**

```
arm 1  release/acquire   -- the assumption under test
       observations 590605       violations 0
arm 2  relaxed/relaxed   -- the same shape without the ordering
       observations 696341       violations 0
arm 3  flag BEFORE load  -- positive control, MUST fall
       observations 204693       violations 3079
       first witness: flag 1 stood above payload 0
```

> **Der dritte Arm ist der, der die anderen zwei lesbar macht.** Eine Sonde, die nichts
> findet, hat zwei mögliche Gründe: es war nichts da, oder sie kann nicht sehen. Arm 3 kehrt
> die **Programmordnung** um — der Schreiber setzt die Flagge VOR der Nutzlast — und muss
> deshalb auf jeder Maschine fallen. *Fällt er nicht, endet die Sonde mit 1 über sich selbst.*
>
> **Arm 1 grün ist das erwartete Ergebnis und stützt die Annahme durch gar nichts.** x86 ist
> für diese Form nahe an sequentieller Konsistenz. Was der Lauf zeigt, ist ausschliesslich:
> *auf DIESER Maschine, in DIESEM Lauf, wurde keine Umordnung beobachtet* — und dass der
> Detektor sie gesehen hätte.

### 5.4 Warum genau eine, und was die 26 benannten bräuchten

**Die Einschätzung je Name ist ein Urteil, keine Messung** — sie steht hier, damit jemand sie
bestreiten kann.

| was die Sonde bräuchte | von 26 | die Namen |
|---|---:|---|
| **Ring 0** | **9** | `sonde_cr0`, `sonde_cr3`, `sonde_cr4`, `sonde_efer`, `sonde_invlpg`, `sonde_tlb_nach_cr3`, `sonde_pf_bei_p0`, `sonde_gastausbruch`, `sonde_irq_maskiert` |
| **ein GERÄT** | **9** | `sonde_vtd_srtp`, `sonde_vtd_te`, `sonde_virtio_avail`, `sonde_deskriptor_zu_frueh`, `sonde_dma_ohne_barriere`, `sonde_geraet_antwortet`, `sonde_karte_antwortet`, `sonde_zaehlwerk_antwortet`, `sonde_zeitgeber_tickt` |
| **einen Mechanismus, den der Erzeuger nicht erzeugt** | **4** | `sonde_leser_holt_ab`, `sonde_quelle_endet`, `sonde_eingabe_endet`, `sonde_leser_noch_drin` |
| **nichts — läuft im Userland** | **4** | `sonde_mxcsr_rne`, `sonde_keine_ueberbreite`, `sonde_tsc`, `sonde_rdtscp` |

```bash
ssh … './target/debug/gabbro annahmen beispiele/*.gab' | grep -o 'sonde_[a-zA-Z0-9_]*' | sort -u | wc -l
# 26
```

> **Vier von 26 könnten hier heute laufen, und gebaut ist KEINE von ihnen. Der Zähler
> `0 von 27` aus `AXIOMSCHICHT.md` §3 steht unverändert.** Die eine gebaute Sonde gehört zu
> **keinem** der 26 Namen.

*Das ist die Wahl und nicht ein Versehen.* `sonde_mxcsr_rne` wäre billiger gewesen und hätte
den Zähler auf `1 von 27` gebracht — und über Rennen nichts gesagt. **Die gebaute Sonde steht
an der Annahme, auf der die Paarung ruht**, und hat dabei den Befund aus §5.2 mitgebracht.

**Und der bitterste Einzelposten dieses Abschnitts:** von den drei Annahmen, die die
Rennklasse wirklich trägt, kann **keine** heute eine laufende Sonde bekommen —
`sonde_leser_noch_drin` bräuchte eine Gnadenfrist, die der Erzeuger nicht erzeugt;
`ein_kern` bräuchte einen Zweikernstart; und `release_stellt_sichtbarkeit_her` **hat jetzt
eine, aber unter einem Namen, den keine `falsifier`-Zeile nennt.**

---

## 6. Was diese Messung **nicht** sagt

* **Die Tafel in §1 ist von Hand geführt.** Was mechanisch gestützt ist, sind die Spalten
  *„getragen von"* (jede Kennung existiert, `pruefe-kennungen.py`) und *„Giftprobe"*
  (`head -1 beispiele/gift/*.gab`). **Die Abgrenzung der 28 Rennformen ist ein Urteil.** Eine
  29., die niemand aufgeschrieben hat, taucht hier nicht auf — die Zahl ist in dieser
  Richtung eine **untere Schranke** (W10). *Sie ist ausserdem gegenüber dem abgegrenzt, was
  Gabbro AUSSPRECHEN kann: `A4` steht in der Tafel nur, weil ein Fragment danach verlangt
  hat.*
* **`getragen` heisst nicht `bewiesen`.** Alle 51 Sätze des Passregisters stehen auf
  `measured` oder `CONJECTURED`; **`PROVED` ist 0.** Jede Zeile der Tafel ist um genau diesen
  Betrag schwächer.
* **`getragen` heisst auch nicht `gemessen am Korpus`.** `H013`, `H101` und `H017` haben auf
  dem sauberen Korpus **null Bisse**; ihr Beleg ist Gift und Mutation. Der saubere Korpus
  wirft heute nur drei `E009`-Hinweise:
  ```bash
  ssh … './target/debug/gabbro pruefe beispiele/*.gab' | grep -oE '\[[A-Z][0-9]{3}\]' | sort | uniq -c
  # 3 [E009]
  ```
* **Die Aliasfläche ist über EINHEITEN summiert.** Eine Rufstelle in Einheit A auf eine
  Funktion in Einheit B ist beiden unsichtbar; die Summe erbt diese Blindheit, statt sie zu
  heilen.
* **Der `alias`-Zähler sieht keinen Ruf über einen ORT** (`t->f(x)`): ein solcher Ruf trägt
  einen `FnZeiger`-Vertrag und keine Parameternamen. *Das ist eine Unterzählung, keine Null.*
* **Nichts hier sagt etwas über aarch64.** Die Hälfte ist versiegelt („blockiert —
  Abstammung", 2026-08-15) und wurde nicht angefasst. Insbesondere ist §5.3 Arm 1 auf x86
  gemessen; auf einer schwach geordneten Maschine wäre dieselbe Sonde ein anderer Versuch.
