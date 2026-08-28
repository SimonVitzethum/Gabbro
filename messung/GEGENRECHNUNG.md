# Die Gegenrechnung — was Rust+Verus+Loom heute schon abnehmen, und was übrig bleibt

*Gemessen am 2026-08-28 gegen `../caprock-messbasis`, Zweig `arch/x86_64`, **nur gelesen**.
Der Posten steht seit dem 2026-08-13 in `dokumente/PLAN.md` §6 offen.*

**Jede Zahl unten nennt den Befehl, der sie nachrechnet** (Hausordnung 6). Die Skripte liegen
in [`gegenrechnung/`](gegenrechnung/); sie rechnen, aber sie bauen nicht — der ganze Lauf ist
reines Textzählen und bleibt lokal diesseits der 1-GB-Grenze.

> **Zwei Sätze vorweg, damit niemand die falsche Hälfte liest.**
> **Die 10-%-Annahme ist gegen den Nenner des Ordners fast punktgenau richtig und gegen den
> ehrlichen Nenner um den Faktor 2,4 zu niedrig.** Und der 5 : 1-Faktor, mit dem der Ordner
> sie multipliziert, ist **an Caprocks eigenem Verus-Korpus um etwa den Faktor 3 zu hoch**.
> Die beiden Fehler heben sich im Produkt weitgehend auf. *Das ist nicht dasselbe wie richtig
> zu liegen — es heißt, dass das bedingte Ja auf zwei ungemessenen Zahlen ruht, deren Irrtümer
> zufällig in verschiedene Richtungen zeigen.*

---

## 0. Der Stand des Baumes, und warum die Zahlen um 7 abweichen

```bash
cd ../caprock-messbasis && git log --format='%h %ad %s' --date=short | head -1
# a1bf707 2026-08-14 Veralteter Kommentar: FP_SWITCHES hiess ...
```

Der Ordner hat am **2026-08-13** gemessen, also an `e561a8b`. Beides ist nachgerechnet:

```bash
cd ../caprock-messbasis
for c in e561a8b a1bf707; do
  git ls-tree -r --name-only $c | grep -E '^(kernel/src/|crates/[^/]*/src/|programs/).*\.rs$' \
  | while read f; do git cat-file -p $c:"$f" | grep -vc '^[[:space:]]*$'; done \
  | awk -v c=$c '{s+=$1} END{print c": "s}'
done
# e561a8b: 66651        <- die Zahl im Ordner
# a1bf707: 66658        <- HEAD heute
```

**Die 66 651 reproduzieren exakt.** Die sieben Zeilen Unterschied sind die drei Commits vom
2026-08-14. Alles Weitere unten rechnet gegen **HEAD (66 658)**, weil dort auch die
Verus-Beweise stehen; wo es auf die Ordner-Zahl ankommt, steht sie daneben.

---

## 1. Die 15,7 % Gerüst — nachgerechnet, und sie sind **19 849 Zeilen, nicht 10 471**

### 1a. Die Ordnerzahl reproduziert — samt einer Datei, die nicht in ihrer Liste steht

Der Ordner bucht *„`bringup.rs`, `fuzz.rs`, `selftest.rs`, `dmatests.rs` und die drei
`*mark.rs`: 10 471 Zeilen, 15,7 %"*. Das sind **sieben** Namen. Sieben Dateien ergeben aber
nur 10 221:

```bash
cd ../caprock-messbasis
for f in kernel/src/arch/x86_64/bringup.rs kernel/src/threads/fuzz.rs kernel/src/selftest.rs \
         kernel/src/dmatests.rs kernel/src/kstackmark.rs kernel/src/sperrmark.rs \
         kernel/src/userstackmark.rs kernel/src/arch/x86_64/dmar_selftest.rs; do
  grep -vc '^[[:space:]]*$' $f; done | awk '{s+=$1} END{print s}'
# 10471   -- nur MIT der achten Datei dmar_selftest.rs (250 Zeilen)
```

**Die 10 471 stimmen, die Liste dazu nicht.** Das ist ein Schönheitsfehler, kein Befund —
aber er zeigt, dass die Zahl per Dateinamen gebildet wurde. Genau daran liegt der eigentliche
Fehler.

### 1b. Das Gerüst hat ein **mechanisches** Kriterium, und es liegt bei 29,8 %

Caprock gattert seinen Prüfcode selbst, mit `#[cfg(feature = "selftest")]`,
`kernel-fuzz`, `soak`, `dfprobe`. Und `kernel/Cargo.toml` sagt es in eigenen Worten:

```bash
grep -n 'Viertel des Kernels' ../caprock-messbasis/kernel/Cargo.toml
# 24: # Farbtest, `system::testsupport`). Rund ein Viertel des Kernels ist Testcode, und er wurde bis
# 35: # `system::testsupport`. Rund ein Viertel des Kernels war Testcode und wurde bis hierher bei JEDEM
```

`gegenrechnung/vier-toepfe.py` verfolgt diese Attribute über die Klammerbilanz des folgenden
Items und trennt zugleich Kommentar von Code:

```bash
cd ../caprock-messbasis && python3 ../Gabbro/messung/gegenrechnung/vier-toepfe.py \
  $(find kernel/src crates/*/src programs -name '*.rs' | sort)
```

| | Zeilen | Anteil an 66 658 |
|---|---:|---:|
| Gerüst, Kommentar | 4 695 | 7,0 % |
| Gerüst, Code | 15 154 | 22,7 % |
| **Gerüst gesamt** | **19 849** | **29,8 %** |
| Produktion, Kommentar | 20 019 | 30,0 % |
| **Produktion, Code** | **26 790** | **40,2 %** |

**Der Ordner bucht 15,7 %; gemessen sind 29,8 %.** Der Unterschied ist kein Rundungsfehler,
sondern eine Klasse: die Dateinamensliste erfasst nur ganze Dateien. Der halbe Prüfcode
Caprocks steht aber **innerhalb** von Produktionsdateien —

```bash
cd ../caprock-messbasis && python3 ../Gabbro/messung/gegenrechnung/vier-toepfe.py \
  kernel/src/colors.rs kernel/src/handlermess.rs crates/caprock-hal/src/x86_64/irte.rs \
  crates/caprock-fat/src/lib.rs crates/caprock-mem/src/alloc.rs
```

| Datei | gegattert / nichtleer | |
|---|---:|---|
| `kernel/src/handlermess.rs` | 670 / 700 | **95,7 %** — die ganze Datei ist eine Prüfzeile |
| `kernel/src/colors.rs` | 841 / 1 440 | 58,4 % |
| `crates/caprock-hal/src/x86_64/irte.rs` | 633 / 1 430 | 44,3 % |
| `crates/caprock-fat/src/lib.rs` | 314 / 652 | 48,2 % |
| `crates/caprock-mem/src/alloc.rs` | 391 / 813 | 48,1 % |

*Damit ist der Satz des Ordners, das Gerüst sei „mehr als dreimal so groß wie alles, was die
sieben Konstrukte hart decken", nicht widerlegt, sondern **verschärft**: es ist das
Sechsfache.*

### 1c. Und 37,1 % des Baumes sind Kommentar

```bash
cd ../caprock-messbasis && grep -rhc '^\s*//' --include=*.rs kernel/src crates/*/src programs \
  | awk '{s+=$1}END{print s}'
# 24322    (vier-toepfe.py zaehlt 24714 -- Differenz: Blockkommentare und Rumpfzeilen mit //)
```

**24 714 der 66 658 nichtleeren Zeilen sind Kommentar.** Das ist der Hausstil dieses Projekts
und eine Stärke — aber eine Kommentarzeile wirft keine Beweispflicht auf. Wer eine
Beweis-zu-Code-Metrik gegen 66 651 rechnet, rechnet gegen einen Nenner, der zu **37 % Prosa**
und zu **30 % Prüfgerüst** besteht.

---

## 2. Der algorithmische Rest — nachgerechnet statt übernommen

Der Ordner bucht **45 851 Zeilen (68,8 %)**. **Diese Zahl konnte ich nicht reproduzieren.**
Sie steht in `PLAN.md`:52 ohne Herleitung und ohne Befehl (`grep -rn '45.851' dokumente/` findet
genau eine Stelle). `66 651 − 45 851 = 20 800`; die im selben Abschnitt gebuchten Posten (Gerüst
10 471 + großzügige Deckungsobergrenze ~6 000) ergeben rund 16 500. **Rund 4 300 Zeilen der
Subtraktion sind unbenannt.** Hier ist stattdessen die Zerlegung, Klasse für Klasse, mit dem
Befehl:

```bash
cd ../caprock-messbasis
python3 ../Gabbro/messung/gegenrechnung/vier-toepfe.py $(find kernel/src crates/*/src programs -name '*.rs'|sort)
python3 ../Gabbro/messung/gegenrechnung/schleifen.py  $(find kernel/src crates/*/src programs -name '*.rs'|sort)
python3 ../Gabbro/messung/gegenrechnung/klassentabelle.py
```

Die Klassenzuordnung steht **namentlich je Datei** in `klassentabelle.py` und ist damit
nachlesbar und bestreitbar — kein Regelwerk, eine Liste.

| Kl. | Klasse | Prod-**Code** | Prod-Komm. | Gerüst | Schleifen | `Ordering::` | `unsafe {` |
|---|---|---:|---:|---:|---:|---:|---:|
| **N** | nebenläufiger Kern | **8 445** | 6 420 | 1 836 | 141 | 259 | 63 |
| **T** | Tabellen + Invarianten | **7 410** | 4 901 | 1 627 | 169 | 125 | 151 |
| **D** | Treiber / HAL / Register | **4 256** | 3 105 | 100 | 67 | 85 | 134 |
| **F** | Formate / Parser | **3 175** | 2 329 | 3 265 | 77 | 0 | 8 |
| **B** | Boot / Entry / arch-Glue | **2 327** | 2 114 | 3 140 | 39 | 103 | 8 |
| **P** | Userland-Programme | **941** | 709 | 0 | 19 | 0 | 23 |
| **M** | Messcode im Produktivbau | **236** | 441 | 866 | 20 | 28 | 3 |
| **G** | reine Gerüstdateien | 0 | 0 | 9 015 | 0 | 0 | 0 |
| | **Summe** | **26 790** | 20 019 | 19 849 | **532** | **600** | **390** |

**Der algorithmische Rest ist nicht 45 851 Zeilen, sondern höchstens 26 790** — und davon
sind 4 256 Treiber, 2 327 Boot-Glue und 941 Userland, an denen kein funktionaler Beweis
hängt. Der Kern der Frage sind **N + T = 15 855 Codezeilen (59,2 % des Produktionscodes)**.

### Der Befund, der die Beweisführung des Ordners umdreht: `threads/mod.rs`

Der Ordner führt als Hauptzeugen an, *„**872 `Ordering::`-Stellen allein in `threads/mod.rs`**"*
sagten: in einem Mikrokernel sei der algorithmische Kern kein Zehntel, er **sei** der Kernel.

```bash
cd ../caprock-messbasis && head -2 kernel/src/threads/mod.rs
# //! Demo-Threads + Hot-Reload (Phase 4–7).
grep -B1 '^mod threads;' kernel/src/main.rs
# #[cfg(all(target_arch = "aarch64", feature = "selftest"))]
```

**`threads/mod.rs` ist die Demo-Thread-Datei, und sie wird auf dem gemessenen Zweig in keiner
einzigen Konfiguration übersetzt** — `arch/x86_64` ist der einzige Zweig des Repos
(`git branch -a`), und das Gatter verlangt `aarch64` **und** `selftest`. Ihre Atomics sind
Prüfstands-Telemetrie:

```bash
grep -n 'static [A-Z_0-9]*: *Atomic' kernel/src/threads/mod.rs | head
# WORKER_COUNTS, FP_OK_MASK, PRIO_DONE, KILLER_DONE, XFER_DONE, MCS_OK, STALE_STEP,
# RGONE_DONE, DDON_OK, RCAP_RESULT ...  -- *_DONE / *_OK / *_STEP / *_RESULT
```

Über den ganzen Baum:

```bash
cd ../caprock-messbasis && python3 ../Gabbro/messung/gegenrechnung/vier-toepfe.py \
  $(find kernel/src crates/*/src programs -name '*.rs'|sort) | grep Ordering
# Ordering:: Produktion 600, Geruest 1631
```

> **Von den 2 231 `Ordering::`-Vorkommen stehen 1 631 (73,1 %) in test-gegattertem Code.
> Im Produktionskernel sind es 600.** Der Satz des Ordners *„die 2 231 Atomics sind die
> Antwort auf die Frage"* misst zu drei Vierteln den Prüfstand.

*(Nebenbei: die 872 sind **Zeilen** mit `Ordering::` in `threads/mod.rs`, die 2 231 sind
**Vorkommen** im Baum. `grep -c` gegen `grep -o | wc -l`. In derselben Tabelle stehen zwei
Einheiten.)*

---

## 3. Was ein handgeschriebener funktionaler Beweis wäre — an gelesenen Stellen

Der Maßstab steht in `BEWEIS.md`: **Klempnerei nennt nur die Maschine, Logik nennt den
Gegenstand.** Drei Messungen dazu, alle am echten Code.

### 3a. Caprock hat seine Invarianten schon aufgeschrieben — **548 Codezeilen**

Die Audit-Funktionen *sind* die Formulierung der Invarianten in ausführbarer Form. Das ist
genau der Posten, den `BEWEIS.md` als unabnehmbar bucht (*„die **Formulierung** der
Invariante"*).

```bash
cd ../caprock-messbasis && python3 ../Gabbro/messung/gegenrechnung/audit-umfang.py
# 100 Code + 20 Komm.  crates/caprock-cap/src/space.rs::audit_cdt
#  74 Code + 28 Komm.  crates/caprock-sched/src/lib.rs::audit
#  47 Code + 12 Komm.  crates/caprock-microkit/src/lib.rs::domain_audit
#  ... 16 Funktionen ...
# --- SUMME: 548 Codezeilen + 112 Kommentarzeilen
```

> **548 Zeilen sind alles, was Caprock über sich selbst an Invarianten sagen kann —
> 2,0 % des Produktionscodes.** Das ist eine **gemessene Untergrenze** für die Logik im Sinne
> von `BEWEIS.md`, keine Schätzung. Die Spezifikation, die niemand abnimmt, ist klein.

### 3b. `revoke` — DAS Tor des Ordners, im echten Code gelesen

`PLAN.md` sagt: *„P0.1 (`revoke` auf Papier) ist nicht ein Tor unter vielen, sondern DAS Tor."*

```bash
cd ../caprock-messbasis && sed -n '619,661p' crates/caprock-cap/src/space.rs   # `pub fn revoke`
```

Der Rumpf hat **rund 30 Zeilen** und zwei Schleifen. Beide sind durch `cdt_step_limit()`
begrenzt, und beim Anschlag ruft Caprock `note_overrun()` und **bricht ab**:

```rust
// Der Teilbaum ist nicht baumfoermig. Abbrechen ist die einzig richtige
// Antwort — aber **gezaehlt**: dieses `revoke` ist unvollstaendig, es leben
// noch Abkoemmlinge, die weg sein sollten.
```

**Drei Feststellungen, und die dritte ist die wichtige:**

1. Die **Terminierung** ist hier ein Zähler gegen eine Schranke — *„endet, weil es über eine
   endliche Menge läuft"*, also **Klempnerei** nach `BEWEIS.md`, und sie fällt hier nicht durch
   Konstruktion, sondern durch eine Laufzeitprüfung.
2. Die **Logik**-Aussage — *„nach `revoke` hat `s` keine Abkömmlinge"* — wird von diesem Code
   **nicht hergestellt**. Er sagt selbst, dass sie verletzt sein kann.
3. `Verification/README.md` bucht `move`/`revoke`-Reachability ausdrücklich als **offene**
   Ausbaustufe. **Das Tor ist heute nicht durchschritten, in keiner Sprache** — und der Posten,
   den es kostet, ist 30 Zeilen Rumpf, nicht ein Modul.

### 3c. 532 Schleifen im Produktionscode — und **0** in allen Beweisdateien

```bash
cd ../caprock-messbasis && python3 ../Gabbro/messung/gegenrechnung/schleifen.py \
  $(find kernel/src crates/*/src programs -name '*.rs'|sort) | tail -5
# Produktionsfunktionen: 1758
#   davon mit Schleife:  248  (14.1%)
# Schleifen gesamt:      532
grep -rhoE '(^|[^\w.])(for|while)\s|(^|[^\w.])loop\s*\{' Verification/*/proofs/*.rs verus/*.rs | wc -l
# 0
grep -rho '\bdecreases\b' Verification/*/proofs/*.rs verus/*.rs | wc -l   # 12
grep -rho '\binvariant\b' Verification/*/proofs/*.rs verus/*.rs | wc -l   # 2
```

> **Das ist die schärfste Einzelzahl dieser Messung.** `PLAN.md` B1/B2 nennen die
> Schleifeninvariante als den größten Einzelposten. Caprocks 90 Verus-Beweise enthalten
> **2 Schleifeninvarianten und 12 `decreases`** — nicht weil das Problem gelöst wäre, sondern
> weil die Modelle **Zustandsübergänge** sind und keine Traversierungen. *Der Posten ist nicht
> abgetragen; er ist wegabstrahiert.* Und Verus verlangt (Commit `e561a8b`, Befund I5) ein
> `decreases` an **jeder** Schleife — an 532 Stellen, sobald man den echten Code nimmt.

---

## 4. Die Gegenrechnung: was Rust, Verus und Loom **heute schon** abnehmen

Der entscheidende Umstand: **Caprock hat die Gegenrechnung teilweise schon gefahren.** Sie
liegt im gemessenen Baum, und sie ist CI-gegated.

```bash
cd ../caprock-messbasis && sed -n '34,36p' Verification/README.md
# Gesamtstand: sieben Komponenten sind im Kern funktional verifiziert (Verus, 90 verified
# ueber 16 Dateien, CI-gated); zusaetzlich Kani-Speichersicherheit der Kategorie-A-unsafe.
ls tools/ | grep -E 'verus|kani|loom'
# kani-verify.sh  loom-verify.sh  verus-modelltreue-ipc.sh  verus-modelltreue-sched.sh
# verus-modelltreue.sh  verus-verify.sh
```

### 4a. Der Preis, gemessen: 2 266 Codezeilen Beweis

```bash
cd ../caprock-messbasis && python3 ../Gabbro/messung/gegenrechnung/spez-gegen-beweis.py
```

| | Zeilen | |
|---|---:|---|
| **Spezifikation** (`spec fn`-Rümpfe) | **527** | *unabnehmbar — die Aussage selbst* |
| Typen (Modellstrukturen) | 175 | teils unabnehmbar |
| **Beweis** (`proof fn`-Rümpfe: Lemmata, `assert`, Induktion) | **1 312** | **das, was eine Sprache abnehmen kann** |
| Rahmen / exec | 252 | |
| Kommentar | 973 | |
| **Code gesamt** | **2 266** | |

> **Beweis zu Spezifikation = 1 312 : 702 = 1,87 : 1.** In Caprocks eigenem Verus-Korpus ist
> der abnehmbare Teil fast doppelt so groß wie der unabnehmbare. *Das stützt die These des
> Ordners* — und es beziffert sie zum ersten Mal an echtem Code statt an seL4 aus dem
> Gedächtnis.

### 4b. Und der gemessene Deckungsfaktor liegt bei **0,42 : 1**, nicht bei 5 : 1

Die sieben Komponenten-Beweise unter `Verification/` (1 545 Codezeilen) decken die Kerne von
`caprock-cap` (space+object 722), `caprock-ipc` (473), `caprock-sched` (1 131),
`caprock-region` (526), `caprock-loader` (652) und `caprock-dma` (218) — zusammen
**3 722 Produktionscodezeilen**.

| Beweisdatei | Code | deckt | Code | Verhältnis |
|---|---:|---|---:|---:|
| `capability-system/proofs/cap_space.rs` | 593 | `caprock-cap/src/space.rs` | 664 | **0,89 : 1** |
| `ipc/proofs/endpoint.rs` | 372 | `caprock-ipc/src/lib.rs` | 473 | **0,79 : 1** |
| `scheduler/proofs/runqueue.rs` | 248 | `caprock-sched/src/lib.rs` | 1 131 | 0,22 : 1 |
| alle sieben | **1 545** | die sechs Crates | **3 722** | **0,42 : 1** |

> **`PLAN.md` rechnet die 10-%-Annahme mit `5 : 1` durch.** Diese Zahl steht ohne Herleitung
> im Ordner. **Gemessen an dem einzigen Ort, wo funktionale Verus-Beweise gegen echten
> Kernelcode existieren, liegt sie zwischen 0,2 : 1 und 0,9 : 1.**
>
> **Und die Gegenwarnung gehört in denselben Absatz:** das ist Deckung im **Kern**. Caprock
> bucht selbst als offen: CDT-Reachability (`move`/`revoke`), Endowment, RegionSource/Zero-Copy,
> Reply-Caps, Prioritätsauswahl, Budget-Donation, Multi-Waiter — **und durchgängig die
> Nebenläufigkeit.** Der Faktor 0,42 ist eine **Untergrenze mit benannter Fehlerrichtung**.

### 4c. Der Riss, den keine dieser Zahlen zeigt: Modell ≠ Code

```bash
cd ../caprock-messbasis && sed -n '20,21p' Verification/scheduler/proofs/runqueue.rs
# Dieses Modell hat 7 Thread-Felder und 7 Uebergaenge. `crates/caprock-sched/src/lib.rs::Tcb` hat
# 20 Felder, und 20 Funktionen schreiben Scheduler-Zustand.
sed -n '8,12p' tools/verus-modelltreue-ipc.sh
# `endpoint.rs` beweist etwas ueber ein Modell mit NEUN Feldern und ACHT Operationen.
# `caprock-ipc::Endpoint` hat SECHS Felder und rund fuenfzehn Operationen.
```

Caprock **misst diesen Riss selbst** (drei Modelltreue-Wächter) und schreibt die
Übertragungslücke je Paar auf. *Das ist die ehrlichste Stelle des ganzen fremden Baumes* — und
es ist zugleich genau der Posten, gegen den `M-Gold-3` (Spezifikation und Implementierung in
**derselben** Sprache) argumentiert. **Der Riss ist real, gemessen, und keine Sprache außer
einer, die beide Ebenen trägt, macht ihn kleiner.**

### 4d. Die Tabelle: was jede Schicht abnimmt

| Klasse | Prod-Code | (a) **Rust heute** | (b) **Verus + lineare Ghost-Permissions** | (c) **Loom** | **Rest: handgeschriebener funktionaler Beweis** *(Schätzung)* |
|---|---:|---|---|---|---:|
| **F** Formate | 3 175 | `#![forbid(unsafe_code)]` in `part`, `fat`, `loader`, `dmar`, `irte`, `dma`, `wait` — **Speichersicherheit vollständig**, gemessen: 8 `unsafe {` in 3 175 Zeilen | `ensures` = der Deskriptor; `load_gate.rs`/`trust_keydb.rs`/`loader_disjoint.rs` decken das Gate | — | **~10 %** ≈ **320** |
| **T** Tabellen | 7 410 | Ownership hält den Baum nicht; 151 `unsafe {` (Seitentabellen, IOMMU) | **der Kern des Gewinns**: `cap_inv` über install/copy/mint/delete bewiesen, 0,89 : 1. `move`/`revoke`-Reachability **offen** | — | **~45 %** ≈ **3 335** |
| **N** neben­läufiger Kern | 8 445 | `#[must_use]` an `Parked`/`MemoryCap`/`Grant`/MSI-Ticket, Typestate `Owned<Driver>`/`Owned<Device>` — echte Klassen fallen heute | *„der Aufrufer hält die Sperre"* hat in Verus eine Ausdrucksform (`tracked`-Zeuge, gemessen in `e561a8b`) | 8 Modelle **gegen den echten Quelltext** von `caprock-sync`; Rennfreiheit der Primitive erledigt | **~30 %** ≈ **2 534** |
| **D** Treiber/HAL | 4 256 | wenig — 134 `unsafe {`, MMIO | Registerlayout ja, Hardwarevertrag nein | **nein** — Loom modelliert keine Unterbrechungen (sagt `caprock-sync` selbst) | **~3 %** ≈ **128** |
| **B** Boot/Entry | 2 327 | nichts; unterhalb jedes Typsystems | nichts | nichts | **~0 %** ≈ **0** |
| **P** Userland | 941 | `forbid(unsafe_code)` in `init`, `fs`, `svc-demo` | gewöhnlich | — | **~5 %** ≈ **47** |
| **M** Messcode | 236 | — | — | — | **0 %** ≈ 0 |
| **G** Gerüst | (15 154) | — | — | — | **0 %** — *und keine Sprache sagt dazu etwas* |
| | **26 790** | | | | **≈ 6 360 = 23,7 %** |

**Die Schätzungen in der letzten Spalte sind Schätzungen.** Sie sind je Klasse an gelesenen
Stellen begründet (§3, §4b–c), aber sie sind nicht gemessen, und sie könnten je Klasse um
±10 Prozentpunkte danebenliegen. **Was gemessen ist, steht links davon.**

> **Die Restmenge, die eine Sprache rechtfertigt: rund 6 360 Codezeilen von 26 790.**
> Davon liegen **5 869 (92 %) in genau zwei Klassen: T und N.** Alles andere — Treiber, Boot,
> Userland, Formate, Gerüst — ist zusammen **493 Zeilen** Rest.
>
> ```
> F 3 175×10% = 318   T 7 410×45% = 3 335   N 8 445×30% = 2 534
> D 4 256× 3% = 128   B 2 327× 0% =     0   P   941× 5% =    47   ->  6 360
> ```

---

## 5. Die Deckungsanteile gegen den ehrlicheren Nenner

Der Ordner bucht **3 081 Zeilen hart gedeckt (4,6 %)**. Nachgerechnet:

```bash
cd ../caprock-messbasis
for f in crates/caprock-part/src/lib.rs crates/caprock-fat/src/lib.rs \
         crates/caprock-cap/src/checkpoint.rs crates/caprock-cap/src/space.rs; do
  grep -vc '^[[:space:]]*$' $f; done | awk '{s+=$1}END{print s}'
# 3081   -- reproduziert exakt
```

Aufgeschlüsselt mit `vier-toepfe.py` über dieselben vier Dateien:
**Gerüst 881, Produktionskommentar 817, Produktionscode 1 383.**

| Nenner | harte Deckung | Anteil |
|---|---:|---:|
| 66 651 nichtleere Zeilen *(Ordner)* | 3 081 | **4,6 %** |
| 46 809 Produktionszeilen *(ohne Gerüst)* | 3 081 | **6,6 %** |
| **26 790 Produktions-CODE** *(ohne Gerüst, ohne Kommentar)* | **1 383** | **5,2 %** |

**Beide Zahlen, wie verlangt: 4,6 % gegen den Ordner-Nenner, 6,6 % gegen die
Produktionszeilen** — und 5,2 %, wenn man Code gegen Code stellt, was die ehrlichste der drei
Rechnungen ist. *Die Ordner-Aussage „≤ 9 % großzügig gerechnet" wird durch keinen dieser
Nenner besser oder schlechter. Sie hält.*

---

## 6. Das Urteil über die 10-%-Annahme — mit Zahl, und zweiseitig

### Gegen den Nenner des Ordners: **sie hält, fast punktgenau**

```
6 360 Restzeilen / 66 658 nichtleere Zeilen = 9,5 %
```

Der Ordner rechnet seine Anteile gegen 66 651. Gegen diesen Nenner ist die Annahme **9,5 %
statt 10 %** — die am schlechtesten gestützte Zahl des Ordners trifft ihre eigene Skala.

### Gegen den ehrlichen Nenner: **sie ist um den Faktor 2,4 zu niedrig**

```
6 360 Restzeilen / 26 790 Produktionscodezeilen = 23,7 %
```

**Und das ist der Nenner, den `PLAN.md` selbst vorschreibt.** Die Zählregel dort lautet
*„Spezifikationszeilen je Zeile **Code**"*, mit dem Nenner „Gabbro-Code". Ein Kommentar ist
kein Code, und ein Prüfgerüst, das in Gabbro geschrieben ist, ist Code, das keinen Beweis
braucht. **Der richtige Nenner ist 26 790, und dort liegt der Anteil bei 23,7 %.**

*Damit hat der Ordner mit seiner eigenen Sorge recht:* er schreibt, *„liegt der Anteil bei
25–30 %, steht der Mittelwert jenseits von 1,5"*. **Gemessen: 23,7 %, also am unteren Rand
genau dieses Bandes.**

### Aber der zweite Faktor ist ebenso ungemessen — und er zeigt in die andere Richtung

`PLAN.md` rechnet `Anteil × 5 = Aufschlag`. Mit dem gemessenen Anteil:

| Faktor | Herkunft | Aufschlag | Metrik = 0,5 + Aufschlag |
|---|---|---:|---:|
| **5 : 1** | *im Ordner ohne Herleitung* | 0,237 × 5 = **1,19** | **1,69** |
| **1,5 : 1** | großzügige Fortschreibung von Caprocks 0,42–0,89 auf die offenen Ausbaustufen *(Schätzung)* | 0,237 × 1,5 = **0,36** | **0,86** |
| **0,9 : 1** | Caprocks gemessener Höchstwert (`cap_space.rs`) | 0,237 × 0,9 = **0,21** | **0,71** |

> **Das Ergebnis, und es ist keins von beiden allein:** die 10-%-Annahme ist **zu optimistisch
> um den Faktor 2,4**, und der 5 : 1-Faktor daneben ist **zu pessimistisch um etwa den Faktor
> 3**. Multipliziert man beide Ordner-Zahlen, kommt `0,10 × 5 = 0,50` heraus; multipliziert man
> beide gemessenen, `0,237 × 1,5 = 0,36`. **Das bedingte Ja steht — aber nicht aus dem Grund,
> den der Ordner nennt.**
>
> **Die Abbruchmarke 3 : 1 wird in keiner der drei Zeilen erreicht.** Selbst mit dem
> ungeprüften 5 : 1 landet die Rechnung bei 1,69 — jenseits der 1,5, die der Ordner fürchtet,
> und deutlich diesseits des Abbruchs.

### Und der Satz „in einem MIKROkernel ist der algorithmische Kern kein Zehntel, er IST der Kernel"

**Geprüft, und er hält nicht in dieser Form.** Drei Messungen dagegen:

1. Der Hauptzeuge des Satzes, `threads/mod.rs`, ist eine Demo-Datei, die auf dem gemessenen
   Zweig **gar nicht übersetzt wird** (§2).
2. **73 % der Atomics stehen im Prüfgerüst**, nicht im Kern (§2).
3. Der Kernel besteht zu **29,8 % aus Prüfgerüst und zu 37,1 % aus Kommentar**; von
   26 790 Codezeilen sind **59,2 %** überhaupt Kandidat (N+T), und davon braucht nach dieser
   Schätzung **weniger als die Hälfte** einen handgeschriebenen funktionalen Beweis.

**Was stattdessen hält:** *in einem Mikrokernel ist der algorithmische Kern rund ein Viertel
des Codes und praktisch der gesamte Beweisaufwand.* Das ist eine schwächere Aussage als die
des Ordners — und eine, die man verteidigen kann.

---

## 7. Was diese Rechnung **NICHT** sagt

1. **Sie sagt nicht, dass Verus den Kernel beweist.** Caprocks 90 Beweise gelten an
   **Modellen**. Der Scheduler-Beweis kennt 7 von 20 TCB-Feldern. Was zwischen Modell und Code
   liegt, ist in drei Wächtern *aufgeschrieben*, nicht *bewiesen*.
2. **Sie sagt nichts über Aufwand in Stunden.** Alle Verhältnisse sind Zeilen zu Zeilen. Eine
   Zeile `assert` kann zehn Minuten oder drei Tage kosten. **Der Ordner misst Zeilen, also
   misst diese Gegenrechnung Zeilen — beide messen damit denselben Stellvertreter.**
3. **Die letzte Spalte von §4d ist geschätzt.** Sie ist an gelesenen Dateien begründet, aber
   nicht gemessen. Wer sie je Klasse um 10 Prozentpunkte dreht, bewegt das Ergebnis zwischen
   etwa 17 % und 31 %. **Das Urteil „zu optimistisch" hält über dieses ganze Band; das Urteil
   „Faktor 2,4" hält nur in der Mitte.**
4. **Sie sagt nichts über `aarch64`.** Der Baum ist der Zweig `arch/x86_64`; `threads/`
   und die halbe aarch64-HAL werden hier nicht übersetzt. **Auf dem aarch64-Zweig sähe die
   Gerüstquote anders aus** — er ist im Ordner versiegelt und wurde nicht angesehen.
5. **Sie misst einen Kernel, der beweisbar gebaut wurde.** Caprock hat `forbid(unsafe_code)`,
   Typestate, `must_use`, Audits, Fuzzer, Kani, Verus und Loom — es ist **nicht** der
   Durchschnittskernel. Ein Kernel ohne diese Disziplin hätte einen größeren Rest.
   **Das verzerrt die Gegenrechnung zugunsten von „Rust+Verus+Loom reichen".**
6. **Sie entscheidet `revoke` nicht.** P0.1 bleibt offen: der Rumpf ist klein (30 Zeilen), die
   Aussage wird heute von niemandem hergestellt, und `Verification/README.md` bucht sie als
   offene Ausbaustufe. **Diese Messung sagt nur, wie **groß** der Posten ist, nicht, ob er
   fällt.**
7. **Die Klassenzuordnung ist eine Meinung.** `mmu.rs` steht unter T und könnte unter D
   stehen; `kernel/src/loader.rs` steht unter T und ist zur Hälfte N. Die Liste steht
   namentlich in `klassentabelle.py`, damit man sie ändern und neu rechnen kann.
   **Verschiebt man `mmu.rs` (1 742 Zeilen) von T nach D, fällt der Rest von 23,7 % auf
   21,0 %.**
8. **Sie sagt nicht, dass Gabbro sich lohnt.** Sie beziffert nur den Rest. Ob 6 400 Zeilen
   handgeschriebener Beweis eine Sprache samt Übersetzer rechtfertigen, ist eine Frage der
   Kosten der Sprache, und die steht nicht in dieser Datei.

---

## 8. Der eine Posten, den die Gegenrechnung **bestätigt**

Von den drei Größen, die diese Messung anfasst, hält eine ohne Abstrich:

> **15,7 % Mess- und Selbsttestgerüst, über das keine Sprache etwas sagt** — und gemessen
> sind es **29,8 %, also 19 849 Zeilen (davon 15 154 Code).** Code gegen Code gestellt ist das
> **so groß wie der nebenläufige Kern und die Tabellen zusammen** (8 445 + 7 410 = 15 855) und
> **fast zehnmal so groß wie die 1 545 Zeilen Beweis, die im ganzen Baum stehen.**
>
> Rust sagt dazu nichts, Verus sagt dazu nichts, Loom sagt dazu nichts. `PLAN.md` schreibt:
> *„Wenn dieser Ordner ein Recht auf Existenz als volle Sprache hat, dann hier."*
> **Diese Messung stützt genau diesen Satz — und keinen der Sätze über die Atomics.**
