# Wie Lean auf `ki-pc-fisch-101` kam

*Gemessen 2026-08-25. Ohne `sudo`, ohne Passwort — genau wie Isabelle2025-2 am
2026-08-19 (`CLAUDE.md`, „Was sonst gilt").*

---

## Der Befehl, vollständig

```bash
ssh ki-pc-fisch-101 '
  export ELAN_HOME=$HOME/.elan
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
       -o /tmp/elan-init.sh
  sh /tmp/elan-init.sh -y --default-toolchain stable
'
```

Danach steht die Kette unter `~/.elan`:

```bash
ssh ki-pc-fisch-101 'export PATH=$HOME/.elan/bin:$PATH; elan --version; lean --version; lake --version'
#   elan 4.2.3 (b6cec7e10 2026-06-08)
#   Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6)
#   Lake version 5.0.0-src+819816b (Lean version 4.33.1)
```

| | |
|---|---|
| Ort | `~/.elan` auf `ki-pc-fisch-101` (Nutzer `fisch`) |
| Größe | **2,9 GB** (`du -sh ~/.elan`) |
| `sudo` | **nicht benutzt.** `elan` installiert vollständig ins Heimatverzeichnis |
| Passwort | **nicht nötig und nicht benutzt** |
| Version | **Lean 4.33.1**, festgehalten in `passlogik/lean-toolchain` |

> **Dieselbe Version wie lokal.** `lean-toolchain` nennt `leanprover/lean4:v4.33.1`; ein
> Bau, der lokal grün ist, ist es auf dem Server aus demselben Grund. *Zwei Ketten mit
> zwei Versionen wären dieselbe Klasse wie `rsync -a` gegen `cargo` — ein Werkzeug, das
> eine Mischung misst.*

---

## Zwei Fallen, beide gemessen

### 1. `elan --version` lädt noch keine Werkzeugkette herunter

`elan-init.sh` legt nur `elan` selbst an und **schreibt** die Standardkette in die
Konfiguration. Heruntergeladen wird sie erst beim **ersten `lean`-Aufruf**. Der dauert
mehrere Minuten (`~200 MB` komprimiert, 2,9 GB ausgepackt) und sieht aus wie ein Hänger.

```
info: downloading https://releases.lean-lang.org/lean4/v4.33.1/lean-4.33.1-linux.tar.zst
```

*Erst nach `info: installing …/leanprover--lean4---v4.33.1` ist es eine Installation.*
**Dieselbe Regel wie bei Isabelle:** ein abgebrochener Lauf hinterlässt etwas, das
startet und beim ersten Bauen stirbt.

### 2. Zwei gleichzeitige `lean`-Aufrufe blockieren einander

Am 2026-08-25 liefen zwei Prüfbefehle parallel gegen dieselbe frische Installation:

```
~/.elan/toolchains/leanprover--lean4---v4.33.lock
```

Der zweite wartete auf die Sperre des ersten und **verbrauchte 0 % CPU** — nicht
abgestürzt, nicht fertig, nur unsichtbar wartend. *Behoben durch Beenden des zweiten;
der erste lief durch.* **Beim ersten Lauf genau EIN `lean`-Aufruf**, danach ist die
Sperre gegenstandslos.

---

## Warum der Bau auf den Server gehört — die Zahl

*Gemessen 2026-08-25, `passlogik` mit sieben Theoriedateien:*

| | Spitzenspeicher | Zeit |
|---|---:|---|
| eine **triviale** Einzeldatei (Grundlast von `lean` selbst, lokal gemessen) | 485 MB | — |
| **eine einzelne Theoriedatei** (`lean Passlogik/Bereich.lean`, 757 Zeilen) | **539 MB** | 1,0 s |
| **`lake build` über das ganze Projekt** (parallel, 7 Dateien) | **3 385 MB** | 1,3 s |

> **Die erste Zeile ist die wichtigere:** 485 MB kostet `lean` schon für eine leere
> Datei. Der Inhalt dieser sieben Theorien kostet **54 MB obendrauf** — die Last liegt
> praktisch vollständig in der Grundlast des Werkzeugs, nicht in den Beweisen. *Ein
> größeres Projekt verschiebt darum nicht die Einzeldatei über die Grenze, sondern
> allein die Parallelität.*

> **Die lokale Wachhundgrenze liegt bei 1 GB** (`CLAUDE.md`, seit 2026-08-20). Eine
> einzelne Datei bleibt darunter; **der parallele Bau liegt mit 3,4 GB klar darüber**,
> weil `lake` bis zu `nproc` Prozesse gleichzeitig fährt und jeder für sich schon rund
> 500 MB braucht.
>
> **Ein Abbruch aus Speichermangel ist kein Befund** — dieselbe Regel, aus der Isabelle
> auf diesen Rechner gekommen ist. Deshalb:
>
> * **lokal**: `lean <eine Datei>` während des Schreibens,
> * **auf `ki-pc-fisch-101`**: jedes `lake build` über das Projekt.

So gemessen (die Zahl kann jederzeit nachgerechnet werden):

```bash
ssh ki-pc-fisch-101 'cd gabbro-lean && export PATH=$HOME/.elan/bin:$PATH && rm -rf .lake && \
  (lake build >/dev/null 2>&1 & BP=$!; MAX=0
   while kill -0 $BP 2>/dev/null; do
     S=$(ps -o rss= -C lean 2>/dev/null | awk "{s+=\$1} END {print s+0}")
     [ "$S" -gt "$MAX" ] && MAX=$S; sleep 0.05
   done; wait $BP; echo "Spitze aller lean-Prozesse zusammen: $((MAX/1024)) MB")'
```

---

## Das Serververzeichnis

**`gabbro-lean/`** — nicht `gabbro-baum`, dort arbeiten andere (`CLAUDE.md`, „Wenn ein
Agent nebenher rechnet").

```bash
rsync -rlpgoD --delete --exclude '.lake/' passlogik/ ki-pc-fisch-101:gabbro-lean/
ssh ki-pc-fisch-101 'cd gabbro-lean && export PATH=$HOME/.elan/bin:$PATH && lake build'
```

> **`-rlpgoD` und nicht `-a`, auch hier.** `lake` entscheidet Aktualität wie `cargo`
> nach Zeitstempeln; eine übertragene Quelle mit alter `mtime` gälte als aktuell und der
> Bau liefe aus einer Mischung. **`--exclude '.lake/'`** hält die Bauartefakte des
> Servers von denen des Arbeitsrechners getrennt.

---

## Kein `mathlib` — und was das kostet

`lakefile.toml` hat **keine `require`-Zeile**. Der Bau lädt nichts nach und dauert
**1,3 s**; mit `mathlib` wären es Minuten und ein zweites Gigabyte-Paket.

`TODO.md` begründet es: *„Der Prüferalgorithmus — Bereichsverbände, Wirkungshüllen über
dem Aufrufgraphen, Rangordnung, Linearität — ist endliche Mathematik ohne
`mathlib`-Tiefe."* **Das hat sich bestätigt**, mit einer Ausnahme und zwei Auslassungen,
die in `README.md` unter „Was `mathlib` gekostet hätte" stehen.

Selbstgebaut wurden dafür: `imin`/`imax` über `Int` (`Bereich.lean`), `Menge`/`teilmenge`
als Prädikate (`Wirkung.lean`), `zaehle` über `Nat` (`Terminierung.lean`). *Zusammen
unter fünfzig Zeilen* — und `Fintype` wurde nirgends gebraucht.
