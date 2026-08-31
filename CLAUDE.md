# Gabbro — Arbeitsanweisungen

## Rechenlast gehört auf `ki-pc-fisch-101`

**Alles, was rechnet, läuft über SSH auf `ki-pc-fisch-101`** — dort stehen **128 GB RAM**
(gemessen 2026-08-19: `free -g` meldet 110 GB gesamt, 108 GB frei, **16 Kerne**; Hostname
`fisch`).
Das gilt zuerst für **Isabelle/HOL** (`./instrumente/pruefe-beweise.sh`, `isabelle build`), und ebenso für
jede andere Last, die den Arbeitsrechner an seine Grenze bringt: Mutationsläufe über den
ganzen Prüfer, Fuzzing, ein Lauf über den zweiten Korpus.

```bash
# Die Beweise, gemessen 2026-08-19: zwoelf Theorien, 8 s Wanduhr, 23 s CPU (Faktor 2,8).
rsync -a beweise/ ki-pc-fisch-101:gabbro/beweise/
ssh ki-pc-fisch-101 'cd gabbro/beweise && ~/Isabelle2025-2/bin/isabelle build -D . -o threads=12'
```

**Warum es hier steht und nicht im Kopf:** der lokale Beweislauf trägt einen 3-GB-Wachhund,
und ein Beweis, der daran stirbt, sieht aus wie ein Beweis, der nicht durchgeht. *Ein
Abbruch aus Speichermangel ist kein Befund.*

**Seit dem 2026-08-20 liegt die Grenze bei 1 GB, und damit fällt `rustc` darunter.**

> **Am 2026-08-30 lag sie nicht dort, und das ist gemessen und nicht vermutet:** `free -g`
> meldete 31 GB gesamt und 13 GB verfügbar, `ulimit -v` stand auf `unlimited`, 20 Kerne.
> `cargo test` (15 Sammlungen), `pruefe-emission.sh` und `isabelle build` über alle fünfzehn
> Theorien liefen lokal durch — der Isabelle-Lauf in 12 s. Gefahren wurde lokal, weil
> `ki-pc-fisch-101` ab 19:42 nicht erreichbar war: **nicht der Zielrechner, der Sprunghost.**
>
> **Die Regel bleibt trotzdem stehen.** Sie ist eine Aussage über den Speicher, nicht über die
> Gewohnheit, und wer sie fallen lässt, weil sie einmal nicht griff, hat die nächste
> Speichergrenze nicht gemessen, sondern vergessen. *Vor einem lokalen Lauf gehört ein
> `free -g` daneben — dann ist es eine Messung und keine Hoffnung.* Auf den
Server gehören deshalb auch **`cargo build` und `cargo test`**, `./instrumente/pruefe-emission.sh` (ruft
`cargo run` je Einheit) und `./instrumente/pruefe-luecken.py` (baut dreizehnmal neu).

```bash
# **`-rlpgoD` und NICHT `-a`** -- siehe darunter, das ist kein Schoenheitsfehler.
rsync -rlpgoD --delete --exclude 'target/' --exclude '__pycache__/' --exclude '.claude/worktrees/' \
      ./ ki-pc-fisch-101:gabbro-baum/
ssh ki-pc-fisch-101 'cd gabbro-baum && export PATH=$HOME/.cargo/bin:$PATH && cargo test'
```

> **`rsync -a` erhaelt Zeitstempel, und `cargo` entscheidet Aktualitaet nach Zeitstempel.**
> Eine uebertragene Quelle behaelt damit ihre alte `mtime` -- ist die aelter als das
> Bauartefakt auf dem Server, haelt `cargo` die Datei fuer aktuell und **baut aus einer
> Mischung**. Am 2026-08-20 hat das einen Test rot gemeldet, der lokal gruen war: `M107` fiel
> hier und dort nicht, bei **byteidentischen Quellen** (md5 ueber den ganzen Baum verglichen).
>
> *Ein `touch crates/gabbro-check/src/m1.rs` auf dem Server hat es geheilt* -- und damit war
> die Ursache benannt: nicht der Code, sondern die Messapparatur. `-a` ist `-rlptgoD`; ohne
> das `t` bekommt jede UEBERTRAGENE Datei die aktuelle Zeit, und unveraenderte werden gar
> nicht erst uebertragen. **Genau die Semantik, die `cargo` braucht.**
>
> Dieselbe Klasse wie `W16`: ein Werkzeug, das eine Mischung misst, sieht plausibel aus.

Lokal bleibt, was sicher darunter liegt: ein einzelner `gabbro emit`/`pruefe`-Lauf über ein
schon gebautes Binärprogramm, ein `cc` auf einer Datei, und die Textwächter
(`pruefe-todo.py`, `-englisch`, `-kennungen`, `-syntax`). *Die Grenze ist der Speicher, nicht
die Gewohnheit.*

**Der Mutationslauf misst sich selbst**: `./instrumente/mutiere-pruefer.py` über alle
~~159~~ **340** Mutationen braucht ~~2 min 20 s~~ **10 min 25 s** lokal (nachgemessen
2026-08-30; die alte Zahl stammt vom 2026-08-19, und der Katalog ist seither auf mehr als das
Doppelte gewachsen). *Ein Katalog, der wächst, macht jede Zahl daneben zu einer Jahreszahl.*
`--anker` kostet gar nichts — reines Textzählen, kein Bau. *Vor dem Lauf muss `crates/`
sauber sein; die Probe schreibt in Quellen, und zwei Läufe auf denselben Dateien
zerstören einander.*

Seit dem 2026-08-19 liegt auch eine **Rust-Kette auf `ki-pc-fisch-101`**
(`~/.cargo/bin`, rustup, ohne `sudo` installiert — der Rechner hatte vorher kein `cargo`).

**Nach `abnahme.py --voll` ist die naechste `abnahme.py` ROT, und das ist kein Befund.**
Der Mutationslauf schreibt in jede Pruefer-Quelle und stellt sie byteweise zurueck — *aber
mit einer neuen `mtime`*. Damit ist jede Quelle juenger als das gebaute Binaerprogramm, und
`pruefe-saetze.py` bricht mit `ABBRUCH: das Binaerprogramm ist AELTER als N Quelldatei(en)`
ab. **Der Waechter hat recht** — er kann nicht wissen, dass der Inhalt derselbe ist —, aber
die Ursache ist die Messapparatur und nicht der Baum.

*Gemessen am 2026-08-31:* ein Lauf rot direkt nach `--voll`, fuenf Laeufe gruen danach, und
`touch crates/gabbro-check/src/saetze.rs` stellt den roten Zustand auf Knopfdruck her
(`exit=2`). **Die Heilung ist ein Bau, kein `touch` auf das Binaerprogramm** — den
Zeitstempel zu faelschen macht genau die Mischung unsichtbar, gegen die der Riegel steht:

```bash
ssh ki-pc-fisch-101 'cd gabbro-k && export PATH=$HOME/.cargo/bin:$PATH && cargo build'
rsync -a ki-pc-fisch-101:gabbro-k/target/debug/gabbro target/debug/gabbro
```

Dieselbe Klasse wie `rsync -a` gegen `cargo`, nur andersherum: dort log der Zeitstempel,
hier sagt er die Wahrheit ueber etwas, das keine Rolle spielt. *Ein Werkzeug, das die Zeit
misst statt den Inhalt, irrt in beide Richtungen.*

## Wenn ein Agent nebenher rechnet

**Jeder Agent bekommt sein EIGENES Serververzeichnis** (`gabbro-a`, `gabbro-b`, …), nie
`gabbro-baum`. *Am 2026-08-21 lief ein `rsync` in ein Verzeichnis, in dem gerade ein
Mutationslauf arbeitete, und zwei grüne Testsammlungen wurden rot* — **kein Befund, eine
Kollision.** Ein Mutationslauf schreibt in Quellen und stellt sie hinterher byteweise zurück;
wer ihm dazwischen eine Datei unterschiebt, misst eine Mischung. Dieselbe Klasse wie `W16`,
nur zwischen zwei Läufen statt in einem.

**Und der Arbeitsbaum eines Agenten steht vor Laufbeginn auf `master`.** Ein Zweig, der drei
Commits zurückliegt, misst gegen einen Stand, den es nicht mehr gibt — am 2026-08-21 hat das
dreimal Zahlen erzeugt, die beim Zusammenführen einzeln nachgerechnet werden mussten. *Der
`--ff-only`-Vorlauf ist kein Commit und kostet nichts; ihn zu vergessen kostet den Merge.*

**In EIN Agentenverzeichnis gehören BEIDE Übertragungen, und zwar in dieser Reihenfolge:**

```bash
rsync -rlpgoD --delete --exclude 'target/' … ./ ki-pc-fisch-101:gabbro-p/   # fuer `cargo`
rsync -a                                  beweise/ ki-pc-fisch-101:gabbro-p/beweise/
```

Oben stehen die zwei Übertragungen mit **verschiedenen Zielverzeichnissen** (`gabbro` und
`gabbro-baum`), und darum kollidieren sie dort nicht. *Ein Agent hat nur eines* — und wer nur
die erste fährt, bekommt `pruefe-beweise.sh` **`OHNE NACHWEIS`** über fünfzehn tadellose
Theorien. **Am 2026-08-31 hat das eine volle Abnahme rot gemeldet, mit `[1]` und ohne einen
Befund darin.** Der Wächter nennt die Ursache und die Heilung in seiner eigenen Absage — *aber
er nennt sie erst, nachdem der Lauf zwölf Minuten gebraucht hat.*

## Was sonst gilt

* **Commit-Nachrichten nur über `arbeitsprotokoll/.commitmsg` + `./commit.sh`** (R19).
* **Caprock liegt schreibgeschützt** in `../caprock-messbasis` (Zweig `arch/x86_64`) —
  **nie hineincommitten.** Korrekturvorschläge stehen im Protokoll, nicht im fremden Baum.
* **`aarch64` bleibt versiegelt** („blockiert — Abstammung"), kein dritter Anlauf.
* Isabelle2025-2 liegt lokal unter `/home/simon/Isabelle2025-2` **und seit dem 2026-08-19
  auch unter `~/Isabelle2025-2` auf `ki-pc-fisch-101`**; **kein AFP**.
  *Ohne `sudo` installiert* — Isabelle bringt sein eigenes JDK mit, `java` gibt es auf dem
  Rechner gar nicht. **Ein Passwort war dafür nicht nötig und wurde nicht benutzt.**
  Übertragen mit `rsync -a --delete ~/Isabelle2025-2/ ki-pc-fisch-101:Isabelle2025-2/` —
  ein *abgebrochener* Lauf lässt eine Installation zurück, die startet und beim ersten Bauen
  an einer fehlenden Quelldatei stirbt. **Erst nach `rsync fertig` ist sie eine.**
