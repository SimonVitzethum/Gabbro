# Gabbro — Arbeitsanweisungen

## Rechenlast gehört auf `ki-pc-fisch-101`

**Alles, was rechnet, läuft über SSH auf `ki-pc-fisch-101`** — dort stehen **128 GB RAM**
(gemessen 2026-08-19: `free -g` meldet 110 GB gesamt, 108 GB frei, **16 Kerne**; Hostname
`fisch`).
Das gilt zuerst für **Isabelle/HOL** (`./pruefe-beweise.sh`, `isabelle build`), und ebenso für
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

**Seit dem 2026-08-20 liegt die Grenze bei 1 GB, und damit fällt `rustc` darunter.** Auf den
Server gehören deshalb auch **`cargo build` und `cargo test`**, `./pruefe-emission.sh` (ruft
`cargo run` je Einheit) und `./pruefe-luecken.py` (baut dreizehnmal neu).

```bash
rsync -a --delete --exclude 'target/' --exclude '__pycache__/' --exclude '.claude/worktrees/' \
      ./ ki-pc-fisch-101:gabbro-baum/
ssh ki-pc-fisch-101 'cd gabbro-baum && export PATH=$HOME/.cargo/bin:$PATH && cargo test'
```

Lokal bleibt, was sicher darunter liegt: ein einzelner `gabbro emit`/`pruefe`-Lauf über ein
schon gebautes Binärprogramm, ein `cc` auf einer Datei, und die Textwächter
(`pruefe-todo.py`, `-englisch`, `-kennungen`, `-syntax`). *Die Grenze ist der Speicher, nicht
die Gewohnheit.*

**Der Mutationslauf misst sich selbst**: `./mutiere-pruefer.py` über alle 159 Mutationen
braucht **2 min 20 s** lokal (gemessen 2026-08-19) und bleibt damit diesseits der Grenze.
`--anker` kostet gar nichts — reines Textzählen, kein Bau. *Vor dem Lauf muss `crates/`
sauber sein; die Probe schreibt in Quellen, und zwei Läufe auf denselben Dateien
zerstören einander.*

Seit dem 2026-08-19 liegt auch eine **Rust-Kette auf `ki-pc-fisch-101`**
(`~/.cargo/bin`, rustup, ohne `sudo` installiert — der Rechner hatte vorher kein `cargo`).

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
