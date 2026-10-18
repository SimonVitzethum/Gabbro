# Gabbro — Arbeitsanweisungen

**Betriebshandbuch: [`AGENTS.md`](AGENTS.md)** — Stand, Ziel, Abläufe (Bahnen, Merge, Push),
Nummernkreise und die teuren Fallen. Die Arbeitsliste ist `TODO.md`. Das Handbuch wird hier mitgeladen:

@AGENTS.md

*Gekürzt am 2026-10-17: die Wächter-Anekdoten (Mutationslauf, Zahlenwächter, Abbruch-Regeln) gehören zu
den 80 Wächtern, die es nicht mehr gibt. Sie stehen in Git (`git log -p CLAUDE.md`); was davon als
Regel gilt, steht unten.*

## Sprache und Syntax folgen dem Lean-Modell (Simon, 2026-10-17)

**Das Lean-Modell (`grammatik/`) ist die einzige Quelle für Sprache und Syntax.** Wenn irgendetwas an der
Sprache oder ihrer Syntax geändert wird (ein Konstrukt, eine Klausel, eine Typregel, eine Regel, die eine
Form annimmt oder ablehnt), steht es ZUERST im Lean-Modell (Maschine G, `Akzeptiert`, `gabbro_ziel` bleibt
auf `propext`/`Classical.choice`/`Quot.sound`, ein geprüfter `Spec.lean`-Diff, wenn die Aussage wandert).
Danach folgen Prüfer, Compiler und `SYNTAX.md`/`SPRACHE.md` — nie umgekehrt. Nimmt der Prüfer etwas an, das
das Modell nicht kennt, dann irrt der Prüfer. Eine reine Absenkung einer vorhandenen Form (LLVM) ändert
die Sprache nicht und fällt nicht darunter.

## Kein Legacy in Compiler, Prüfer und Parser (Simon, 2026-10-17, feste Regel)

**Compiler, Prüfer und Parser tragen kein Legacy: nur der neueste Stand.** Wird etwas ersetzt, wird das Alte
gelöscht (die Historie steht in Git), nicht daneben gehalten: keine Kompatibilitäts-Schichten, keine
deprecated-Pfade, keine alten Namen oder Flag-Aliase, keine Absagecodes für Dinge, die es nicht mehr gibt,
keine Reste des C-Emitters (C-Namensregeln, C-Schablonen, `emit.rs`-Verweise). Eine Änderung ist erst fertig,
wenn sie ihren Vorgänger entfernt hat.

## Es gibt genau vier Wächter

| Wächter | Gegenstand | Was er prüft |
|---|---|---|
| `instrumente/pruefe-lean.py` | das Lean-Modell (`grammatik/`) | `lake build`, `gabbro_ziel` nur auf `propext`/`Classical.choice`/`Quot.sound`, kein `sorry`/`admit`/`native_decide`/`axiom`, höchstens 20 Einträge je Ordner |
| `instrumente/pruefe-llvm.py` | der LLVM-Compiler | `cargo test --test llvm`, neun Programme als Binärdatei auf x86_64 und aarch64 (qemu) mit gleichem Ergebnis, die Halde bleibt bis zur Belegung frei (keine Lese/Schreib-Abbildung über 1 GiB) |
| `instrumente/pruefe-pruefer.py` | der Prüfer (Rust) | `cargo test --workspace --no-fail-fast`, Satzregister, Kennungen nur einmal vergeben |
| `instrumente/pruefe-gabbrov.py` | GabbroV (`programmlogik/`) | `lake build`, Beweise ohne `sorry`, `gabbro prove` GREEN, kein GREEN ohne Lean |

`./instrumente/abnahme.py` fährt alle vier nacheinander (`--lean`, `--llvm`, `--pruefer`, `--gabbrov`
je einzeln). Ausgang: `0` gemessen und grün, `1` gemessen und rot, `2` **nichts oder nicht alles gemessen** —
das ist kein Grün. Hilfsteile (Satzregister, Layout-Werkzeug, Modelldeckung, `baue-llvm.sh`) liegen in
`instrumente/teile/` und laufen nur über die vier. **Ein fünfter Wächter wird nicht gebaut**: was neu geprüft
werden soll, wird ein Test in `cargo test`, ein Lean-Satz oder eine Stufe in einem der vier.

## Alles läuft lokal, mit Blick auf den Speicher

Alles, was rechnet, läuft in diesem Checkout: jeder Lean-Bau, jeder `cargo`-Lauf, jede Abnahme. Es gibt
keine zweite Maschine mehr (seit 2026-09-27); Rezepte für Server oder SSH in alten Notizen sind Historie.
`git push` geht über `~/.ssh/id_ed25519_github`.

* **Ein schwerer Lauf zur Zeit, `free -g` daneben.** Schwer sind `cargo build`, `cargo test`, `lake build`
  und die Abnahme. *Ein Abbruch aus Speichermangel ist kein Befund.*
* **`cargo test` und ein Lean-Lauf dürfen nicht gleichzeitig in EINEM Baum laufen:** `cargo test` ruft
  `gabbro prove`, das baut mit `lake` neu und ersetzt die `.olean`, die laufende `lean`-Prozesse lesen
  (gemessen: 52 Phantomfehler `Body.olean … does not exist`).
* **`cargo test` immer mit `--no-fail-fast`**, sonst meldet es nur die erste gefallene Probe. Wer zählen
  will, darf nicht beim ersten Treffer abbrechen (gilt für jede Messung, auch `set -e` in Skripten).
* **`-rlpgoD` und nicht `-a`, wenn ein von `cargo` gebauter Baum kopiert wird:** `cargo` entscheidet
  Aktualität nach Zeitstempel; ohne das `t` baut es aus einer Mischung.
* **Nicht mit `pgrep -f`/`pkill -f` warten:** das Muster findet die eigene Kommandozeile. Auf einen Lauf
  wartet man mit einer Datei, deren letzte Zeile man liest, oder mit `ps -C`.
* `rustc`/`cargo` liegen in `~/.cargo/bin`; Lean über `elan` (`ELAN_TOOLCHAIN` darf nicht gesetzt sein,
  `lean-bau`/`lean-probe` entfernen es).

## Agenten

* **Jeder Agent bekommt sein EIGENES Verzeichnis** (eigener Worktree neben dem Checkout, nie dieser
  Checkout) und sein eigenes Kratzverzeichnis. Zwei Läufe in einem Baum messen eine Mischung.
* **Der Arbeitsbaum eines Agenten steht vor Laufbeginn auf `master`** (`--ff-only`-Vorlauf kostet nichts).
* **Beide Bäume in ein Agentenverzeichnis:** `crates/` und `grammatik/`; `programmlogik/` braucht seinen
  warmen `.lake` (Mathlib), sonst hängt `cargo test` (`gabbro prove` geht klonen). Ein veralteter
  `.lake` ist schlimmer als keiner.
* Höchstens zwei Opus-Agenten gleichzeitig (AGENTS.md §6).

## Was sonst gilt

* **Arbeitssprache ist ENGLISCH, alles außer dem Gespräch:** Quelltext-Kommentare, alle `.md`,
  Commit-Nachrichten, Diagnostik, `gabbro hilfe`. Deutsch bleibt nur das Gespräch mit dem Ordner.
  Die Commit-Historie wird nicht umgeschrieben.
* **Höchstens 30 `.md`-Dateien im Repo** (Stand 2026-10-17: 27). Neue Dokumente nur, wenn ein bestehendes
  keinen Platz hat; Berichte, Urteile und Zwischenstände gehören in Git, nicht in den Baum.
* **Commit-Nachrichten nur über `arbeitsprotokoll/.commitmsg` + `./commit.sh`** (R19; committet nur
  gestagte Änderungen).
* **Caprock liegt schreibgeschützt in `../caprock-messbasis`: nie hineincommitten.** Korrekturvorschläge
  stehen im Protokoll, nicht im fremden Baum.
* **`aarch64` bleibt versiegelt** („blockiert — Abstammung"), kein dritter Anlauf — für die alte
  C-Emitter-Linie. Der LLVM-Weg trägt beide Ziele (`x86_64`, `aarch64`); der Lean-Teil der Hardware läuft
  über `ARM-PLAN.md`.
* **Der Isabelle-Teil ist nach Lean übertragen, die `.thy`-Menge ist eingefroren** (15 Theorien in
  `grammatik/Beweise/` gegen 15 Lean-Dateien in `grammatik/Grammatik/Isabelle/`). Ein neuer Beweis gehört
  nach Lean. Isabelle2025-2 liegt unter `~/Isabelle2025-2` (ohne `sudo`, eigenes JDK, kein AFP).
* **Ein Wächter, der abbricht, liest sich wie einer, der durchging.** Wer einen Lauf rot oder abgebrochen
  findet, sucht die Ursache zuerst in dem, was NICHT mehr gedruckt wurde, und misst die Basis in einem
  Wegwerf-Worktree vor dem Merge nach, statt zu schätzen.
