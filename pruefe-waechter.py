#!/usr/bin/env python3
"""**Der Waechter ueber den Waechtern -- weil vier von ihnen aufgehoert hatten zu messen.**

Am 2026-08-20 wurden an einem einzigen Tag vier Instrumente dabei erwischt, dass sie nicht
mehr messen:

* `pruefe-emission.sh` **hing** an seiner eigenen Sprechprobe. `baum41`s Gift lenkt den
  Abstieg von `erstes_kind` auf `elter`, der Lauf klettert zur Wurzel und dreht dort -- ohne
  Frist. Auf `ki-pc-fisch-101` standen **einundzwanzig** Laeufe nebeneinander, der aelteste
  seit dreieinhalb Stunden.
* `zaehle-pflichten.py` **verweigerte** die Ableitung (*„15 Bloecke statt 10"*), seit «F0» und
  «K2» in derselben Datei stehen -- und der Modus, der noch antwortete, lief VOR der Pruefung.
* `gift/214` **prueft etwas anderes** als es behauptete; der Mutationslauf hat es gesagt.
* die B22-Sonde in `pruefe-notation.py` **mass einen fremden Fehler** (`gates g` mit
  undeklariertem `g`) und meldete die Luecke als offen.

> **Ein Haenger sieht aus wie „laeuft noch", nicht wie ein Befund.** Und ein Waechter, der
> still abbricht, sieht aus wie einer, der nichts gefunden hat. *Beide Male wird nichts rot.*

Drei Forderungen, und sie stehen hier, weil keine von ihnen sich selbst durchsetzt:

1. **FRIST** -- wer etwas ausfuehrt, tut es mit einer Frist. Sonst ist ein Haenger ein Zustand
   und kein Befund.
2. **SPRECHPROBE** -- in beide Richtungen: was fallen soll, faellt; was nicht, faellt nicht.
   *Ein Waechter, der nicht rot werden kann, misst nichts* (R14).
3. **ROT BEI ABBRUCH** -- ein Abbruch verlaesst mit einem Ruecklaufwert ungleich null. `set -e`
   mit `timeout` ist genau die Falle, in die `pruefe-emission.sh` am selben Tag noch lief:
   die Frist beendete den Waechter STILL, mit Ruecklaufwert 0 und einer Ausgabe, die mit `ok`
   endete.
4. **ARBEITSMENGE** -- neben dem Urteil steht, WIE VIEL angesehen wurde. *Ohne sie ist ein
   gruener Lauf von einem leeren nicht zu unterscheiden.*

**Zu (4) gehoert eine eigene Klasse, und sie hat am 2026-08-20 dreimal zugeschlagen:**

| | |
|---|---|
| `isabelle build -D .` | waehlte NICHTS und endete gruen |
| `zaehle-b3.py` | druckte `! ABBRUCH` und endete mit 0 |
| das README-Muster fuer die Waechterzahl | traf nichts mehr und meldete „sauber" |

**Drei Faelle, eine Form: ERFOLG OHNE ARBEIT.** Nicht ein falsches Urteil, sondern ein
*positives Urteil ueber nichts* -- und das ist gefaehrlicher, weil es wie ein Ergebnis
aussieht. Die Vorkehrung ist die Zahl neben dem Urteil (W11: jede Quote nennt ihr N).

    ./pruefe-waechter.py [--lauf]

**Und was das NICHT heisst:** die statische Haelfte liest QUELLTEXT. Dass ein `timeout` im
Text steht, heisst nicht, dass es an der richtigen Stelle steht. `--lauf` fuehrt die leichten
Waechter wirklich aus und verlangt einen bestimmten Ruecklaufwert innerhalb der Frist -- die
schweren stehen mit Grund daneben. *Eine Flaeche, die kein Werkzeug erreicht, faellt in keiner
Statistik auf.*
"""
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent
FRIST = 300

# Waechter, die zu schwer fuer einen Lauf hier sind -- mit Grund, nicht als Freibrief.
SCHWER = {
    "pruefe-emission.sh": "46 Einheiten, je erzeugen/uebersetzen/ausfuehren/UBSan -- ~25 min",
    "pruefe-beweise.sh": "zwoelf Isabelle-Theorien; gehoert ohnehin auf den Server",
    "pruefe-luecken.py": "baut dreizehnmal neu",
    "mutiere-pruefer.py": "234 Mutationen, je ein Bau -- 2 min 20 s, und es SCHREIBT in Quellen",
    "pruefe-notation.py": "vierzehn `cargo run` ueber je ein erzeugtes Programm",
}
# Waechter, die ein Argument brauchen.
ARGUMENTE = {
    "pruefe-wortschatz.py": ["dokumente/SYNTAX.md"],
    # **Ohne Argument endet es mit 2 und hat nichts gemessen** -- und ein Ruecklaufwert 2 in
    # einer Kette sieht aus wie ein Befund. Gefunden 2026-08-20 beim ersten `--lauf`.
    "zaehle-b3.py": ["../caprock-messbasis"],
}
# Werkzeuge, die messen statt zu bewachen: sie duerfen ohne Sprechprobe stehen, brauchen aber
# Frist und roten Abbruch wie jedes andere.
ZAEHLER = {"zaehle-b3.py", "zaehle-bereichspflichten.py", "zaehle-narrow.py", "zaehle-fallen.sh"}

FUEHRT_AUS = re.compile(r"subprocess\.|os\.system|check_output|\bcargo\b|\bcc\b|\bisabelle\b")
# **Eine DEKLARIERTE Frist** -- `timeout`, `timeout=`, `TimeoutExpired` oder eine benannte
# Konstante (`FRIST`, `ZEIT`). Dass sie dasteht, heisst nicht, dass sie greift; `--lauf` ist
# die Haelfte, die das misst. *Die statische Haelfte verpflichtet, sie spricht nicht frei.*
HAT_FRIST = re.compile(r"timeout=|\btimeout\b|TimeoutExpired|\bFRIST\b|\bZEIT\b")
HAT_PROBE = re.compile(r"[Ss]prechprobe|speech test|Gegenprobe|[Ss]elbsttest")
HAT_ROT = re.compile(r"sys\.exit\(\s*[1-9]|SystemExit\(\s*[1-9]|exit\s+1\b|return\s+1\b|returncode")
# **Eine ARBEITSMENGE in der Ausgabe**: `N von M`, `N Dateien`, `N Stellen`. Statisch ist das
# nur ein Hinweis; `--lauf` liest die wirkliche Ausgabe, und das ist die Haelfte, die zaehlt.
ARBEIT = re.compile(r"\b\d+\s+(?:von|of)\s+\d+\b|\b\d+\s+[A-Za-zÄÖÜäöüß][A-Za-zÄÖÜäöüß-]{3,}")


def waechter():
    aus = []
    for p in sorted(W.glob("pruefe-*.py")) + sorted(W.glob("pruefe-*.sh")) \
            + sorted(W.glob("zaehle-*.py")) + sorted(W.glob("zaehle-*.sh")) \
            + sorted(W.glob("mutiere-*.py")):
        aus.append(p)
    return aus


def statisch(p):
    """Die drei Forderungen am Quelltext. Gibt die Liste der VERLETZUNGEN."""
    t = p.read_text(encoding="utf-8", errors="replace")
    fehlt = []
    if FUEHRT_AUS.search(t) and not HAT_FRIST.search(t):
        fehlt.append("FRIST")
    if p.name not in ZAEHLER and not HAT_PROBE.search(t):
        fehlt.append("SPRECHPROBE")
    if not HAT_ROT.search(t):
        fehlt.append("ROT-BEI-ABBRUCH")
    return fehlt


def sprechprobe():
    """**In beide Richtungen, an erfundenen Quellen.** Ein Waechter, der nur die eigenen
    Dateien liest, misst, wie gut sie zu ihm passen."""
    import tempfile
    gut = ('import subprocess, sys\n'
           '# Sprechprobe: eine kaputte Eingabe MUSS fallen\n'
           'subprocess.run(["true"], timeout=5)\n'
           'sys.exit(1)\n')
    schlecht = 'import subprocess\nsubprocess.run(["cargo", "build"])\nprint("ok")\n'
    with tempfile.TemporaryDirectory() as d:
        a = pathlib.Path(d) / "pruefe-gut.py"
        b = pathlib.Path(d) / "pruefe-schlecht.py"
        a.write_text(gut, encoding="utf-8")
        b.write_text(schlecht, encoding="utf-8")
        f_gut, f_schlecht = statisch(a), statisch(b)
    # **Und die vierte Forderung, an ihrer eigenen Regex.** Ein gruener Lauf ohne Zahl
    # daneben MUSS auffallen; einer mit Zahl NICHT.
    leer_faellt = not ARBEIT.search("== ALL PASS ==\nok\n")
    voll_faellt = bool(ARBEIT.search("== 23 von 23 tragen alle drei ==\n"))
    ok = (not f_gut and set(f_schlecht) == {"FRIST", "SPRECHPROBE", "ROT-BEI-ABBRUCH"}
          and leer_faellt and voll_faellt)
    return ok, f_gut, f_schlecht, leer_faellt, voll_faellt


def main():
    ok, f_gut, f_schlecht, leer_faellt, voll_faellt = sprechprobe()
    print("== Sprechprobe des Waechters ==")
    print(f"  saubere Quelle: {len(f_gut)} Verletzungen -- "
          + ("ok" if not f_gut else f"GESCHEITERT (falsches Rot: {f_gut})"))
    print(f"  kaputte Quelle: {len(f_schlecht)} Verletzungen -- "
          + ("ok" if len(f_schlecht) == 3 else f"GESCHEITERT (der Waechter ist stumm: {f_schlecht})"))
    print("  Arbeitsmenge:   " + ("ok (eine Ausgabe ohne Zahl faellt, eine mit Zahl nicht)"
                                  if leer_faellt and voll_faellt else "GESCHEITERT"))
    if not ok:
        return 1

    print()
    print("== Die drei Forderungen, am Quelltext ==")
    befunde = []
    alle = waechter()
    for p in alle:
        fehlt = statisch(p)
        marke = "ok      " if not fehlt else "FEHLT   "
        zusatz = "" if not fehlt else "  " + ", ".join(fehlt)
        print(f"  {marke}{p.name:<28}{zusatz}")
        if fehlt:
            befunde.append((p.name, fehlt))

    print()
    print(f"== {len(alle) - len(befunde)} von {len(alle)} tragen alle drei ==")

    if "--lauf" in sys.argv:
        print()
        print("== Und die leichten laufen wirklich, mit Frist ==")
        for p in alle:
            if p.name in SCHWER:
                print(f"  schwer  {p.name:<28}  {SCHWER[p.name]}")
                continue
            befehl = [str(p)] + ARGUMENTE.get(p.name, [])
            try:
                r = subprocess.run(befehl, cwd=W, capture_output=True, text=True, timeout=FRIST)
                arbeit = ARBEIT.search(r.stdout)
                marke = "Ende" if r.returncode in (0, 1) else "USAGE?"
                zusatz = "" if arbeit else "   !! OHNE ARBEITSMENGE"
                print(f"  {marke} {r.returncode:<2} {p.name:<28}{zusatz}")
                # **Erfolg ohne Arbeit.** Ein gruener Lauf ohne eine Zahl daneben ist von
                # einem leeren nicht zu unterscheiden -- `isabelle build` waehlte nichts und
                # endete gruen, dasselbe Muster.
                if not arbeit:
                    befunde.append((p.name, ["OHNE-ARBEITSMENGE"]))
                # **Ein Ruecklaufwert ausserhalb {0,1} ist kein Befund, sondern ein
                # FEHLAUFRUF** -- das Werkzeug hat nichts gemessen und sieht doch rot aus.
                if r.returncode not in (0, 1):
                    befunde.append((p.name, [f"RUECKLAUFWERT-{r.returncode}"]))
            except subprocess.TimeoutExpired:
                print(f"  HAENGT  {p.name:<28}  Frist {FRIST} s ueberschritten")
                befunde.append((p.name, ["LAEUFT-NICHT-DURCH"]))
            except PermissionError:
                print(f"  NICHT AUSFUEHRBAR  {p.name} -- ein Waechter, den niemand starten kann")
                befunde.append((p.name, ["NICHT-AUSFUEHRBAR"]))

    print()
    print("== Und was das NICHT heisst ==")
    print("  Die statische Haelfte liest QUELLTEXT. Dass ein `timeout` im Text steht, heisst")
    print("  nicht, dass es an der richtigen Stelle steht -- `pruefe-emission.sh` hatte am")
    print("  2026-08-20 eine Frist und beendete sich damit STILL, weil `set -e` auf den")
    print("  Ruecklaufwert 124 traf. **Die Frist war da, die Forderung nicht erfuellt.**")
    print(f"  {len(SCHWER)} Waechter sind zu schwer fuer den Lauf hier und stehen mit Grund")
    print("  daneben; ihre Frist ist damit nur statisch geprueft.")
    return 1 if befunde else 0


if __name__ == "__main__":
    sys.exit(main())
