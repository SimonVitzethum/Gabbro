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
5. **GEBIETSSCHEMA** -- whoever calls a foreign tool and reads its MESSAGE pins
   `LC_ALL=C`. Measured 2026-08-25: under `de_DE.UTF-8` the linker says
   `Mehrfachdefinition von`, not `multiple definition`. `pruefe-emission.sh` searched for
   the English words, did not find them and reported *„der Binder faellt aus anderem
   Grund"* -- **an error that did not exist.** The same class as `W16`: a tool that measures
   its own locale and looks plausible doing it.

**Zu (4) gehoert eine eigene Klasse, und sie hat am 2026-08-20 dreimal zugeschlagen:**

| | |
|---|---|
| `isabelle build -D .` | waehlte NICHTS und endete gruen |
| `zaehle-b3.py` | druckte `! ABBRUCH` und endete mit 0 |
| das README-Muster fuer die Waechterzahl | traf nichts mehr und meldete „sauber" |

**Drei Faelle, eine Form: ERFOLG OHNE ARBEIT.** Nicht ein falsches Urteil, sondern ein
*positives Urteil ueber nichts* -- und das ist gefaehrlicher, weil es wie ein Ergebnis
aussieht. Die Vorkehrung ist die Zahl neben dem Urteil (W11: jede Quote nennt ihr N).

    ./instrumente/pruefe-waechter.py [--lauf]

**Und was das NICHT heisst:** die statische Haelfte liest QUELLTEXT. Dass ein `timeout` im
Text steht, heisst nicht, dass es an der richtigen Stelle steht. `--lauf` fuehrt die leichten
Waechter wirklich aus und verlangt einen bestimmten Ruecklaufwert innerhalb der Frist -- die
schweren stehen mit Grund daneben. *Eine Flaeche, die kein Werkzeug erreicht, faellt in keiner
Statistik auf.*

**Nachgetragen 2026-08-20, und der Befund gehoert dem Waechter selbst:** derselbe `--lauf` war
hier gruen und auf `ki-pc-fisch-101` rot -- bei identischen Quellen. Nicht der Code, sondern
der **Gegenstand** fehlte: `zaehle-b3.py` und `zaehle-narrow.py` messen FREMDE Baeume
(Caprock-Messbasis, SEL4Lake), und die liegen nur auf dem Arbeitsrechner. *Ein Waechter,
dessen Urteil davon abhaengt, auf welchem Rechner er laeuft, ohne es zu sagen, misst den
Rechner.* Die zwei stehen jetzt in `FREMDER_KORPUS`, und ein fehlender Baum wird als **nicht
gemessen** gezaehlt statt als Befund gedruckt -- mit seiner Zahl in der Schlusszeile.

*Dieselbe Falle noch einmal, eine Ebene tiefer:* `../caprock-messbasis` ist ein RELATIVER
Pfad. In einem `git worktree` zeigt er neben den Arbeitsbaum -- und `zaehle-b3.py` lief bis
heute darueber bis in eine `ZeroDivisionError`.
"""
import pathlib
import re
import subprocess
import sys
import time

W = pathlib.Path(__file__).resolve().parent.parent
FRIST = 300

# **Waechter, die NICHT im `--lauf` stehen -- und der Grund ist seit dem 2026-08-20 GEMESSEN.**
#
# Bis dahin standen hier fuenf Eintraege mit geschaetzten Kosten, und **vier von fuenf waren
# falsch** -- am schlimmsten `pruefe-emission.sh` mit *„46 Einheiten … ~25 min"*. Gemessen auf
# `ki-pc-fisch-101`: **13,7 Sekunden.** Die 25 Minuten stammen vom Vormittag desselben Tages,
# als der Waechter an `baum41` HING; die Frist hat den Haenger beseitigt, und die Zahl, die ihn
# beschrieb, blieb stehen -- **als Begruendung dafuer, ihn nicht zu messen.**
#
# > **Eine Ausnahme, deren Grund niemand nachrechnet, ist dieselbe Klasse wie eine Zahl, die
# > niemand nachrechnet** -- nur teurer, weil sie eine ganze Messung abschaltet statt sie zu
# > verfaelschen. *Erfolg ohne Arbeit, eine Ebene ueber dem Urteil: die Arbeit wird gar nicht
# > erst angeordnet.*
#
# Was blieb, steht jetzt mit dem RICHTIGEN Grund da, und der ist in keinem der vier die Zeit:
# es ist der ORT (Speicher, Rechenlast gehoert auf den Server -- `CLAUDE.md`) oder die
# WIRKUNG (es schreibt in Quellen). `pruefe-notation.py` ist ganz herausgefallen: 0,56 s, und
# es ruft kein `cargo` -- **es stand vier Wochen auf einer Liste, auf die es nie gehoerte.**
SCHWER = {
    "mutiere-pruefer.py":
        "es SCHREIBT in Quellen -- zwei Laeufe zerstoeren einander (2 min 20 s, 2026-08-19)",
    "pruefe-beweise.sh":
        "1,45 GB Spitze -- ueber der lokalen 1-GB-Grenze; 8,1 s auf `fisch` (2026-08-20)",
    "pruefe-emission.sh":
        "`cargo run` je Einheit -- gehoert auf den Server; 13,7 s dort (2026-08-20)",
    "pruefe-luecken.py":
        "baut dreizehnmal neu -- gehoert auf den Server; 10,7 s / 27,8 s CPU dort (2026-08-20)",
}
# **Waechter, deren Gegenstand ein FREMDER BAUM ist** -- einer, der nicht in diesem
# Verzeichnis liegt und den `git` nicht mitbringt. Je Eintrag: der Pfad und was dort steht.
#
# **Fehlt er, hat das Werkzeug NICHTS gemessen** -- und dann ist sein Ruecklaufwert ein
# Fehlaufruf und kein Befund. Bis zum 2026-08-20 wurde daraus ein rotes `--lauf`, und zwar
# genau auf `ki-pc-fisch-101`: dorthin gehoert die Rechenlast, und dort liegen weder die
# Caprock-Messbasis noch SEL4Lake. *Ein Waechter, dessen Urteil davon abhaengt, auf welchem
# Rechner er laeuft, ohne es zu sagen, misst den Rechner.*
#
# **Und `../caprock-messbasis` ist zusaetzlich relativ**: in einem `git worktree` zeigt der
# Pfad neben den Arbeitsbaum statt neben die Hauptauscheckung. Auch dort fehlt er also --
# lautlos, bis dieser Eintrag es sagt.
#
# *Das ist kein Freibrief.* Was hier steht, wird NICHT gruen gebucht, sondern als **nicht
# gemessen** gezaehlt und in der Schlusszeile mit seiner Zahl genannt (W17).
FREMDER_KORPUS = {
    "zaehle-b3.py": ("../caprock-messbasis", "die Caprock-Messbasis (Zweig arch/x86_64)"),
    "zaehle-narrow.py": ("~/Dokumente/SEL4Lake/SEL4Lake", "der zweite Korpus, SEL4Lake"),
}
# Waechter, die ein Argument brauchen.
ARGUMENTE = {
    "pruefe-wortschatz.py": ["dokumente/SYNTAX.md"],
    # **Ohne Argument endet es mit 2 und hat nichts gemessen** -- und ein Ruecklaufwert 2 in
    # einer Kette sieht aus wie ein Befund. Gefunden 2026-08-20 beim ersten `--lauf`.
    "zaehle-b3.py": ["../caprock-messbasis"],
    # **`zaehle-narrow.py` nahm bis zum 2026-08-20 den Standardbaum stillschweigend an** und
    # endete mit 2, wo er fehlt. Jetzt steht der Pfad hier, sichtbar neben dem von `b3`.
    "zaehle-narrow.py": ["~/Dokumente/SEL4Lake/SEL4Lake"],
}


def korpus_fehlt(name):
    """Der fremde Baum dieses Waechters -- oder `None`, wenn er keinen braucht/hat.

    Gibt `(pfad, was)` zurueck, wenn der Baum DEKLARIERT ist und FEHLT.
    """
    eintrag = FREMDER_KORPUS.get(name)
    if not eintrag:
        return None
    pfad, was = eintrag
    ort = pathlib.Path(pfad).expanduser()
    if not ort.is_absolute():
        ort = (W / pfad).resolve()
    return None if ort.is_dir() else (str(ort), was)


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
# **Fifth requirement: the LOCALE.** These tools report translated -- whoever calls them
# must set `LC_ALL=C`, or they measure the user's language.
#
# **The name alone is NOT enough as detection.** `mutiere-pruefer.py` mentions `cc` nine
# times in mutation descriptions and runs only `cargo test` -- a word pattern reports it red,
# and a guardian with false alarms gets ignored. So what is searched for is the CALL SITE:
# in Python the tool name as a string in an argument list, in the shell at the start of a
# command and without comment lines.
UEBERSETZTE = "cc|gcc|clang|ld|nm|objdump|readelf"
RUFT_UEBERSETZT_PY = re.compile(rf"""["'](?:{UEBERSETZTE})["']""")
# `sort` orders and `date` formats by locale -- but only in the SHELL. Python's `sorted`
# orders by code point and is untouched by it; the requirement does not apply there.
RUFT_UEBERSETZT_SH = re.compile(rf"(?m)^\s*(?:[!(]\s*)*(?:{UEBERSETZTE}|sort|date)\b")
KOMMENTARZEILE = re.compile(r"(?m)^\s*#.*$")
HAT_GEBIETSSCHEMA = re.compile(r"\bLC_ALL\b")


def waechter():
    aus = []
    # **`abnahme.py` joined on 2026-08-30, and it very nearly did not.** The collective run is
    # not called `pruefe-*` and would have slipped through every mesh above -- a tool that
    # establishes the reach of acceptance while standing outside acceptance itself. *Exactly
    # what it was built against, one level up.*
    for p in sorted(W.glob("instrumente/pruefe-*.py")) + sorted(W.glob("instrumente/pruefe-*.sh")) \
            + sorted(W.glob("instrumente/zaehle-*.py")) + sorted(W.glob("instrumente/zaehle-*.sh")) \
            + sorted(W.glob("instrumente/mutiere-*.py")) + sorted(W.glob("instrumente/abnahme.py")):
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
    if p.suffix == ".sh":
        ruft_uebersetzt = RUFT_UEBERSETZT_SH.search(KOMMENTARZEILE.sub("", t))
    else:
        ruft_uebersetzt = RUFT_UEBERSETZT_PY.search(t)
    if ruft_uebersetzt and not HAT_GEBIETSSCHEMA.search(t):
        fehlt.append("GEBIETSSCHEMA")
    return fehlt


def sprechprobe():
    """**In beide Richtungen, an erfundenen Quellen.** Ein Waechter, der nur die eigenen
    Dateien liest, misst, wie gut sie zu ihm passen."""
    import tempfile
    gut = ('import subprocess, sys\n'
           '# Sprechprobe: eine kaputte Eingabe MUSS fallen\n'
           'subprocess.run(["true"], timeout=5)\n'
           'sys.exit(1)\n')
    # **`cc` instead of `cargo`** -- so the broken source violates the FIFTH one too: it
    # calls a tool that reports translated and does not pin the locale.
    schlecht = 'import subprocess\nsubprocess.run(["cc", "-o", "a", "a.c"])\nprint("ok")\n'
    # **And the counter-direction of the fifth:** the same source WITH `LC_ALL` must not
    # violate it. Without this half the requirement would be a ban on `cc`, not a
    # requirement.
    gut_lc = ('import subprocess, sys\n'
              '# Sprechprobe: eine kaputte Eingabe MUSS fallen\n'
              'subprocess.run(["cc", "-o", "a", "a.c"], timeout=5,\n'
              '               env={"LC_ALL": "C"})\n'
              'sys.exit(1)\n')
    with tempfile.TemporaryDirectory() as d:
        a = pathlib.Path(d) / "pruefe-gut.py"
        b = pathlib.Path(d) / "pruefe-schlecht.py"
        c = pathlib.Path(d) / "pruefe-gut-lc.py"
        a.write_text(gut, encoding="utf-8")
        b.write_text(schlecht, encoding="utf-8")
        c.write_text(gut_lc, encoding="utf-8")
        # **Third direction: prose about `cc` is not a call.** Exactly the false alarm
        # `mutiere-pruefer.py` triggered before the detection looked for the call site.
        e = pathlib.Path(d) / "pruefe-prosa.py"
        e.write_text('import subprocess, sys\n'
                     '# Sprechprobe: `cc` und `ld` stehen hier nur im Text.\n'
                     'subprocess.run(["cargo", "test"], timeout=5)\n'
                     'sys.exit(1)\n', encoding="utf-8")
        f_gut, f_schlecht, f_gut_lc = statisch(a), statisch(b), statisch(c)
        f_prosa = statisch(e)
    # **Und die vierte Forderung, an ihrer eigenen Regex.** Ein gruener Lauf ohne Zahl
    # daneben MUSS auffallen; einer mit Zahl NICHT.
    leer_faellt = not ARBEIT.search("== ALL PASS ==\nok\n")
    voll_faellt = bool(ARBEIT.search("== 23 von 23 tragen alle drei ==\n"))
    ok = (not f_gut and not f_gut_lc and not f_prosa
          and set(f_schlecht) == {"FRIST", "SPRECHPROBE", "ROT-BEI-ABBRUCH", "GEBIETSSCHEMA"}
          and leer_faellt and voll_faellt)
    return ok, f_gut, f_schlecht, f_gut_lc, f_prosa, leer_faellt, voll_faellt


def main():
    ok, f_gut, f_schlecht, f_gut_lc, f_prosa, leer_faellt, voll_faellt = sprechprobe()
    print("== Sprechprobe des Waechters ==")
    print(f"  saubere Quelle: {len(f_gut)} Verletzungen -- "
          + ("ok" if not f_gut else f"GESCHEITERT (falsches Rot: {f_gut})"))
    print(f"  kaputte Quelle: {len(f_schlecht)} Verletzungen -- "
          + ("ok" if len(f_schlecht) == 4 else f"GESCHEITERT (der Waechter ist stumm: {f_schlecht})"))
    print(f"  cc mit LC_ALL:  {len(f_gut_lc)} Verletzungen -- "
          + ("ok (die fuenfte verbietet nicht `cc`, sie fordert das Gebietsschema)"
             if not f_gut_lc else f"GESCHEITERT (falsches Rot: {f_gut_lc})"))
    print(f"  cc nur als Prosa: {len(f_prosa)} Verletzungen -- "
          + ("ok (der Name im Text ist keine Aufrufstelle)"
             if not f_prosa else f"GESCHEITERT (Fehlalarm: {f_prosa})"))
    print("  Arbeitsmenge:   " + ("ok (eine Ausgabe ohne Zahl faellt, eine mit Zahl nicht)"
                                  if leer_faellt and voll_faellt else "GESCHEITERT"))
    if not ok:
        return 1

    print()
    print("== Die vier STATISCHEN Forderungen, am Quelltext ==")
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
    print(f"== {len(alle) - len(befunde)} von {len(alle)} tragen die vier STATISCHEN ==")
    print("   Die ARBEITSMENGE neben dem Urteil (W17) -- steht in der Ausgabe")
    print("   und nicht im Quelltext. Sie wird in `--lauf` gemessen, sonst gar nicht.")

    if "--lauf" in sys.argv:
        print()
        print("== Und die leichten laufen wirklich, mit Frist -- und mit der vierten Forderung ==")
        nicht_gemessen = []
        gesamtzeit = [0.0]
        for p in alle:
            if p.name in SCHWER:
                print(f"  schwer  {p.name:<28}  {SCHWER[p.name]}")
                continue
            fehlt_korpus = korpus_fehlt(p.name)
            if fehlt_korpus:
                ort, was = fehlt_korpus
                print(f"  KORPUS FEHLT  {p.name:<22}  {was}")
                print(f"                {'':<22}  {ort}")
                nicht_gemessen.append(p.name)
                continue
            befehl = [str(p)] + [str(pathlib.Path(a).expanduser())
                                 if a.startswith("~") else a
                                 for a in ARGUMENTE.get(p.name, [])]
            try:
                t0 = time.monotonic()
                r = subprocess.run(befehl, cwd=W, capture_output=True, text=True, timeout=FRIST)
                dauer = time.monotonic() - t0
                arbeit = ARBEIT.search(r.stdout)
                marke = "Ende" if r.returncode in (0, 1) else "USAGE?"
                zusatz = "" if arbeit else "   !! OHNE ARBEITSMENGE"
                # **Die Zeit gehoert neben das Urteil, wie die Arbeitsmenge.** Wer eine
                # Ausnahme mit Kosten begruendet, muss die Kosten irgendwo ablesen koennen --
                # sonst wird die Begruendung so alt wie die „~25 min" oben.
                print(f"  {marke} {r.returncode:<2} {p.name:<28}{dauer:6.2f} s{zusatz}")
                gesamtzeit[0] += dauer
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

    if "--lauf" in sys.argv:
        ohne = [n for n, f in befunde if "OHNE-ARBEITSMENGE" in f]
        gelaufen = len(alle) - len(SCHWER) - len(nicht_gemessen)
        print()
        print(f"== {gelaufen - len(ohne)} von {gelaufen} gelaufenen nennen ihre ARBEITSMENGE ==")
        print("   Ein gruener Lauf ohne Zahl daneben ist von einem leeren nicht zu")
        print(f"   unterscheiden (W17). Die {len(SCHWER)} schweren sind hier NICHT gemessen,")
        print(f"   und {len(nicht_gemessen)} weitere nicht, weil ihr fremder Korpus fehlt:")
        print(f"   {', '.join(nicht_gemessen) if nicht_gemessen else '(keiner)'}")
        print("   **Das ist ein Loch mit einer Zahl, kein gruener Haken.** Ein Waechter,")
        print("   dessen Gegenstand nicht da ist, hat nichts gemessen -- und das steht hier,")
        print("   statt sich als roter Ruecklaufwert zu tarnen, den keiner lesen kann.")
        print()
        print(f"== {gesamtzeit[0]:.1f} s fuer {gelaufen} Waechter ==")
        print("   Die Zeit steht hier, weil die AUSNAHMEN mit Kosten begruendet werden. Eine")
        print("   Ausnahme, deren Grund niemand nachrechnet, ist dieselbe Klasse wie eine Zahl,")
        print("   die niemand nachrechnet -- nur teurer: sie schaltet eine ganze Messung ab.")
        print("   *Am 2026-08-20 stand `pruefe-emission.sh` mit ~25 min auf dieser Liste und")
        print("   braucht 13,7 s; die Schaetzung stammte von dem Vormittag, an dem er HING.*")

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
