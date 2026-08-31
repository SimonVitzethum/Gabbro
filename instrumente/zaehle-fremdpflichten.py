#!/usr/bin/env python3
"""**Die drei Zustaende einer fremden Pflicht -- und der VIERTE, den niemand vergeben hatte.**

`zaehle-fremdverengung.py` kennt zwei Zahlen: wie viele fremde Ruempfe ihre Pflicht
AUSSPRECHEN und an wie vielen Stellen daraus im Rufer eine Tatsache wurde (10 und 1, gemessen
2026-08-21). **Dazwischen fehlt der Zustand, der die Luecke dieser Stufe ist:** eine Zeile,
die dasteht und die kein Pass liest.

    STUMM       es gibt keinen Ort, an den die Zeile geschrieben werden koennte
    SCHWEIGT    der Ort ist da, die Zeile fehlt
    UNGELESEN   die Zeile steht da -- und kein Pass macht daraus eine Tatsache
    WIRKT       die Zeile wurde am Rufort eine Tatsache

**Der vierte Zustand ist STUMM, und er war es, der den Posten falsch aussehen liess.** Das
TODO sagt: *„die Sperre etwa schuldet gegenseitigen Ausschluss, Fortschritt und die
Rangordnung, und keine Zeile sagt das heute"* -- und daneben: *„die Zeilen hinschreiben
(kostet nichts)"*. Fuer die Sperre kostet es nicht nichts, **es geht gar nicht**:
`LockDecl` (`ast.rs`) hat kein `ensures`-Feld, und `zeugnis.rs` schiebt den Sperreintrag von
Hand in die Liste, ohne `vertrag(f)` und ohne `fremde_mit_pflicht` zu erhoehen. *Dieselbe
Lage bei `rcu`, `guest`, `entry`, `boot` und `gabbro_kern`.* Wer diese Zeilen will, aendert
die GRAMMATIK, nicht seine Sorgfalt.

    ./instrumente/zaehle-fremdpflichten.py               die vier Zustaende
    ./instrumente/zaehle-fremdpflichten.py --stellen     je fremder Rumpf eine Zeile
    ./instrumente/zaehle-fremdpflichten.py --sprechprobe nur die Sprechprobe, beide Richtungen

WAS DIE ZAHLEN NICHT SAGEN
--------------------------
* **`UNGELESEN` heisst nicht „wirkungslos".** Es heisst: an KEINER Rufstelle dieser Einheit
  wurde daraus eine Tatsache. Eine Klausel an einer Funktion, die niemand ruft, steht hier
  genauso wie eine, die an jeder Rufstelle nichts bewegt. *Der Unterschied steht in
  `messung/FREMDPFLICHTEN.md`, nicht in dieser Zahl.*
* **`WIRKT` sagt nicht, dass die Zusage STIMMT.** Nur, dass Gabbro sie glaubt -- und der
  Glaube reicht bis ins Erzeugnis.
* **Der Giftkorpus steht nicht in der Summe.** Er ist gebaut, um abgewiesen zu werden, und
  ueber einer abgewiesenen Einheit gibt es kein Zeugnis (W10). Seine Zahl steht daneben.
* **Die Aufschluesselung von `UNGELESEN` nach `result` ist ein TEXTGRIFF**, kein Parser --
  sie liest die `ensures`-Zeile der Deklaration aus der Quelle. Sie steht unter dem Urteil,
  nicht darin: die vier Zustaende kommen aus dem Zeugnis, diese Teilung aus `grep`.
"""
import pathlib
import re
import subprocess
import sys
import tempfile

W = pathlib.Path(__file__).resolve().parent.parent

# **Jede Ausfuehrung mit Frist.** Ein Haenger sieht aus wie „laeuft noch", nicht wie ein
# Befund -- am 2026-08-20 standen deswegen einundzwanzig Laeufe nebeneinander.
FRIST = 600

MUSTER = ["beispiele/*.gab", "messung/*/*.gab"]
GIFT = "beispiele/gift/*.gab"

KOPF = re.compile(r"^== Translation certificate: (\S+) ==$")
# **The pattern had lost its subject, and the tool said so EVERY TIME.**
#
# Measured 2026-08-31 on the state BEFORE any change of that day: the speech probe reported
# `GESCHEITERT` four times over with `gemessen []`, and the run ended with 1. **Since
# 2026-08-30 the finding line carries a third currency** -- `N assumptions (M of them NOT
# FALSIFIABLE, K UNCOVERED -- …)` -- and this pattern still demanded a comma right after
# `assumptions`. With no match `je_datei` stays empty, every probe measures `[]`, and the
# cross-check agrees trivially against nothing.
#
# > *The sister file `zaehle-fremdverengung.py` carried the parenthesis over on 2026-08-30
# > and wrote the reason beside it; here it did not.* **Two patterns over one line, and only
# > one of them travelled** -- W7, at the place where it hurts.
#
# **The good part: it did not report a silent zero.** The speech probe named it and aborted
# the run instead of printing `0 foreign duties`. *A tool that cross-checks its own reading
# fails loudly.*
#
# (This note is English because `MARKE_PY` is a ratchet: a new German comment line in
# `instrumente/` raises it, and a ratchet may only fall.)
BEFUND = re.compile(
    r"^\s+\d+ assumptions \(\d+ of them NOT FALSIFIABLE, \d+ UNCOVERED[^)]*\), "
    r"\d+ templates \(\d+ of them UNPROVED\), \d+ direct forms, "
    r"(\d+) foreign bodies \((\d+) state their duty\), (\d+) narrowings from foreign "
    r"contracts$"
)
MARKE_E = "the checker uses to reason about them:"
# `       melde_roh                  effects { reads text }, mit `costs`, ensures (1)`
# **Der Vertrag beginnt genau dann mit `effects {`, wenn er aus `vertrag(f)` kam** -- und
# `vertrag(f)` gibt es nur fuer eine `FnDecl`. Alles andere hat kein `ensures`-Feld.
FREMD = re.compile(r"^ {7}(\S+)\s+(effects \{ .*)$")
FREMD_ROH = re.compile(r"^ {7}(\S.*)$")
STELLE = re.compile(r"^\s+(\d+):\s+(\S+) -> (\S+)\s+(\S+)\s+(.*)$")

STUMM, SCHWEIGT, UNGELESEN, WIRKT = "STUMM", "SCHWEIGT", "UNGELESEN", "WIRKT"
ZUSTAENDE = [STUMM, SCHWEIGT, UNGELESEN, WIRKT]
SATZ = {
    STUMM: "kein Ort fuer die Zeile -- `lock`/`rcu`/`guest`/`entry`/`boot` ohne `ensures`-Feld",
    SCHWEIGT: "der Ort ist da, die Zeile fehlt",
    UNGELESEN: "die Zeile steht da, und kein Pass macht daraus eine Tatsache",
    WIRKT: "die Zeile wurde am Rufort eine Tatsache",
}


def dateien(wurzel, muster):
    aus = []
    for m in muster:
        aus += sorted(wurzel.glob(m))
    return aus


def messe(wurzel, pfade):
    """(je_datei, roh); je_datei: Datei -> {"koerper": [(name, zustand)], "befund": (f, p, v)}.

    **Bricht sichtbar ab, statt null zu zaehlen** (R14a): laeuft der Uebersetzer nicht, ist
    das kein Ergebnis von null Pflichten, sondern gar kein Ergebnis.
    """
    if not pfade:
        print("!! ABBRUCH: kein Korpus gefunden -- das ist KEINE Zaehlung von null.")
        sys.exit(2)
    namen = [str(p.relative_to(wurzel)) if p.is_absolute() and p.is_relative_to(wurzel)
             else str(p) for p in pfade]
    r = subprocess.run(
        ["cargo", "run", "-q", "-p", "gabbro-cli", "--", "zeugnis"] + namen,
        cwd=wurzel, capture_output=True, text=True, timeout=FRIST)
    # Ruecklaufwert 1 heisst nur: mindestens eine Einheit traegt Fehler -- ueber dem
    # Fragmentkorpus der Normalfall und kein Abbruch.
    if r.returncode not in (0, 1) or "Translation certificate" not in r.stdout:
        print("!! ABBRUCH: `gabbro zeugnis` lief nicht -- das ist KEINE Zaehlung von null.")
        print((r.stderr or r.stdout)[-800:])
        sys.exit(2)

    je_datei, datei = {}, None
    koerper, gewirkt, in_e = [], set(), False
    for zeile in r.stdout.splitlines():
        k = KOPF.match(zeile)
        if k:
            datei, koerper, gewirkt, in_e = k.group(1), [], set(), False
            continue
        if datei is None:
            continue
        if MARKE_E in zeile:
            in_e = True
            continue
        s = STELLE.match(zeile)
        if s:
            gewirkt.add(s.group(3))
            continue
        if in_e:
            m = FREMD.match(zeile)
            if m:
                koerper.append((m.group(1), True, ", ensures (" in zeile))
                continue
            roh = FREMD_ROH.match(zeile)
            if roh:
                # Kein `effects {` -> der Eintrag kam nicht aus `vertrag(f)`, also gibt es
                # keine `FnDecl` und damit keinen Ort fuer ein `ensures`.
                koerper.append((roh.group(1).split()[0], False, False))
                continue
            if zeile.strip():
                in_e = False
        b = BEFUND.match(zeile)
        if b:
            eingestuft = []
            for name, hat_ort, spricht in koerper:
                if not hat_ort:
                    eingestuft.append((name, STUMM))
                elif not spricht:
                    eingestuft.append((name, SCHWEIGT))
                elif name in gewirkt:
                    eingestuft.append((name, WIRKT))
                else:
                    eingestuft.append((name, UNGELESEN))
            je_datei[datei] = {
                "koerper": eingestuft,
                "befund": (int(b.group(1)), int(b.group(2)), int(b.group(3))),
            }
            datei = None
    return je_datei, r.stdout


def gegenrechnung(je_datei):
    """**Die Einstufung gegen die Buchung des Uebersetzers selbst.**

    Ein Muster, das seine eigene Zahl erzeugt, ist unbewacht und sieht bewacht aus (W16).
    Hier steht neben jeder selbstgezaehlten Zahl die, die `zeugnis.rs` gedruckt hat --
    *stimmen sie nicht ueberein, ist die Einstufung falsch und nicht die Buchung.*
    """
    fehler = []
    for name, d in sorted(je_datei.items()):
        f_soll, p_soll, _ = d["befund"]
        f_ist = len(d["koerper"])
        p_ist = sum(1 for _, z in d["koerper"] if z in (UNGELESEN, WIRKT))
        if (f_ist, p_ist) != (f_soll, p_soll):
            fehler.append(f"  !! {name}: eingestuft {f_ist} Ruempfe / {p_ist} sprechen, "
                          f"Zeugnis sagt {f_soll} / {p_soll}")
    return fehler


VORLAGE_WIRKT = """module p {
    type Zahl = u32 in 0 .. 4096;
    reason Leer { Nichts = 1 "nichts da" exhaustive }
    extern fn hole() -> Zahl or Leer
        ensures result >= 1
        effects { pure }
        costs   <= 8 ops;
    impl fn nutze() -> Zahl
        effects { pure }
        costs   <= 32 ops
    {
        let n = hole() else (e) { return 1; }
        return n;
    }
}
"""
VORLAGE_UNGELESEN = """module p {
    type Zahl = u32 in 1 .. 4096;
    reason Leer { Nichts = 1 "nichts da" exhaustive }
    extern fn hole() -> Zahl or Leer
        ensures result >= 1
        effects { pure }
        costs   <= 8 ops;
    impl fn nutze() -> Zahl
        effects { pure }
        costs   <= 32 ops
    {
        let n = hole() else (e) { return 1; }
        return n;
    }
}
"""
VORLAGE_SCHWEIGT = """module p {
    extern fn hole() -> u32
        effects { pure }
        costs   <= 8 ops;
}
"""
VORLAGE_STUMM = """module p {
    static mut auftragsliste : u32 = 0;
    lock WARTESCHLANGE protects { auftragsliste } rank 0 held <= 20000 ops;
}
"""


def sprechprobe():
    """**In BEIDE Richtungen, an vier erfundenen Quellen -- eine je Zustand.**

    Eine Einstufung, die nur den eigenen Korpus liest, misst, wie gut sie zu ihm passt. Hier
    steht je Zustand eine Einheit, die genau in ihn fallen MUSS:

        WIRKT      `u32 in 0 .. 4096` + `ensures result >= 1`  -- die Grenze wandert
        UNGELESEN  `u32 in 1 .. 4096` + dieselbe Zeile         -- sie wandert nicht
        SCHWEIGT   `extern fn` ohne `ensures`                  -- der Ort ist da
        STUMM      `lock` -- es gibt kein `ensures`-Feld

    *Faellt einer davon in den falschen Topf, misst das Werkzeug nichts mehr.* Der Unterschied
    zwischen `WIRKT` und `UNGELESEN` ist EIN Zeichen der Untergrenze -- das ist die schaerfste
    Stelle, und sie steht deshalb zuerst.
    """
    erwartet = {
        "wirkt": (WIRKT, VORLAGE_WIRKT),
        "ungelesen": (UNGELESEN, VORLAGE_UNGELESEN),
        "schweigt": (SCHWEIGT, VORLAGE_SCHWEIGT),
        "stumm": (STUMM, VORLAGE_STUMM),
    }
    with tempfile.TemporaryDirectory(dir=str(W / "target")) as d:
        ort = pathlib.Path(d)
        for k, (_, text) in erwartet.items():
            (ort / f"{k}.gab").write_text(text, encoding="utf-8")
        je_datei, roh = messe(W, [ort / f"{k}.gab" for k in erwartet])

    print("== Sprechprobe, in beide Richtungen -- eine Einheit je Zustand ==")
    gut = True
    for k, (soll, _) in erwartet.items():
        d = next((v for n, v in je_datei.items() if n.endswith(f"{k}.gab")), None)
        ist = [z for _, z in d["koerper"]] if d else []
        # Genau EIN fremder Rumpf je Probe, und er muss in seinen Topf fallen.
        ok = ist == [soll]
        gut = gut and ok
        print(f"  {k:<10} erwartet {soll:<10} gemessen {str(ist):<14} "
              + ("ok" if ok else "GESCHEITERT"))
    fehler = gegenrechnung(je_datei)
    print("  Gegenrechnung gegen die BEFUND-Zeile: "
          + ("stimmt" if not fehler else "WIDERSPRUCH"))
    for f in fehler:
        print(f)
    if not gut or fehler:
        print("\n  Das Werkzeug misst nicht, was es behauptet. Die Zahlen unten waeren ein")
        print("  Urteil im Gewand einer Messung.")
        print(roh[-1500:])
        return False
    return True


def ensures_text(wurzel, datei, name):
    """**Die `ensures`-Zeilen einer fremden Deklaration -- aus der QUELLE, nicht aus dem Baum.**

    Ein Textgriff, und er steht deshalb unter dem Urteil und nicht darin. Er dient genau einer
    Frage: nennt die Klausel `result`, oder redet sie ueber Weltzustand?
    """
    p = wurzel / datei
    if not p.exists():
        return []
    # **Kommentarzeilen zaehlen nicht -- und das war kein theoretischer Fall.**
    # `beispiele/22` fuehrt seine eigene Deklaration in Zeile 26 noch einmal als Beispiel im
    # Kopfkommentar. Der erste Treffer war der Kommentar, der Absteig lief von dort und fand
    # kein `ensures` -- *und „keine Zeile gefunden" fiel still in den Weltzustandstopf, wo es
    # zufaellig richtig lag.* Genau die Bewegung, gegen die dieser Ordner gebaut ist: eine
    # Blindheit, die sich als Antwort liest.
    zeilen = [z for z in p.read_text(encoding="utf-8").splitlines()
              if not z.lstrip().startswith("--")]
    anfang = next((i for i, z in enumerate(zeilen)
                   if re.search(rf"\bfn\s+{re.escape(name)}\s*\(", z)), None)
    if anfang is None:
        return []
    aus = []
    for z in zeilen[anfang:]:
        s = z.strip()
        if s.startswith("ensures") or s.startswith("maintains"):
            aus.append(s.rstrip(","))
        if s.endswith(";"):
            break
    return aus


def main():
    # **TOOTH 0 -- THE SUBJECT HAS TO BE THERE** (2026-08-31). Over a tree without
    # its subject this tool died of a `FileNotFoundError`: return code **1**, a
    # traceback, and in a chain that reads like a finding. *A crash is not a refusal
    # -- a NAMED refusal is*, and a missing subject says the SETUP has to change.
    # Here the subject is the BUILD DIRECTORY: the speech test writes its invented units
    # into `target/`, and without it `tempfile` raises before a single line is read.
    if not (W / "target").is_dir():
        print("ABBRUCH: target/ fehlt -- die Sprechprobe kann ihre erfundenen Einheiten "
              "nicht anlegen; gebaut wird auf ki-pc-fisch-101 (CLAUDE.md).", file=sys.stderr)
        return 2
    nur_probe = "--sprechprobe" in sys.argv
    if not sprechprobe():
        # 2, not 1: a fallen speech test has measured NOTHING.
        return 2
    if nur_probe:
        return 0

    pfade = dateien(W, MUSTER)
    gift = sorted(W.glob(GIFT))
    je_datei, _ = messe(W, pfade)

    fehler = gegenrechnung(je_datei)
    if fehler:
        print("\n!! ABBRUCH: die Einstufung widerspricht der BEFUND-Zeile des Zeugnisses.")
        print("   Nicht die Buchung ist falsch, sondern dieses Werkzeug.")
        for f in fehler:
            print(f)
        return 2

    zahl = {z: 0 for z in ZUSTAENDE}
    for d in je_datei.values():
        for _, z in d["koerper"]:
            zahl[z] += 1
    gesamt = sum(zahl.values())

    if "--stellen" in sys.argv:
        print()
        print("== Jeder fremde Rumpf mit seinem Zustand ==")
        for name in sorted(je_datei):
            for k, z in je_datei[name]["koerper"]:
                print(f"  {z:<10} {name}:{k}")

    print()
    print("== Die vier Zustaende einer fremden Pflicht ==")
    for z in ZUSTAENDE:
        anteil = f"{100 * zahl[z] / gesamt:.0f} %" if gesamt else "--"
        print(f"  {z:<10} {zahl[z]:>4}  ({anteil:>4})  {SATZ[z]}")
    print(f"  {'':<10} {gesamt:>4}  fremde Ruempfe in {len(je_datei)} Einheiten mit Zeugnis")

    # **Die Aufschluesselung von UNGELESEN -- und sie ist ein Textgriff.**
    ueber_welt, ueber_ergebnis, verfehlt = [], [], []
    for name in sorted(je_datei):
        for k, z in je_datei[name]["koerper"]:
            if z != UNGELESEN:
                continue
            klauseln = ensures_text(W, name, k)
            if not klauseln:
                # **Nicht gefunden ist nicht „redet ueber Weltzustand"** (W10). Ein
                # Textgriff, der danebengreift, darf nicht in den haeufigeren Topf fallen --
                # sonst waechst genau die Zahl, die den Posten traegt.
                verfehlt.append((name, k, []))
            elif any("result" in c for c in klauseln):
                ueber_ergebnis.append((name, k, klauseln))
            else:
                ueber_welt.append((name, k, klauseln))
    print()
    print(f"== Wovon die {zahl[UNGELESEN]} ungelesenen Zeilen REDEN (Textgriff, nicht Parser) ==")
    print(f"  ueber WELTZUSTAND (nennt `result` nicht) {len(ueber_welt):>3}  "
          "-- kollidiert mit U4/U5: ein Aufruf toetet jeden nichtlokalen Fakt")
    print(f"  ueber das ERGEBNIS (nennt `result`)      {len(ueber_ergebnis):>3}  "
          "-- der Bereich bewegt sich nicht, oder niemand ruft die Funktion")
    if verfehlt:
        print(f"  !! VOM TEXTGRIFF VERFEHLT                {len(verfehlt):>3}  "
              "-- die Deklaration wurde nicht gefunden; das ist KEINE Aussage ueber sie")
    for n, k, c in ueber_welt + ueber_ergebnis + verfehlt:
        print(f"     {n}:{k:<24} {'; '.join(c) or '(VERFEHLT)'}")

    print()
    print(f"== {zahl[WIRKT]} von {gesamt} fremden Ruempfen tragen eine Pflicht, die WIRKT ==")
    print(f"   {zahl[STUMM]} koennen gar keine tragen: `lock`, `rcu`, `guest`, `entry`, `boot`")
    print("   und `gabbro_kern` haben kein `ensures`-Feld in der Grammatik. **Fuer sie ist")
    print("   „die Zeile hinschreiben\" keine Sorgfaltsfrage, sondern eine Grammatikaenderung.**")
    print(f"   Arbeitsmenge: {len(je_datei)} von {len(pfade)} Dateien mit Zeugnis, "
          f"{len(pfade) - len(je_datei)} tragen Fehler.")
    print(f"   NICHT angesehen: {len(gift)} Giftdateien -- ueber einer abgewiesenen Einheit")
    print("   gibt es kein Zeugnis (W10).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
