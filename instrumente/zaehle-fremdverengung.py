#!/usr/bin/env python3
"""**Wie oft entscheidet die Zusage eines FREMDEN Rumpfes im Pruefer?**

`gabbro zeugnis` druckt die Zahl je Datei. Dieses Werkzeug druckt sie fuer den ganzen
Korpus -- und die Bezugsgroesse daneben, ohne die sie nichts sagt.

    Flaeche    fremde Ruempfe, die ihre Pflicht AUSSPRECHEN (`ensures` / `maintains`)
    Wirkung    Stellen, an denen daraus im Rufer eine Tatsache wurde

**Der Unterschied zwischen beiden ist der ganze Gegenstand.** Eine `ensures`-Zeile an einer
Deklaration ohne Rumpf steht in der Grammatik seit jeher; sie kostet nichts und bindet
niemanden, solange kein Bereich sich bewegt. *Gezaehlt wird hier die WIRKSAME Verengung.*

    ./instrumente/zaehle-fremdverengung.py               die Zahl fuer den ganzen Korpus
    ./instrumente/zaehle-fremdverengung.py --stellen     jede Stelle mit Datei, Zeile und Klausel
    ./instrumente/zaehle-fremdverengung.py --sprechprobe nur die Sprechprobe, in beide Richtungen

WAS DIE ZAHL NICHT SAGT
-----------------------
* **Sie ist eine UNTERE Schranke.** Gezaehlt wird nur, wo ein Zeugnis entsteht -- und das
  entsteht nur ueber einer Einheit ohne Fehler. Der Giftkorpus (`beispiele/gift/`) ist
  bauartbedingt abgewiesen und wird gar nicht erst angesehen; er steht mit seiner Zahl in
  der Ausgabe, nicht in der Summe (W10).
* **Sie ist in der anderen Richtung eine OBERE Schranke der GEBRAUCHTEN Tatsachen.** Eine
  Verengung, die entsteht und die niemand braucht, zaehlt hier mit. Der Pruefer weiss an
  dieser Stelle nicht, ob sie spaeter eine Absage entscheidet.
* **Sie sagt nichts darueber, ob die Zusage STIMMT.** Sie sagt, dass Gabbro sie glaubt.
"""
import pathlib
import re
import subprocess
import sys
import tempfile

W = pathlib.Path(__file__).resolve().parent.parent

# **Jede Ausfuehrung mit Frist.** Ein Haenger sieht aus wie „laeuft noch", nicht wie ein
# Befund -- am 2026-08-20 standen deswegen einundzwanzig Laeufe von `pruefe-emission.sh`
# nebeneinander, der aelteste seit dreieinhalb Stunden.
FRIST = 600

# **Der Korpus: jede Uebersetzungseinheit, ueber der ein Zeugnis ueberhaupt entstehen
# kann.** Der Giftkorpus steht bewusst NICHT hier: er ist gebaut, um abgewiesen zu werden,
# und ein Zeugnis ueber eine abgewiesene Einheit gibt es nicht. *Seine Zahl steht in der
# Ausgabe, damit die Luecke benannt ist statt unsichtbar.*
MUSTER = ["beispiele/*.gab", "messung/*/*.gab"]
GIFT = "beispiele/gift/*.gab"

KOPF = re.compile(r"^== Translation certificate: (\S+) ==$")
# **Carried over 2026-08-30:** the certificate's finding line took a THIRD currency, `N
# UNCOVERED` -- an assumption naming a probe that no program redeems. *The old pattern lost
# its subject that way and reported the search path as gone* -- correctly, and that is what
# the message is for. The pattern moves onto the wording that stands there.
BEFUND = re.compile(
    r"^\s+\d+ assumptions \(\d+ of them NOT FALSIFIABLE, \d+ UNCOVERED[^)]*\), "
    r"\d+ templates \(\d+ of them UNPROVED\), \d+ direct forms, "
    r"(\d+) foreign bodies \((\d+) state their duty\), (\d+) narrowings from foreign "
    r"contracts$"
)
# Eine Stelle: `     127:     abarbeiten -> naechste_menge         range    result >= 1`
STELLE = re.compile(r"^\s+(\d+):\s+(\S+) -> (\S+)\s+(\S+)\s+(.*)$")


def dateien(wurzel, muster):
    aus = []
    for m in muster:
        aus += sorted(wurzel.glob(m))
    return aus


def messe(wurzel, pfade):
    """(je_datei, roh) -- je Datei (fremde, mit_pflicht, verengungen, stellen).

    **Bricht sichtbar ab, statt null zu zaehlen** (R14a): laeuft der Uebersetzer nicht, ist
    das kein Ergebnis von null Verengungen, sondern gar kein Ergebnis.
    """
    if not pfade:
        print("!! ABBRUCH: kein Korpus gefunden -- das ist KEINE Zaehlung von null.")
        sys.exit(2)
    # **Relativ uebergeben, weil das Zeugnis den Namen abdruckt, den es bekommt.** Ein
    # absoluter Pfad macht aus jeder Fundstelle den Rechnernamen des Laufs.
    namen = [str(p.relative_to(wurzel)) if p.is_absolute() and p.is_relative_to(wurzel)
             else str(p) for p in pfade]
    r = subprocess.run(
        ["cargo", "run", "-q", "-p", "gabbro-cli", "--", "zeugnis"] + namen,
        cwd=wurzel,
        capture_output=True,
        text=True, timeout=FRIST)
    # Ruecklaufwert 1 heisst nur: mindestens eine Einheit traegt Fehler. Das ist ueber dem
    # Fragmentkorpus der Normalfall und kein Abbruch.
    if r.returncode not in (0, 1) or "Translation certificate" not in r.stdout:
        print("!! ABBRUCH: `gabbro zeugnis` lief nicht -- das ist KEINE Zaehlung von null.")
        print((r.stderr or r.stdout)[-800:])
        sys.exit(2)
    je_datei, datei, stellen = {}, None, []
    for zeile in r.stdout.splitlines():
        k = KOPF.match(zeile)
        if k:
            datei, stellen = k.group(1), []
            continue
        if datei is None:
            continue
        s = STELLE.match(zeile)
        if s:
            stellen.append((int(s.group(1)), s.group(2), s.group(3), s.group(4),
                            s.group(5).strip()))
            continue
        b = BEFUND.match(zeile)
        if b:
            je_datei[datei] = (int(b.group(1)), int(b.group(2)), int(b.group(3)), stellen)
            datei = None
    return je_datei, r.stdout


def sprechprobe():
    """**In BEIDE Richtungen, an erfundenen Quellen.**

    Eine Zaehlung, die nur die eigenen Korpusdateien liest, misst, wie gut sie zu ihnen
    passt. Hier stehen zwei Einheiten, die sich in genau EINEM Zeichen unterscheiden --
    der Untergrenze des Ergebnistyps:

        Rest   = u32 in 0 .. 4096   `ensures result >= 1` VERENGT      -> 1
        Laenge = u32 in 1 .. 4096   `ensures result >= 1` bindet keinen -> 0

    *Faellt die erste Zahl auf 0, misst das Werkzeug nichts mehr. Steigt die zweite auf 1,
    zaehlt es Klauseln statt Wirkungen.* Beide Richtungen muessen stimmen.
    """
    vorlage = (
        "module p {{\n"
        "    type Zahl = u32 in {lo} .. 4096;\n"
        "    reason Leer {{ Nichts = 1 \"nichts da\" exhaustive }}\n"
        "    extern fn hole() -> Zahl or Leer\n"
        "        ensures result >= 1\n"
        "        effects {{ pure }}\n"
        "        costs   <= 8 ops;\n"
        "    impl fn nutze() -> Zahl\n"
        "        effects {{ pure }}\n"
        "        costs   <= 32 ops\n"
        "    {{\n"
        "        let n = hole() else (e) {{ return 1; }}\n"
        "        return n;\n"
        "    }}\n"
        "}}\n"
    )
    with tempfile.TemporaryDirectory(dir=str(W / "target")) as d:
        ort = pathlib.Path(d)
        (ort / "wirkt.gab").write_text(vorlage.format(lo=0), encoding="utf-8")
        (ort / "stumm.gab").write_text(vorlage.format(lo=1), encoding="utf-8")
        je_datei, roh = messe(W, [ort / "wirkt.gab", ort / "stumm.gab"])
    wirkt = next((v[2] for k, v in je_datei.items() if k.endswith("wirkt.gab")), None)
    stumm = next((v[2] for k, v in je_datei.items() if k.endswith("stumm.gab")), None)
    print("== Sprechprobe, in beide Richtungen ==")
    print(f"  verengende Klausel  (u32 in 0 .. 4096):  {wirkt}  "
          + ("ok" if wirkt == 1 else "GESCHEITERT -- erwartet 1"))
    print(f"  bindende Klausel ohne Wirkung (1 .. 4096): {stumm}  "
          + ("ok" if stumm == 0 else "GESCHEITERT -- erwartet 0"))
    if wirkt != 1 or stumm != 0:
        print("\n  Das Werkzeug misst nicht, was es behauptet. Die Zahl unten waere ein")
        print("  Urteil im Gewand einer Messung.")
        print(roh[-1200:])
        return False
    return True


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

    fremde = sum(v[0] for v in je_datei.values())
    pflicht = sum(v[1] for v in je_datei.values())
    verengt = sum(v[2] for v in je_datei.values())

    if "--stellen" in sys.argv:
        print()
        print("== Jede Stelle, an der ein fremder Vertrag im Rufer WIRKT ==")
        for name in sorted(je_datei):
            for zeile, rufer, gerufener, art, klausel in je_datei[name][3]:
                print(f"  {name}:{zeile:<5} {rufer} -> {gerufener:<24} {art:<9} {klausel}")

    print()
    print("== Die Flaeche und ihre Wirkung ==")
    for name in sorted(je_datei):
        f, p, v, _ = je_datei[name]
        if p or v:
            print(f"  {name:<38} {f:>3} fremd, {p:>2} sprechen, {v:>2} verengen")
    print()
    print(f"== {verengt} wirksame Fremdverengungen aus {pflicht} ausgesprochenen "
          f"Vertraegen, {len(je_datei)} von {len(pfade)} Dateien mit Zeugnis ==")
    print(f"   {fremde} fremde Ruempfe insgesamt; {len(pfade) - len(je_datei)} Dateien "
          f"tragen Fehler und haben kein Zeugnis.")
    print(f"   NICHT angesehen: {len(gift)} Giftdateien -- sie sind gebaut, um abgewiesen")
    print("   zu werden, und ueber einer abgewiesenen Einheit gibt es kein Zeugnis (W10).")
    print("   Was die Zahl NICHT sagt: ob die Zusage stimmt. Nur, dass Gabbro sie glaubt.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
