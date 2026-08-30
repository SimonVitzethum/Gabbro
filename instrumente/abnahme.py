#!/usr/bin/env python3
"""**Die Abnahme -- EIN Befehl, der JEDEN Waechter faehrt und je Waechter ein Urteil nennt.**

Am 2026-08-30 gab es 26 `pruefe-*`-Waechter und **keinen Lauf, der alle faehrt**.
`dokumente/PLAN-AUTONOM.md` §1.7 nannte elf; jede Sitzung stellte sich den Rest aus dem
Gedaechtnis zusammen. Sieben standen in KEINER Liste und in keinem Sammellauf --
`pruefe-abstieg.py`, `pruefe-aufloesung.py`, `pruefe-reichweite.py`, `pruefe-widerruf.py`,
`pruefe-lean-beweis.sh`, `pruefe-lean-programm.sh`, `pruefe-p6-beweis.sh`. Zwei rote Ratschen
sind darunter **zwei Tage lang durch vier Zusammenfuehrungen** gelaufen.

> **Ein Waechter, den niemand faehrt, ist von einem, den es nicht gibt, nicht zu
> unterscheiden.**

ABGRENZUNG ZU `pruefe-waechter.py` -- ZWEI GEGENSTAENDE, NICHT ZWEI REGISTER
----------------------------------------------------------------------------
`pruefe-waechter.py` fragt: **ist das ein taugliches Instrument?** (Frist, Sprechprobe, roter
Abbruch, Arbeitsmenge, Gebietsschema). Sein `--lauf` fuehrt zwar aus, liest aber das URTEIL
nicht -- ein Ruecklaufwert 1 ist ihm ein ordentliches Ende, denn ein Waechter DARF rot werden.

Dieser Lauf fragt das andere: **steht der Baum gruen?** Er liest genau den Ruecklaufwert, den
der andere ignoriert. *Zwei Fragen, ein Verzeichnis.*

*Damit daraus nicht zwei Register ueber einer Sache werden* (W7), haelt diese Datei **keine
eigene Liste**: `SCHWER`, `ARGUMENTE`, `FREMDER_KORPUS` und `FRIST` werden aus
`pruefe-waechter.py` GELESEN. Wer dort einen Eintrag pflegt, pflegt ihn hier mit.

DIE BESETZUNG KOMMT AUS DEM VERZEICHNIS, NICHT AUS DIESER DATEI
----------------------------------------------------------------
Eine Liste im Skript haette dasselbe Problem eine Ebene tiefer: sie veraltet lautlos --
genau so ist §1.7 bei elf von 26 stehengeblieben. Gelesen wird `instrumente/pruefe-*` und
`instrumente/mutiere-*`. **Ein neuer Waechter ist damit am Tag seiner Entstehung dabei**, und
einer, der ein Argument braucht, faellt BENANNT auf.

Die `zaehle-*` sind NICHT in der Abnahme -- sie messen, sie bewachen nicht. *Diese Grenze
wird gedruckt und nicht verschwiegen*, mit ihrer Zahl; wer sie verschieben will, sieht sie.

VIER URTEILE, UND DAS DRITTE IST DER GRUND FUER DIESE DATEI
------------------------------------------------------------
    gruen             Ruecklaufwert 0
    ROT               Ruecklaufwert != 0 -- ein Befund
    NICHT FAHRBAR     das Werkzeug ist gar nicht gelaufen (Absturz, Frist, fehlender Korpus)
    ausgelassen       teuer, und der Schnellauf SAGT es

**Ein Absturz ist keine Absage.** `pruefe-wortschatz.py` stirbt ohne Dateiargument mit
`IndexError` -- Ruecklaufwert 1, und es sieht aus wie ein Befund. Es ist keiner: das Werkzeug
hat nichts angesehen. Wer den Unterschied nicht druckt, bucht eine Luecke als Fund.

**Und eine unangemeldete Luecke ist ROT.** Ein Waechter, dessen Argument in `ARGUMENTE`
steht, wird mit dem Argument gefahren. Steht es dort NICHT und er stuerzt ab, ist er nicht
bloss ausgewiesen, sondern rot -- genau der Zustand, gegen den dieser Lauf gebaut ist. *Ein
angemeldetes Loch ist ein Loch mit einem Namen; ein unangemeldetes ist eine Behauptung.*

    ./instrumente/abnahme.py            der Schnellauf -- teure ausgelassen und GENANNT
    ./instrumente/abnahme.py --voll     alle, auch die teuren
    ./instrumente/abnahme.py --probe    nur die Sprechprobe

**W17 -- die Arbeitsmenge steht neben dem Urteil.** Der Lauf nennt, WIE VIELE Waechter er
gefahren hat, und **ein Lauf, der null faehrt, ist rot und nicht gruen**. Das ist keine
Vorsicht, sondern der dreimal bezahlte Fall: `isabelle build -D .` waehlte nichts und endete
gruen.
"""
import importlib.util
import pathlib
import subprocess
import sys
import tempfile
import time

W = pathlib.Path(__file__).resolve().parent.parent

# The registers live in `pruefe-waechter.py` and are READ, not copied -- a second list over
# the same thing is W7. The hyphen in the file name rules out a plain `import`.
_spec = importlib.util.spec_from_file_location("pw", W / "instrumente" / "pruefe-waechter.py")
_pw = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_pw)

SCHWER = _pw.SCHWER
ARGUMENTE = _pw.ARGUMENTE
FRIST = _pw.FRIST
korpus_fehlt = _pw.korpus_fehlt

# **The heavy ones get their own deadline, and it is not a comfort setting.**
# `mutiere-pruefer.py` WRITES INTO SOURCES and puts them back byte for byte afterwards. Killed
# by a deadline halfway through, it leaves a mutated tree behind -- and the next measurement
# runs against a mixture, which is `W16` word for word. Measured 2026-08-30: the full run
# takes 10 min 25 s, well past `FRIST`. *A deadline that fires mid-write is worse than none.*
FRIST_VOLL = 1800

# **The cheap half of an expensive guardian, so the quick run is not blind to it.**
# `--anker` counts text and builds nothing (`CLAUDE.md`), and it is the half that catches a
# dead anchor -- a mutation whose source line moved away silently shrinks the denominator and
# reads like coverage. The expensive half stays behind `--voll` and is named there.
SCHNELL_TEIL = {"mutiere-pruefer.py": ["--anker"]}

# A Python interpreter that dies in its own prologue has not rendered a verdict. This is the
# ONE signal that separates "did not run" from "found something".
ABSTURZ = "Traceback (most recent call last)"


def besetzung(wurzel):
    """Every guardian in `wurzel` -- from the DIRECTORY, never from a list in here."""
    return sorted(
        set(wurzel.glob("pruefe-*")) | set(wurzel.glob("mutiere-*")),
        key=lambda p: p.name,
    )


def fahre_einen(p, voll, arbeitsverzeichnis):
    """One guardian. Returns `(marke, ruecklauf, dauer, bemerkung)`.

    `marke` is one of `gruen` · `ROT` · `NICHT FAHRBAR` · `ausgelassen`.
    """
    teuer = p.name in SCHWER
    args = [str(pathlib.Path(a).expanduser()) if a.startswith("~") else a
            for a in ARGUMENTE.get(p.name, [])]
    angemeldet = p.name in ARGUMENTE
    nachsatz = ""
    if teuer and not voll:
        if p.name not in SCHNELL_TEIL:
            return "ausgelassen", None, 0.0, SCHWER[p.name]
        args = SCHNELL_TEIL[p.name]
        nachsatz = f"nur `{' '.join(args)}` -- der volle Lauf steht unter `--voll`"
    fehlt = korpus_fehlt(p.name)
    if fehlt:
        ort, was = fehlt
        return "NICHT FAHRBAR", None, 0.0, f"fremder Korpus fehlt: {was} ({ort})"
    frist = FRIST_VOLL if teuer else FRIST
    t0 = time.monotonic()
    try:
        r = subprocess.run([str(p)] + args, cwd=arbeitsverzeichnis, capture_output=True,
                           text=True, timeout=frist)
    except subprocess.TimeoutExpired:
        return "NICHT FAHRBAR", None, time.monotonic() - t0, f"HAENGT -- Frist {frist} s"
    except (PermissionError, OSError) as e:
        return "NICHT FAHRBAR", None, time.monotonic() - t0, f"nicht startbar: {e}"
    dauer = time.monotonic() - t0
    if angemeldet and not nachsatz:
        nachsatz = f"braucht ein Argument, bekommt `{' '.join(args)}`"
    if ABSTURZ in (r.stderr or ""):
        zeilen = [z for z in r.stderr.strip().splitlines() if z.strip()]
        grund = zeilen[-1] if zeilen else "Absturz"
        # An unannounced crash is RED: the guardian measured nothing and nobody declared it.
        marke = "NICHT FAHRBAR" if angemeldet else "ROT"
        return marke, r.returncode, dauer, f"ABGESTUERZT, kein Urteil -- {grund}"
    if r.returncode == 0:
        return "gruen", 0, dauer, nachsatz
    kopf = [z for z in (r.stdout or "").splitlines() if z.strip()]
    schluss = kopf[-1].strip()[:80] if kopf else ""
    return "ROT", r.returncode, dauer, "; ".join(x for x in (schluss, nachsatz) if x)


def fahre(wurzel, voll, arbeitsverzeichnis):
    """The whole cast. Returns the list of `(name, marke, ruecklauf, dauer, bemerkung)`."""
    return [(p.name,) + fahre_einen(p, voll, arbeitsverzeichnis)
            for p in besetzung(wurzel)]


def urteil(ergebnisse):
    """`(ruecklaufwert, gefahren, gruen, rot, nicht_fahrbar, ausgelassen)`.

    **Null gefahrene Waechter sind ROT.** Ein positives Urteil ueber nichts sieht aus wie ein
    Ergebnis und ist keines (W17).
    """
    gruen = sum(1 for e in ergebnisse if e[1] == "gruen")
    rot = sum(1 for e in ergebnisse if e[1] == "ROT")
    nf = sum(1 for e in ergebnisse if e[1] == "NICHT FAHRBAR")
    aus = sum(1 for e in ergebnisse if e[1] == "ausgelassen")
    gefahren = gruen + rot + nf
    return (1 if (rot or gefahren == 0) else 0), gefahren, gruen, rot, nf, aus


def sprechprobe():
    """**In alle Richtungen, auf ERFUNDENEN Waechtern.**

    Ein Sammellauf, der nur die eigenen Waechter liest, misst, wie gut sie zu ihm passen.
    Gepruefte Behauptung: ein kuenstlich rot gemachter Waechter macht den Sammellauf rot,
    ein gruener nicht, ein abstuerzender faellt als eigener Fall auf -- und **ein leeres
    Verzeichnis ist rot, nicht gruen**.
    """
    proben = []
    with tempfile.TemporaryDirectory() as d:
        dp = pathlib.Path(d)
        (dp / "pruefe-gruen.sh").write_text("#!/bin/sh\necho '== 3 von 3 =='\nexit 0\n")
        (dp / "pruefe-rot.sh").write_text("#!/bin/sh\necho '! RATSCHE: 28, erlaubt 27'\nexit 1\n")
        (dp / "pruefe-sturz.py").write_text(
            "#!/usr/bin/env python3\nimport sys\nsys.argv[1]\n")
        for f in dp.iterdir():
            f.chmod(0o755)
        erg = fahre(dp, voll=True, arbeitsverzeichnis=dp)
        rc, gefahren, gruen, rot, nf, _ = urteil(erg)
        marken = {n: m for n, m, *_ in erg}
        proben.append(("drei Waechter gefunden und gefahren", gefahren == 3 and len(erg) == 3))
        proben.append(("der gruene ist gruen", marken.get("pruefe-gruen.sh") == "gruen"))
        proben.append(("der rote ist ROT", marken.get("pruefe-rot.sh") == "ROT"))
        # It is not in `ARGUMENTE`, so an unannounced crash must be RED, not a soft gap.
        proben.append(("der abstuerzende faellt auf", marken.get("pruefe-sturz.py") == "ROT"))
        proben.append(("ein roter macht den Lauf rot", rc == 1 and rot == 2 and gruen == 1))
        leer = dp / "leer"
        leer.mkdir()
        rc0, gefahren0, *_ = urteil(fahre(leer, voll=True, arbeitsverzeichnis=leer))
        proben.append(("null gefahren ist ROT, nicht gruen", rc0 == 1 and gefahren0 == 0))
    return proben


def main():
    voll = "--voll" in sys.argv
    proben = sprechprobe()
    print("== Sprechprobe -- auf erfundenen Waechtern, in alle Richtungen ==")
    for was, ok in proben:
        print(f"  {'ok         ' if ok else 'GESCHEITERT'}  {was}")
    if not all(ok for _, ok in proben):
        print("\n! Der Sammellauf misst nicht, was er behauptet. ABBRUCH.")
        return 2
    if "--probe" in sys.argv:
        return 0

    inst = W / "instrumente"
    alle = besetzung(inst)
    zaehler = sorted(set(inst.glob("zaehle-*")))
    print()
    print(f"== Abnahme ueber {len(alle)} Waechter aus {inst.name}/ "
          f"{'(VOLL)' if voll else '(Schnellauf)'} ==")
    print()

    erg = fahre(inst, voll, W)
    for name, marke, rc, dauer, bem in erg:
        rcs = "" if rc is None else f"[{rc}]"
        print(f"  {marke:<14} {name:<26} {dauer:6.1f} s {rcs:<4} {bem}")

    code, gefahren, gruen, rot, nf, aus = urteil(erg)

    print()
    print(f"== Arbeitsmenge: {gefahren} von {len(alle)} Waechtern GEFAHREN -- "
          f"{gruen} gruen, {rot} ROT, {nf} nicht fahrbar ==")

    teilweise = [n for n, m, _, _, b in erg if n in SCHNELL_TEIL and "--voll" in b]
    if aus or teilweise:
        print()
        print(f"== {aus + len(teilweise)} teure AUSGELASSEN oder halbiert -- "
              f"und sie stehen hier, statt zu fehlen ==")
        for name, marke, _, _, bem in erg:
            if marke == "ausgelassen" or name in teilweise:
                print(f"   {name:<26} {bem}")
        print("   `--voll` faehrt sie mit. **Ein Sammellauf, der die teuren stillschweigend")
        print("   auslaesst, ist genau der Waechter, gegen den dieser Lauf gebaut ist.**")

    braucht_arg = [n for n, _, _, _, b in erg if b.startswith("braucht ein Argument")]
    if braucht_arg:
        print()
        print(f"== {len(braucht_arg)} Waechter sind NICHT selbststaendig fahrbar ==")
        print("   " + ", ".join(braucht_arg))
        print("   Ihr Argument steht in `pruefe-waechter.py:ARGUMENTE` und wird von hier")
        print("   gestellt. **Ohne es stuerzen sie ab und der Absturz sieht aus wie ein")
        print("   Befund** -- ein Ruecklaufwert 1 aus einem `IndexError` ist kein Urteil.")

    print()
    print(f"== Nicht in der Abnahme: {len(zaehler)} `zaehle-*` ==")
    print("   Sie messen, sie bewachen nicht -- kein Ruecklaufwert, der ein Urteil traegt.")
    print("   Die Grenze steht hier, damit sie jemand verschieben KANN. Ein Werkzeug,")
    print("   das niemand nennt, verschiebt niemand.")

    print()
    print("== Und was das NICHT heisst ==")
    print("   Gruen heisst: jeder gefahrene Waechter endete mit 0. Was KEIN Waechter")
    print("   ansieht, faellt auch hier nicht auf -- die Abnahme verpflichtet, sie")
    print("   spricht nicht frei (W10). Und `nicht fahrbar` ist eine LUECKE mit einem")
    print("   Namen, kein gruener Haken.")
    if gefahren == 0:
        print("\n! NULL Waechter gefahren. Ein positives Urteil ueber nichts ist keines (W17).")
    if rot:
        print(f"\n! ABNAHME ROT: {rot} von {gefahren} gefahrenen Waechtern melden einen Befund.")
        for name, marke, rc, _, bem in erg:
            if marke == "ROT":
                print(f"   {name:<26} [{rc}]  {bem}")
    elif nf:
        print(f"\n  ABNAHME GRUEN MIT LUECKE: {nf} Waechter sind nicht gefahren.")
    else:
        print(f"\n  ABNAHME GRUEN: {gruen} von {gruen} gefahrenen Waechtern.")
    return code


if __name__ == "__main__":
    sys.exit(main())
