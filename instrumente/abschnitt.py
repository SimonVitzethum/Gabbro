#!/usr/bin/env python3
"""**Wer mitten im Lauf aussteigt, sagt WO.** Die gemeinsame Form, in einem Modul.

`messung/RUECKLAUFWERTE.md` hat den leeren Baum ueber jeden Waechter gefahren und die
Klasse gefunden, die er NICHT erreicht: eine Vorbedingung, die erst **mitten im Lauf**
wegbricht. Gemessen wurden 251 Ausgangsstellen hinter dem jeweils ersten; das Sieb darunter
(`pruefe-waechter.py`) laesst **92** uebrig, die eine Teilmessung hinterlassen, die wie eine
ganze aussieht -- und **104**, die erreichbar sind, ohne dass irgendetwas kaputt ist.

**Der Fall mit Datum.** `pruefe-emission.sh` starb am 2026-08-31 an `F06`s `N043` in der
vierten von zehn Stufen, mit `exit 1`. Die Stufen 9 und 10 liefen nie, und keine Zeile sagte
das; dahinter standen zwei Befunde, die zwei Wochen niemand gesehen hat.

> *Eine leere Grundgesamtheit ist ein gruenes Urteil ueber nichts (W17). Eine ABGESCHNITTENE
> sieht aus wie ein Urteil ueber alles.*

**Der Ruecklaufwert kann es nicht sagen, und darum sagt es die Ausgabe.** `1` heisst
„Befund"; ein Befund in Stufe 4 ist zugleich ein Abbruch fuer die Stufen 5 bis 10. Die drei
Klassen der Tafel kennen „nichts gemessen"; sie kennen „die Haelfte gemessen" nicht.

ANWENDUNG -- drei Zeilen, und keine davon je Stufe
--------------------------------------------------

    import abschnitt                       # `instrumente/` steht in `sys.path[0]`

    def main():
        ...
        abschnitt.fertig()                 # ab hier wird nichts mehr gemessen
        return 1 if befunde else 0

    if __name__ == "__main__":
        sys.exit(abschnitt.fahre(main))

**Das WO kommt aus der eigenen Ausgabe und nicht aus einer zweiten Liste.** Jeder Waechter
dieses Ordners druckt seine Abschnitte als `== … ==`; `fahre()` legt sich um `sys.stdout`
und merkt sich die letzte solche Zeile. Eine Marke je Stufe waere ein zweites Register ueber
derselben Sache (`W7`) -- und sie veraltet lautlos, genau wie die Liste, die Stufe 9 einmal
war.

**`fertig()` ist die einzige Zeile, die Urteilskraft braucht**, und sie ist notwendig: ein
Waechter, der an seinem LETZTEN Ausgang mit `1` endet, hat alles gemessen, und ein Waechter,
der am vorletzten mit `1` endet, nicht. Von aussen sieht beides gleich aus.

**Sie gehoert vor die URTEILSKETTE, nicht vor die letzte Rueckgabe** -- vor den letzten
zusammenhaengenden Block aus `if …: … return`. Der erste Anlauf setzte sie vor die letzte
Rueckgabe, und `pruefe-grammatiktafel.py` meldete daraufhin seinen VOLLSTAENDIGEN Befund als
abgeschnitten: sein rotes Ende und sein gruenes sind zwei verschiedene Rueckgaben, und beide
sind ganz. *Wer sie zu spaet setzt, bekommt eine Warnung zu viel -- wer sie zu frueh setzt,
eine zu wenig.*

Ein Waechter mit BETRIEBSARTEN traegt sie mehrfach: `mutiere-pruefer.py` dreimal, denn
`--anker`, `--schnell` und der volle Lauf sind jeder fuer sich ein ganzer Lauf.

**Und was diese Form NICHT tut** (W10): sie verhindert keinen Schnitt. Ein gedeckter Lauf
bricht genauso mitten im Lauf ab -- **er sagt es nur.** Das ist der ganze Unterschied, und
es ist der, der zwei Wochen gekostet hat.
"""
import sys

_MARKE = "Kopf (vor dem ersten Abschnitt)"
_FERTIG = False
_AN = False


class _Mitschnitt:
    """A pass-through around `sys.stdout` that remembers the last `== … ==` heading.

    It writes everything on, unchanged and in order; the only state it keeps is one string.
    A tool that changed its own output in order to describe itself would be measuring
    something else than it prints.
    """

    def __init__(self, unten):
        self._unten = unten
        self._rest = ""

    def write(self, s):
        global _MARKE
        self._rest += s
        while "\n" in self._rest:
            zeile, self._rest = self._rest.split("\n", 1)
            z = zeile.strip()
            if z.startswith("==") and len(z) > 2:
                _MARKE = z.strip("= ").strip() or _MARKE
        return self._unten.write(s)

    def __getattr__(self, name):
        return getattr(self._unten, name)


def marke():
    """The last heading printed -- the answer to *where did it stop?*"""
    return _MARKE


def fertig():
    """**Ab hier wird nichts mehr gemessen.** Directly before the final `return`."""
    global _FERTIG
    _FERTIG = True


def melde(rc, ziel=None):
    """Print the truncation notice for return code `rc` -- or nothing, if there is none."""
    if not rc or _FERTIG:
        return False
    ziel = ziel or sys.stdout
    print(file=ziel)
    print(f"== ABGESCHNITTEN in: {_MARKE} -- Ruecklaufwert {rc} ==", file=ziel)
    print("   Was DAHINTER steht, wurde NICHT gemessen -- weder ja noch nein. Dieser Lauf",
          file=ziel)
    print("   endete VOR seiner letzten Messung, und sein Ruecklaufwert sagt das nicht:",
          file=ziel)
    print("   eine `1` liest sich als Befund und ist hier zugleich ein Abbruch fuer alles",
          file=ziel)
    print("   dahinter. **Eine halbe Messung sieht aus wie eine ganze.**", file=ziel)
    print("   messung/RUECKLAUFWERTE.md, Abschnitt *Der Schnitt mitten im Lauf*.", file=ziel)
    return True


def fahre(hauptteil, *args, **kw):
    """Run `hauptteil` and, if it leaves early, say WHERE. Returns its return code.

    An uncaught exception is announced too and then re-raised: a crash is the earliest
    possible cut, and until today it looked like a finding with a traceback attached.
    """
    global _AN
    unten = sys.stdout
    if not _AN:
        sys.stdout = _Mitschnitt(unten)
        _AN = True
    try:
        rc = hauptteil(*args, **kw)
    except SystemExit as e:
        melde(e.code if isinstance(e.code, int) else 1)
        raise
    except BaseException:
        melde(1)
        raise
    finally:
        sys.stdout.flush()
        sys.stdout = unten
        _AN = False
    melde(rc)
    return rc


# **THE SPEECH TEST, IN FIVE DIRECTIONS -- and it runs on `python3 abschnitt.py`.**
# *A guardian that is green on the first attempt, without anyone having seen it fall, is an
# ornament* (R11). This module is not a guardian, but it is the thing every guardian's
# honesty about its own cut now rests on. `pruefe-waechter.py` drives it.
def sprechprobe():
    """`[(what, ok)]` -- a cut must be announced, a complete run must not be."""
    global _MARKE, _FERTIG
    import io

    def lauf(koerper):
        global _MARKE, _FERTIG
        _MARKE, _FERTIG = "Kopf (vor dem ersten Abschnitt)", False
        puffer = io.StringIO()
        echt = sys.stdout
        sys.stdout = puffer
        try:
            rc = fahre(koerper)
        except SystemExit as e:
            rc = e.code
        finally:
            sys.stdout = echt
        return rc, puffer.getvalue()

    def abgeschnitten():
        print("== Sprechprobe ==")
        print("== Stufe 4: der Differenztest ==")
        return 1

    def ganz():
        print("== Sprechprobe ==")
        print("== Stufe 9: jede Datei uebersetzt ==")
        fertig()
        return 1

    def gruen():
        print("== Stufe 9: jede Datei uebersetzt ==")
        return 0

    def stuerzt():
        print("== Stufe 2: der Kopf ==")
        raise ValueError("gestuerzt")

    rc_ab, aus_ab = lauf(abgeschnitten)
    rc_ganz, aus_ganz = lauf(ganz)
    rc_gruen, aus_gruen = lauf(gruen)
    try:
        _MARKE, _FERTIG = "Kopf (vor dem ersten Abschnitt)", False
        puffer = io.StringIO()
        echt = sys.stdout
        sys.stdout = puffer
        try:
            fahre(stuerzt)
        finally:
            sys.stdout = echt
        aus_sturz = puffer.getvalue()
    except ValueError:
        aus_sturz = puffer.getvalue()
    return [
        ("ein Lauf, der VOR seinem Ende mit 1 aussteigt, wird angesagt",
         rc_ab == 1 and "ABGESCHNITTEN in: Stufe 4: der Differenztest" in aus_ab),
        ("ein Lauf, der ALLES gemessen hat, wird NICHT angesagt -- auch mit 1",
         rc_ganz == 1 and "ABGESCHNITTEN" not in aus_ganz),
        ("ein gruener Lauf ohne `fertig()` wird ebenfalls nicht angesagt",
         rc_gruen == 0 and "ABGESCHNITTEN" not in aus_gruen),
        ("ein ABSTURZ ist der frueheste Schnitt und wird angesagt",
         "ABGESCHNITTEN in: Stufe 2: der Kopf" in aus_sturz),
        ("die eigene Ausgabe geht unveraendert durch",
         "== Stufe 9: jede Datei uebersetzt ==" in aus_ganz),
    ]


if __name__ == "__main__":
    print("== Sprechprobe der Abschnittsmeldung, in fuenf Richtungen ==")
    _proben = sprechprobe()
    for _was, _ok in _proben:
        print(f"  {'ok         ' if _ok else 'GESCHEITERT'}  {_was}")
    print(f"== {sum(1 for _, o in _proben if o)} von {len(_proben)} Richtungen halten ==")
    if not all(o for _, o in _proben):
        print("\n! Die Abschnittsmeldung misst nicht, was sie behauptet. ABBRUCH.",
              file=sys.stderr)
        sys.exit(2)
    sys.exit(0)
