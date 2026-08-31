#!/usr/bin/env python3
"""**FORM x ZUSTAENDIGKEIT aus der GRAMMATIK -- und `UNGEDECKT` muss leer sein.**

`gabbro blindstellen` rechnet Form mal Stellung ueber einem **Korpus** und nennt die leeren
Felder. Das beantwortet die Vollstaendigkeitsfrage nicht, und das Werkzeug sagt es selbst:
*der Korpus ist von der Sprache nach aussen geschrieben.* **Falle 80.**

Hier ist die Grundgesamtheit die **Grammatik**: `dokumente/SYNTAX.md` fuehrt 154 Regeln und
**219 Terminale**, und das ist die Menge, die „beliebig" meint. Je Terminal genau ein
Zustand:

    gesenkt       ein Programm mit diesem Wort emittiert C -- OHNE eine einzige Absage
    abgesagt      der Erzeuger sagt es benannt ab, und ein PRUEFERFEHLER nennt es auch
    vom Pruefer   nur ein Prueferfehler nennt es; der Erzeuger sieht die Form nie
    UNGEDECKT     keines davon

> **`UNGEDECKT` ist die ganze Frage.** Alles andere ist Buchhaltung.

WARUM `gesenkt` GEMESSEN IST UND NICHT GELESEN
------------------------------------------------
Ein Wort gilt genau dann als abgesenkt, wenn es in einer `.gab`-Datei steht, die
**vollstaendig emittiert**: null Prueferfehler UND null `C001`. Dann ist alles, was in
dieser Datei steht, durch den Erzeuger gegangen -- das Wort eingeschlossen. *Das ist kein
Textabgleich, sondern ein Lauf.*

**Und es ist tragfaehig, weil der Wortschatz GESCHLOSSEN ist.** `kw.rs` fuehrt 213 der 222
Woerter als `res` -- reserviert, nirgends ein Bezeichner. Ein Vorkommen IST damit ein
Schluesselwort. Die neun `ctx`-Woerter koennen ein Bezeichner sein; **sechs von ihnen stehen
in dieser Tafel** (`r`, `w`, `x` sind einbuchstabig und fallen schon aus der Terminalmenge),
und der Lauf NENNT sie neben dem Urteil, statt sie still mitlaufen zu lassen.

DREI REGISTER, GELESEN STATT KOPIERT (W7)
-------------------------------------------
    die Terminale       `pruefe-wortschatz.py`   -- es haelt sie schon gegen die EBNF
    die Absageformen    `zaehle-absagen.py`      -- 139 Stellen, 130 Formen
    die Prueferfehler   `Absage::fehler(…)` in jeder `gabbro-check/src/*.rs` AUSSER `emit.rs`

*Ein zweites Register ueber derselben Sache laeuft weg* -- dieser Ordner hat das oft genug
bezahlt, dass es keine dritte Kopie der Terminalliste gibt.

WAS DIESE TAFEL NICHT SAGT
----------------------------
**Eine besetzte Zelle heisst nicht, dass die Absenkung RICHTIG ist.** Sie heisst, dass es
eine gibt. `messung/fragmente/F06.gab` emittierte 161 Zeilen, die `cc -Werror` zurueckwies --
diese Tafel haette das Wort trotzdem als `gesenkt` gefuehrt. Die Gegenprobe dafuer ist Stufe 9
von `pruefe-emission.sh`, und sie laeuft seit dem 2026-08-31 auch ueber `messung/`.

    ./instrumente/pruefe-grammatiktafel.py            die Tafel und das Urteil
    ./instrumente/pruefe-grammatiktafel.py --probe    nur die Sprechprobe
    ./instrumente/pruefe-grammatiktafel.py --tafel    alle 219 Zeilen
"""
import collections
import contextlib
import importlib.util
import io
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
SYNTAX = W / "dokumente" / "SYNTAX.md"
CHECK = W / "crates" / "gabbro-check" / "src"
KW = W / "crates" / "gabbro-syntax" / "src" / "kw.rs"

# `Absage::fehler(code, span, text)` -- the message, and only the ERROR one. A `hinweis`
# does not reject: `beispiele/gift/166` carries `S007` as a hint, checks with zero errors
# and falls at `C001`. *A guardian that counts hints as refusals reads its own leniency as
# coverage.*
FEHLER = re.compile(r'Absage::fehler\([^,]+,[^,]+,\s*(?:format!\()?\s*"((?:[^"\\]|\\.)*)"', re.S)
WORT = re.compile(r"[A-Za-z_@][A-Za-z0-9_]*")


def _lade(name, argv):
    """Import an instrument as a MODULE -- its registers are read, never copied."""
    spec = importlib.util.spec_from_file_location(name.replace("-", "_").replace(".py", ""),
                                                  W / "instrumente" / name)
    mod = importlib.util.module_from_spec(spec)
    alt = sys.argv
    sys.argv = argv
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            spec.loader.exec_module(mod)
    except SystemExit:
        pass          # `pruefe-wortschatz.py` ends in `sys.exit`; its globals stand
    finally:
        sys.argv = alt
    return mod


def terminale(syntax=None):
    """The EBNF terminals -- from `pruefe-wortschatz.py`, which already holds them."""
    return set(_lade("pruefe-wortschatz.py", ["x", str(syntax or SYNTAX), "--probe"]).term)


def kontextuell():
    """The `ctx` words of `kw.rs`: they may also be an identifier."""
    return {t for t, k in re.findall(r'=>\s*"([^"]+)",\s*(res|ctx);', KW.read_text()) if k == "ctx"}


def _in_ruecken(text):
    """Every word inside backticks -- that is how this folder names a Gabbro form."""
    aus = set()
    for w in re.findall(r"`([^`]+)`", text):
        aus |= set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", w))
    return aus


def absageworte():
    """The words the EMITTER names in a refusal."""
    za = _lade("zaehle-absagen.py", ["x"])
    return _in_ruecken(" ".join(t for _, t, _ in za.formen())), za


def prueferworte():
    """The words a CHECKER ERROR names -- every pass but the emitter."""
    texte = []
    for q in sorted(CHECK.glob("*.rs")):
        if q.name != "emit.rs":
            texte += FEHLER.findall(q.read_text())
    return _in_ruecken(" ".join(texte)), len(texte)


def gesenkte_worte(korpus, wurzel=None):
    """Every word of every `.gab` that emits COMPLETELY -- 0 checker errors, 0 refusals.

    A file that produced C without a single `C001` has carried every construct in it
    through the emitter. *That is why this state is a run and not a reading.*
    """
    wurzel = wurzel or W
    aus = set()
    dateien = []
    for d, e in sorted(korpus.items()):
        if e["codes"] or e["c001"]:
            continue
        p = pathlib.Path(wurzel) / d
        if not p.exists():
            continue
        dateien.append(d)
        # `--` to end of line is a comment: a word EXPLAINED is not a word WRITTEN.
        aus |= set(WORT.findall(re.sub(r"--.*$", "", p.read_text(), flags=re.M)))
    return aus, dateien


def tafel(term, gesenkt, absage, pruefer):
    """Terminal -> one of the four states."""
    aus = {}
    for t in sorted(term):
        if t in gesenkt:
            aus[t] = "gesenkt"
        elif t in absage and t in pruefer:
            aus[t] = "abgesagt"
        elif t in pruefer:
            aus[t] = "vom Pruefer"
        else:
            aus[t] = "UNGEDECKT"
    return aus


def sprechprobe(term, gesenkt, absage, pruefer):
    """**In beide Richtungen, und beide sind im Auftrag genannt.**

    * eine kuenstlich ENTFERNTE Absenkung muss die Tafel rot machen,
    * eine kuenstlich ERFUNDENE Grammatikregel auch,
    * und ein unveraenderter Lauf darf das Wort NICHT nennen.

    *Ein Werkzeug, das ueber die Sprache urteilt und selbst ungeprueft ist, ist die
    teuerste Sorte Waechter.*
    """
    proben = []
    sauber = tafel(term, gesenkt, absage, pruefer)

    # (a) The REMOVED lowering. It takes a word that is `gesenkt` today -- the first in a
    #     fixed order, so that the probe does not travel with the corpus.
    kandidaten = sorted(t for t, z in sauber.items() if z == "gesenkt"
                        and t not in absage and t not in pruefer)
    if not kandidaten:
        proben.append(("kein Wort ist NUR durch Absenkung gedeckt -- die Probe misst nichts", False))
    else:
        w = kandidaten[0]
        gift = tafel(term, gesenkt - {w}, absage, pruefer)
        proben.append((f"entfernte Absenkung `{w}` faellt als UNGEDECKT",
                       gift[w] == "UNGEDECKT"))
        proben.append((f"und im sauberen Lauf ist `{w}` gesenkt", sauber[w] == "gesenkt"))

    # (b) The INVENTED grammar rule -- through a COPY of `SYNTAX.md`, hence through the very
    #     extraction that also yields the real 219, and not through a second one.
    import tempfile
    kopie = SYNTAX.read_text().replace("```ebnf\n", '```ebnf\nzzprobe = "zztafelprobe" ;\n', 1)
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as f:
        f.write(kopie)
        name = f.name
    try:
        erfunden = terminale(name)
        t2 = tafel(erfunden, gesenkt, absage, pruefer)
        proben.append(("erfundene Grammatikregel `zztafelprobe` faellt als UNGEDECKT",
                       t2.get("zztafelprobe") == "UNGEDECKT"))
        proben.append(("und sie steht nicht schon in der echten Grammatik",
                       "zztafelprobe" not in term))
    finally:
        pathlib.Path(name).unlink()
    return proben


def main():
    nur_probe = "--probe" in sys.argv
    volle_tafel = "--tafel" in sys.argv

    # **TOOTH 0 -- THE SUBJECT HAS TO BE THERE** (2026-08-31). Over a tree without
    # `dokumente/` this tool died INSIDE THE MODULE IT LOADS: `pruefe-wortschatz.py` read
    # `SYNTAX.md` at import time and the `FileNotFoundError` came back through
    # `exec_module` -- return code **1**, a traceback, and in a chain that reads like one
    # more uncovered cell. *A crash is not a refusal -- a NAMED refusal is*, and a missing
    # subject says the SETUP has to change, not the tree.
    gegenstand = [SYNTAX, KW]
    fehlend = [str(d.relative_to(W)) for d in gegenstand if not d.is_file()]
    if not CHECK.is_dir():
        fehlend.append(str(CHECK.relative_to(W)))
    if fehlend:
        print("ABBRUCH: es fehlen: %s -- es wurde NICHTS gemessen." % ", ".join(fehlend),
              file=sys.stderr)
        print("  Ohne Grammatik, Schluesselwoerter und Paesse hat die Tafel keine Achse;\n"
              "  `0 ungedeckt` waere ein Urteil ueber nichts (W1, W17).", file=sys.stderr)
        return 2

    term = terminale()
    absage, za = absageworte()
    pruefer, n_fehler = prueferworte()

    # **The deadline sits with whoever executes, and is NAMED here instead of duplicated.**
    # `zaehle-absagen.korpuslauf` aborts per file after `za.FRIST` seconds -- and there an
    # expiry is an abort, not an empty result. *A second deadline beside it would be a
    # second register over the same thing* (W7).
    print(f"   (Frist je Datei: {za.FRIST} s, aus `zaehle-absagen.py` -- ein Ablauf bricht ab)",
          file=sys.stderr)
    korpus = za.korpuslauf()
    if korpus is None:
        print("== GRAMMATIKTAFEL: KEIN LAUF -- es wurde NICHTS gemessen ==")
        print("   Ohne `gabbro emit` ueber dem Korpus gibt es den Zustand `gesenkt` nicht,")
        print("   und ohne ihn ist jede Zelle UNGEDECKT. Das waere kein Befund, sondern")
        print("   ein fehlendes Werkzeug (W1).")
        # **2, not 1 -- and that single digit cost an hour on 2026-08-31.**
        # The refusal above says NOTHING was measured, and the return code said the opposite:
        # `1` is the colour of the four UNGEDECKT cells this tool reports on a good day. In
        # the collective run the two were indistinguishable, so a lost guardian read as a
        # known backlog. *A tool that measured nothing must not look like one that found
        # something.*
        return 2
    gesenkt, sauber = gesenkte_worte(korpus)

    print("== Sprechprobe -- in beide Richtungen ==")
    proben = sprechprobe(term, gesenkt, absage, pruefer)
    for was, ok in proben:
        print(f"  {'ok         ' if ok else 'GESCHEITERT'}  {was}")
    if not all(ok for _, ok in proben):
        print("\n! Die Tafel misst nicht, was sie behauptet. ABBRUCH.")
        return 2
    if nur_probe:
        return 0

    z = tafel(term, gesenkt, absage, pruefer)
    zahl = collections.Counter(z.values())
    ctx = kontextuell() & set(term)

    print()
    print(f"== {len(term)} EBNF-Terminale aus {SYNTAX.name}, "
          f"gegen {len(sauber)} vollstaendig emittierende Dateien ==")
    print(f"   {len(za.formen())} Absagestellen im Erzeuger · {n_fehler} Prueferfehlertexte")
    print()
    for name in ("gesenkt", "abgesagt", "vom Pruefer", "UNGEDECKT"):
        print(f"   {name:<12} {zahl.get(name, 0):>4}")

    if volle_tafel:
        print()
        for t in sorted(z):
            marke = " (ctx)" if t in ctx else ""
            print(f"   {z[t]:<12} {t}{marke}")

    offen = sorted(t for t, s in z.items() if s == "UNGEDECKT")
    print()
    if ctx:
        print(f"== {len(ctx)} KONTEXTUELLE Woerter -- ein Vorkommen kann ein Bezeichner sein ==")
        print("   " + ", ".join(sorted(ctx)))
        print("   `kw.rs` fuehrt sie als `ctx`. Fuer sie ist `gesenkt` eine OBERE Schranke;")
        print("   die anderen 213 sind reserviert, und dort ist ein Vorkommen ein Wort.")
        print()

    print("== Und was diese Tafel NICHT sagt ==")
    print("   Eine besetzte Zelle heisst, dass es eine Absenkung GIBT -- nicht, dass sie")
    print("   richtig ist. `F06` emittierte 161 Zeilen, die `cc -Werror` zurueckwies, und")
    print("   diese Tafel haette sein Wort als `gesenkt` gefuehrt. Die Gegenprobe dafuer")
    print("   ist Stufe 9 von `pruefe-emission.sh`.")

    if offen:
        print()
        print(f"! GRAMMATIKTAFEL ROT: {len(offen)} von {len(term)} Terminalen sind UNGEDECKT.")
        print("  Die Grammatik erlaubt sie, kein Programm senkt sie ab, und keine Regel")
        print("  weist sie ab. **Das ist die Arbeitsmenge, und sie steht hier statt in")
        print("  einer Zahl:**")
        for t in offen:
            woher = []
            if t in absage:
                woher.append("der Erzeuger sagt ab, der Pruefer nicht")
            if t in ctx:
                woher.append("kontextuell")
            print(f"    {t:<16} {'; '.join(woher) if woher else 'niemand nennt es'}")
        return 1

    print()
    print(f"== GRAMMATIKTAFEL GRUEN: 0 von {len(term)} Terminalen UNGEDECKT ==")
    return 0


if __name__ == "__main__":
    sys.exit(main())
