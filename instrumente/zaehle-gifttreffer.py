#!/usr/bin/env python3
"""**Jede Giftprobe gegen ihre eigene Zusage -- faellt der erwartete Code ALLEIN?**

`crates/gabbro-check/tests/beispiele.rs` fragt `gefallen.contains(&erwartet)`. Das ist
**nicht** `==` und **nicht** `[0]`: eine Probe ist gruen, sobald ihr Code irgendwo in der
Liste steht -- an erster Stelle, an vierzehnter, oder als einer von sechzehn.

> **Eine Probe, deren erwarteter Code erst an dritter Stelle faellt, misst zwei andere Regeln
> mit -- und wenn eine davon ausfiele, bliebe sie gruen.**

Gemessen am 2026-08-31 (`messung/GIFT-GEGEN-ZUSAGE.md`): von 317 Proben fiel in **87** mehr
als ein Code, und in **38** fiel vor dem erwarteten ein anderer. **Sechsundzwanzig davon
gingen auf vier Regeln zurueck, die es beim Schreiben der Probe noch nicht gab** -- `N040`
(ein Typname, den die Probe nie deklariert), `D011` (`ops` ohne `occupied`), `N025`, `N028`.
*Ein Platzhalter, der beim Schreiben nichts kostete, war ueber Nacht ein zweiter Gegenstand.*

Genau diese Drift bewacht dieses Werkzeug. Sie faellt nicht auf, solange nur `contains`
gefragt wird.

DIE VIER KLASSEN, MECHANISCH ENTSCHIEDEN
-----------------------------------------
    sauber      ausser dem erwarteten faellt NICHTS
    begleitet   der erwartete ist der erste SEINER STUFE; was sonst faellt, kommt danach
    verdeckt    vor dem erwarteten faellt ein Code DERSELBEN STUFE
    FEHLT       der erwartete faellt gar nicht -- dann ist auch `cargo test` rot

**Die Stufe trennt zwei Toepfe, und der Testrahmen tut das auch.** Ein `Hinweis E009` vor
einem `Fehler K008` verdeckt nichts: die Zusicherung filtert erst nach Stufe und sucht dann.

DIE MARKEN
----------
    MARKE_SAUBER    Boden -- faellt sie, hat eine Probe einen zweiten Gegenstand bekommen
    MARKE_VERDECKT  DECKE -- steigt sie, verdeckt eine neue Regel eine alte Probe

*Die Richtung ist der Ertrag.* Eine verdeckte Probe mehr ist kein Wachstum, sondern eine
Probe, die etwas anderes misst als das, was ueber ihr steht. **Steigt die Decke, gehoert der
Grund an die Marke** -- und in `messung/GIFT-GEGEN-ZUSAGE.md` §10 steht, welche sieben aus
einem SPRACHGRUND nicht trennbar sind (`F001`/`M101`, `N021`/`N027`, `L102`/`E008`,
`U003`/`H007`, `O006`/`L108`, `O009`/`O010`).

    ./instrumente/zaehle-gifttreffer.py            die Tafel
    ./instrumente/zaehle-gifttreffer.py --lang     dazu jede nicht-saubere Probe einzeln
    ./instrumente/zaehle-gifttreffer.py --json     maschinenlesbar
"""
import importlib
import json
import os
import pathlib
import re
import subprocess
import sys

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.py`.
# `sys.path` gets the tool's own directory because this file is also LOADED by
# `abnahme.py` (via `importlib`), and then `sys.path[0]` is the working directory.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

W = pathlib.Path(__file__).resolve().parent.parent
GIFT = W / "beispiele" / "gift"

# **One deadline per file, and an expiry is an ABORT and not an empty result** (W17).
FRIST = 120

# The diagnostic header, exactly as `Absagen::zeige` prints it. The order of the list is the
# order the PASSES filed them -- `zeige` does not sort by position -- and that is the same
# order the test harness sees.
KOPF = re.compile(r"^(error|hint): \[([A-Z][0-9]{3})\] (.+?):(\d+):(\d+): (.*)$")
ZUSAGE = "-- erwartet: "

# **THE MARKS, measured 2026-08-31 after the repair** (`messung/GIFT-GEGEN-ZUSAGE.md` §9).
# 255 clean, 54 accompanied, 7 covered, 1 `-- erwartet: cc`.
#
# **258 -> 262 and 320 -> 324 on 2026-08-31**, and it is a growing SUBJECT and not a raised
# bar: four probes came in for the silent `N042` collisions (`417`-`420`,
# `messung/STILLE-KOLLISIONEN.md`), and each of the four falls with its code and nothing
# else. *A floor that lags behind the corpus is slack, not safety* -- it would take four
# probes losing their subject without a word.
MARKE_SAUBER = 262
MARKE_VERDECKT = 7
# The population is a floor of its own: a corpus that SHRINKS says the checker lost a probe,
# and neither of the two marks above would notice.
MARKE_PROBEN = 324


def binaer():
    """Das Binaerprogramm -- geliehen von `zaehle-absagen.py`, damit es EIN Register bleibt.

    Dort steht der Riegel gegen ein Binaerprogramm, das aelter ist als die Quellen (W16:
    *ein veraltetes Binaerprogramm antwortet fuer einen Pruefer, den niemand gebaut hat*).
    Ihn hier ein zweites Mal zu schreiben waere ein zweites Register ueber einer Sache --
    und die Kopie ist die, die den Riegel als erste vergisst.
    """
    sys.path.insert(0, str(W / "instrumente"))
    return importlib.import_module("zaehle-absagen").binaer()


def zusage(quelle):
    """Die erste Zeile als (Stufe, Code) -- oder `None`, wenn keine dasteht."""
    erste = quelle.splitlines()[0] if quelle else ""
    if not erste.startswith(ZUSAGE):
        return None
    e = erste[len(ZUSAGE):].strip()
    if e == "cc":
        return ("cc", "cc")
    if e.startswith("Hinweis "):
        return ("hint", e[len("Hinweis "):].strip())
    # **`CODE allein` is a normal error contract with a SECOND half** (2026-08-31). The
    # second half -- `cc` must ACCEPT the emitted unit -- lives in `tests/beispiele.rs`,
    # because it needs a `cc` run and this counter never starts one. Here the suffix is
    # simply not part of the code. *Until today it was, and four probes counted as `FEHLT`
    # while every one of them was falling exactly as written.*
    if e.endswith(" allein"):
        return ("error", e[: -len(" allein")].strip())
    return ("error", e)


def einordnen(stufe, code, treffer):
    """Die Klasse einer Probe aus ihrer Zusage und den gefallenen Codes.

    Getrennt von jedem Dateizugriff, damit die Sprechprobe unten sie an ERFUNDENEN Listen
    fahren kann -- eine Probe am echten Korpus wandert mit ihrem Gegenstand.
    """
    topf = [t for t in treffer if t["stufe"] == stufe]
    stellen = [i for i, t in enumerate(topf) if t["code"] == code]
    if not stellen:
        return "FEHLT"
    if len(treffer) == 1:
        return "sauber"
    if topf[: stellen[0]]:
        return "verdeckt"
    if all(t["code"] == code and t["stufe"] == stufe for t in treffer):
        # The same code several times and nothing else -- one subject, several sites.
        return "sauber"
    return "begleitet"


def lauf(befehl, pfad, quelle, erwartet):
    """Ein Prozess je Datei -- `gabbro pruefe`, und `emit` fuer die `C001`-Proben.

    Ein eigener Prozess, weil `gabbro pruefe` sein Bindungsregister ueber eine Dateiliste
    hinweg teilt; der Testrahmen liest jede Datei fuer sich. Und der Erzeuger laeuft nur
    dort, wo die Datei ihn meint -- genau wie in `beispiele.rs::absagen_von`.
    """
    unterbefehl = "emit" if erwartet == "C001" else "pruefe"
    # **The locale is pinned because the OUTPUT is parsed, not just read** (requirement five).
    # `gabbro` speaks English today, but every tool this measurement leans on -- and every
    # library underneath it -- may report translated, and `KOPF` matches `error`/`hint`
    # literally. *A parser that measures in its own locale looks plausible doing it.*
    umgebung = dict(os.environ, LC_ALL="C")
    r = subprocess.run(befehl + [unterbefehl, str(pfad)],
                       capture_output=True, text=True, timeout=FRIST, cwd=W, env=umgebung)
    treffer = []
    for zeile in (r.stdout + r.stderr).splitlines():
        m = KOPF.match(zeile)
        if m:
            treffer.append({"stufe": m.group(1), "code": m.group(2),
                            "zeile": int(m.group(4)), "text": m.group(6)})
    return treffer


def sprechprobe():
    """**Die Einordnung an erfundenen Listen -- in beide Richtungen.**

    Was verdeckt sein soll, ist verdeckt; was es nicht ist, ist es nicht. Die dritte und die
    vierte Probe sind die, an denen die erste Fassung dieses Werkzeugs falsch lag: sie zaehlte
    einen HINWEIS vor einem Fehler als Verdeckung, obwohl der Testrahmen die Stufen trennt.
    """
    def t(stufe, code):
        return {"stufe": stufe, "code": code, "zeile": 1, "text": ""}

    return [
        ("allein ist sauber",
         einordnen("error", "M104", [t("error", "M104")]) == "sauber"),
        ("ein Code DANACH ist begleitet",
         einordnen("error", "M104", [t("error", "M104"), t("error", "M101")]) == "begleitet"),
        ("ein Code DAVOR ist verdeckt",
         einordnen("error", "M104", [t("error", "N040"), t("error", "M104")]) == "verdeckt"),
        ("ein HINWEIS davor verdeckt NICHT",
         einordnen("error", "K008", [t("hint", "E009"), t("error", "K008")]) == "begleitet"),
        ("derselbe Code zweimal ist sauber",
         einordnen("error", "N016", [t("error", "N016"), t("error", "N016")]) == "sauber"),
        ("was gar nicht faellt, FEHLT",
         einordnen("error", "M104", [t("error", "M101")]) == "FEHLT"),
        ("eine Zusage wird gelesen", zusage("-- erwartet: Hinweis S007\n") == ("hint", "S007")),
        # **The `allein` half belongs to `tests/beispiele.rs`, and this line says so.** A
        # counter that read the suffix as part of the code called four falling probes `FEHLT`.
        ("`allein` ist ein Fehlercode wie jeder andere",
         zusage("-- erwartet: N042 allein\n") == ("error", "N042")),
        ("und eine Zeile ohne Zusage ergibt nichts", zusage("module gift {\n") is None),
    ]


def main():
    lang = "--lang" in sys.argv
    als_json = "--json" in sys.argv

    # **TOOTH 0 -- THE SUBJECT HAS TO BE THERE.** A tree without the poison corpus must not
    # look like a tree whose corpus is clean. *Zero files is a refusal, not a result* (W1).
    if not GIFT.is_dir():
        print("ABBRUCH: `beispiele/gift/` ist nicht da -- NICHTS gemessen.")
        return 2
    dateien = sorted(GIFT.glob("*.gab"))
    if not dateien:
        print("ABBRUCH: `beispiele/gift/` ist LEER -- NICHTS gemessen.")
        return 2

    proben = sprechprobe()
    if not all(ok for _, ok in proben):
        for name, ok in proben:
            print(f"  {'ok' if ok else 'GESCHEITERT'}  {name}")
        print("ABBRUCH: SPRECHPROBE GESCHEITERT -- die Einordnung selbst irrt.")
        return 2

    try:
        befehl = binaer()
    except SystemExit as e:
        print(str(e))
        print("ABBRUCH: kein brauchbares Binaerprogramm -- NICHTS gemessen.")
        return 2

    klassen = {"sauber": [], "begleitet": [], "verdeckt": [], "FEHLT": [], "cc": []}
    ohne_zusage = []
    ketten = {}
    for p in dateien:
        quelle = p.read_text(encoding="utf-8", errors="replace")
        z = zusage(quelle)
        if z is None:
            ohne_zusage.append(p.name)
            continue
        stufe, code = z
        if code == "cc":
            klassen["cc"].append(p.name)
            continue
        try:
            treffer = lauf(befehl, p, quelle, code)
        except subprocess.TimeoutExpired:
            print(f"ABBRUCH: `{p.name}` hat die Frist von {FRIST} s ueberschritten "
                  "-- NICHTS gemessen.")
            return 2
        klassen[einordnen(stufe, code, treffer)].append(p.name)
        ketten[p.name] = (code, [(t["code"], t["stufe"], t["zeile"]) for t in treffer])

    if ohne_zusage:
        print("ABBRUCH: ohne `-- erwartet:` in der ersten Zeile -- "
              + ", ".join(ohne_zusage) + "\n  NICHTS ueber sie gemessen.")
        return 2

    z = {k: len(v) for k, v in klassen.items()}
    gesamt = len(dateien)
    if als_json:
        json.dump({"zahlen": z, "gesamt": gesamt, "ketten": ketten},
                  sys.stdout, indent=1, ensure_ascii=False)
        print()
        return 0

    print(f"== Giftproben gegen ihre Zusage: {gesamt} angesehen ==")
    for k in ("sauber", "begleitet", "verdeckt", "FEHLT", "cc"):
        print(f"  {z[k]:5d}  {k}")

    if lang:
        print("\n== jede nicht-saubere Probe, in Passreihenfolge ==")
        for k in ("verdeckt", "begleitet", "FEHLT"):
            for name in klassen[k]:
                code, kette = ketten[name]
                gedruckt = " · ".join(
                    (f"**{c}**@{n}" if c == code and s != "hint" else
                     f"{c}{'?' if s == 'hint' else ''}@{n}") for c, s, n in kette)
                print(f"  {k:10s} {name}  erwartet {code}: {gedruckt}")

    befunde = []
    if z["FEHLT"]:
        befunde.append("der erwartete Code faellt NICHT in: " + ", ".join(klassen["FEHLT"]))
    if gesamt < MARKE_PROBEN:
        befunde.append(f"der Korpus ist GESCHRUMPFT: {gesamt} statt {MARKE_PROBEN} "
                       "-- eine Probe ist fort, und keine Klasse sagt welche")
    if z["sauber"] < MARKE_SAUBER:
        befunde.append(f"BODEN sauber: {z['sauber']} statt {MARKE_SAUBER} "
                       "-- eine Probe hat einen zweiten Gegenstand bekommen")
    if z["verdeckt"] > MARKE_VERDECKT:
        befunde.append(f"DECKE verdeckt: {z['verdeckt']} statt {MARKE_VERDECKT} "
                       "-- eine neue Regel faellt vor einer alten Probe")

    abschnitt.fertig()
    if befunde:
        print("\n== BEFUND ==")
        for b in befunde:
            print("  " + b)
        print("  Die Marken stehen in diesem Werkzeug; der Grund gehoert daneben.")
        print("  Was aus einem SPRACHGRUND nicht trennbar ist, steht in")
        print("  `messung/GIFT-GEGEN-ZUSAGE.md` §10 -- sieben Proben, mit Grund.")
        return 1

    print(f"\n== GIFTTREFFER: ALL PASS -- {z['sauber']} von {gesamt} treffen ALLEIN ==")
    print("  Und was das NICHT heisst: dass nur EIN Code faellt, sagt nichts darueber,")
    print("  ob er aus dem Grund faellt, den der Kommentar der Probe nennt. Gemessen")
    print("  ist der Ort und die Reihenfolge, nicht das Argument.")
    return 0


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
