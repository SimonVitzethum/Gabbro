#!/usr/bin/env python3
"""**Die Sprachflaeche von Gabbro ist englisch -- und ohne Waechter driftet sie zurueck.**

Entschieden am 2026-08-19 (`SYNTAX.md`, *„The surface of Gabbro is English"*). Die
Schluesselwoerter waren es von Anfang an; **alles andere, was ein Nutzer von Gabbro LIEST, war
nie entschieden** -- und es war gewandert.

Gemessen am Tag der Entscheidung: **41 von 100 Absagetexten waren deutsch**, und die Mischung
lief durch einzelne Saetze:

    M101   "die Rueckgabe requires `u32 in 0 .. 100`, the value has `u32`"

DIE LINIE
---------
    englisch    Schluesselwoerter · Absagetexte und ihre Notizen · die Berichte von
                `gabbro paesse`, `schablonen`, `pflichten`, `zeugnis`
    deutsch     die Arbeitsdokumente dieses Ordners, Quellkommentare, und jeder
                Bezeichner, den ein NUTZER waehlt

**Was Gabbro sagt, ist englisch; was der Ordner ueber Gabbro sagt, nicht.** *Ein Bezeichner ist
das Wort des Nutzers, nicht das der Sprache* -- `beispiele/01` darf einen Platz weiter
`Kappenraum` nennen.

DAS MASS
--------
Gemessen werden die Zeichenketten in `Absage::fehler(…)`, `Absage::hinweis(…)` und
`.mit_notiz(…)` -- die Flaeche, die als Meldung beim Nutzer ankommt. Ein Text gilt als deutsch,
wenn er ein Wort aus einer geschlossenen Funktionswortliste enthaelt. **Funktionswoerter, nicht
Fachwoerter:** `Bereich` koennte ein Bezeichner sein, `nicht` nicht.

> **Die Vergroeberung geht in die sichere Richtung.** Was der Waechter nennt, ist echt; was er
> nicht nennt, kann trotzdem deutsch sein (W10). *Er darf verpflichten und nicht freisprechen.*

    ./pruefe-englisch.py
"""
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent
QUELLEN = sorted((W / "crates" / "gabbro-check" / "src").glob("*.rs")) + [
    W / "crates" / "gabbro-cli" / "src" / "main.rs",
]

# **Geschlossene Liste deutscher FUNKTIONSWOERTER.** Keine Fachwoerter -- `Bereich`, `Schranke`
# und `Traeger` koennten Bezeichner eines Nutzers sein und stehen darum nicht drin.
DEUTSCH = {
    # **`die` und `war` stehen NICHT in dieser Liste**, obwohl sie deutsche Funktionswoerter
    # sind: beide sind auch englische Woerter (*to die*, *a war*). Eine Erkennungsliste, die
    # auf englischem Text laeuft, darf keine englischen Woerter enthalten -- gefunden beim
    # ersten Lauf an einer vollstaendig englischen Meldung. *Der Preis ist eine Luecke, und
    # sie geht in die sichere Richtung: der Waechter verpflichtet, er spricht nicht frei.*
    "ist", "sind", "waere", "wird", "werden", "wurde", "muss", "muessen", "darf",
    "kann", "koennen", "hat", "haben", "gibt", "steht", "stehen", "liegt", "faellt",
    "nennt", "traegt", "sagt", "macht", "geht", "bleibt", "heisst", "gilt",
    "nicht", "kein", "keine", "keinen", "keiner", "keins", "und", "oder", "aber", "sondern",
    "eine", "einen", "einem", "einer", "eines", "der", "das", "den", "dem", "des",
    "dieser", "diese", "dieses", "diesem", "jeder", "jede", "jedes", "seiner", "seine",
    "ihre", "ihrer", "ohne", "mit", "von", "vom", "zum", "zur", "beim", "durch", "fuer",
    "auf", "aus", "bei", "nach", "ueber", "unter", "vor", "hier", "dort", "damit", "weil",
    "wenn", "dann", "schon", "noch", "nur", "auch", "sonst", "immer", "nie",
}
WORT = re.compile(r"[A-Za-zÄÖÜäöüß_]+")
# **Die Flaechen, auf denen ein Text beim Nutzer ankommt -- alle, seit 2026-08-19.**
#
# Der erste Lauf sah nur die ABSAGEN und meldete `ALL PASS`, waehrend `gabbro paesse` und
# `gabbro zeugnis` deutsch ausgaben. *Eine Regel, die nur die Haelfte ihrer Flaeche misst, ist
# eine halbe Regel* -- der Satz stand im TODO, bevor er hier eingeloest wurde.
STELLEN = re.compile(
    r"(?:"
    r"Absage::(?:fehler|hinweis)\([^,]+,[^,]+,\s*(?:format!\()?"   # die Meldung
    r"|\.mit_notiz\(\s*(?:format!\()?"                            # ihre Notiz
    r"|push_str\(&?(?:format!\()?"                                 # die Berichte
    r"|(?:e?println!)\(\s*"                                        # die CLI
    r"|Zustand::(?:Teilgebaut|Offen)\(\s*"                         # die Passliste
    r")"
    r'\s*"((?:[^"\\]|\\.)*)"',
    re.S,
)


# **Ein Formatplatzhalter ist keine Prosa.** `{von:#x}` und `{ist}` nennen RUST-Variablen,
# und die stehen unter Quelltext -- die Linie laeuft zwischen dem, was Gabbro SAGT, und dem,
# was der Ordner schreibt. *Gefunden beim ersten Lauf: zwei Meldungen, die vollstaendig
# englisch waren und an ihren eigenen Platzhaltern haengenblieben.*
PLATZHALTER = re.compile(r"\{[^{}]*\}")


def deutsch(text):
    """Die deutschen Funktionswoerter in diesem Text -- Platzhalter zaehlen nicht."""
    zusammen = PLATZHALTER.sub(" ", text.replace("\\\n", " "))
    return sorted({w.lower() for w in WORT.findall(zusammen) if w.lower() in DEUTSCH})


def messe(quellen):
    gefunden, gesamt = [], 0
    for f in quellen:
        t = f.read_text(encoding="utf-8")
        for m in STELLEN.finditer(t):
            gesamt += 1
            woerter = deutsch(m.group(1))
            if woerter:
                zeile = t[: m.start()].count("\n") + 1
                gefunden.append((f.name, zeile, woerter, m.group(1)[:58]))
    return gesamt, gefunden


def sprechprobe():
    """R14, in beide Richtungen: ein deutscher Text musz fallen, ein englischer nicht."""
    gift = deutsch("die Rueckgabe requires `u32`, der Wert ist zu gross")
    sauber = deutsch("the return requires `u32`, the value is too large")
    print("== Sprechprobe (R14) ==")
    print("  deutscher Text faellt:   %s" % ("ja" if gift else "NEIN"))
    print("  englischer bleibt frei:  %s" % ("ja" if not sauber else "NEIN -- %s" % sauber))
    return bool(gift) and not sauber


def main():
    if not sprechprobe():
        print("== ENGLISCH: der Waechter misst nicht ==")
        return 2
    gesamt, gefunden = messe(QUELLEN)
    print("\n== Sprachflaeche: %d Meldungstexte in %d Dateien ==" % (gesamt, len(QUELLEN)))
    if not gefunden:
        print("== ENGLISCH: ALL PASS -- kein deutsches Funktionswort in einer Meldung ==")
        print("   Und was das NICHT heisst: gemessen wird gegen eine GESCHLOSSENE Liste von")
        print("   %d Funktionswoertern. Was der Waechter nicht nennt, kann trotzdem" % len(DEUTSCH))
        print("   deutsch sein -- er verpflichtet, er spricht nicht frei (W10).")
        return 0
    for datei, zeile, woerter, text in gefunden:
        print("  %s:%d  [%s]  %s" % (datei, zeile, ", ".join(woerter[:4]), text))
    print("\n== ENGLISCH: %d von %d Meldungen sind deutsch ==" % (len(gefunden), gesamt))
    print("   Die Sprachflaeche von Gabbro ist englisch (SYNTAX.md, 2026-08-19).")
    print("   Quellkommentare und die Arbeitsdokumente sind es NICHT -- die Linie laeuft")
    print("   zwischen dem, was Gabbro sagt, und dem, was der Ordner ueber Gabbro sagt.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
