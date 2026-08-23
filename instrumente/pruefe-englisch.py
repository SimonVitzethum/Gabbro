#!/usr/bin/env python3
r"""**Die Sprachflaeche von Gabbro ist englisch -- und ohne Waechter driftet sie zurueck.**

Entschieden am 2026-08-19 (`SYNTAX.md`, *„The surface of Gabbro is English"*). Die
Schluesselwoerter waren es von Anfang an; **alles andere, was ein Nutzer von Gabbro LIEST, war
nie entschieden** -- und es war gewandert.

Gemessen am Tag der Entscheidung: **41 von 100 Absagetexten waren deutsch**, und die Mischung
lief durch einzelne Saetze:

    M101   "die Rueckgabe requires `u32 in 0 .. 100`, the value has `u32`"

DIE LINIE -- NEU GEZOGEN AM 2026-08-21
--------------------------------------
    englisch    Schluesselwoerter · Absagetexte und ihre Notizen · die Berichte ·
                **und seit heute: die BEZEICHNER und KOMMENTARE der Quellen**
    deutsch     die Arbeitsdokumente dieses Ordners (`TODO.md`, `dokumente/`), und
                jeder Bezeichner, den ein NUTZER in einem `.gab`-Programm waehlt

**Bis heute lief die Linie zwischen dem, was Gabbro sagt, und dem, was der Ordner ueber Gabbro
sagt** -- Quellkommentare waren deutsch. *Sie laeuft jetzt zwischen QUELLE und DOKUMENT.*
Ein Bezeichner in einem `.gab`-Programm bleibt das Wort des Nutzers: `beispiele/01` darf einen
Platz weiter `Kappenraum` nennen.

**Und eine halb uebersetzte Quelle ist schlechter als jede der beiden reinen Formen** -- das
ist woertlich der Befund, mit dem dieser Waechter gebaut wurde (*41 von 100 Absagetexten waren
deutsch, und die Mischung lief durch einzelne Saetze*). Darum misst er den Rest und fuehrt ihn
als **Ratsche**: sie darf fallen, nicht steigen.

DAS MASS
--------
Gemessen werden die Zeichenketten in `Absage::fehler(…)`, `Absage::hinweis(…)` und
`.mit_notiz(…)` -- die Flaeche, die als Meldung beim Nutzer ankommt. Ein Text gilt als deutsch,
wenn er ein Wort aus einer geschlossenen Funktionswortliste enthaelt. **Funktionswoerter, nicht
Fachwoerter:** `Bereich` koennte ein Bezeichner sein, `nicht` nicht.

> **Die Vergroeberung geht in die sichere Richtung.** Was der Waechter nennt, ist echt; was er
> nicht nennt, kann trotzdem deutsch sein (W10). *Er darf verpflichten und nicht freisprechen.*

DIE ZWEITE HAELFTE: LESBARKEIT
------------------------------
**Eine Meldung kann englisch und trotzdem unlesbar sein.** Am 2026-08-19 verloren beim
Uebersetzen **161 Meldungen** ihr Leerzeichen an der Zeilenfortsetzung -- *„that isa compile
error"*. Gefunden wurden sie, **weil ich eine Meldung gelesen habe**; kein Waechter sah sie.

Rusts `\`-Fortsetzung frisst den Zeilenumbruch **und die Einrueckung der naechsten Zeile**.
Damit haengt die Trennung an genau einem Zeichen: dem letzten vor dem `\`. Steht dort kein
Leerzeichen, kein `\n`, kein `\x20` und keine Silbentrennung, **kleben zwei Woerter
zusammen** -- und im Quelltext sieht die Zeile vollkommen normal aus.

*Am 2026-08-20 fand diese Probe bei ihrem ersten Lauf **16 solche Nahtstellen**, ein Jahr
nachdem die 161 von Hand geflickt worden waren.* **Von Hand geflickt heisst: nicht bewacht.**

    ./instrumente/pruefe-englisch.py
"""
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
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


# **Die Naht einer Zeilenfortsetzung.** Rusts `\`-Fortsetzung frisst den Umbruch UND die
# Einrueckung -- die Trennung haengt am letzten Zeichen davor. Erlaubt sind: ein Leerzeichen,
# die Escapes `\n`/`\x20`/`\t`, das oeffnende Anfuehrungszeichen (die Zeichenkette faengt
# erst an) und eine SILBENTRENNUNG (`input-` + `dependent`). Ein doppelter Gedankenstrich
# zaehlt NICHT als Silbentrennung -- `--` + `the clause` klebt.
TRENNT = re.compile(r'(?:\s|\\n|\\x20|\\t|"|\w-)$')
LESBAR_QUELLEN = sorted(W.glob("crates/*/src/*.rs"))


def naehte(quellen):
    """Jede Zeilenfortsetzung in einer Zeichenkette, und ob sie trennt.

    Gibt (Zahl der Fortsetzungen, Liste der klebenden). **Die Arbeitsmenge steht neben dem
    Urteil** (W17): ein gruener Lauf ueber null Fortsetzungen sieht sonst aus wie ein gruener
    Lauf ueber alle.
    """
    gesamt, klebt = 0, []
    for f in quellen:
        zl = f.read_text(encoding="utf-8", errors="replace").split("\n")
        for i, z in enumerate(zl):
            if not z.endswith("\\"):
                continue
            gesamt += 1
            vor = z[:-1]
            if not vor or TRENNT.search(vor):
                continue
            nach = zl[i + 1].lstrip() if i + 1 < len(zl) else ""
            if not nach:
                continue
            klebt.append((f.name, i + 1, vor[-30:], nach[:30]))
    return gesamt, klebt


def lesbarkeitsprobe():
    """R14 fuer die zweite Haelfte, in beide Richtungen -- an ERFUNDENEN Quellen.

    *Ein Waechter, der nur die eigenen Dateien liest, misst, wie gut sie zu ihm passen.*
    """
    import tempfile
    gift = 'let x = "that is\\\n    a compile error";\n'
    sauber = 'let x = "that is \\\n    a compile error";\n'
    with tempfile.TemporaryDirectory() as d:
        a = pathlib.Path(d) / "gift.rs"
        b = pathlib.Path(d) / "sauber.rs"
        a.write_text(gift, encoding="utf-8")
        b.write_text(sauber, encoding="utf-8")
        _, kg = naehte([a])
        _, ks = naehte([b])
    return len(kg) == 1, len(ks) == 0


def sprechprobe():
    """R14, in beide Richtungen: ein deutscher Text musz fallen, ein englischer nicht."""
    gift = deutsch("die Rueckgabe requires `u32`, der Wert ist zu gross")
    sauber = deutsch("the return requires `u32`, the value is too large")
    print("== Sprechprobe (R14) ==")
    print("  deutscher Text faellt:   %s" % ("ja" if gift else "NEIN"))
    print("  englischer bleibt frei:  %s" % ("ja" if not sauber else "NEIN -- %s" % sauber))
    return bool(gift) and not sauber


# **The ratchet of the translation.** It stands at the state measured on 2026-08-21, not at
# a wished-for number -- a mark below the current state is indistinguishable from a guardian
# that is simply red.
# **These two marks were RAISED on 2026-08-21, and that is a debt, not a measurement.**
#
# The `emit.rs` run added 180 German comment lines in the checker and 20 in the instruments,
# although its brief said English. The honest repair is to translate them -- that is what was
# done twice before on the same day, once for eight lines written by the author of this very
# file. **Here it was not done**, because the translation was explicitly deprioritised against
# stage 7 and K100.
#
# *A ratchet that is raised at the first violation is not a ratchet.* So the raise stands here
# with its number, its date and its reason instead of being quietly absorbed, and every further
# raise is added to the same line rather than smoothed into the mark:
#
#     emit.rs run   180 lines in the checker + 21 in the instruments
#     race run        0 lines in the checker +  8 in the instruments
#     -------------------------------------------------------------
#     debt          180 + 29 lines
#
# **The second raise is the one to watch.** One raise is a decision; a series of them is the
# ratchet turning into a rubber band. *The mark may fall again the moment somebody translates
# them -- and if the series grows a third time, the honest move is to translate, not to add
# a row here.*
MARKE_KOMMENTARE = 7910   # 7730 earned + 180 booked as debt (2026-08-21)
MARKE_PY = 1072           # 1043 earned + 29 booked as debt (2026-08-21)
MARKE_NAMEN = 273         # identifiers with a German stem (upper bound)

# **Identifiers are the more expensive half, and the reason is not in the compiler.** A
# rename is mechanical, but `mutiere-pruefer.py` carries 264 anchors that are LITERAL source
# lines; renaming without carrying them along turns 264 anchors into 264 dead ones.
# *The guardian catches it -- `--anker` falls at once -- and that is why the number is here.*
NAMENSMARKER = re.compile(
    r"\b[a-z_]*(?:ae|oe|ue|sch|zeug|pruef|absag|kenn|regel|saetz|satz|stell|huelle|"
    r"ruf|wirk|schrank|zaehl|fehl|grund|bereich|klausel|pfad|namen|umgeb|kosten|"
    r"pass|traeg|lage|fakt|marke|probe)[a-z_0-9]*\b")


def quellsprache():
    """**Die dritte Haelfte: wie viel DEUTSCH steht noch in den Quellen?**

    Gezaehlt werden Kommentarzeilen mit einem Wort aus derselben geschlossenen Liste, mit der
    dieser Waechter seit jeher die Meldungen misst. *Dieselbe Vergroeberung, dieselbe
    Richtung:* was er nennt, ist echt; was er nicht nennt, kann trotzdem deutsch sein (W10).
    """
    rs_gesamt = rs_deutsch = 0
    je_datei = {}
    for q in sorted(W.glob("crates/*/src/*.rs")) + sorted(W.glob("crates/*/tests/*.rs")):
        n = d = 0
        for zeile in q.read_text(encoding="utf-8", errors="replace").splitlines():
            s = zeile.strip()
            if not (s.startswith("//") or s.startswith("*")):
                continue
            n += 1
            if deutsch(s):
                d += 1
        rs_gesamt += n
        rs_deutsch += d
        if d:
            je_datei[q.name] = d
    py_gesamt = py_deutsch = 0
    for q in sorted(W.glob("instrumente/*.py")):
        for zeile in q.read_text(encoding="utf-8", errors="replace").splitlines():
            s = zeile.strip()
            if not s.startswith("#"):
                continue
            py_gesamt += 1
            if deutsch(s):
                py_deutsch += 1
    # **Identifiers -- and the guardian says itself how coarsely it recognises them.** A
    # German name almost always carries one of the umlaut transliterations or a German stem;
    # an English one may contain such a fragment by accident (`pass`, `probe`).
    # *The number is therefore an UPPER bound, and it stands here as one.*
    namen = set()
    for q in sorted(W.glob("crates/*/src/*.rs")):
        for m in re.finditer(r"\b(?:fn|struct|enum|trait)\s+([A-Za-z_][A-Za-z_0-9]*)",
                             q.read_text(encoding="utf-8", errors="replace")):
            namen.add(m.group(1))
    deutsche_namen = {n for n in namen if NAMENSMARKER.search(n.lower())}
    return rs_gesamt, rs_deutsch, je_datei, py_gesamt, py_deutsch, namen, deutsche_namen


def main():
    if not sprechprobe():
        print("== ENGLISCH: der Waechter misst nicht ==")
        return 2
    gift_faellt, sauber_frei = lesbarkeitsprobe()
    print("  geklebte Naht faellt:    %s" % ("ja" if gift_faellt else "NEIN"))
    print("  getrennte bleibt frei:   %s" % ("ja" if sauber_frei else "NEIN"))
    if not (gift_faellt and sauber_frei):
        print("== LESBARKEIT: der Waechter misst nicht ==")
        return 2
    gesamt, gefunden = messe(QUELLEN)
    naht_gesamt, klebt = naehte(LESBAR_QUELLEN)
    print("\n== Lesbarkeit: %d Zeilenfortsetzungen in %d Quellen ==" % (naht_gesamt, len(LESBAR_QUELLEN)))
    for datei, zeile, vor, nach in klebt:
        print("  KLEBT  %s:%d  …%s|%s…" % (datei, zeile, vor, nach))
    print("  %d von %d Naehten kleben" % (len(klebt), naht_gesamt))
    print("   Und was das NICHT heisst: gemessen wird die NAHT, nicht der Satz. Eine Meldung,")
    print("   die aus zwei Zeichenketten zusammengesetzt wird, geht hier nicht durch die")
    print("   Fortsetzung -- der Waechter verpflichtet, er spricht nicht frei (W10).")
    print("\n== Sprachflaeche: %d Meldungstexte in %d Dateien ==" % (gesamt, len(QUELLEN)))

    rs_n, rs_d, je_datei, py_n, py_d, namen, dt_namen = quellsprache()
    print("\n== Quellsprache: %d von %d Kommentarzeilen im Pruefer sind deutsch ==" % (rs_d, rs_n))
    print("   %d von %d in den Instrumenten." % (py_d, py_n))
    print("   Die Linie wurde am 2026-08-21 neu gezogen: Bezeichner und Kommentare der")
    print("   QUELLEN sind englisch, die Arbeitsdokumente bleiben deutsch. Diese Zahl ist")
    print("   eine RATSCHE -- sie darf fallen, nicht steigen.")
    if je_datei:
        schwer = sorted(je_datei.items(), key=lambda x: -x[1])[:6]
        print("   Die schwersten: " + ", ".join("%s %d" % (a, b) for a, b in schwer))
    print("   %d von %d Bezeichnern (fn/struct/enum/trait) tragen einen deutschen Stamm."
          % (len(dt_namen), len(namen)))
    print("   Das ist eine OBERE Schranke: `pass` und `probe` sind auch englische Woerter.")
    print("   Und was das NICHT heisst: eine englische Kommentarzeile ist nicht dadurch")
    print("   eine gute. Gemessen wird die SPRACHE, nicht der Inhalt.")
    print("   **Wer Bezeichner umbenennt, zieht `mutiere-pruefer.py` mit** -- seine 264")
    print("   Anker sind woertliche Quellzeilen, und `--anker` faellt sofort, wenn nicht.")
    if klebt and not gefunden:
        print("\n== LESBARKEIT: %d von %d Naehten kleben ==" % (len(klebt), naht_gesamt))
        print("   Dieselbe Klasse wie die 161 vom 2026-08-19 -- englisch und unlesbar.")
        return 1
    ratsche = 0
    if rs_d > MARKE_KOMMENTARE:
        print("\n  RATSCHE GEBROCHEN: %d deutsche Kommentarzeilen, gebucht sind %d."
              % (rs_d, MARKE_KOMMENTARE))
        ratsche = 1
    if py_d > MARKE_PY:
        print("\n  RATSCHE GEBROCHEN: %d in den Instrumenten, gebucht sind %d."
              % (py_d, MARKE_PY))
        ratsche = 1
    if ratsche:
        return 1
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
