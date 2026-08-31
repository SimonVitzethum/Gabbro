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

# **The file list was EIGHT files short, and the parser was among them** (2026-08-31).
#
# Until today this said `gabbro-check/src/*.rs` + `gabbro-cli/src/main.rs` -- 37 of 45
# sources. Never read: `crates/gabbro-syntax/src/*.rs` (seven files) and
# `crates/gabbro-cli/src/fragmente.rs`. **Those eight held 27 German messages AT A SINK**,
# and the guardian printed `ALL PASS` beside them.
#
# > *The parser is the FIRST thing a user of Gabbro reads.* A typo in a `.gab` file never
# > reaches `gabbro-check`; it ends in `parse.rs`. The surface the guardian did not look at
# > was the one visited first.
#
# **So the list is no longer a list but a pattern.** A new crate under `crates/` is in on
# the day it is created -- the same reason `abnahme.py` reads its cast from the directory
# instead of an enumeration that goes stale without a sound.
QUELLEN = sorted(W.glob("crates/*/src/*.rs"))

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
    # **`[^,]+` for the `Span` was too narrow, and it cost four messages** (2026-08-31).
    # `Absage::fehler("L001", Span::neu(…, …), "…")` carries a comma INSIDE
    # its second argument, so the expression did not match. The code string anchors it now:
    # between the code and the message stands an expression with NO quote in it, so `[^"]*`
    # suffices. *Narrower is impossible, wider would be guessing.*
    r'Absage::(?:fehler|hinweis)\(\s*"[A-Z][A-Za-z0-9_]*",[^"]*'   # die Meldung
    r"|\.mit_notiz\(\s*(?:format!\()?"                            # ihre Notiz
    r"|push_str\(&?(?:format!\()?"                                 # die Berichte
    r"|(?:e?println!)\(\s*"                                        # die CLI
    r"|Zustand::(?:Teilgebaut|Offen)\(\s*"                         # die Passliste
    # **`Kosten::Unbekannt` -- a sink nobody recognised as one** (2026-08-31).
    # The payload of the variant is printed twice in `kosten.rs`: as `{grund}` inside the
    # `K003` text, and as the column `-- {warum}` in the report of `gabbro kosten`. *The
    # text reached the user without ever being counted.*
    r"|Kosten::Unbekannt\(\s*(?:format!\()?"
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


# **THE FOURTH HALF: THE FEEDERS -- and the reason it exists is the reason it is not a list.**
#
# Measured 2026-08-31: the guardian saw **931 of 1870** prose strings in the sources, so
# half. The other half reached the user all the same, along paths no expression above names.
# Seven were found, and the tally is the point:
#
#     path                                          example                          texts
#     ------------------------------------------------------------------------------------
#     payload of a variant                          `Kosten::Unbekannt(grund, _)`        8
#     parameter of a helper                         `m1::passt(.., was)`                 6
#     return value of a helper                      `namen::grund(n)` -> `mit_notiz`     2
#     conditional expression at a sink              `.mit_notiz(if .. {..} else {..})`   2
#     literal inside an INNER `format!` / closure    `einigen`s `zeig` closure            2
#     head of a report through `String::from`       `kosten.rs::zeige`                   1
#     static register table printed by a            `schablonen.rs`, `zeugnis.rs`,
#     subcommand                                    `saetze.rs`, `manifest.rs`         173
#
# **A reach widened once around a known case is too small again at the next unknown one.**
# The eighth path is not in that table because I do not know it -- and that is exactly why
# this half counts not the paths but the REST: every prose literal of the sources that
# stands at NO sink.
#
# > The two halves are a PARTITION. Together they are every prose literal of every source.
# > *A new path can therefore no longer slip past the reach; it can only raise the residue,
# > and the residue is a ratchet.*
#
# What this half does NOT say: that every feeder reaches a user. The C templates in
# `emit.rs` are no sentence to a reader. *The coarsening runs, as everywhere here, in the
# safe direction -- it obliges, it does not acquit (W10).*


def literale(t):
    """Jedes Zeichenkettenliteral AUSSERHALB von Kommentaren, als `(anfang, inhalt)`.

    **Ein `re.findall` auf `"…"` reicht dafuer nicht**, und das ist gemessen: der erste
    Anlauf zaehlte 2126 Literale statt 1870 und legte Treffer quer ueber den Quelltext, weil
    ein `//`-Kommentar mit einem Anfuehrungszeichen die Paarung verschiebt. *Ein Werkzeug,
    das eine Mischung misst, sieht plausibel aus* -- W16, hier im eigenen Haus.

    Erkannt werden Zeilen- und Blockkommentare, Zeichenliterale (`'a'` gegen die Lebensdauer
    `'a`), Rohketten (`r"…"`, `r#"…"#`) und Byteketten (`b"…"`).
    """
    i, n, aus = 0, len(t), []
    while i < n:
        c = t[i]
        if c == "/" and t.startswith("//", i):
            j = t.find("\n", i)
            i = n if j < 0 else j + 1
            continue
        if c == "/" and t.startswith("/*", i):
            tiefe, i = 1, i + 2
            while i < n and tiefe:
                if t.startswith("/*", i):
                    tiefe, i = tiefe + 1, i + 2
                elif t.startswith("*/", i):
                    tiefe, i = tiefe - 1, i + 2
                else:
                    i += 1
            continue
        if c == "'":
            m = re.match(r"'(?:\\.|[^\\'])'", t[i:])
            i += m.end() if m else 1
            continue
        if c == "r" and t[i + 1 : i + 2] in ("#", '"'):
            m = re.match(r'r(#*)"', t[i:])
            if m:
                zaun = '"' + m.group(1)
                a = i + m.end()
                j = t.find(zaun, a)
                if j < 0:
                    break
                aus.append((a, t[a:j]))
                i = j + len(zaun)
                continue
        if c == "b" and t[i + 1 : i + 2] == '"':
            i, c = i + 1, '"'
        if c == '"':
            a = j = i + 1
            while j < n:
                if t[j] == "\\":
                    j += 2
                    continue
                if t[j] == '"':
                    break
                j += 1
            aus.append((a, t[a:j]))
            i = j + 1
            continue
        i += 1
    return aus


def ist_prosa(s):
    """Drei Woerter oder mehr, Platzhalter abgezogen -- ein Satz an einen Leser.

    Die Grenze ist grob und steht hier als Zahl, damit sie jemand verschieben kann. Unter
    drei Woertern liegen `"index into "`, `"slots of"`, Formatstuecke und C-Bruchstuecke;
    darueber liegt, was jemand gelesen haben will.
    """
    k = PLATZHALTER.sub(" ", s.replace("\\\n", " "))
    return len(re.findall(r"[A-Za-zÄÖÜäöüß]{2,}", k)) >= 3


def zubringer(quellen):
    """Prosa-Literale, die an KEINEM Sink stehen -- die andere Haelfte der Partition.

    Gibt `(gesamt, deutsche, je_datei)`. **Die Arbeitsmenge steht neben dem Urteil** (W17).
    """
    gesamt, deutsche, je_datei = 0, [], {}
    for f in quellen:
        t = f.read_text(encoding="utf-8", errors="replace")
        sinken = {m.start(1) for m in STELLEN.finditer(t)}
        for a, s in literale(t):
            if a in sinken or not ist_prosa(s):
                continue
            gesamt += 1
            if deutsch(s):
                zeile = t[:a].count("\n") + 1
                deutsche.append((f.name, zeile, deutsch(s), s[:58]))
                je_datei[f.name] = je_datei.get(f.name, 0) + 1
    return gesamt, deutsche, je_datei


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


def flaechenprobe():
    """R14 fuer die dritte und vierte Haelfte, in BEIDE Richtungen -- an ERFUNDENEN Quellen.

    **Der neue Weg wird mit einem Konstruktor geprueft, den es nicht gibt** (`Kosten::Wolke`).
    Das ist Absicht: haette die Reichweite ihn kennen muessen, waere sie wieder eine
    Aufzaehlung von Wegen. *Ein deutsches Wort auf einem Weg, den niemand genannt hat, muss
    rot machen -- sonst ist die Partition nur behauptet.*

    Gibt fuenf Wahrheitswerte: Sink rot/frei, Zubringer rot/frei -- und einen fuenften, der
    misst, dass ein deutscher Satz IM KOMMENTAR keine Meldung ist (der Lexer trennt sie).
    """
    import tempfile

    def schreibe(ort, name, text):
        f = pathlib.Path(ort) / name
        f.write_text(text, encoding="utf-8")
        return f

    with tempfile.TemporaryDirectory() as ort:
        sg = schreibe(ort, "sg.rs", 'fn f() { Kosten::Unbekannt("die Zahl steht nicht fest"); }\n')
        ss = schreibe(ort, "ss.rs", 'fn f() { Kosten::Unbekannt("the number is not fixed"); }\n')
        zg = schreibe(ort, "zg.rs", 'fn f() { Kosten::Wolke("die Zahl steht nicht fest"); }\n')
        zs = schreibe(ort, "zs.rs", 'fn f() { Kosten::Wolke("the number is not fixed"); }\n')
        ko = schreibe(ort, "ko.rs", '// hier steht ein deutscher Satz mit "einer langen Kette"\n')
        _, sink_gift = messe([sg])
        _, sink_frei = messe([ss])
        _, zub_gift, _ = zubringer([zg])
        _, zub_frei, _ = zubringer([zs])
        _, ko_zub, _ = zubringer([ko])
        _, ko_sink = messe([ko])
    return (
        len(sink_gift) == 1,
        not sink_frei,
        len(zub_gift) == 1,
        not zub_frei,
        not ko_zub and not ko_sink,
    )


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

# **THE FEEDER MARK -- IT CAME INTO BEING TODAY AND SO RISES FROM NOTHING TO 179.**
#
# **That is not a backlog that grew, but a population that did not exist before.** Until
# 2026-08-31 this guardian measured 1103 sites at five named sinks and reported `ALL PASS`.
# What was measured on that day is how large its surface REALLY is: 2140 prose strings in
# 45 sources. **It saw half.**
#
#     what                            before      after   where the difference comes from
#     ---------------------------------------------------------------------------------
#     sources in view                     37         45   `gabbro-syntax`, `fragmente.rs`
#     sites at a sink                   1103       1209   + `Kosten::Unbekannt`, + parser
#     prose BESIDE the sinks               0        931   the fourth half
#     German messages at a sink            0          0   27 found, 27 translated
#     German prose beside them             -        173   this mark
#
# **A ratchet that rises because its subject grows is not a broken ratchet -- and one where
# that is not written down beside it is indistinguishable from a broken one.** So it stands
# here, with the number and the date.
#
# The 173 are NOT an even fog. Two registers carry 136 of them:
#
#     schablonen.rs   79   `gabbro schablonen` -- premise/obligation/construct per template
#     zeugnis.rs      57   `gabbro zeugnis`    -- `grund:` per carrier kind
#     saetze.rs       19   `gabbro paesse`     -- `gemessen_an`, mostly German FILE NAMES
#     the rest        18   spread over thirteen files
#
# **They are printed reports and therefore language surface** -- the frame is already
# English (`A THE ASSUMPTIONS`, `B THE TEMPLATES`), the table contents are not. *Exactly
# the mixture this guardian was built against* (`M101`, 2026-08-19).
#
# **Not translated, and named as such:** two registers with 136 pieces of prose are a
# session of their own, not a side branch. A translation that stops halfway leaves behind
# precisely the state this guardian calls the worst of all -- *"a half-translated source is
# worse than either of the two pure forms"*. **The mark falls when somebody takes one
# register whole.**
#
# *It already fell once on the day it was set, from 177 to 173:* rewriting the sentence
# `kosten.domaenenschranke` for the domain measurement put four pieces of its prose into
# English on the way past. **That is the direction a ratchet is for** -- nobody translated a
# register, the number simply cannot go back up without somebody writing German into a
# report.
MARKE_ZUBRINGER = 173     # 177 measured, then 173 -- see the last paragraph of the note
MARKE_MELDUNGEN = 0       # German at a sink -- 27 found on 2026-08-31, 27 translated


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
    sf, sr, zf, zr, kk = flaechenprobe()
    print("  deutsch am neuen Sink faellt:   %s" % ("ja" if sf else "NEIN"))
    print("  englisch am neuen Sink frei:    %s" % ("ja" if sr else "NEIN"))
    print("  deutsch auf UNGENANNTEM Weg:    %s" % ("faellt" if zf else "NEIN"))
    print("  englisch auf demselben Weg:     %s" % ("frei" if zr else "NEIN"))
    print("  deutscher KOMMENTAR zaehlt nicht als Meldung: %s" % ("ja" if kk else "NEIN"))
    if not (sf and sr and zf and zr and kk):
        print("== FLAECHE: der Waechter misst nicht ==")
        return 2
    gesamt, gefunden = messe(QUELLEN)
    zub_gesamt, zub_deutsch, zub_datei = zubringer(QUELLEN)
    naht_gesamt, klebt = naehte(LESBAR_QUELLEN)
    print("\n== Lesbarkeit: %d Zeilenfortsetzungen in %d Quellen ==" % (naht_gesamt, len(LESBAR_QUELLEN)))
    for datei, zeile, vor, nach in klebt:
        print("  KLEBT  %s:%d  …%s|%s…" % (datei, zeile, vor, nach))
    print("  %d von %d Naehten kleben" % (len(klebt), naht_gesamt))
    print("   Und was das NICHT heisst: gemessen wird die NAHT, nicht der Satz. Eine Meldung,")
    print("   die aus zwei Zeichenketten zusammengesetzt wird, geht hier nicht durch die")
    print("   Fortsetzung -- der Waechter verpflichtet, er spricht nicht frei (W10).")
    print("\n== Sprachflaeche: %d Meldungstexte an einem Sink, in %d Dateien ==" % (gesamt, len(QUELLEN)))
    print("== Zubringer: %d Prosastuecke NEBEN den Sinken, %d davon deutsch ==" % (zub_gesamt, len(zub_deutsch)))
    print("   Die zwei Zahlen sind eine PARTITION: zusammen sind sie jedes Prosa-Literal")
    print("   jeder Quelle. Ein Weg, den niemand genannt hat, kann darum nicht an der")
    print("   Reichweite vorbei -- er hebt die zweite Zahl, und die ist eine Ratsche.")
    if zub_datei:
        schwer = sorted(zub_datei.items(), key=lambda x: -x[1])[:6]
        print("   Die schwersten: " + ", ".join("%s %d" % (a, b) for a, b in schwer))
    print("   Und was das NICHT heisst: nicht jeder Zubringer kommt beim Nutzer an. Die")
    print("   C-Vorlagen in `emit.rs` sind kein Satz an einen Leser -- die Vergroeberung")
    print("   geht in die sichere Richtung, sie verpflichtet und spricht nicht frei (W10).")

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
    if len(zub_deutsch) > MARKE_ZUBRINGER:
        print("\n  RATSCHE GEBROCHEN: %d deutsche Zubringer, gebucht sind %d."
              % (len(zub_deutsch), MARKE_ZUBRINGER))
        print("   Ein NEUER Weg, auf dem Text in eine Meldung gelangt, sieht genau so aus.")
        for datei, zeile, woerter, text in zub_deutsch[-8:]:
            print("     %s:%d  [%s]  %s" % (datei, zeile, ", ".join(woerter[:3]), text))
        ratsche = 1
    if len(gefunden) > MARKE_MELDUNGEN:
        print("\n  RATSCHE GEBROCHEN: %d deutsche Meldungen an einem Sink, gebucht sind %d."
              % (len(gefunden), MARKE_MELDUNGEN))
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
