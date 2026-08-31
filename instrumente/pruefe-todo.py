#!/usr/bin/env python3
"""Der vierte Waechter: haelt `TODO.md` gegen sich selbst und gegen den Ordner.

Am 2026-08-14 stand die Aufgabenliste **in acht Punkten unwahr ueber sich selbst** — acht
erledigte Eintraege unter der Ueberschrift „ausschliesslich Offenes", sechs vom Ordner
ueberholte Aussagen, drei doppelt gefuehrte Themen, zwei kollidierende Etikettensysteme,
stehengebliebene Zahlen. **Alle acht waren maschinell nachweisbar, und keiner wurde
bemerkt**, weil die Grammatik zwei Waechter hat, der Pruefer eine Mutationsprobe — und die
Liste, die den Weg vorgibt, gar nichts.

*Eine Liste, die nicht stimmt, kostet mehr als keine: sie sagt an jeder Stelle „das ist noch
offen", und der Leser glaubt es.*

    ./instrumente/pruefe-todo.py            prueft
    ./instrumente/pruefe-todo.py --probe    nur die Sprechprobe des Waechters
"""
import pathlib
import re
import subprocess
import sys

WURZEL = pathlib.Path(__file__).resolve().parent.parent

# **Jede Ausfuehrung mit Frist.** Ein Haenger sieht aus wie „laeuft noch", nicht wie
# ein Befund -- am 2026-08-20 standen deswegen einundzwanzig Laeufe von
# `pruefe-emission.sh` nebeneinander, der aelteste seit dreieinhalb Stunden.
FRIST = 600

# Die Etiketten des Prueferplans. Wer sie zweitvergibt, hat zwei Systeme mit denselben Namen.
#
# **Englisch seit der Uebersetzung von `TODO.md` (2026-08-17).** Die Werte werden gegen den
# Ueberschriftentext gehalten (`gemeint.split()[0]`); stuende hier weiter `Grammatikvereinigung`,
# meldete der Waechter jede englische Ueberschrift als Kollision -- ein falsches Rot, und zwar
# eines, das mit der Zeit als richtig gilt.
PRUEFERPLAN = {
    "P0": "repeat measurement on paper",
    "P1": "grammar unification",
    "P2": "lexer+parser",
    "P3": "M1+V1–V3",
    "P4": "M2 + generator template",
    "P5": "C emission",
    "P6": "pairing pass",
    "P7": "one Caprock module end-to-end",
}

# **Und PLAN.md fuehrt DIESELBEN Etiketten mit anderem Inhalt** (gefunden 2026-08-19).
#
# Der Waechter hielt bis heute nur TODO.md-Ueberschriften gegen `PRUEFERPLAN` -- und sah
# deshalb nicht, dass die groesste Zweitvergabe im Ordner in `dokumente/PLAN.md` steht: eine
# vollstaendige zweite P-Reihe, P0 bis P8, die von P1 an etwas anderes bedeutet.
#
#   SPRACHE.md  P6  Paarungspass + `entry`-Emission
#   PLAN.md     P6  `spec fn`/`impl fn` und die erzeugte Verfeinerungspflicht
#
# Beide sind Baureihenfolgen derselben Sache -- PLAN.md hat eine Stufe mehr, und ab P1
# verschiebt sich alles. **Das ist keine Namenskollision, sondern zwei Fassungen EINES Plans,
# die auseinandergelaufen sind**, und `pflichten.rs`, `TODO.md` und PLAN.md folgen der einen,
# `SPRACHE.md` und dieser Waechter der anderen.
#
# *Welche gilt, ist ein Urteil und steht nicht hier.* Gebucht ist der Stand; eine NEUE
# Abweichung faellt.
PLAN_ABWEICHUNG_GEBUCHT = {
    # P0 heisst in beiden "Papier zuerst" und ist die EINZIGE Stufe, die sich noch deckt --
    # der Wortlaut steht trotzdem hier, denn gebucht wird der Stand, nicht die Absicht.
    "P0": "Paper. Three questions, each can kill the thesis",
    "P1": "`check` as a Rust macro library, without a language",
    "P2": "The core as a CHECKER, without code generation",
    "P3": "Lowering to C, syntax-directed",
    "P4": "M3 and `device`",
    "P5": "Axiom layer and entry",
    "P6": "`spec fn` / `impl fn` and the generated refinement obligation",
    "P7": "Race freedom",
    "P8": "Migration by the strangler pattern",
}


def plan_etiketten():
    """**Die zweite P-Reihe, gegen die gebuchte Abweichung.** Zwei Wege, ein Waechter.

    Neu abgewichen  -> FEHLER: eine dritte Bedeutung fuer dasselbe Etikett.
    Angeglichen     -> FEHLER: der Eintrag ist gestiegen und gehoert geloescht (Sperrklinke).
    """
    text = (WURZEL / "dokumente" / "PLAN.md").read_text()
    heute = {}
    for z in text.splitlines():
        m = re.match(r"^## (P\d) — (.+)$", z)
        if m:
            heute[m.group(1)] = m.group(2).strip()
    befunde = []
    for et, titel in sorted(heute.items()):
        gebucht = PLAN_ABWEICHUNG_GEBUCHT.get(et)
        if gebucht is None:
            if et in PRUEFERPLAN:
                befunde.append(f"PLAN.md '{et} — {titel[:44]}' weicht NEU vom Prueferplan ab")
            continue
        if titel != gebucht:
            befunde.append(f"PLAN.md '{et}' hat sich geaendert: gebucht war '{gebucht[:44]}'")
    for et, gebucht in sorted(PLAN_ABWEICHUNG_GEBUCHT.items()):
        if et not in heute:
            befunde.append(f"PLAN.md '{et}' ist weg -- gebuchte Abweichung geloest? Eintrag loeschen")
    return befunde


# **A struck-through number is a WITHDRAWN one, and rule 7 counted it anyway** (2026-08-30).
#
# The registers of this folder correct rather than overwrite: the old value stays visible in
# `~~...~~` with the new one beside it. Rule 7 read the whole text, so **the moment a register
# quoted its own outdated number, the guardian reported it as current** -- `DONE.md` was
# corrected on 2026-08-30 and went red on the very sentence that recorded the correction.
#
# > *A guardian that cannot tell a correction from a claim forces the correction to be hidden*
# > -- and hiding it is exactly what R14 and the strike-through convention exist against.
#
# `zaehle-pflichten.py` has drawn the same line since 2026-08-25 for `gap:` rows, in the same
# words: **a struck-through entry is a retraction, and whoever counts it counts a retraction.**
DURCHGESTRICHEN = re.compile(r"~~.+?~~", re.S)


def ohne_durchgestrichenes(text):
    """Der Text ohne die zurueckgezogenen Stellen -- fuer Zaehlungen, nicht fuer Regel 6."""
    return DURCHGESTRICHEN.sub(" ", text)


def done_korpuszahlen(dt, n_bsp, n_gift):
    """**Die Korpuszahlen von `DONE.md` gegen das Dateisystem** (2026-08-30).

    Regel 7 haelt *„N saubere Beispiele"* und *„N Giftproben"* seit dem 2026-08-16 gegen
    `beispiele/` -- **aber nur in dem Text, mit dem `pruefe` gerufen wird, und das ist
    `TODO.md`.** `DONE.md` trug dieselben zwei Wendungen in seiner Schlusszeile und ging an
    demselben Waechter unbemerkt vorbei, waehrend der Korpus auf 53 und 310 wuchs.

    > *Eine Regel, die eine Datei nennt, bewacht eine Datei.* Der zweite Leser ist die
    > Stelle, an der die Zahl ungesehen altert.

    Durchgestrichenes zaehlt nicht mit -- ein zurueckgezogener Wert ist keine Behauptung.
    """
    befunde = []
    lebend = ohne_durchgestrichenes(dt)
    for muster, n_ist, was in ((r"(\d+) clean examples", n_bsp, "saubere Beispiele"),
                               (r"(\d+) saubere Beispiele", n_bsp, "saubere Beispiele"),
                               (r"(\d+) poison probes", n_gift, "Giftproben"),
                               (r"(\d+) Giftproben", n_gift, "Giftproben")):
        for m in re.finditer(muster, lebend):
            if int(m.group(1)) != n_ist:
                befunde.append(f"DONE.md: '{m.group(1)} {was}' -- es sind {n_ist}")
    return befunde


def pruefe(text, zahlen, vollstaendig=False):
    """Gibt die Liste der Befunde. Leer heisst: die Liste stimmt ueber sich selbst.

    `vollstaendig` heisst: der Text ist die ECHTE `TODO.md` und traegt darum jede bewachte
    Zahl. Nur dann ist ein Muster ohne Treffer ein Befund -- die zwei Vorlagen der
    Sprechprobe sind kurz und sollen es nicht sein.
    """
    befunde = []

    # 1. Behauptet die Datei „ausschliesslich Offenes" und fuehrt Erledigtes?
    #    **Beide Sprachen, seit der Uebersetzung.** Die deutsche Wendung bleibt stehen: die
    #    Sprechprobe unten fuehrt sie, und ein Waechter, der nur die neue Fassung kennt, faellt
    #    still aus, sobald irgendwo die alte steht.
    if any(s in text for s in ("Ausschliesslich Offenes", "ausschliesslich Offenes",
                               "Exclusively what is open", "exclusively what is open")):
        erledigt = re.findall(r"^- \[x\][^\n]*", text, re.M)
        for e in erledigt:
            befunde.append(
                f"erledigter Eintrag in einer Datei, die 'ausschliesslich Offenes' "
                f"behauptet: {e[:70]}"
            )

    # 2. Ueberschriften, die Etiketten des Prueferplans zweitvergeben.
    for m in re.finditer(r"^## (P\d)\b\s*—?\s*([^\n]*)", text, re.M):
        etikett, rest = m.group(1), m.group(2)
        gemeint = PRUEFERPLAN.get(etikett, "")
        if gemeint and gemeint.split()[0].lower() not in rest.lower():
            befunde.append(
                f"Ueberschrift '{etikett} — {rest[:40]}' vergibt ein Etikett des "
                f"Prueferplans zweit ({etikett} = {gemeint})"
            )

    # 3. Zahlen, die der Ordner ueberholt hat.
    #
    # **Since 2026-08-28 a pattern without a hit is a FINDING here too.** The README half of
    # this tool has said so in its own words since 2026-08-20 -- *„a pattern that loses its
    # object is no guardian any more, it is a comment"* -- and the TODO half did not. **Two
    # halves of one tool that answer differently, and the quieter one had been right:** the
    # pattern for the unwatched bold numbers and the one for the rule count both hit nothing
    # any more, and both numbers had stood unwatched in `TODO.md` ever since. *An unwatched
    # number never draws attention.*
    #
    # The speech test must not be caught by this: its two templates are short and do not carry
    # most of the patterns at all. So the rule applies only to the REAL text -- `pruefe` takes
    # `vollstaendig` for that.
    for muster, heute, was in zahlen:
        treffer = re.findall(muster, text)
        if not treffer and vollstaendig:
            befunde.append(
                f"das Muster fuer {was} trifft nichts mehr -- die Zahl ist umformuliert "
                f"und damit UNBEWACHT"
            )
            continue
        for t in treffer:
            if t != heute:
                befunde.append(
                    f"stehengebliebene Zahl: {was} steht als {t}, heute {heute}"
                )

    # 4. Themen, die mehrfach als eigener Punkt gefuehrt werden.
    themen = [
        (r"^- \[ \] \*\*[^\n]*`?narrow`?[- ](Vollzaehlung|full count)", "narrow-Vollzaehlung"),
        (r"^- \[ \] \*\*Variable (L[äa]ngen|lengths)", "Variable Laengen"),
        (r"^- \[ \] \*\*Version(sevolution| evolution)", "Versionsevolution"),
    ]
    for muster, name in themen:
        n = len(re.findall(muster, text, re.M))
        if n > 1:
            befunde.append(f"'{name}' steht {n} mal als eigener Punkt")

    # 5. **Passzahlen gegen `gabbro paesse`.** Der Abgleich vom 2026-08-14 fand „Sechs der
    #    neun Paesse fehlen", wo es fuenf ganze und zwei halbe waren. Eine Zahl ueber den
    #    eigenen Uebersetzer, die niemand gegen den Uebersetzer haelt, ist Falle 80.
    ganz, halb, getragen = paesse_heute()
    if ganz is not None:
        for muster in (r"\*\*(\w+) der neun Paesse fehlen ganz\*\*",
                       r"\*\*\"?(\w+) of the nine passes are missing entirely\"?\*\*"):
            for m in re.finditer(muster, text):
                if ZAHLWORT.get(m.group(1).lower()) != ganz:
                    befunde.append(
                        f"Passzahl stimmt nicht: '{m.group(1)} von neun Paessen fehlt ganz', "
                        f"`gabbro paesse` sagt {ganz}"
                    )
        for muster in (r"\*\*(\w+) sind nur\s+teilweise gebaut\*\*",
                       r"\*\*(\w+) are only\s+partially built\*\*"):
            for m in re.finditer(muster, text):
                if ZAHLWORT.get(m.group(1).lower()) != halb:
                    befunde.append(
                        f"Passzahl stimmt nicht: '{m.group(1)} nur teilweise gebaut', "
                        f"`gabbro paesse` sagt {halb}"
                    )

    # 6. **Durchgestrichenes ohne Datum.** Eine Regel, die als verletzt markiert ist, muss
    #    sagen WANN -- sonst steht sie als geltend da und ist es nicht (Befund 3 des
    #    Abgleichs). Geprueft wird der Absatz, nicht die Zeile: die Begruendung folgt oft
    #    darunter.
    for m in re.finditer(r"~~[^~]+~~", text):
        absatz = text[m.start() : m.start() + 400]
        if not re.search(r"20\d\d-\d\d-\d\d", absatz):
            befunde.append(
                f"durchgestrichener Eintrag ohne Datum: {m.group(0)[:60]} -- "
                f"eine verletzte Regel ohne Datum liest sich wie eine geltende"
            )

    # 7. **Beispielzahlen gegen das Dateisystem.**
    n_bsp = len(list((WURZEL / "beispiele").glob("*.gab")))
    n_gift = len(list((WURZEL / "beispiele/gift").glob("*.gab")))
    lebend = ohne_durchgestrichenes(text)
    for muster in (r"(\d+) saubere Beispiele", r"(\d+) clean examples"):
        for m in re.finditer(muster, lebend):
            if int(m.group(1)) != n_bsp:
                befunde.append(f"'{m.group(1)} saubere Beispiele' -- es sind {n_bsp}")
    for muster in (r"(\d+) Giftproben", r"(\d+) poison probes"):
        for m in re.finditer(muster, lebend):
            if int(m.group(1)) != n_gift:
                befunde.append(f"'{m.group(1)} Giftproben' -- es sind {n_gift}")

    # 8. **Die Gegenrichtung, seit 2026-08-16:** `DONE.md` fuehrt ausschliesslich
    #    Erledigtes, und jeder Eintrag traegt seinen Beleg (W7). Ein offener Haken dort ist
    #    derselbe Fehler wie ein `[x]` im TODO, nur spiegelverkehrt -- und er faellt
    #    niemandem auf, weil ihn niemand sucht.
    d = WURZEL / "DONE.md"
    if d.is_file():
        dt = d.read_text()
        # **Rule 7 named ONE file, and that is why the other one went stale** (2026-08-30).
        #
        # The counts above run over `TODO.md`, because that is the text this function is
        # called with. `DONE.md` carried the SAME two phrases in its closing line -- *25
        # clean examples, 78 poison probes* -- and went past this guardian untouched while
        # the corpus grew to 53 and 310. **The rule was right and its reach was one file.**
        #
        # > *A guardian that names a file guards a file.* The counts are the same, the object
        # > is the same, and the second reader is where the number ages unseen.
        befunde += done_korpuszahlen(dt, n_bsp, n_gift)
        for offen in re.findall(r"^- \[ \][^\n]*", dt, re.M):
            befunde.append(
                f"offener Eintrag in DONE.md, die 'exclusively what is done' "
                f"behauptet: {offen[:70]}"
            )
        for zeile in dt.splitlines():
            if zeile.startswith("| **") and "|" in zeile[4:]:
                # Die Zeichenklasse MUSS Grossbuchstaben tragen -- `dokumente/BEWEIS.md`
                # ist ein Beleg. Meine erste Fassung sah ihn nicht, und die Sprechprobe
                # hat es an der SAUBEREN Liste gefangen (falsches Rot).
                if not re.search(# **`.thy` fehlte bis zum 2026-08-17**, und der Waechter hat einen Eintrag
                # abgewiesen, dessen Beleg eine ISABELLE-THEORIE war -- also der staerkste
                # Beleg, den dieser Ordner kennt. *Ein Beleglisten-Waechter, der die
                # Beweise nicht kennt, misst die Buchhaltung und nicht die Sache.*
                r"`[\w./-]+\.(rs|py|sh|md|gab|tsv|thy)`|`[A-Z][0-9]{3}`"
                                 r"|gabbro |cargo |\./", zeile):
                    befunde.append(f"DONE.md-Eintrag ohne Beleg (W7): {zeile[:70]}")

    return befunde


ZAHLWORT = {
    "eine": 1, "eins": 1, "zwei": 2, "drei": 3, "vier": 4, "fuenf": 5, "fünf": 5,
    "sechs": 6, "sieben": 7, "acht": 8, "neun": 9,
    # Seit der Uebersetzung stehen die Zahlwoerter englisch in der Prosa. Beide Saetze
    # nebeneinander -- ein Waechter, der die alte Schreibweise vergisst, wird an ihr blind.
    "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
    "six": 6, "seven": 7, "eight": 8, "nine": 9,
}


def paesse_heute():
    """Wieviele Paesse fehlen ganz, wieviele sind halb? Aus `gabbro paesse`, nicht von Hand."""
    r = subprocess.run(
        ["cargo", "run", "-q", "-p", "gabbro-cli", "--", "paesse"],
        cwd=WURZEL, capture_output=True, text=True, timeout=FRIST)
    if r.returncode != 0:
        return None, None, None
    # `gabbro paesse` markiert die Zeilen mit `OFFEN` bzw. `TEIL` -- die Zahlen aus
    # der Ausgabe zu nehmen statt aus der Prosa ist der ganze Zweck dieser Pruefung.
    # **`OPEN`/`PART` seit 2026-08-19** -- die Sprachflaeche ist englisch. *Dieser Leser hing
    # an `OFFEN`/`TEIL` und haette nach der Uebersetzung stumm null gezaehlt: kein Fehler,
    # keine Meldung, und die Passzahlen im TODO waeren unbewacht gewesen.*
    # **`CARRY` seit 2026-08-19, und der Waechter musste mitwachsen.** Als die neun
    # teilgebauten Paesse auf *getragen mit benanntem Rest* umgestuft wurden, zaehlte dieser
    # Leser nur noch drei Paesse und meldete den README als falsch. *Er hatte recht in der
    # Rechnung und unrecht in der Frage:* die Gesamtzahl ist gebaut + offen + teil + getragen.
    return (
        len(re.findall(r"^  OPEN  ", r.stdout, re.M)),
        len(re.findall(r"^  PART  ", r.stdout, re.M)),
        len(re.findall(r"^  CARRY ", r.stdout, re.M)),
    )


def heutige_zahlen():
    """Was die Waechter heute melden -- gegen die Zahlen in der Prosa.

    **Die dritte und vierte Zeile sind am 2026-08-17 dazugekommen, und zwar an einem Fund.**
    Befund 5 des Abgleichs vom 14. lautet *„stehengebliebene Zahlen aus P1: 117 Regeln, 187
    Terminale (heute 121 / 189)"* -- und die Klammer *heute* war selbst stehengeblieben: der
    Waechter sagt 130 / 195. Die zwei alten Muster trafen die Zeile nicht, weil sie eine
    andere Schreibweise fuehrt als die, gegen die sie geschrieben waren.

    *Eine Zeile ueber stehengebliebene Zahlen, die eine stehengebliebene Zahl traegt, ist der
    genaue Fall, fuer den dieser Waechter gebaut wurde -- und er hat ihn zwei Tage lang nicht
    gesehen.*
    """
    r = subprocess.run(["./instrumente/pruefe-syntax.sh"], cwd=WURZEL, capture_output=True, text=True, timeout=FRIST)
    aus = r.stdout
    regeln = re.search(r"EBNF: (\d+) Regeln", aus)
    terme = re.search(r"Wortschatz: (\d+) EBNF-Terminale, (\d+) Tabellenwoerter", aus)
    r_heute = regeln.group(1) if regeln else "?"
    t_heute = terme.group(1) if terme else "?"
    # **Die Reichweite des Zahlenregisters kann das Zahlenregister NICHT bewachen** (W18):
    # ein Eintrag, der `pruefe-zahlen.py` selbst nennt, waere ein Fixpunkt, und der
    # Fixpunktriegel dort verbietet ihn mechanisch. **Der Ausweg ist ein ANDERES Werkzeug**,
    # und das ist dieses hier.
    #
    # *Gefunden am 2026-08-20: `TODO.md` fuehrte „12 Kennzahlen mit Befehl" und „11
    # Kennzahlen … 173 fettgedruckte Zahlen" -- beide Zahlen standen seit Tagen still,
    # waehrend das Register auf 20 gewachsen war.* Genau die Klasse, gegen die dieser
    # Waechter gebaut ist, an der einen Zahl, die er nicht ansah.
    z = subprocess.run(["./instrumente/pruefe-zahlen.py"], cwd=WURZEL, capture_output=True, text=True,
                       timeout=FRIST)
    m = re.search(r"(\d+) Kennzahlen mit Befehl, (\d+) fettgedruckte", z.stdout)
    k_heute, f_heute = (m.group(1), m.group(2)) if m else ("?", "?")
    return [
        (r"\*\*(\d+) Kennzahlen mit Befehl\*\*", k_heute, "Kennzahlen mit Befehl"),
        (r"heute (\d+)\s*\n?\s*Kennzahlen mit Befehl", k_heute, "Kennzahlen mit Befehl (Prosa)"),
        (r"\*\*(\d+) fettgedruckte Zahlen in Tabellenzellen ohne einen\*\*", f_heute,
         "unbewachte fettgedruckte Zahlen"),
        # **The rule count stands in `TODO.md` today as „153 EBNF-Regeln"**, no longer as
        # „**N Regeln, 0 offen**" -- the old wording has been gone for weeks. *So this pattern
        # hit nothing, and the TODO half did not say so until 2026-08-28.* Here the pattern is
        # pulled onto the wording that stands there, not the text onto a pattern: a number
        # that stands elsewhere is not reworded, it has moved.
        (r"(\d+) (?:EBNF-Regeln|Regeln, 0 offen|rules, 0 open)", r_heute, "EBNF-Regeln"),
        (r"(\d+) (?:Terminale gegen|terminals against)", t_heute, "EBNF-Terminale"),
        (r"\((?:heute|today) (\d+) / \d+\)", r_heute, "EBNF-Regeln (heute-Klammer)"),
        (r"\((?:heute|today) \d+ / (\d+)\)", t_heute, "EBNF-Terminale (heute-Klammer)"),
    ]


_MUSTER = None


def readme_muster():
    """**Der README traegt eine Kennzahlentafel, und niemand hielt sie nach.**

    Gefunden 2026-08-19: acht Zahlen standen falsch da -- *90 Absagen* (124), *130 Regeln*
    (139), *195 / 195* (206), *19 Schablonen, 4 bewiesen* (20 / 9), *8 Waechter* (10),
    *19 saubere Beispiele* (31), *69 Giftdateien* (104), *79 Tests* (126).

    **Dieselbe Klasse wie die sechs `gap:`-Zeilen und die acht widerrufenen Saetze:** die
    Zahl wurde gepflegt, die Quelle nicht. *Und der README ist die Datei, die ein Fremder
    ZUERST liest.*

    Geprueft wird nur, was sich ohne Uebersetzerlauf zaehlen laesst. Testzahl und
    Mutationsquote kommen aus einem Lauf und tragen darum ihr Messdatum im Text.

    **Diese Funktion MISST nur** -- sie gibt je bewachter Zahl `(Muster, heutiger Wert,
    Bedeutung)`. Getrennt wurde das am 2026-08-28: die Sprechprobe braucht dieselbe Messung,
    um sich eine SAUBERE Vorlage zu bauen, und sie darf sie nicht aus dem README nehmen, den
    sie prueft. *Und die Messung kostet drei Uebersetzerlaeufe; sie dreimal zu fahren war
    schon vorher nur Gewohnheit.*
    """
    global _MUSTER
    if _MUSTER is not None:
        return _MUSTER

    n_bsp = len(list((WURZEL / "beispiele").glob("*.gab")))
    n_gift = len(list((WURZEL / "beispiele/gift").glob("*.gab")))
    n_waechter = len(list(WURZEL.glob("instrumente/pruefe-*.py"))) + len(list(WURZEL.glob("instrumente/pruefe-*.sh")))

    k = subprocess.run(["./instrumente/pruefe-kennungen.py"], cwd=WURZEL, capture_output=True, text=True, timeout=FRIST)
    m = re.search(r"Kennungen: (\d+) vergeben", k.stdout)
    n_kenn = m.group(1) if m else "?"

    s = subprocess.run(["cargo", "run", "--quiet", "--bin", "gabbro", "--", "schablonen"],
                       cwd=WURZEL, capture_output=True, text=True, timeout=FRIST)
    # **Englisch seit 2026-08-19** -- die Sprachflaeche von Gabbro ist es, und dieser Leser
    # hing an der deutschen Fassung. *Ein Waechter, der die Ausgabe eines Werkzeugs liest,
    # gehoert zu dessen Sprache; er hat sie hier zwei Stunden lang nicht gehabt.*
    m = re.search(r"(\d+) templates, \d+ of them unproved, (\d+) machine-checked", s.stdout)
    n_schab, n_bew = (m.group(1), m.group(2)) if m else ("?", "?")

    y = subprocess.run(["./instrumente/pruefe-syntax.sh"], cwd=WURZEL, capture_output=True, text=True, timeout=FRIST)
    m = re.search(r"EBNF: (\d+) Regeln", y.stdout)
    n_regeln = m.group(1) if m else "?"
    m = re.search(r"Wortschatz: (\d+) EBNF-Terminale, (\d+) Tabellenwoerter", y.stdout)
    n_term, n_tab = (m.group(1), m.group(2)) if m else ("?", "?")

    # **Und die Passzahlen, seit 2026-08-19.** Der Leser dafuer stand seit jeher da und
    # verglich gegen die PROSA von `TODO.md`; die Kennzahlentafel des README pruefte ihn
    # niemand. *Beim Nachziehen der englischen Ausgabe kam heraus, dass dort 10 Paesse mit
    # 7 teilgebauten standen -- es sind 12 mit 9.*
    ganz, halb, getragen = paesse_heute()
    fuer = [
        (r"\| \*\*Compiler\*\* \| (\d+) passes",
         str(12 if ganz is None else 3 + ganz + halb + getragen), "Paesse"),
        (r"\| \*\*Compiler\*\* \| \d+ passes, \d+ complete, \*\*(\d+) carried",
         str(getragen), "getragene Paesse"),
        (r"(\d+) diagnostics", n_kenn, "Absagekennungen"),
        (r"\*\*(\d+) EBNF rules\*\*", n_regeln, "EBNF-Regeln"),
        (r"(\d+) / (?:\d+)\s*\|", n_term, "EBNF-Terminale"),
        (r"\*\*(\d+), of which \d+ are machine-checked\*\*", n_schab, "Schablonen"),
        (r"\*\*\d+, of which (\d+) are machine-checked\*\*", n_bew, "bewiesene Schablonen"),
        (r"\| \*\*Guardians\*\* \| (\d+),", str(n_waechter), "Waechter"),
        (r"(\d+) clean examples", str(n_bsp), "saubere Beispiele"),
        (r"(\d+) poison files", str(n_gift), "Giftdateien"),
    ]
    # **Ein Muster, das nichts trifft, meldet nichts -- und sieht aus wie ein Bestehen.**
    #
    # Gefunden 2026-08-20, an dieser Zeile selbst: die Waechterzahl stand als
    # `| **Guardians** | (\d+),` -- mit Komma. Beim Umformulieren auf `| 19 — and …` traf das
    # Muster nichts mehr, und der Waechter meldete „sauber" ueber einer falschen Zahl.
    #
    # > *Dieselbe Richtung wie ein Haenger: nichts wird rot.* Ein Muster, das seinen
    # > Gegenstand verliert, ist kein Waechter mehr, sondern ein Kommentar.
    #
    # Darum ist ein Fehlschlag des Musters seit heute selbst ein BEFUND.

    # **Und der Abschnitt UNTER der Tafel** (Rezension 2026-08-20).
    #
    # Dieser Leser hielt die Kennzahlentafel nach -- und nur sie. Eine Bildschirmhoehe
    # tiefer standen drei Zahlen still: `cargo test  # 126 tests` (es sind ueber 150),
    # `mutiere-pruefer.py  # 168 of 168` (es sind ueber 190) und „the twelve theories"
    # (es sind dreizehn).
    #
    # > *Dieselbe Klasse, die am 2026-08-19 achtmal bezahlt wurde, eine Bildschirmhoehe
    # > tiefer.* Ein Waechter, der einen Abschnitt liest und den naechsten nicht, verlagert
    # > das Problem, statt es zu loesen.
    #
    # Die Theorienzahl und die Isar-Zeilen lassen sich ohne Uebersetzerlauf zaehlen; die
    # Test- und Mutationszahl nicht -- die stehen im Lauf und tragen darum ihr Datum. Was
    # hier geprueft wird, ist deshalb genau das Zaehlbare.
    # **Die vier Blindstellenzahlen standen in KEINEM Register** -- gefunden 2026-08-20.
    # Der README sagte `79 blind · 166 covered · 25 poison-only`, das Werkzeug sagt
    # `80 · 164 · 26`, und `TODO.md`:642 (bewacht von `pruefe-zahlen.py`) sagte die 80.
    # *Zwei Dokumente, eine Messung, und nur eines hatte einen Leser.* Sie sind ohne
    # Uebersetzerlauf nicht zaehlbar -- aber `gabbro` laeuft hier ohnehin schon, also gibt
    # es keinen Grund, sie unbewacht zu lassen.
    bl = subprocess.run(["sh", "-c",
                         "cargo run -q --bin gabbro -- blindstellen beispiele/*.gab "
                         "-- beispiele/gift/*.gab"],
                        cwd=WURZEL, capture_output=True, text=True, timeout=FRIST)
    m = re.search(r"(\d+) blind · (\d+) covered · (\d+) poison-only · (\d+) no cell "
                  r"\(of (\d+) pairs\)", bl.stdout)
    n_blind, n_deck, n_gift_only, n_keine, n_paare = m.groups() if m else ("?",) * 5
    fuer += [
        (r"\*\*(\d+) blind · \d+ covered", n_blind, "blinde Zellen"),
        (r"\*\*\d+ blind · (\d+) covered", n_deck, "besetzte Zellen"),
        (r"covered · (\d+) poison-only", n_gift_only, "nur im Gift besetzte Zellen"),
        (r"poison-only · (\d+) no cell", n_keine, "Zellen ohne Kombination"),
        (r"no cell\*\* \*\(of (\d+) pairs\)\*", n_paare, "Zellen der Tafel"),
    ]

    n_thy = len(list((WURZEL / "beweise").glob("*.thy")))
    # `count("\\n")` und nicht `split`: das ist, was `wc -l` zaehlt, und danach wird gefragt.
    n_isar = sum(f.read_text().count("\n") for f in (WURZEL / "beweise").glob("*.thy"))
    fuer += [
        (r"The (\d+) theories in", str(n_thy), "Theorien (Fliesstext)"),
        (r"across all (\d+) theories", str(n_thy), "Theorien (Klammer)"),
        (r"\((\d[\d\s]*) across all \d+ theories\)",
         str(n_isar), "Isar-Zeilen"),
    ]
    _MUSTER = fuer
    return fuer


# **Tausenderpunkte zaehlen nicht mit.** `2 304` und `2304` sind dieselbe Zahl, und ein
# Waechter, der daran scheitert, zwingt den Text in seine Schreibweise statt umgekehrt.
def blank(s):
    return str(s).replace(" ", "").replace("\u00a0", "").replace(".", "")


def pruefe_readme(text=None):
    """Die Kennzahlentafel gegen ihren Gegenstand. Ohne `text`: der echte README."""
    if text is None:
        r = WURZEL / "README.md"
        if not r.is_file():
            return []
        text = r.read_text()
    befunde = []
    for muster, heute, was in readme_muster():
        treffer = list(re.finditer(muster, text))
        # **Ein Muster ohne Treffer ist ein BEFUND, kein Bestehen** (2026-08-20, an der
        # Waechterzahl selbst gefunden: sie stand als `| **Guardians** | (\d+),` mit Komma,
        # wurde auf `| 17, and ...` umformuliert und war damit unbewacht -- der Waechter
        # meldete "sauber" ueber einer falschen Zahl). *Dieselbe Richtung wie ein Haenger:
        # nichts wird rot.*
        if not treffer:
            befunde.append(f"README: das Muster fuer {was} trifft nichts mehr -- "
                           f"die Zahl ist umformuliert und damit UNBEWACHT")
            continue
        for t in treffer:
            if blank(t.group(1)) != blank(heute):
                befunde.append(f"README: '{t.group(1)}' als {was} -- es sind {heute}")
    return befunde


def readme_vorlage(text):
    """**Der README mit JEDER bewachten Zahl auf ihrem heutigen Wert** -- die saubere
    Vorlage der Sprechprobe.

    *Gebaut am 2026-08-28, und der Grund ist der Waechter selbst.* Die Sprechprobe hielt
    ihre "saubere" Haelfte gegen den ECHTEN README -- also gegen eine Datei, die
    stehengebliebene Zahlen tragen DARF, denn genau die zu finden ist ihr Zweck. Elf davon
    standen darin, und die Probe meldete **"falsches Rot"**: sie sprach ueber das Werkzeug
    und meinte den Gegenstand. **Schlimmer noch:** `main()` bricht nach einer gefallenen
    Sprechprobe ab -- die elf Zahlen wurden nie gedruckt.

    > *Ein Waechter, der auf einen echten Befund mit "ich bin kaputt" antwortet und dabei
    > den Befund verschluckt, misst etwas anderes als seinen Gegenstand* (W16/W21).

    Die Vorlage hier ist mechanisch sauber statt hoffentlich sauber. Was an ihr NICHT zu
    heilen ist, bleibt ein Befund: ein Muster, das gar nichts trifft, laesst sich nicht
    korrigieren -- und DAS ist dann wirklich ein Fehler des Waechters.
    """
    for muster, heute, _was in readme_muster():
        def ersetze(t, heute=str(heute)):
            a, b = t.start(1) - t.start(0), t.end(1) - t.start(0)
            return t.group(0)[:a] + heute + t.group(0)[b:]
        text = re.sub(muster, ersetze, text)
    return text


def sprechprobe(zahlen):
    """In beide Richtungen: eine kaputte Liste MUSS fallen, eine saubere NICHT."""
    gift = """# Probe

- [x] **Etwas Erledigtes** steht hier.
- [ ] **Die `narrow`-Vollzaehlung** einmal.
- [ ] **Die `narrow`-Vollzaehlung** zweimal.

## P1 — `check` ohne Sprache

Stehengebliebene Zahlen aus P1: 117 Regeln, 187 Terminale (heute 1 / 1)

**Ausschliesslich Offenes.**
"""
    sauber = """# Probe

- [ ] **Etwas Offenes** steht hier.

## `check` ohne Sprache

**Ausschliesslich Offenes.**
"""
    b_gift = pruefe(gift, zahlen)
    b_sauber = pruefe(sauber, zahlen)
    # **Fuenf statt drei, seit die heute-Klammer mitgeprueft wird.** Die Marke wandert mit dem
    # Waechter mit: eine Untergrenze, die stehenbleibt, waehrend Regeln dazukommen, misst
    # irgendwann nur noch die aeltesten.
    print(f"  Giftliste:    {len(b_gift)} Befunde", end="")
    print(" -- ok" if len(b_gift) >= 5 else " -- GESCHEITERT (der Waechter ist stumm)")
    for b in b_gift:
        print(f"     {b}")
    print(f"  Saubere Liste: {len(b_sauber)} Befunde", end="")
    print(" -- ok" if not b_sauber else " -- GESCHEITERT (falsches Rot)")

    # **The DONE count, both ways** (2026-08-30). It lives in the same function as the other
    # rules and would otherwise be carried along by the two lists above -- *a rule that is
    # only ever checked together with others is not checked.* The third line is the real one:
    # **a struck-through value must NOT count**, or no register can write down its own
    # correction without the guardian reporting the retracted number as a claim.
    #
    # **And the clean half took its yardstick from yesterday** (found 2026-08-30). It stood
    # here as the literal `**53 clean examples, 310 poison probes**`, and the corpus grew by
    # one example and one poison file the same day: the probe reported
    # *„GESCHEITERT (erwartet 0)"* -- a speech test failing over a RIGHT number -- and
    # `main()` does not read its return value, so the line printed red and the guard exited
    # green. **Exactly the fault the paragraph below this one describes for the README half,
    # one probe further over.** Both literals are derived now.
    n_b = len(list((WURZEL / "beispiele").glob("*.gab")))
    n_g = len(list((WURZEL / "beispiele/gift").glob("*.gab")))
    d_gift = f"**{n_b - 1} clean examples, {n_g - 1} poison probes** —\n"
    d_sauber = f"**{n_b} clean examples, {n_g} poison probes** —\n"
    d_zurueck = f"~~*{n_b - 1} clean examples, {n_g - 1} poison probes*~~ — berichtigt\n"
    # **And the verdict counts them** (2026-08-30). The three lines below were PRINTED and
    # left out of the `return` -- so the DONE half could report `GESCHEITERT` while the guard
    # exited green. *A speech test whose failure changes nothing is a decoration* (R11), and
    # this one had been one since the day it was written.
    d_ok = True
    for was, txt, erwartet in (("veraltete Zahl faellt", d_gift, 2),
                               ("richtige bleibt frei", d_sauber, 0),
                               ("zurueckgezogene zaehlt nicht", d_zurueck, 0)):
        n = len(done_korpuszahlen(txt, n_b, n_g))
        d_ok = d_ok and n == erwartet
        print(f"  DONE-Zahlen ({was}): {n}", end="")
        print(" -- ok" if n == erwartet else f" -- GESCHEITERT (erwartet {erwartet})")

    # **Und die README-Haelfte, in beide Richtungen.** Eine Kennzahlentafel, die keiner
    # nachhaelt, faellt sonst genauso lautlos aus wie die acht Zahlen, die sie ersetzt hat.
    #
    # **Since 2026-08-28 both halves run on the TEMPLATE and not on the real README**
    # (`readme_vorlage`). The reason is a double finding at this very spot:
    #
    # * the *clean* half ran against the real README, and that one carried eleven stale
    #   numbers -- it reported „false red" over a RIGHT red and swallowed the eleven findings
    #   in doing so, because `main()` aborts after a failed speech test;
    # * the *poison* half had gone blunt at the same time: it misstated `51 clean examples`,
    #   the README said `51` and today there are 53 -- the replacement hit nothing, and the
    #   eleven real findings still let it report „ok". **A probe that passes for the wrong
    #   reason is none.**
    #
    # *The same cause both times: the probe took its yardstick from its object.*
    echt = (WURZEL / "README.md").read_text()
    vorlage = readme_vorlage(echt)
    # **Die Sprechprobe muss die HEUTIGE Zahl verstellen, nicht eine von gestern.**
    # *Gefunden 2026-08-19: der Korpus wuchs auf 32, und die Probe verstellte weiter „31" --
    # sie fand nichts und meldete damit, sie koenne nicht messen.* Der Waechter faengt seinen
    # eigenen Fall, weil er in BEIDE Richtungen prueft.
    n_bsp_heute = len(list((WURZEL / "beispiele").glob("*.gab")))
    verstellt = vorlage.replace("%d clean examples" % n_bsp_heute, "17 clean examples")
    r_gift = pruefe_readme(verstellt)
    r_sauber = pruefe_readme(vorlage)
    # **And it is not enough that ANYTHING falls** -- the misstated number is what is asked.
    getroffen = [b for b in r_gift if "saubere Beispiele" in b]
    print(f"  README-Gift:   {len(r_gift)} Befunde", end="")
    print(" -- ok" if getroffen else " -- GESCHEITERT (verstellte Zahl kam durch)")
    for b in r_gift:
        print(f"     {b}")
    print(f"  README sauber: {len(r_sauber)} Befunde", end="")
    print(" -- ok" if not r_sauber else " -- GESCHEITERT (der Waechter ist der Befund)")
    for b in r_sauber:
        print(f"     {b}")

    return len(b_gift) >= 5 and not b_sauber and bool(getroffen) and not r_sauber and d_ok


def main():
    zahlen = heutige_zahlen()
    print("== Sprechprobe des Waechters ==")
    if not sprechprobe(zahlen):
        # **2, not 1: a guardian that fails its own speech test has measured NOTHING.**
        # What it says about `TODO.md` afterwards is not a statement about `TODO.md`.
        print("\n! Der Waechter misst nicht, was er behauptet. ABBRUCH.")
        return 2
    if "--probe" in sys.argv:
        return 0

    p_befunde = plan_etiketten()
    print("\n== Die zweite P-Reihe (dokumente/PLAN.md) ==")
    if p_befunde:
        for b in p_befunde:
            print(f"  {b}")
        print("== PLAN: FEHLER ==")
        return 1
    print(f"  {len(PLAN_ABWEICHUNG_GEBUCHT)} gebuchte Abweichungen, keine neue.")
    print("  Zwei Fassungen EINES Plans -- welche gilt, ist ein Urteil und steht im TODO.")

    r_befunde = pruefe_readme()
    print("\n== README.md ==")
    if r_befunde:
        for b in r_befunde:
            print(f"  {b}")
        print(f"== README: {len(r_befunde)} stehengebliebene Zahlen ==")
    else:
        print("  Kennzahlentafel deckt sich mit dem Gegenstand.")

    text = (WURZEL / "TODO.md").read_text()
    befunde = pruefe(text, zahlen, vollstaendig=True)
    print("\n== TODO.md ==")
    if not befunde and not r_befunde:
        offen = len(re.findall(r"^- \[ \]", text, re.M))
        print(f"  {offen} offene Punkte, keine Doppelung, keine Etikettenkollision,")
        print("  kein Erledigtes, keine stehengebliebene Zahl.")
        print("== TODO: ALL PASS ==")
        return 0
    for b in befunde:
        print(f"  {b}")
    print(f"== TODO: {len(befunde) + len(r_befunde)} BEFUNDE ==")
    return 1


if __name__ == "__main__":
    sys.exit(main())
