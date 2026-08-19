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

    ./pruefe-todo.py            prueft
    ./pruefe-todo.py --probe    nur die Sprechprobe des Waechters
"""
import pathlib
import re
import subprocess
import sys

WURZEL = pathlib.Path(__file__).resolve().parent

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


def pruefe(text, zahlen):
    """Gibt die Liste der Befunde. Leer heisst: die Liste stimmt ueber sich selbst."""
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
    for muster, heute, was in zahlen:
        for treffer in re.findall(muster, text):
            if treffer != heute:
                befunde.append(
                    f"stehengebliebene Zahl: {was} steht als {treffer}, heute {heute}"
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
    for muster in (r"(\d+) saubere Beispiele", r"(\d+) clean examples"):
        for m in re.finditer(muster, text):
            if int(m.group(1)) != n_bsp:
                befunde.append(f"'{m.group(1)} saubere Beispiele' -- es sind {n_bsp}")
    for muster in (r"(\d+) Giftproben", r"(\d+) poison probes"):
        for m in re.finditer(muster, text):
            if int(m.group(1)) != n_gift:
                befunde.append(f"'{m.group(1)} Giftproben' -- es sind {n_gift}")

    # 8. **Die Gegenrichtung, seit 2026-08-16:** `DONE.md` fuehrt ausschliesslich
    #    Erledigtes, und jeder Eintrag traegt seinen Beleg (W7). Ein offener Haken dort ist
    #    derselbe Fehler wie ein `[x]` im TODO, nur spiegelverkehrt -- und er faellt
    #    niemandem auf, weil ihn niemand sucht.
    d = WURZEL / "DONE.md"
    if d.is_file():
        dt = d.read_text()
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
        cwd=WURZEL, capture_output=True, text=True,
    )
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
    r = subprocess.run(["./pruefe-syntax.sh"], cwd=WURZEL, capture_output=True, text=True)
    aus = r.stdout
    regeln = re.search(r"EBNF: (\d+) Regeln", aus)
    terme = re.search(r"Wortschatz: (\d+) EBNF-Terminale, (\d+) Tabellenwoerter", aus)
    r_heute = regeln.group(1) if regeln else "?"
    t_heute = terme.group(1) if terme else "?"
    return [
        (r"\*\*(\d+) (?:Regeln, 0 offen|rules, 0 open)", r_heute, "EBNF-Regeln"),
        (r"(\d+) (?:Terminale gegen|terminals against)", t_heute, "EBNF-Terminale"),
        (r"\((?:heute|today) (\d+) / \d+\)", r_heute, "EBNF-Regeln (heute-Klammer)"),
        (r"\((?:heute|today) \d+ / (\d+)\)", t_heute, "EBNF-Terminale (heute-Klammer)"),
    ]


def pruefe_readme(text=None):
    """**Der README traegt eine Kennzahlentafel, und niemand hielt sie nach.**

    Gefunden 2026-08-19: acht Zahlen standen falsch da -- *90 Absagen* (124), *130 Regeln*
    (139), *195 / 195* (206), *19 Schablonen, 4 bewiesen* (20 / 9), *8 Waechter* (10),
    *19 saubere Beispiele* (31), *69 Giftdateien* (104), *79 Tests* (126).

    **Dieselbe Klasse wie die sechs `gap:`-Zeilen und die acht widerrufenen Saetze:** die
    Zahl wurde gepflegt, die Quelle nicht. *Und der README ist die Datei, die ein Fremder
    ZUERST liest.*

    Geprueft wird nur, was sich ohne Uebersetzerlauf zaehlen laesst. Testzahl und
    Mutationsquote kommen aus einem Lauf und tragen darum ihr Messdatum im Text.
    """
    r = WURZEL / "README.md"
    if text is None:
        if not r.is_file():
            return []
        text = r.read_text()
    befunde = []

    n_bsp = len(list((WURZEL / "beispiele").glob("*.gab")))
    n_gift = len(list((WURZEL / "beispiele/gift").glob("*.gab")))
    n_waechter = len(list(WURZEL.glob("pruefe-*.py"))) + len(list(WURZEL.glob("pruefe-*.sh")))

    k = subprocess.run(["./pruefe-kennungen.py"], cwd=WURZEL, capture_output=True, text=True)
    m = re.search(r"Kennungen: (\d+) vergeben", k.stdout)
    n_kenn = m.group(1) if m else "?"

    s = subprocess.run(["cargo", "run", "--quiet", "--bin", "gabbro", "--", "schablonen"],
                       cwd=WURZEL, capture_output=True, text=True)
    # **Englisch seit 2026-08-19** -- die Sprachflaeche von Gabbro ist es, und dieser Leser
    # hing an der deutschen Fassung. *Ein Waechter, der die Ausgabe eines Werkzeugs liest,
    # gehoert zu dessen Sprache; er hat sie hier zwei Stunden lang nicht gehabt.*
    m = re.search(r"(\d+) templates, \d+ of them unproved, (\d+) machine-checked", s.stdout)
    n_schab, n_bew = (m.group(1), m.group(2)) if m else ("?", "?")

    y = subprocess.run(["./pruefe-syntax.sh"], cwd=WURZEL, capture_output=True, text=True)
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
    for muster, heute, was in fuer:
        for t in re.finditer(muster, text):
            if t.group(1) != str(heute):
                befunde.append(f"README: '{t.group(1)}' als {was} -- es sind {heute}")
    return befunde


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

    # **Und die README-Haelfte, in beide Richtungen.** Eine Kennzahlentafel, die keiner
    # nachhaelt, faellt sonst genauso lautlos aus wie die acht Zahlen, die sie ersetzt hat.
    echt = (WURZEL / "README.md").read_text()
    # **Die Sprechprobe muss die HEUTIGE Zahl verstellen, nicht eine von gestern.**
    # *Gefunden 2026-08-19: der Korpus wuchs auf 32, und die Probe verstellte weiter „31" --
    # sie fand nichts und meldete damit, sie koenne nicht messen.* Der Waechter faengt seinen
    # eigenen Fall, weil er in BEIDE Richtungen prueft.
    n_bsp_heute = len(list((WURZEL / "beispiele").glob("*.gab")))
    verstellt = echt.replace("%d clean examples" % n_bsp_heute, "17 clean examples")
    r_gift = pruefe_readme(verstellt)
    r_sauber = pruefe_readme(echt)
    print(f"  README-Gift:   {len(r_gift)} Befunde", end="")
    print(" -- ok" if r_gift else " -- GESCHEITERT (verstellte Zahl kam durch)")
    print(f"  README sauber: {len(r_sauber)} Befunde", end="")
    print(" -- ok" if not r_sauber else " -- GESCHEITERT (falsches Rot)")

    return len(b_gift) >= 5 and not b_sauber and bool(r_gift) and not r_sauber


def main():
    zahlen = heutige_zahlen()
    print("== Sprechprobe des Waechters ==")
    if not sprechprobe(zahlen):
        return 1
    if "--probe" in sys.argv:
        return 0

    r_befunde = pruefe_readme()
    print("\n== README.md ==")
    if r_befunde:
        for b in r_befunde:
            print(f"  {b}")
        print(f"== README: {len(r_befunde)} stehengebliebene Zahlen ==")
    else:
        print("  Kennzahlentafel deckt sich mit dem Gegenstand.")

    text = (WURZEL / "TODO.md").read_text()
    befunde = pruefe(text, zahlen)
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
