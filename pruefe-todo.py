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
PRUEFERPLAN = {
    "P0": "Wiederholungsmessung auf Papier",
    "P1": "Grammatikvereinigung",
    "P2": "Lexer+Parser",
    "P3": "M1+V1–V3",
    "P4": "M2 + Erzeuger-Schablone",
    "P5": "C-Emission",
    "P6": "Paarungs-Pass",
    "P7": "ein Caprock-Modul end-to-end",
}


def pruefe(text, zahlen):
    """Gibt die Liste der Befunde. Leer heisst: die Liste stimmt ueber sich selbst."""
    befunde = []

    # 1. Behauptet die Datei „ausschliesslich Offenes" und fuehrt Erledigtes?
    if "Ausschliesslich Offenes" in text or "ausschliesslich Offenes" in text:
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
        (r"^- \[ \] \*\*[^\n]*`?narrow`?-Vollzaehlung", "narrow-Vollzaehlung"),
        (r"^- \[ \] \*\*Variable L[äa]ngen", "Variable Laengen"),
        (r"^- \[ \] \*\*Versionsevolution", "Versionsevolution"),
    ]
    for muster, name in themen:
        n = len(re.findall(muster, text, re.M))
        if n > 1:
            befunde.append(f"'{name}' steht {n} mal als eigener Punkt")

    # 5. **Passzahlen gegen `gabbro paesse`.** Der Abgleich vom 2026-08-14 fand „Sechs der
    #    neun Paesse fehlen", wo es fuenf ganze und zwei halbe waren. Eine Zahl ueber den
    #    eigenen Uebersetzer, die niemand gegen den Uebersetzer haelt, ist Falle 80.
    ganz, halb = paesse_heute()
    if ganz is not None:
        for m in re.finditer(r"\*\*(\w+) der neun Paesse fehlen ganz\*\*", text):
            if ZAHLWORT.get(m.group(1).lower()) != ganz:
                befunde.append(
                    f"Passzahl stimmt nicht: '{m.group(1)} der neun Paesse fehlen ganz', "
                    f"`gabbro paesse` sagt {ganz}"
                )
        for m in re.finditer(r"\*\*(\w+) sind nur\s+teilweise gebaut\*\*", text):
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
    for m in re.finditer(r"(\d+) saubere Beispiele", text):
        if int(m.group(1)) != n_bsp:
            befunde.append(f"'{m.group(1)} saubere Beispiele' -- es sind {n_bsp}")
    for m in re.finditer(r"(\d+) Giftproben", text):
        if int(m.group(1)) != n_gift:
            befunde.append(f"'{m.group(1)} Giftproben' -- es sind {n_gift}")

    return befunde


ZAHLWORT = {
    "eine": 1, "eins": 1, "zwei": 2, "drei": 3, "vier": 4, "fuenf": 5, "fünf": 5,
    "sechs": 6, "sieben": 7, "acht": 8, "neun": 9,
}


def paesse_heute():
    """Wieviele Paesse fehlen ganz, wieviele sind halb? Aus `gabbro paesse`, nicht von Hand."""
    r = subprocess.run(
        ["cargo", "run", "-q", "-p", "gabbro-cli", "--", "paesse"],
        cwd=WURZEL, capture_output=True, text=True,
    )
    if r.returncode != 0:
        return None, None
    # `gabbro paesse` markiert die Zeilen mit `OFFEN` bzw. `TEIL` -- die Zahlen aus
    # der Ausgabe zu nehmen statt aus der Prosa ist der ganze Zweck dieser Pruefung.
    return (
        len(re.findall(r"^  OFFEN ", r.stdout, re.M)),
        len(re.findall(r"^  TEIL  ", r.stdout, re.M)),
    )


def heutige_zahlen():
    """Was die Waechter heute melden -- gegen die Zahlen in der Prosa."""
    r = subprocess.run(["./pruefe-syntax.sh"], cwd=WURZEL, capture_output=True, text=True)
    aus = r.stdout
    regeln = re.search(r"EBNF: (\d+) Regeln", aus)
    terme = re.search(r"Wortschatz: (\d+) EBNF-Terminale, (\d+) Tabellenwoerter", aus)
    return [
        (r"\*\*(\d+) Regeln, 0 offen", regeln.group(1) if regeln else "?", "EBNF-Regeln"),
        (r"(\d+) Terminale gegen", terme.group(1) if terme else "?", "EBNF-Terminale"),
    ]


def sprechprobe(zahlen):
    """In beide Richtungen: eine kaputte Liste MUSS fallen, eine saubere NICHT."""
    gift = """# Probe

- [x] **Etwas Erledigtes** steht hier.
- [ ] **Die `narrow`-Vollzaehlung** einmal.
- [ ] **Die `narrow`-Vollzaehlung** zweimal.

## P1 — `check` ohne Sprache

**Ausschliesslich Offenes.**
"""
    sauber = """# Probe

- [ ] **Etwas Offenes** steht hier.

## `check` ohne Sprache

**Ausschliesslich Offenes.**
"""
    b_gift = pruefe(gift, zahlen)
    b_sauber = pruefe(sauber, zahlen)
    print(f"  Giftliste:    {len(b_gift)} Befunde", end="")
    print(" -- ok" if len(b_gift) >= 3 else " -- GESCHEITERT (der Waechter ist stumm)")
    for b in b_gift:
        print(f"     {b}")
    print(f"  Saubere Liste: {len(b_sauber)} Befunde", end="")
    print(" -- ok" if not b_sauber else " -- GESCHEITERT (falsches Rot)")
    return len(b_gift) >= 3 and not b_sauber


def main():
    zahlen = heutige_zahlen()
    print("== Sprechprobe des Waechters ==")
    if not sprechprobe(zahlen):
        return 1
    if "--probe" in sys.argv:
        return 0

    text = (WURZEL / "TODO.md").read_text()
    befunde = pruefe(text, zahlen)
    print("\n== TODO.md ==")
    if not befunde:
        offen = len(re.findall(r"^- \[ \]", text, re.M))
        print(f"  {offen} offene Punkte, keine Doppelung, keine Etikettenkollision,")
        print("  kein Erledigtes, keine stehengebliebene Zahl.")
        print("== TODO: ALL PASS ==")
        return 0
    for b in befunde:
        print(f"  {b}")
    print(f"== TODO: {len(befunde)} BEFUNDE ==")
    return 1


if __name__ == "__main__":
    sys.exit(main())
