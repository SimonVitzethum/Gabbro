#!/usr/bin/env python3
"""**Jede Kennzahl im Ordner nennt den Befehl, der sie nachrechnet -- und der laeuft hier.**

Am 2026-08-20 wichen an einem einzigen Tag fuenf Buchungen vom Gegenstand ab:

* die Registerklasse war *durch `R002`/`R003`* gebucht -- die pruefen Zeigerrechte;
* «B33» stand als Zusage da und der Pruefer tat das Gegenteil;
* «B26» stand als *„kein benannter Ausgang"* und hat gar keinen Leser;
* der Netzwerkstack stand als blockiert und war offen;
* `H = 2` war eine Zahl, die niemand nachgerechnet hatte.

**Vier zu optimistisch, einer zu pessimistisch -- und die Richtungsmischung ist die
Diagnose.** Eine Buchfuehrung, die nur schoente, waere Selbstbetrug und braeuchte Misstrauen
als Gegengewicht. Eine, die in BEIDE Richtungen abweicht, **veraltet** bloss. *Dagegen hilft
kein Misstrauen, sondern ein Befehl, der die Zahl neu ableitet.*

> **Eine Zelle, die auf eine REGEL zeigt, prueft niemand nach. Ein BEFEHL, der eine Zahl
> druckt, ist nachrechenbar.**

Dieses Werkzeug ist das Register dieser Befehle. Je Eintrag: die Datei, das Muster, unter dem
die Zahl dort steht, der Befehl und der Auszug daraus. Weicht eines ab, faellt es hier.

    ./pruefe-zahlen.py [--reichweite]

**Und die zweite Haelfte, ohne die die erste sich selbst lobt:** das Werkzeug zaehlt die
Kennzahlen, die es NICHT bewacht. Eine fettgedruckte Zahl in einer Tabellenzelle ist die
Form, in der dieser Ordner seine Kennzahlen schreibt; wie viele davon keinen Befehl haben,
steht am Ende. *Ein Waechter, der nur seine eigenen Eintraege zaehlt, misst seine eigene
Leseweite* (W16).

**Der README wird NICHT hier bewacht, sondern in `pruefe-todo.py`.** Zwei Register ueber
derselben Sache sind W7; dies hier nennt das andere, statt es zu verdoppeln.
"""
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent
FRIST = 180  # Sekunden je Befehl. Ein Waechter ohne Frist meldet einen Haenger als „laeuft".

# Je Eintrag: (Datei, Muster mit EINER Gruppe = die Zahl im Text, Befehl, Auszug mit EINER
# Gruppe = die Zahl aus dem Lauf, was die Zahl bedeutet)
EINTRAEGE = [
    (
        "dokumente/PFLICHTEN.md",
        r"of which \*\*`H = (\d+)` are K\*\*",
        ["./zaehle-pflichten.py", "--haengend"],
        r"^\s+H\s+(\d+)\s*$",
        "H -- haengende Klempnereipflichten",
    ),
    (
        "dokumente/PLAN.md",
        r"\| `H` \| 0 \| \*\*(\d+)\*\*",
        ["./zaehle-pflichten.py", "--haengend"],
        r"^\s+H\s+(\d+)\s*$",
        "H in der K100-Statustafel",
    ),
    (
        "dokumente/PLAN.md",
        r"\| `A` \| 19 \| \*\*(\d+)\*\*",
        ["sh", "-c", "cargo run -q --bin gabbro -- annahmen beispiele/*.gab"],
        r"^-- (\d+) Annahmen",
        "A -- Annahmen mit Sonde oder Grund",
    ),
    (
        "dokumente/PLAN.md",
        r"\| `L` \| ≤ 4 \| \*\*(\d+)\*\*",
        ["cargo", "run", "-q", "--bin", "gabbro", "--", "schablonen"],
        r"CARRIED unproved \(the compiler rests on them\): (\d+)",
        "L -- getragen und unbewiesen",
    ),
    (
        "dokumente/PLAN.md",
        r"daneben aber \*\*(\d+) Prämissen ohne Pass\*\*",
        ["cargo", "run", "-q", "--bin", "gabbro", "--", "schablonen"],
        r"PREMISES WITHOUT A PASS \(tooth 3\): (\d+)",
        "Praemissen ohne Pass (Zahn 3)",
    ),
    (
        "README.md",
        r"\*\*(\d+) of 23 instruments carry all three requirements\*\*",
        ["./pruefe-waechter.py"],
        r"== (\d+) von \d+ tragen alle drei ==",
        "Instrumente mit Frist, Sprechprobe und rotem Abbruch",
    ),
    (
        "README.md",
        r"of (\d+) instruments carry all three",
        ["./pruefe-waechter.py"],
        r"von (\d+) tragen alle drei",
        "Instrumente insgesamt",
    ),
    (
        "TODO.md",
        r"heute (\d+) Codes, null Sätze",
        ["./pruefe-kennungen.py"],
        r"Kennungen: (\d+) vergeben",
        "Absagekennungen",
    ),
    (
        "TODO.md",
        r"\*\*(\d+) fremde Rümpfe im Korpus, 0 sprechen ihre Pflicht aus\.\*\*",
        ["sh", "-c",
         "cargo run -q --bin gabbro -- zeugnis beispiele/*.gab | "
         "grep -oE '[0-9]+ foreign bodies' | awk '{s+=$1} END {print s\" fremde\"}'"],
        r"^(\d+) fremde",
        "fremde Ruempfe im Korpus",
    ),
    (
        "TODO.md",
        r"Kombinationen\*\*: (\d+) blinde Zellen",
        ["sh", "-c",
         "cargo run -q --bin gabbro -- blindstellen beispiele/*.gab -- beispiele/gift/*.gab"],
        r"== (\d+) blind",
        "blinde Zellen (Form x Stellung)",
    ),
    (
        "TODO.md",
        r"blinde Zellen von (\d+)\.",
        ["sh", "-c",
         "cargo run -q --bin gabbro -- blindstellen beispiele/*.gab -- beispiele/gift/*.gab"],
        r"of (\d+) pairs",
        "Zellen der Tafel insgesamt",
    ),
]

# **Die Reichweite.** Eine fettgedruckte Zahl in einer Tabellenzelle ist die Form, in der
# dieser Ordner seine Kennzahlen schreibt. Was davon keinen Befehl hat, ist unbewacht -- und
# das ist keine Schande, sondern die Zahl, die dieses Werkzeug ueber sich selbst schuldet.
BEWACHTE_DATEIEN = [
    "dokumente/PFLICHTEN.md",
    "dokumente/PLAN.md",
    "dokumente/MESSUNGEN.md",
    "dokumente/SYNTAX.md",
    "TODO.md",
]
KENNZAHL = re.compile(r"\|\s*\*\*([0-9][0-9  .,]*)\*\*\s*(?:\||$)")


def lauf(befehl):
    """Ein Befehl mit Frist. **Ein Haenger sieht aus wie „laeuft noch", nicht wie ein Befund.**"""
    try:
        r = subprocess.run(befehl, cwd=W, capture_output=True, text=True, timeout=FRIST)
    except subprocess.TimeoutExpired:
        return None, f"FRIST ({FRIST} s) ueberschritten"
    if "error[E" in r.stderr or "could not compile" in r.stderr:
        return None, "der Pruefer baut nicht -- es wurde NICHTS gemessen"
    return r.stdout, None


ZWISCHEN = {}


def pruefe_eintraege(verstellen=None):
    """Alle Eintraege gegen ihren Befehl.

    `verstellen` verstellt die Zahl IM TEXT (nur im Speicher) -- das ist die Sprechprobe.
    **Ein Waechter, der nicht rot werden kann, misst nichts** (R14).
    """
    befunde, geprueft, bewacht = [], 0, {}
    zwischenspeicher = ZWISCHEN
    for nr, (datei, muster, befehl, auszug, was) in enumerate(EINTRAEGE):
        p = W / datei
        if not p.is_file():
            befunde.append(f"{datei}: fehlt -- es wird NICHT null gezaehlt")
            continue
        text = p.read_text(encoding="utf-8")
        if verstellen is not None and nr == verstellen:
            t = re.search(muster, text)
            if t:
                text = (text[: t.start(1)] + "999999" + text[t.end(1) :])
        treffer = re.search(muster, text)
        if not treffer:
            befunde.append(f"{datei}: das Muster fuer „{was}\" trifft nichts mehr -- "
                           f"die Zahl ist umformuliert und damit UNBEWACHT")
            continue
        schluessel = tuple(befehl)
        if schluessel not in zwischenspeicher:
            zwischenspeicher[schluessel] = lauf(befehl)
        ausgabe, fehler = zwischenspeicher[schluessel]
        if fehler:
            befunde.append(f"{datei} / {was}: {fehler}")
            continue
        m2 = re.search(auszug, ausgabe, re.M)
        if not m2:
            befunde.append(f"{datei} / {was}: der Befehl druckt die Zahl nicht mehr "
                           f"({' '.join(befehl)[:60]}) -- der Suchweg ist ab")
            continue
        geprueft += 1
        im_text = treffer.group(1).replace(" ", "").replace(" ", "")
        aus_lauf = m2.group(1)
        bewacht.setdefault(datei, set()).add(im_text)
        if im_text != aus_lauf:
            befunde.append(f"{datei}: „{was}\" steht als {im_text}, der Lauf sagt {aus_lauf}")
    return befunde, geprueft, bewacht


def main():
    # **Die Sprechprobe zuerst, und in beide Richtungen.** Eine verstellte Zahl MUSS fallen,
    # eine unverstellte NICHT -- sonst misst dieses Werkzeug seine eigene Nachsicht.
    print("== Sprechprobe des Waechters ==")
    stumm = []
    for nr in range(len(EINTRAEGE)):
        b, _, _ = pruefe_eintraege(verstellen=nr)
        if not any("der Lauf sagt" in x for x in b):
            stumm.append(EINTRAEGE[nr][4])
    if stumm:
        print(f"  GESCHEITERT -- {len(stumm)} Eintraege bleiben stumm, wenn ihre Zahl verstellt wird:")
        for x in stumm:
            print(f"     {x}")
        return 1
    print(f"  ok -- alle {len(EINTRAEGE)} Eintraege fallen, wenn ihre Zahl verstellt wird")
    print()

    befunde, geprueft, bewacht = pruefe_eintraege()
    print("== Kennzahlen gegen ihren Befehl ==")
    print(f"  {geprueft} von {len(EINTRAEGE)} Eintraegen nachgerechnet")
    for b in befunde:
        print(f"  BEFUND  {b}")

    # Die zweite Haelfte: wie weit reicht dieses Register?
    offen = []
    for datei in BEWACHTE_DATEIEN:
        p = W / datei
        if not p.is_file():
            continue
        for zeile in p.read_text(encoding="utf-8").splitlines():
            for m in KENNZAHL.finditer(zeile):
                z = m.group(1).replace(" ", "").replace(" ", "")
                if z not in bewacht.get(datei, set()):
                    offen.append((datei, z, zeile.strip()[:70]))
    print()
    print("== Reichweite: was dieses Register NICHT bewacht ==")
    print(f"  {geprueft} Kennzahlen mit Befehl, {len(offen)} fettgedruckte Zahlen in "
          f"Tabellenzellen ohne einen")
    if "--reichweite" in sys.argv:
        for d, z, zeile in offen:
            print(f"     {d}:{z}  {zeile}")
    else:
        print("     (`--reichweite` listet sie einzeln)")
    print()
    print("  **Und was das NICHT heisst:** eine unbewachte Zahl ist nicht falsch, sie ist")
    print("  unnachrechenbar. Genau das war der Zustand, in dem am 2026-08-20 fuenf Buchungen")
    print("  vom Gegenstand abwichen -- vier zu optimistisch, eine zu pessimistisch.")
    print("  *Eine Buchfuehrung, die in beide Richtungen abweicht, veraltet; sie luegt nicht.*")
    print()
    print("  Der README steht nicht in diesem Register, sondern in `pruefe-todo.py`.")
    print("  Zwei Register ueber derselben Sache sind W7.")

    return 1 if befunde else 0


if __name__ == "__main__":
    sys.exit(main())
