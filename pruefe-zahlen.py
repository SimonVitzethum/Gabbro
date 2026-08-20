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
        "messung/fragmente/README.md",
        r"(\d+) von 10 prüfen sauber",
        ["./zaehle-fragmente.py"],
        r"^  (\d+) von 10 pruefen sauber",
        "vervollstaendigte Fragmente, die sauber pruefen",
    ),
    (
        "messung/fragmente/README.md",
        r"(\d+) von 10 senken ab",
        ["./zaehle-fragmente.py"],
        r"^  (\d+) von 10 senken ab",
        "vervollstaendigte Fragmente, die absenken",
    ),
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
        "dokumente/MESSUNGEN.md",
        r"`N_folgenlos` — ein `narrow`, dessen Entfernung nichts ändert, ist Zierde\. Heute\n> \*\*(\d+)\*\*",
        ["./zaehle-bereichspflichten.py"],
        r"N_folgenlos = (\d+)",
        "N_folgenlos -- folgenlose `narrow`-Stellen",
    ),
    (
        "README.md",
        r"\*\*(\d+) of \d+ instruments carry all four requirements\*\*",
        ["./pruefe-waechter.py"],
        r"== (\d+) von \d+ tragen die drei STATISCHEN ==",
        "Instrumente mit Frist, Sprechprobe und rotem Abbruch",
    ),
    (
        "README.md",
        r"of (\d+) instruments carry all four",
        ["./pruefe-waechter.py"],
        r"von (\d+) tragen die drei STATISCHEN",
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

# **Nicht alle unbewachten Zahlen sind gleich viel wert.**
#
# Eine Zahl, die in einer ZUSAGE oder einem VERGLEICH steht, traegt eine Behauptung nach
# aussen -- Vertrauensflaeche, Deckungsgrad, das Verhaeltnis gegen seL4. Eine, die einen
# Zwischenstand beschreibt, traegt nichts. **Wer die naechsten zwoelf nach diesem Kriterium
# waehlt statt nach Aufwand, senkt das Risiko schneller als die Zahl.**
#
# *Und was diese Einteilung NICHT ist:* eine Messung. Sie liest Stichwoerter in der Zeile und
# irrt in beide Richtungen -- sie sortiert eine Arbeitsliste, sie spricht nichts frei (W10).
TRAEGT = re.compile(
    "seL4|CompCert|Verus|Rust|%|Vertrauen|trust|Zusage|promise|guarantee|bewiesen|proved|"
    "unproved|Schablone|template|Deckung|coverage|Abdeckung|Anteil|ratio|" + "Verh\u00e4ltnis|"
    "Annahme|assumption|blind|Mutation|gefangen|caught|Klempnerei|plumbing|"
    "h\u00e4ngend|hanging|Beweis|proof",
    re.I,
)


def kein_selbstbezug():
    """**Ein Register, das seine eigene Ausgabe enthaelt, hat einen FIXPUNKT statt einer
    Messung.**

    Am 2026-08-20 habe ich die zwei Zahlen, die dieses Werkzeug ueber sich selbst druckt
    (bewachte und unbewachte Kennzahlen), in sein eigenes Register eingetragen. Der Eintrag
    ruft das Werkzeug, das Werkzeug prueft den Eintrag.

    **Und der Ruecklauf ist nicht das Schlimme daran.** Ein Fixpunkt, der TERMINIERT, waere
    gefaehrlicher: die Zahl stimmt dann immer, **unabhaengig davon, ob irgendetwas gemessen
    wurde**. *Das ist die Ausweg-Zusicherung aus R15 in ihrer reinsten Form -- „erfuellt, weil
    nichts geschah" -- eine Ebene ueber dem Werkzeug.*

    Die Regel ist mechanisch pruefbar und billig, und darum steht sie hier als Code und nicht
    als Satz: **kein Registereintrag darf einen Befehl nennen, der das registerfuehrende
    Werkzeug selbst ist.**
    """
    ich = pathlib.Path(__file__).name
    schlecht = []
    for datei, _m, befehl, _a, was in EINTRAEGE:
        if any(ich in str(t) for t in befehl):
            schlecht.append(f"{datei} / {was}")
    return schlecht


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
    # **Der Riegel gegen den Fixpunkt, vor allem anderen.**
    if schlecht := kein_selbstbezug():
        print("== SELBSTBEZUG -- das Register nennt sich selbst als Befehl ==")
        for x in schlecht:
            print(f"  {x}")
        print("  **Ein Register, das seine eigene Ausgabe enthaelt, hat einen FIXPUNKT statt")
        print("  einer Messung**: die Zahl stimmt dann immer, unabhaengig davon, ob irgendetwas")
        print("  gemessen wurde. *Die Ausweg-Zusicherung aus R15, eine Ebene ueber dem")
        print("  Werkzeug.* Die zwei eigenen Zahlen tragen ihr Datum, wie jede aus einem Lauf.")
        return 1

    # **Die Sprechprobe zuerst, und in beide Richtungen.** Eine verstellte Zahl MUSS fallen,
    # eine unverstellte NICHT -- sonst misst dieses Werkzeug seine eigene Nachsicht.
    print("== Sprechprobe des Waechters ==")
    # **Auch der Fixpunktriegel muss beissen koennen.** Ein Riegel, der nie zuschlaegt, ist
    # von einem fehlenden nicht zu unterscheiden -- genau das war die Zeitgrenze in
    # `pruefe-beweise.sh` bis heute frueh.
    EINTRAEGE.append(("TODO.md", r"(\d+)", ["./" + pathlib.Path(__file__).name], r"(\d+)", "Probe"))
    biss = bool(kein_selbstbezug())
    EINTRAEGE.pop()
    print("  Fixpunktriegel: " + ("ok (ein selbstbezueglicher Eintrag faellt)" if biss
                                  else "GESCHEITERT -- er laesst sich selbst durch"))
    if not biss:
        return 1
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
                    offen.append((datei, z, zeile.strip()[:70], bool(TRAEGT.search(zeile))))
    print()
    print("== Reichweite: was dieses Register NICHT bewacht ==")
    traegt = [o for o in offen if o[3]]
    print(f"  {geprueft} Kennzahlen mit Befehl, {len(offen)} fettgedruckte Zahlen in "
          f"Tabellenzellen ohne einen")
    print(f"  davon TRAGEND (Zusage oder Vergleich): {len(traegt)}   "
          f"Zwischenstand: {len(offen) - len(traegt)}")
    print()
    print("  **Nicht alle unbewachten Zahlen sind gleich viel wert.** Eine, die in einer")
    print("  ZUSAGE oder einem VERGLEICH steht, traegt eine Behauptung nach aussen; eine, die")
    print("  einen Zwischenstand beschreibt, traegt nichts. *Wer die naechsten zwoelf nach")
    print("  diesem Kriterium waehlt statt nach Aufwand, senkt das Risiko schneller als die")
    print("  Zahl.* Die Einteilung liest Stichwoerter und irrt in beide Richtungen -- sie")
    print("  sortiert eine Arbeitsliste, sie spricht nichts frei (W10).")
    if "--reichweite" in sys.argv:
        print()
        for d, z, zeile, t in sorted(offen, key=lambda o: (not o[3], o[0])):
            print(f"     {'TRAEGT' if t else '  --  '}  {d}:{z}  {zeile}")
    else:
        print("     (`--reichweite` listet sie einzeln, tragende zuerst)")
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
