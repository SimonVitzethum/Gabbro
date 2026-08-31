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

    ./instrumente/pruefe-zahlen.py [--reichweite]

**Und die zweite Haelfte, ohne die die erste sich selbst lobt:** das Werkzeug zaehlt die
Kennzahlen, die es NICHT bewacht. Eine fettgedruckte Zahl in einer Tabellenzelle ist die
Form, in der dieser Ordner seine Kennzahlen schreibt; wie viele davon keinen Befehl haben,
steht am Ende. *Ein Waechter, der nur seine eigenen Eintraege zaehlt, misst seine eigene
Leseweite* (W16).

**Der README wird NICHT hier bewacht, sondern in `pruefe-todo.py`.** Zwei Register ueber
derselben Sache sind W7; dies hier nennt das andere, statt es zu verdoppeln.

**Der Fixpunktriegel reichte einen Schritt weit -- nachgezogen 2026-08-20.** W18 verbietet
einen Eintrag, dessen Befehl dieses Werkzeug NENNT. Der Ring der Laenge ZWEI lag daneben und
offen: `./instrumente/pruefe-waechter.py --lauf` fuehrt jeden leichten Waechter aus, und dieser hier ist
einer davon -- ein einziger Eintrag mit `--lauf` haette den Ring geschlossen, und der
Namensriegel haette ihn durchgelassen. *Seit heute haengt der Riegel an einer Marke in der
Prozessumgebung: sie wird an jeden Registerbefehl vererbt, und wer sie beim Start vorfindet,
ist von sich selbst gerufen worden.* **Er wird an einem echten Kindprozess gemessen, nicht
behauptet.**
"""
import os
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
FRIST = 180  # Sekunden je Befehl. Ein Waechter ohne Frist meldet einen Haenger als „laeuft".

# **Die Pflichten summiert -- `gabbro pflichten` druckt sie JE DATEI.** Eine Zahl ueber dem
# Korpus muss addiert werden, und diese Zeile ist der Suchweg dorthin.
PFLICHTEN_SUMME = (
    # **Carried over 2026-08-24**: since `refines` the header line carries a fifth column
    # (`R`, refinement). The old pattern no longer matched it and reported that the search
    # path was gone -- correctly, and that is exactly what the message is for.
    "cargo run -q --bin gabbro -- pflichten beispiele/*.gab 2>/dev/null | "
    "grep -oE '== [0-9]+ obligations: [0-9]+ refinement, [0-9]+ preservation, "
    "[0-9]+ postcondition, [0-9]+ foreign, [0-9]+ precondition' | "
    "awk '{o+=$2; r+=$4; p+=$6; q+=$8; f+=$10; v+=$12} END "
    "{print \"obl\", o, \"verfeinerung\", r, \"erhaltung\", p, \"nachbed\", q, \"fremd\", f, \"vorbed\", v}'"
)

# Je Eintrag: (Datei, Muster mit EINER Gruppe = die Zahl im Text, Befehl, Auszug mit EINER
# Gruppe = die Zahl aus dem Lauf, was die Zahl bedeutet)
EINTRAEGE = [
    (
        "messung/fragmente/README.md",
        r"(\d+) von 10 prüfen sauber",
        ["./instrumente/zaehle-fragmente.py"],
        r"^  (\d+) von 10 pruefen sauber",
        "vervollstaendigte Fragmente, die sauber pruefen",
    ),
    (
        "messung/fragmente/README.md",
        r"(\d+) von 10 senken ab",
        ["./instrumente/zaehle-fragmente.py"],
        r"^  (\d+) von 10 senken ab",
        "vervollstaendigte Fragmente, die absenken",
    ),
    (
        "TODO.md",
        r"Marke (\d+) — eine Ratsche, keine Zielzahl · 0 ohne Adresse",
        ["./instrumente/pruefe-schablonen.py"],
        r"^   Marke (\d+) -- eine Ratsche",
        "Zahn 3 -- Praemissen bewiesener Schablonen ohne Pass",
    ),
    (
        "messung/netz/README.md",
        r"(\d+) von 3 Proben grün",
        ["./instrumente/zaehle-netz.py"],
        r"^== (\d+) von 3 Proben gruen ==",
        "Netzstack gegen veroeffentlichte Vektoren",
    ),
    # --- The translation ratchet: source language, since 2026-08-21 ---
    #
    # **A half-translated source is worse than either pure form** -- that is literally the
    # finding this guardian was built from. So the remainder is measured, not estimated.
    (
        "TODO.md",
        r"\*\*(\d+) von \d+ Kommentarzeilen\*\* im Pruefer sind deutsch",
        ["./instrumente/pruefe-englisch.py"],
        r"^== Quellsprache: (\d+) von \d+ Kommentarzeilen",
        "deutsche Kommentarzeilen im Pruefer -- die Ratsche der Uebersetzung",
    ),
    # --- Der Vergabewaechter: eine Kennung, eine REGEL ---
    #
    # **Die zweite Zahl ist die teurere.** Sie sagt, wie viele Giftproben ihre
    # Deckungsaussage heute nicht halten koennen, weil ihre Kennung mehrdeutig ist.
    (
        "TODO.md",
        r"(\d+) Proben zeigen auf eine Kennung mit unaehnlichen Vergabestellen",
        ["./instrumente/pruefe-vergabe.py"],
        r"^== Was das RUECKWIRKEND kostet: (\d+) von \d+ Giftproben ==",
        "Giftproben auf einer mehrdeutigen Kennung",
    ),
    # --- PL.1: das Passregister, und seine Ratsche ---
    #
    # **Die Zahl „Kennungen ohne Satz" ist eine RATSCHE**, und eine Ratsche ohne Befehl ist
    # eine Absicht. *Sie hat am Tag ihrer Entstehung gebissen* -- der Registerbaum war acht
    # Commits aelter, und drei Kennungen aus Stufe 6 standen ohne Satz da.
    (
        "messung/PASSREGISTER.md",
        r"\| Sätze im Register \| \*\*(\d+)\*\* \|",
        ["./instrumente/pruefe-saetze.py"],
        r"^   (\d+) Saetze beanspruchen \d+ Kennungen",
        "Saetze im Passregister",
    ),
    (
        "messung/PASSREGISTER.md",
        r"\| \*\*Kennungen ohne Satz — die Ratsche\*\* \| \*\*(\d+)\*\* \|",
        ["./instrumente/pruefe-saetze.py"],
        r"^== Zahn 2: (\d+) von \d+ Kennungen ohne Satz ==",
        "Zahn 2 -- Kennungen ohne Satz",
    ),
    # --- Stufe 6, Teil E: die drei Zahlen, die den Bau von «B39» VERHINDERT haben ---
    #
    # **Eine Null, die einen Bau verhindert, muss nachrechenbar sein.** Sie ist die
    # leichteste Zahl, die spaeter jemand stillschweigend anders liest -- und drei Posten
    # dieses Ordners sind heute mit „nicht bauen" entschieden worden.
    # **`--exclude-dir=.claude` -- found 2026-08-24, and it was a GUARDIAN fault.**
    #
    # The registered command greps `-r ... .` from the repo root. Locally that root also holds
    # `.claude/worktrees/` -- agent worktrees, **4 369 further `.gab` files**, copies of the
    # corpus. The count read 46 where the corpus has 3, and 99 where it has 8.
    #
    # > *The number was right and the SEARCH PATH was wrong* -- and it showed as a guardian
    # > that went red locally and green on the server, over a byte-identical tree (`rsync`
    # > excludes the worktrees). **A guardian with two verdicts over one subject is W16.**
    #
    # `target/` excluded for the same reason, pre-emptively: it holds no `.gab` today, and a
    # search path that only happens to be right is one nobody notices going wrong.
    (
        "messung/TRAEGER-UND-HARDWARE.md",
        r"\| `walk`-Deklarationen im ganzen Korpus \| \*\*(\d+)\*\*",
        ["sh", "-c", r"grep -rh '^walk \|^ *walk ' --include=*.gab --exclude-dir=.claude --exclude-dir=target . | wc -l"],
        r"^\s*(\d+)\s*$",
        "walk-Deklarationen im Korpus",
    ),
    (
        "messung/TRAEGER-UND-HARDWARE.md",
        r"\| `group`-Deklarationen \| \*\*(\d+)\*\*",
        ["sh", "-c", r"grep -rh '^group \|^ *group ' --include=*.gab --exclude-dir=.claude --exclude-dir=target . | wc -l"],
        r"^\s*(\d+)\s*$",
        "group-Deklarationen im Korpus",
    ),
    # **Entscheidung 12 ruht auf diesen zwei Zahlen** -- und bis zum 2026-08-21 waren sie von
    # Hand genommen. Die NULL ist die tragende: sie ist der gemessene Bedarf, gegen den
    # `locks ordered` gestorben ist.
    (
        "TODO.md",
        r"(\d+) `@version`-Textstellen in Korpus \+ FRAGMENTE",
        ["./instrumente/zaehle-formate.py"],
        r"^  (\d+) @version-Textstellen in Korpus \+ FRAGMENTE",
        "`@version`-Textstellen -- die Menge, auf die sich Entscheidung 12 beruft",
    ),
    (
        "TODO.md",
        r"(\d+) Formate mit einer zweiten Fassung",
        ["./instrumente/zaehle-formate.py"],
        r"^  (\d+) Formate mit einer zweiten Fassung",
        "gemessene Formatentwicklungen -- die NULL, die die Absage traegt",
    ),
    (
        "TODO.md",
        r"(\d+) VERSCHIEDENE Deklarationen",
        ["./instrumente/zaehle-formate.py"],
        r"^  (\d+) verschiedene @version-Deklarationen",
        "verschiedene `@version`-Deklarationen -- die 14 zaehlt sieben doppelt",
    ),
    # **Entscheidung 10 -- die Zaehlung, die vor dem Bau steht.** Sie ist NULL, und eine Null
    # ohne Befehl ist die leichteste Zahl, die man spaeter stillschweigend anders liest.
    (
        "TODO.md",
        r"(\d+) Traversierungsruempfe stehen heute im Korpus",
        ["./instrumente/zaehle-traversierungen.py"],
        r"^  (\d+) Traversierungsruempfe stehen heute im Korpus",
        "Traversierungsruempfe im Korpus -- das N zur Duplikatzahl (W11)",
    ),
    (
        "TODO.md",
        r"(\d+) duplizierte Ruempfe",
        ["./instrumente/zaehle-traversierungen.py"],
        r"^  (\d+) duplizierte Ruempfe -- das ist der gemessene Bedarf",
        "duplizierte Traversierungsruempfe -- der gemessene Bedarf fuer Generizitaet",
    ),
    (
        "README.md",
        r"may fall\*\* — (\d+) and \d+ clause sites",
        ["./instrumente/zaehle-zeremonie.py"],
        r"^  \d+ von (\d+) Stellen duerfen sinken",
        "Zeremoniestellen des Lehrkorpus, in der Kennzahlentafel",
    ),
    (
        "README.md",
        r"may fall\*\* — \d+ and (\d+) clause sites",
        ["./instrumente/zaehle-zeremonie.py"],
        r"^  echter Code: \d+ von (\d+) Stellen duerfen sinken",
        "Zeremoniestellen des echten Codes, in der Kennzahlentafel",
    ),
    (
        "messung/ZEREMONIE.md",
        r"\| \*\*echter Code\*\* .*?\| (\d+) von 109",
        ["./instrumente/zaehle-zeremonie.py"],
        r"^  echter Code: (\d+) von \d+ Stellen duerfen sinken",
        "Zeremoniestellen im ECHTEN Code, die sinken duerfen",
    ),
    (
        "messung/ZEREMONIE.md",
        r"(\d+) von \d+ Stellen dürfen sinken",
        ["./instrumente/zaehle-zeremonie.py"],
        r"^  (\d+) von \d+ Stellen duerfen sinken",
        "Zeremoniestellen, die sinken duerfen -- Ziel 3",
    ),
    (
        "messung/ZEREMONIE.md",
        r"\d+ von (\d+) Stellen dürfen sinken",
        ["./instrumente/zaehle-zeremonie.py"],
        r"^  \d+ von (\d+) Stellen duerfen sinken",
        "Zeremoniestellen insgesamt -- das N zur Quote (W11)",
    ),
    (
        "messung/ZEREMONIE.md",
        r"\*\*(\d+) Regeln, 14 vom Korpus",
        ["./instrumente/zaehle-zeremonie.py"],
        r"^  (\d+) Regeln in der Tafel",
        "Regeln der Kalibriertafel -- jede mit Grund",
    ),
    (
        "dokumente/PFLICHTEN.md",
        r"of which \*\*`H = (\d+)` are K\*\*",
        ["./instrumente/zaehle-pflichten.py", "--haengend"],
        r"^\s+H\s+(\d+)\s*$",
        "H -- haengende Klempnereipflichten",
    ),
    (
        "dokumente/PLAN.md",
        r"\| `H` \| 0 \| \*\*(\d+)\*\*",
        ["./instrumente/zaehle-pflichten.py", "--haengend"],
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
        ["./instrumente/zaehle-bereichspflichten.py"],
        r"N_folgenlos = (\d+)",
        "N_folgenlos -- folgenlose `narrow`-Stellen",
    ),
    (
        "README.md",
        r"\*\*(\d+) of \d+ instruments carry all five requirements\*\*",
        ["./instrumente/pruefe-waechter.py"],
        r"== (\d+) von \d+ tragen die vier STATISCHEN ==",
        "Instrumente mit Frist, Sprechprobe und rotem Abbruch",
    ),
    (
        "README.md",
        r"of (\d+) instruments carry all five",
        ["./instrumente/pruefe-waechter.py"],
        r"von (\d+) tragen die vier STATISCHEN",
        "Instrumente insgesamt",
    ),
    (
        "TODO.md",
        # **Carried over 2026-08-23**: the sentence "heute N Codes, null Saetze" became false
        # with PL.1 and was replaced. *The pattern moved with it* -- a pattern that loses its
        # subject reports nothing and looks exactly like a pass.
        r"Sätze über (\d+) Codes",
        ["./instrumente/pruefe-kennungen.py"],
        r"Kennungen: (\d+) vergeben",
        "Absagekennungen",
    ),
    (
        "TODO.md",
        r"\*\*(\d+) fremde Rümpfe im Korpus, \d+ sprechen ihre Pflicht aus",
        ["sh", "-c",
         "cargo run -q --bin gabbro -- zeugnis beispiele/*.gab | "
         "grep -oE '[0-9]+ foreign bodies' | awk '{s+=$1} END {print s\" fremde\"}'"],
        r"^(\d+) fremde",
        "fremde Ruempfe im Korpus",
    ),
    # **Die ZWEITE Zahl derselben Zeile stand bis zum 2026-08-21 als Literal im Muster
    # darueber** -- also unbewacht, und sie sah bewacht aus. Sie war falsch (0 statt 10).
    # *Dieselbe Klasse wie W16: ein Waechter, dessen Muster die Antwort schon enthaelt,
    # prueft seine eigene Erwartung.*
    (
        "TODO.md",
        r"fremde Rümpfe im Korpus, (\d+) sprechen ihre Pflicht aus",
        ["sh", "-c",
         "cargo run -q --bin gabbro -- zeugnis beispiele/*.gab | "
         "grep -oE '\\([0-9]+ state their duty\\)' | grep -oE '[0-9]+' | "
         "awk '{s+=$1} END {print s\" sprechen\"}'"],
        r"^(\d+) sprechen",
        "fremde Ruempfe, die ihre Pflicht AUSSPRECHEN",
    ),
    (
        "messung/FREMDVERENGUNG.md",
        r"\| \*\*(\d+)\*\* \| davon \*\*verengt wirklich\*\*",
        ["./instrumente/zaehle-fremdverengung.py"],
        r"== (\d+) wirksame Fremdverengungen",
        "wirksame Fremdverengungen im Korpus -- die Zahl mit Wirkung im Erzeugnis",
    ),
    (
        "messung/FREMDVERENGUNG.md",
        r"\| \*\*(\d+)\*\* \| davon \*\*sprechen ihre Pflicht aus\*\*",
        ["./instrumente/zaehle-fremdverengung.py"],
        r"aus (\d+) ausgesprochenen Vertr",
        "fremde Ruempfe, die ihre Pflicht aussprechen",
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

    # ------------------------------------------------------------------------------
    # **Zwoelf weitere, gewaehlt nach TRAGLAST und nicht nach Aufwand** (2026-08-20).
    #
    # `--reichweite` sortiert die unbewachten Zahlen danach, ob sie eine Zusage oder einen
    # Vergleich nach aussen tragen. Von den 42 tragenden sind die hier zuerst genommen, bei
    # denen ein Befehl SCHON EXISTIERTE und niemand ihn gegen den Text gehalten hat --
    # *genau die Lage, in der eine Zahl belegt aussieht und veraltet ist.*
    #
    # **Und die Ausbeute des ersten Laufs sagt, dass das die richtige Wahl war:** sechs der
    # zwoelf standen beim Eintragen falsch da.
    # ------------------------------------------------------------------------------
    (
        "dokumente/PFLICHTEN.md",
        r"### Offen — \*\*`H = (\d+)`\*\*",
        ["./instrumente/zaehle-pflichten.py", "--haengend"],
        r"^\s+H\s+(\d+)\s*$",
        "H in der Postenliste (die UEBERSCHRIFT, nicht die Summenzeile)",
    ),
    (
        "dokumente/PFLICHTEN.md",
        r"\*\*(\d+) anchored at a line, \d+ lowerings\*\*",
        ["./instrumente/zaehle-pflichten.py", "--haengend"],
        r"^\s+verankert\s+(\d+)\s*$",
        "haengende Pflichten, an einer Zeile verankert",
    ),
    (
        "dokumente/PFLICHTEN.md",
        r"\*\*\d+ anchored at a line, (\d+) lowerings\*\*",
        ["./instrumente/zaehle-pflichten.py", "--haengend"],
        r"^\s+Absenkung\s+(\d+)\s",
        "haengende Pflichten, die an der Absenkung haengen",
    ),
    (
        "dokumente/PLAN.md",
        r"\| \*\*Prämissen ohne Pass\*\* \| \*\*(\d+)\*\*",
        ["cargo", "run", "-q", "--bin", "gabbro", "--", "schablonen"],
        r"PREMISES WITHOUT A PASS \(tooth 3\): (\d+)",
        "Praemissen ohne Pass, in der «NL»-Tafel",
    ),
    (
        "TODO.md",
        r"(\d+) sind tragend, \d+ verdächtig",
        ["./instrumente/pruefe-gruende.py"],
        r"\d+ verdaechtig · (\d+) tragend",
        "Absagen, deren Text den tragenden Grund nennt",
    ),
    (
        "TODO.md",
        r"\d+ sind tragend, (\d+) verdächtig",
        ["./instrumente/pruefe-gruende.py"],
        r"^\s+(\d+) verdaechtig ·",
        "Absagen, die sich ueber die DARSTELLUNG begruenden",
    ),
    (
        "TODO.md",
        r"\*\*(\d+) Absagetexte sagen ihren Grund in KEINER der beiden Sprachen\*\*",
        ["./instrumente/pruefe-gruende.py"],
        r"· (\d+) unklar",
        "Absagen ohne erkennbaren Grund",
    ),
    (
        "TODO.md",
        r'\*\*(\d+) von 23 Item-Arten\*\* sind „gelesen"',
        ["./instrumente/pruefe-konstrukte.py"],
        r"^\s+gelesen\s+(\d+)\s*$",
        "Item-Arten, die ein Pass anfasst",
    ),
    (
        "TODO.md",
        r"Mutationskatalog: \*\*(\d+) von \d+ Ankern\*\*",
        ["./instrumente/mutiere-pruefer.py", "--anker"],
        r"== (\d+) von \d+ Ankern greifen",
        "Mutationsanker, die im Pruefer wirklich sitzen",
    ),
    (
        "TODO.md",
        r"\*\*(\d+) Zeilenfortsetzungen\*\* in den Quellen",
        ["./instrumente/pruefe-englisch.py"],
        r"== Lesbarkeit: (\d+) Zeilenfortsetzungen",
        "Zeilenfortsetzungen -- die Flaeche der Klebeprobe",
    ),
    (
        "TODO.md",
        r"Zeilenfortsetzungen\*\* in den Quellen, \*\*(\d+) kleben\*\*",
        ["./instrumente/pruefe-englisch.py"],
        r"^\s+(\d+) von \d+ Naehten kleben",
        "klebende Nahtstellen",
    ),
    (
        "TODO.md",
        r"Schablonenregister führt \*\*(\d+) Einträge\*\*",
        ["cargo", "run", "-q", "--bin", "gabbro", "--", "schablonen"],
        r"^-- (\d+) templates,",
        "Schablonen im Register",
    ),
    (
        "TODO.md",
        r"Einträge\*\*, \*\*(\d+) davon unbewiesen\*\*",
        ["cargo", "run", "-q", "--bin", "gabbro", "--", "schablonen"],
        r"^-- \d+ templates, (\d+) of them unproved",
        "Schablonen, die unbewiesen dastehen",
    ),
    (
        "TODO.md",
        r"\*\*(\d+) Widerrufe\*\* über \d+ Dateien",
        ["./instrumente/pruefe-widerruf.py"],
        r"== Widerrufene Saetze: (\d+) Eintraege",
        "gebuchte Widerrufe",
    ),
    (
        "TODO.md",
        r"\*\*\d+ Widerrufe\*\* über (\d+) Dateien",
        ["./instrumente/pruefe-widerruf.py"],
        r"== Widerrufene Saetze: \d+ Eintraege, (\d+) Dateien",
        "Dateien, die der Widerrufwaechter liest",
    ),
    (
        "TODO.md",
        r"\*\*(\d+) besetzte Zellen\*\* stehen daneben",
        ["sh", "-c",
         "cargo run -q --bin gabbro -- blindstellen beispiele/*.gab -- beispiele/gift/*.gab"],
        r"· (\d+) covered ·",
        "besetzte Zellen der Tafel -- die Zahl, die „gedeckt\" heissen soll",
    ),
    (
        "TODO.md",
        r"besetzte Zellen\*\* stehen daneben, \*\*(\d+) nur im Gift\*\*",
        ["sh", "-c",
         "cargo run -q --bin gabbro -- blindstellen beispiele/*.gab -- beispiele/gift/*.gab"],
        r"· (\d+) poison-only ·",
        "Zellen, die NUR im Giftkorpus vorkommen",
    ),

    # **Und fuenf, deren Befehl es vorher gar nicht gab** -- gebaut am 2026-08-20, weil die
    # Zahl im Text stand und kein Weg zu ihr fuehrte. *Das ist der andere Fall: nicht eine
    # Zahl, die veraltet ist, sondern eine, die nie ableitbar war.*
    (
        "TODO.md",
        r"\*\*(\d+) direkte Blicke\*\* auf die Karten",
        ["./instrumente/zaehle-karten.py"],
        r"direkte Blicke\s+(\d+)",
        "direkte Blicke auf die Karten der `Umgebung`",
    ),
    (
        "TODO.md",
        r"direkte Blicke\*\* auf die Karten[^\n]*\n[^\n]*\*\*(\d+) davon unqualifiziert\*\*",
        ["./instrumente/zaehle-karten.py"],
        r"davon UNQUALIFIZIERT\s+(\d+)",
        "Blicke ohne Modulkandidaten -- jeder ein moegliches `M103`-Loch",
    ),
    (
        "TODO.md",
        # **The theory count stood here as a WORD, and was therefore itself a stale
        # number** (found 2026-08-28, when the fourteenth theory arrived): the locator no
        # longer matched its sentence, and the entry went SILENT instead of red.
        # *A register whose locator goes stale absolves.* Hence `\w+`.
        r"\*\*([0-9  ]+) Zeilen\*\* in \w+ Theorien",
        ["./instrumente/zaehle-theorien.py"],
        r"== \d+ Theorien, (\d+) Zeilen",
        "Zeilen der eigenen Isabelle-Theorien",
    ),
    (
        "TODO.md",
        r"\*\*(\d+) Zeilen Modell und Beweis\*\*",
        ["./instrumente/zaehle-theorien.py"],
        r"Modell \+ Beweis = (\d+) Zeilen",
        "die Haelfte, die einer Verus-Zeilenzahl gegenuebersteht",
    ),
    (
        "TODO.md",
        r"\*\*(\d+) eingefrorene Suchergebnisse\*\*",
        ["./instrumente/zaehle-theorien.py"],
        r"== Suche: \d+ Suchbefehle, (\d+) eingefrorene",
        "`metis`/`blast`/`smt` -- Suchen, die einmal liefen",
    ),

    # **Die «NL»-Tafel, Zeile fuer Zeile** -- sie nennt selbst die Befehle, und drei von fuenf
    # Zahlen standen am 2026-08-20 falsch da. *Eine davon war das Tor von «NL»: `ZUSAGE = 0`
    # war ERREICHT, und die Tafel fuehrte 13.* Ein Tor, dessen Erreichen niemand mitschreibt,
    # ist von einem unerreichten nicht zu unterscheiden.
    (
        "dokumente/PLAN.md",
        r"\| \*\*Erhaltungspflichten\*\* \| \*\*(\d+)\*\*",
        ["sh", "-c", PFLICHTEN_SUMME],
        r"erhaltung (\d+)",
        "Erhaltungspflichten ueber dem Korpus",
    ),
    (
        "dokumente/PLAN.md",
        r"\| \*\*ZUSAGE ohne Leser\*\* \| \*\*(\d+)\*\*",
        ["./instrumente/pruefe-klauseln.py"],
        r"^\s+ZUSAGE\s+(\d+)\s",
        "ZUSAGE-Klauseln ohne Leser -- das Tor von «NL»",
    ),
    (
        "dokumente/PLAN.md",
        r"\| \*\*Fremdpflichten\*\* \| \*\*(\d+)\*\*",
        ["sh", "-c", PFLICHTEN_SUMME],
        r"fremd (\d+)",
        "Fremdpflichten ueber dem Korpus",
    ),
    # **Neu am 2026-08-20** -- der Preis der SCHWACHEN Fassung von `M115`. Der Pruefer weist
    # ab, wo der Bereich des Arguments die Vorbedingung ausschliesst, und schweigt sonst; die
    # Zahl der Rufstellen, an denen er schweigt, stand nirgends. *Ein Preis, der nirgends
    # steht, sieht aus wie null.*
    (
        "dokumente/PLAN.md",
        r"\| \*\*Vorbedingungen am Rufort\*\* \| \*\*(\d+)\*\*",
        ["sh", "-c", PFLICHTEN_SUMME],
        r"vorbed (\d+)",
        "Vorbedingungen an Rufstellen ueber dem Korpus",
    ),
    (
        "dokumente/PLAN.md",
        r"\| \*\*Absenkungspflichten\*\* \| \*\*(\d+)\*\*",
        ["./instrumente/zaehle-pflichten.py", "--haengend"],
        r"^\s+Absenkung\s+(\d+)\s",
        "Absenkungspflichten in der «NL»-Tafel",
    ),
    (
        "dokumente/PLAN.md",
        r"H = (\d+)        ueber den zehn Fragmenten kein Handbeweis mehr",
        ["./instrumente/zaehle-pflichten.py", "--haengend"],
        r"^\s+H\s+(\d+)\s*$",
        "H im «NL»-Kasten",
    ),
    # **The two summary tables of `PFLICHTEN.md`** -- new on 2026-08-30, and the occasion is
    # written in the file itself: the column table added up to 173 K / 65 L, the row beneath
    # it read 171 / 67, and BOTH make 238. *A split whose total matches is not recomputed* --
    # it stood for sixteen days. The recount found the cause one level down: F4 has 31 rows,
    # not 30, so the true split is 173 / 66 over 239.
    #
    # **Six entries for six numbers, not one for the table.** Two tables over the same thing
    # are W7 -- while both stand, every cell gets its own command.
    (
        "dokumente/PFLICHTEN.md",
        r"\| \*\*Obligations in total\*\* \|[^|]*?\*\*(\d+)\*\* \|",
        ["./instrumente/zaehle-pflichten.py", "--spalten"],
        r"^  insgesamt\s+(\d+) =",
        "Pflichten insgesamt -- die Tafel `The totals`",
    ),
    (
        "dokumente/PFLICHTEN.md",
        r"\| \*\*Plumbing \(K\)\*\* \|[^|]*?\*\*(\d+)\*\* \|",
        ["./instrumente/zaehle-pflichten.py", "--spalten"],
        r"^  insgesamt\s+\d+ =\s+(\d+) K",
        "Klempnereipflichten (K) -- die Tafel `The totals`",
    ),
    (
        "dokumente/PFLICHTEN.md",
        r"\| \*\*Logic \(L\)\*\* \|[^|]*?\*\*(\d+)\*\* \|",
        ["./instrumente/zaehle-pflichten.py", "--spalten"],
        r"^  insgesamt\s+\d+ =\s+\d+ K \+\s+(\d+) L",
        "Logikpflichten (L) -- die Tafel `The totals`",
    ),
    (
        "dokumente/PFLICHTEN.md",
        r"(?m)^\| \|[^|]*?\*\*(\d+)\*\* \|[^|]*\|[^|]*\|$",
        ["./instrumente/zaehle-pflichten.py", "--spalten"],
        r"^  insgesamt\s+(\d+) =",
        "Pflichten insgesamt -- die Spaltentafel je Fragment",
    ),
    (
        "dokumente/PFLICHTEN.md",
        r"(?m)^\| \|[^|]*\|[^|]*?\*\*(\d+)\*\* \|[^|]*\|$",
        ["./instrumente/zaehle-pflichten.py", "--spalten"],
        r"^  insgesamt\s+\d+ =\s+(\d+) K",
        "Klempnereipflichten (K) -- die Spaltentafel je Fragment",
    ),
    (
        "dokumente/PFLICHTEN.md",
        r"(?m)^\| \|[^|]*\|[^|]*\|[^|]*?\*\*(\d+)\*\* \|$",
        ["./instrumente/zaehle-pflichten.py", "--spalten"],
        r"^  insgesamt\s+\d+ =\s+\d+ K \+\s+(\d+) L",
        "Logikpflichten (L) -- die Spaltentafel je Fragment",
    ),
    # **The register line from K100's trap section** -- new on 2026-08-30. It stood as
    # `20 Eintraege, 16 unbewiesen, 4 davon lebend` while the command said 21 / 11 / 2.
    # *Two of the three had moved in the GOOD direction* -- the trust surface fell while the
    # register grew -- **and that is exactly the movement K100's second gate exists to make
    # visible.** A hand-kept number shows it in neither direction.
    (
        "dokumente/PLAN.md",
        r"\*\*(\d+) Einträge, \d+ unbewiesen, \d+ davon lebend\*\*",
        ["cargo", "run", "-q", "--bin", "gabbro", "--", "schablonen"],
        r"^-- (\d+) templates, \d+ of them unproved",
        "Schablonen im Register",
    ),
    (
        "dokumente/PLAN.md",
        r"\*\*\d+ Einträge, (\d+) unbewiesen, \d+ davon lebend\*\*",
        ["cargo", "run", "-q", "--bin", "gabbro", "--", "schablonen"],
        r"^-- \d+ templates, (\d+) of them unproved",
        "unbewiesene Schablonen",
    ),
    (
        "dokumente/PLAN.md",
        r"\*\*\d+ Einträge, \d+ unbewiesen, (\d+) davon lebend\*\*",
        ["cargo", "run", "-q", "--bin", "gabbro", "--", "schablonen"],
        r"CARRIED unproved \(the compiler rests on them\): (\d+)",
        "lebend unbewiesene Schablonen (die Registerzeile, nicht die Statustafel)",
    ),
    # **The assumption count in the prose, beside the one in the status table.** Two places
    # over one number are W7 -- while both stand, each gets its own command.
    (
        "dokumente/PLAN.md",
        r"\*\*Heute steht dort (\d+)\*\*",
        ["sh", "-c", "cargo run -q --bin gabbro -- annahmen beispiele/*.gab"],
        r"^-- (\d+) Annahmen",
        "Annahmen -- die Zahl im Fliesstext von K100",
    ),
    # **The trigger for goal 9, and it stood 19 sentences short** (2026-08-30). `TODO.md` reads
    # a sentence naming 52 sentences over 12 of 12 passes, none proved -- and calls that
    # trigger 1 for taking the checker to Lean. The command said 71. **A trigger condition is
    # the most expensive kind of unguarded number**: it is read once, at the moment somebody
    # decides whether to start.
    #
    # *And the reach counter cannot see it* -- it looks for a bold number in a table cell, and
    # this one stands in running text. **The reach figure is a lower bound on the debt, not a
    # measure of it**, and that is the same W10 sentence the tool prints about its own
    # classifier.
    (
        "TODO.md",
        r"stehen ~~\d+~~ (\d+) Sätze über \d+ von \d+ Pässen",
        ["cargo", "run", "-q", "--bin", "gabbro", "--", "paesse"],
        r"SENTENCES: (\d+) over \d+ passes",
        "Saetze ueber den Paessen -- Ausloeser 1 fuer Ziel 9",
    ),
    (
        "TODO.md",
        r"Sätze über (\d+) von \d+ Pässen",
        ["cargo", "run", "-q", "--bin", "gabbro", "--", "paesse"],
        r"SENTENCES: \d+ over (\d+) passes",
        "Paesse, ueber denen die Saetze stehen",
    ),
]

# **THE REGISTER OF REASONS -- for the numbers that CANNOT get a command** (2026-08-30).
#
# `--reichweite` counted 38 load-bearing unguarded figures and read them as debt. Going
# through them one by one showed that **most of them are not unmeasured -- they are
# unguardable, and for three different reasons that must not be added up:**
#
# **The four classes and what each one means stand in `messung/REICHWEITE-GRUENDE.md`.**
# They are named in the entries below and NOT spelled out here, and the reason is measurable:
# two of the four class names carry a German particle, and a class name repeated in a comment
# block lifts the language ratchet by one line per mention. *A name is a comment nobody can
# translate* -- so it lives in the measurement document and the entries point at it.
#
# The shortest form of each: a dated RECORD (giving it a command would turn a record into a
# claim about today, which `MESSUNGEN.md` forbids in its own preamble); a figure measured over
# a FOREIGN tree or by a run this folder does not repeat; an ORDINAL that only looks like a
# metric because a numbered list is written with the same markup; and a judgement argued in
# its own row.
#
# > **Why this is a register and not a paragraph.** A written reason ages exactly like a
# > written number. Every entry here carries the pattern it applies to, and an entry whose
# > pattern hits nothing FALLS -- the same rule the guarded entries live under. *A reason that
# > no longer points at anything is worse than none: it lowers a count and explains nothing.*
#
# And what it is NOT: an acquittal. A figure with a reason is still unguarded; what it is not
# any more is unexplained. **The open bucket is the work list** (W10).
UNBEWACHBAR = [
    # ---- MESSUNGEN.md: the frozen protocol of the reassignment (2026-08-17) -------------
    ("dokumente/MESSUNGEN.md", r"\| \*\*Plumbing \(K\)\*\* \| \*\*173\*\*", "PROTOKOLL",
     "die Aufteilung vom 2026-08-17; die LEBENDE steht in `PFLICHTEN.md` und ist bewacht"),
    ("dokumente/MESSUNGEN.md", r"\| \*\*hanging\*\* \| \*\*50\*\*", "PROTOKOLL",
     "`H = 36` an dem Tag, an dem das Tor verfehlt wurde -- der Torbefund selbst"),
    ("dokumente/MESSUNGEN.md", r"\| disputed \| \*\*1\*\* \| 0,4 %", "PROTOKOLL",
     "dito, und daneben ein URTEIL: strittig ist keine Messung"),
    ("dokumente/MESSUNGEN.md", r"\| K, carried by construction \| \*\*137\*\*", "PROTOKOLL",
     "137 + 36 = 173, die Ausgangslage von K100 -- sie darf sich nicht bewegen"),
    ("dokumente/MESSUNGEN.md", r"\| \*\*K, hanging — H\*\* \| \*\*36\*\*", "PROTOKOLL",
     "dieselbe Zeile von der anderen Seite"),

    # ---- MESSUNGEN.md: dated before/after tables ----------------------------------------
    ("dokumente/MESSUNGEN.md", r"\| proved \| 1 \| \*\*4\*\*", "PROTOKOLL",
     "Schablonenstand an EINEM Tag; der heutige steht in `PLAN.md` mit Befehl"),
    ("dokumente/MESSUNGEN.md", r"\| \*\*unproved\*\* \| \*\*16\*\* \| \*\*15\*\*", "PROTOKOLL",
     "dito -- eine Vorher/Nachher-Zeile ist ein Ereignis, kein Stand"),
    ("dokumente/MESSUNGEN.md", r"\| mutations \| 67 \| \*\*87\*\*", "PROTOKOLL",
     "der Mutationskatalog an dem Tag; heute 345, und der Weg dorthin ist der Inhalt"),
    ("dokumente/MESSUNGEN.md", r"\| ZUSAGE \| \*\*17\*\*", "PROTOKOLL",
     "der Klauselwaechterlauf; die LEBENDE `ZUSAGE ohne Leser` ist in `PLAN.md` bewacht"),
    ("dokumente/MESSUNGEN.md", r"\| 19 templates, 4 machine-checked \|", "PROTOKOLL",
     "eine Zeile aus der README-Berichtigung jenes Tages"),
    ("dokumente/MESSUNGEN.md", r"\| Prämissen ohne Pass \| 7 \| \*\*9\*\*", "PROTOKOLL",
     "dito; die lebende Zahl steht in `PLAN.md` mit `gabbro schablonen` daneben"),
    ("dokumente/MESSUNGEN.md", r"\| Mutationsanker \| 332 \| 335 \| \*\*340\*\*", "PROTOKOLL",
     "die Zusammenfuehrung vom 2026-08-30 -- genau die Zahl, die der Merge WIDERLEGTE"),
    ("dokumente/MESSUNGEN.md", r"\| \*\*Prosa\*\* \| \*\*1 062\*\*", "PROTOKOLL",
     "die Theorienaufteilung an ihrem Messtag; `zaehle-theorien.py` sagt den heutigen Stand"),

    # ---- MESSUNGEN.md: the foreign corpora ----------------------------------------------
    ("dokumente/MESSUNGEN.md", r"\| Proof obligations in total \| \*\*74\*\*", "KEIN INSTRUMENT",
     "Caprocks Verus-Pflichten -- gemessen im fremden Baum `../caprock-messbasis`"),
    ("dokumente/MESSUNGEN.md", r"\| the \*\*whole file\*\* \(1 448\)", "KEIN INSTRUMENT",
     "Verhaeltnis ueber eine fremde Datei"),
    ("dokumente/MESSUNGEN.md", r"`proof/[a-z-]+`", "KEIN INSTRUMENT",
     "seL4-Beweiszeilen -- veroeffentlichte Zahlen, kein Baum in diesem Ordner"),
    ("dokumente/MESSUNGEN.md", r"\| \*\*functional correctness, ARM\*\*", "KEIN INSTRUMENT",
     "seL4 gesamt, dieselbe Quelle"),
    ("dokumente/MESSUNGEN.md", r"\| `trusted/fs` \| 365 \| 3 \|", "KEIN INSTRUMENT",
     "fremde Vertrauensflaeche, aus der Veroeffentlichung"),
    ("dokumente/MESSUNGEN.md", r"`(?:capability-system|ipc|scheduler)/proofs?/", "KEIN INSTRUMENT",
     "Caprocks Beweisdateien -- fremder Baum, schreibgeschuetzt"),
    ("dokumente/MESSUNGEN.md", r"\| \*\*obligation side\*\* \(Verus bodies", "KEIN INSTRUMENT",
     "Verus-Rumpfgewicht, ueber dem fremden Baum gerechnet"),
    ("dokumente/MESSUNGEN.md", r"\| \*\*were the Index booking to fall\*\*", "KEIN INSTRUMENT",
     "eine Gegenrechnung ueber denselben fremden Baum"),
    ("dokumente/MESSUNGEN.md", r"\| \*\*caught\*\* \| \*\*7\*\* \|", "PROTOKOLL",
     "ein Generatorlauf an seinem Tag; der heutige Stand ist `mutiere-pruefer.py`"),

    # ---- TODO.md: ordinals, not metrics -------------------------------------------------
    ("TODO.md", r"\| \*\*\d+\*\* \| keine Klempnerei beim Endnutzer", "KEINE KENNZAHL",
     "Ziel Nummer vier aus der Zieltafel"),
    ("TODO.md", r"\| \*\*\d+\*\* \| der Maßstab \|", "KEINE KENNZAHL", "Ziel Nummer eins"),
    ("TODO.md", r"\| \*\*\d+\*\* \| die offenen Lesarten entscheiden", "KEINE KENNZAHL",
     "Ziel Nummer drei"),
    ("TODO.md", r"\| \*\*\d+\*\* \| die Beweise tragend machen", "KEINE KENNZAHL",
     "Ziel Nummer fuenf"),
    ("TODO.md", r"\| \*\*\d+\*\* \| der Prüfer als Mathematik, in Lean 4", "KEINE KENNZAHL",
     "Ziel Nummer neun"),
    ("TODO.md", r"\| \*\*\d+\*\* \| Übersetzer einer Gabbro-Teilmenge", "KEINE KENNZAHL",
     "Stufe eins einer Baureihenfolge"),
    ("TODO.md", r"\| \*\*\d+\*\* \| \*\*Two ordering rules stood there", "KEINE KENNZAHL",
     "Befund Nummer drei einer nummerierten Liste"),

    # ---- PLAN.md ------------------------------------------------------------------------
    ("dokumente/PLAN.md", r"\| \*\*together, hard\*\* \| \*\*3 081\*\*", "KEIN INSTRUMENT",
     "Caprock-Zeilen, gemessen 2026-08-13 im fremden Baum"),
    ("dokumente/PLAN.md", r"\| \*\*\d+\*\* \| \*\*The preservation\*\* of the group invariant",
     "KEINE KENNZAHL", "Posten Nummer drei einer nummerierten Aufzaehlung"),
    ("dokumente/PLAN.md", r"117 ms \| 117 ms \|", "KEIN INSTRUMENT",
     "Laufzeitverhaeltnis aus einem Messlauf, den dieser Ordner nicht wiederholt"),
    ("dokumente/PLAN.md", r"156 ms \| 210 ms \|", "KEIN INSTRUMENT", "dieselbe Messreihe"),
    ("dokumente/PLAN.md", r"23,0 ms \| 23,1 ms \|", "KEIN INSTRUMENT", "dieselbe Messreihe"),
    ("dokumente/PLAN.md", r"66,0 ms \| 23,2 ms \|", "KEIN INSTRUMENT", "dieselbe Messreihe"),

    # ---- PFLICHTEN.md -------------------------------------------------------------------
    ("dokumente/PFLICHTEN.md", r"\| \*\*disputed\*\* \| \*\*1\*\*", "URTEIL",
     "`unlink`:194-196 -- in der Zeile ARGUMENTIERT, und ein Argument zaehlt kein Werkzeug"),
]


def unbewachbar_grund(datei, zeile):
    """Der geschriebene Grund zu einer Zeile -- oder `None`, wenn keiner gebucht ist."""
    for d, muster, klasse, grund in UNBEWACHBAR:
        if d == datei and re.search(muster, zeile):
            return klasse, grund
    return None


def unbewachbar_tot():
    """**Ein Grund, der auf nichts mehr zeigt, faellt** -- dieselbe Regel wie fuer die Zahlen."""
    tot = []
    for d, muster, klasse, grund in UNBEWACHBAR:
        p = W / d
        if not p.is_file() or not re.search(muster, p.read_text(encoding="utf-8")):
            tot.append(f"{d}: der Grund „{grund[:44]}\" trifft keine Zeile mehr")
    return tot


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


# **Der Riegel aus W18 war nur EINEN Schritt tief -- gefunden 2026-08-20.**
#
# `kein_selbstbezug()` sucht den Namen dieses Werkzeugs IM BEFEHL eines Eintrags. Das faengt
# den Zyklus der Laenge eins und **keinen laengeren** -- und einer der Laenge zwei liegt hier
# unmittelbar bereit: `./instrumente/pruefe-waechter.py --lauf` fuehrt jeden leichten Waechter aus, und
# `pruefe-zahlen.py` ist einer davon. **Ein einziger Registereintrag mit `--lauf` schliesst
# den Ring**, und der Namensriegel laesst ihn durch, weil im Befehl `pruefe-waechter.py`
# steht und nicht `pruefe-zahlen.py`.
#
# *Und der Ring ueber zwei Ecken ist genau der gefaehrliche Fall aus W18:* nicht der
# Ruecklauf, sondern ein Fixpunkt, der TERMINIERT -- die Zahl stimmt dann immer, unabhaengig
# davon, ob gemessen wurde.
#
# **Die Marke unten schliesst ihn in beliebiger Tiefe**, weil sie an den KINDPROZESSEN haengt
# und nicht am Text: jeder Befehl dieses Registers laeuft mit ihr, jedes Kind erbt sie, und
# wer sie beim Start vorfindet, ist von sich selbst gerufen worden.
MARKE = "GABBRO_ZAHLEN_IM_LAUF"


def gerufen_aus_dem_register():
    """**Wurde dieses Werkzeug aus einem seiner eigenen Befehle heraus gestartet?**"""
    return os.environ.get(MARKE) == "1"


def lauf(befehl):
    """Ein Befehl mit Frist. **Ein Haenger sieht aus wie „laeuft noch", nicht wie ein Befund.**"""
    umgebung = dict(os.environ, **{MARKE: "1"})
    try:
        r = subprocess.run(befehl, cwd=W, capture_output=True, text=True, timeout=FRIST,
                           env=umgebung)
    except subprocess.TimeoutExpired:
        return None, f"FRIST ({FRIST} s) ueberschritten"
    if f"{MARKE}" in r.stdout and "SELBSTBEZUG" in r.stdout:
        return None, ("SELBSTBEZUG ueber mehrere Ecken -- dieser Befehl ruft das Register "
                      "wieder auf. Ein Fixpunkt, der terminiert, stimmt IMMER (W18)")
    if "error[E" in r.stderr or "could not compile" in r.stderr:
        return None, "der Pruefer baut nicht -- es wurde NICHTS gemessen"
    # **A command that says of ITSELF that it cannot measure is not a broken search path**
    # *(2026-08-30)*.
    #
    # `pruefe-saetze.py` compares the claimed identifiers out of the BUILT `gabbro paesse`
    # against the existing ones out of the sources. Where the binary is older, the two halves
    # describe different trees, so it aborts rather than printing a mixture. *That is the
    # right answer, and a different state from "the number is no longer there".*
    #
    # Such an entry is carried BY NAME here: suspended, with a reason and with a count --
    # neither counted as a finding nor left out. **A suspended figure is UNGUARDED**, and the
    # line below says how many there are.
    if "MISCHUNG" in r.stderr:
        return None, "AUSGESETZT: der Befehl kann ohne einen Bau nicht messen (Mischung)"
    return r.stdout, None


ZWISCHEN = {}


def ort_von(text, pos):
    """`(line, column)` of a match -- **the PLACE, not the VALUE.**

    Until 2026-08-31 `bewacht` was a set of NUMBERS per file, so a bold table cell counted
    as guarded the moment ANY other cell of the same file happened to carry the same value
    and have a command. Measured that day: `H` fell from 5 to 4, two register cells in
    `PLAN.md` became a bold four -- and a completely unrelated row dropped out of the
    unguarded list, **without ever having been given a command.** The mark sank from 146 to
    145. *A mark that falls through a collision does not measure what it says* -- and the
    other direction is worse: a cell that DOES get a command fails to lower the count if its
    value appears once more in the same file.
    """
    return text.count("\n", 0, pos), pos - (text.rfind("\n", 0, pos) + 1)


def zellen(text):
    """Every bold table cell as `(place, value, line)` -- **block quotes excluded.**

    Two things stand here, and both were measured on 2026-08-31:

    * The key is the PLACE (`ort_von`), not the value. Otherwise a cell counts as guarded
      the moment any other cell of the same file happens to carry the same digit -- and the
      mark falls through a collision instead of through work.
    * **A QUOTATION of a table row is not a table cell.** The entry that wrote the collision
      down repeated it while writing: its first draft quoted the colliding row verbatim,
      pipes and all, and the counter read the quotation as a cell of its own. *A register
      that counts its own work list.* The numbers inside a block quote belong to whoever is
      being quoted.
    """
    aus = []
    for nr, zeile in enumerate(text.splitlines()):
        if zeile.lstrip().startswith(">"):
            continue
        for m in KENNZAHL.finditer(zeile):
            aus.append(((nr, m.start(1)), m.group(1).replace(" ", "").replace("\u00a0", ""),
                        zeile))
    return aus


def zitierte_zellen(text):
    """How many bold cells stand inside block quotes -- the number is PRINTED."""
    return sum(len(KENNZAHL.findall(z)) for z in text.splitlines()
               if z.lstrip().startswith(">"))


def pruefe_eintraege(verstellen=None):
    """Alle Eintraege gegen ihren Befehl.

    `verstellen` verstellt die Zahl IM TEXT (nur im Speicher) -- das ist die Sprechprobe.
    **Ein Waechter, der nicht rot werden kann, misst nichts** (R14).
    """
    befunde, geprueft, bewacht = [], 0, {}
    ausgesetzt = []
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
            if fehler.startswith("AUSGESETZT:"):
                ausgesetzt.append(f"{datei} / {was}: {fehler[11:].strip()}")
            else:
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
        # **The key carries the PLACE** (see `ort_von`). The value alone let a
        # foreign cell with the same digit pass as guarded.
        bewacht.setdefault(datei, set()).add(ort_von(text, treffer.start(1)))
        if im_text != aus_lauf:
            befunde.append(f"{datei}: „{was}\" steht als {im_text}, der Lauf sagt {aus_lauf}")
    return befunde, geprueft, bewacht, ausgesetzt


def main():
    # **Der dynamische Riegel, noch vor dem statischen.** Er greift in jeder Tiefe.
    if gerufen_aus_dem_register():
        print("== SELBSTBEZUG (dynamisch) -- das Register hat sich selbst aufgerufen ==")
        print(f"  Die Marke {MARKE} stand beim Start schon in der Umgebung: dieser Lauf ist")
        print("  das Kind eines Registerbefehls. **Ein Register, das seine eigene Ausgabe")
        print("  enthaelt, hat einen FIXPUNKT statt einer Messung** (W18) -- und der")
        print("  gefaehrliche Fall ist nicht der Ruecklauf, sondern der Fixpunkt, der")
        print("  TERMINIERT: die Zahl stimmt dann immer, unabhaengig davon, ob gemessen wurde.")
        print("  0 von 0 Eintraegen nachgerechnet -- es wurde NICHTS gemessen.")
        # **2, not 1** (2026-08-31). The line above says nothing was measured, and until
        # today the return code said the opposite. This branch is not a finding about the
        # tree: the register is intact, the RUN is the child of a register command. *The
        # setup has to change, not the tree.*
        return 2

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
        # 2, not 1: a fallen probe has measured NOTHING.
        return 2
    # **Und der DYNAMISCHE Riegel muss ebenso beissen koennen.** Ein Riegel, der nie
    # zuschlaegt, ist von einem fehlenden nicht zu unterscheiden -- darum wird er hier an
    # einem echten Kindprozess gemessen und nicht an einem Satz.
    tief = subprocess.run([str(pathlib.Path(__file__).resolve())], cwd=W, text=True,
                          capture_output=True, timeout=FRIST,
                          env=dict(os.environ, **{MARKE: "1"}))
    tief_ok = tief.returncode == 2 and "SELBSTBEZUG (dynamisch)" in tief.stdout
    print("  Tiefenriegel:   " + ("ok (ein Lauf aus dem Register heraus faellt, in JEDER Tiefe)"
                                  if tief_ok else "GESCHEITERT -- ein Ring ueber zwei Ecken kaeme durch"))
    if not tief_ok:
        return 2
    # **And the register of reasons must be able to bite** (2026-08-30). A written reason ages
    # exactly like a written number: the row it explains gets reworded, the reason keeps
    # lowering the count and explains nothing. *That is worse than no reason at all -- it makes
    # a shorter work list out of a stale pattern.* Both directions, as R14 demands.
    UNBEWACHBAR.append(("TODO.md", r"diese Zeile steht nirgends 998", "PROBE", "Sprechprobe"))
    tot_biss = any("Sprechprobe" in x for x in unbewachbar_tot())
    UNBEWACHBAR.pop()
    tot_still = not unbewachbar_tot()
    print("  Gruenderegister: " + ("ok (ein Grund ohne Zeile faellt)" if tot_biss
                                   else "GESCHEITERT -- ein toter Grund kaeme durch"))
    print("  Gruende leben:   " + ("ok (jeder gebuchte Grund trifft eine Zeile)" if tot_still
                                   else "es steht ein toter Grund im Register -- siehe unten"))
    if not tot_biss:
        return 2
    # **And the key has to carry the PLACE, not the VALUE** (2026-08-31). Two cells with
    # the same digit at two places are TWO cells, and a guarded one must not cover the
    # other. Until today it did: `H` fell from 5 to 4, two register cells in `PLAN.md`
    # became a bold four, and a completely unrelated row dropped out of the unguarded list
    # -- **without ever having been given a command.**
    #
    # Three directions over invented text, and the second is the one that counts: the OLD
    # key has to be blind at the very same spot. Otherwise this probe measures nothing.
    probe_text = ("| **4** | Genericity |\n"
                  "| **4** | eine ganz andere Zeile |\n"
                  "> | **4** | zitiert, also fremd |\n")
    p_zellen = zellen(probe_text)
    bewacht_probe = {p_zellen[0][0]} if p_zellen else set()
    rest = [c for c in p_zellen if c[0] not in bewacht_probe]
    ort_ok = len(p_zellen) == 2 and len(rest) == 1 and rest[0][1] == "4"
    alt_blind = not [c for c in p_zellen if c[1] not in {p_zellen[0][1]}] if p_zellen else False
    zitat_ok = zitierte_zellen(probe_text) == 1 and len(p_zellen) == 2
    print("  Ortsschluessel: " + ("ok (zwei Vieren an zwei Stellen sind ZWEI Zellen)"
                                  if ort_ok else "GESCHEITERT -- eine Kollision deckt zu"))
    print("  Gegenprobe:     " + ("ok (der alte Schluessel WAERE an derselben Stelle blind)"
                                  if alt_blind else "GESCHEITERT -- die Probe misst nichts"))
    print("  Blockzitat:     " + ("ok (eine zitierte Zeile ist keine Tabellenzelle)"
                                  if zitat_ok else "GESCHEITERT -- das Zitat zaehlt mit"))
    if not (ort_ok and alt_blind and zitat_ok):
        # 2, not 1: a fallen speech test has measured NOTHING.
        print("\n! Der Waechter misst nicht, was er behauptet. ABBRUCH.")
        return 2
    stumm = []
    for nr in range(len(EINTRAEGE)):
        b, _, _, _ = pruefe_eintraege(verstellen=nr)
        if not any("der Lauf sagt" in x for x in b):
            stumm.append(EINTRAEGE[nr][4])
    if stumm:
        print(f"  GESCHEITERT -- {len(stumm)} Eintraege bleiben stumm, wenn ihre Zahl verstellt wird:")
        for x in stumm:
            print(f"     {x}")
        return 2
    print(f"  ok -- alle {len(EINTRAEGE)} Eintraege fallen, wenn ihre Zahl verstellt wird")
    print()

    befunde, geprueft, bewacht, ausgesetzt = pruefe_eintraege()
    print("== Kennzahlen gegen ihren Befehl ==")
    print(f"  {geprueft} von {len(EINTRAEGE)} Eintraegen nachgerechnet")
    for b in befunde:
        print(f"  BEFUND  {b}")
    # **Carried by name instead of left out.** A suspended figure is UNGUARDED, and it stands
    # here with its count so that a suspension never reads like a check.
    if ausgesetzt:
        print(f"  {len(ausgesetzt)} Kennzahl(en) AUSGESETZT -- unbewacht, nicht geprueft:")
        for a in ausgesetzt:
            print(f"     {a}")

    # Die zweite Haelfte: wie weit reicht dieses Register?
    offen = []
    zitiert = 0
    for datei in BEWACHTE_DATEIEN:
        p = W / datei
        if not p.is_file():
            continue
        roh = p.read_text(encoding="utf-8")
        zitiert += zitierte_zellen(roh)
        for ort, z, zeile in zellen(roh):
            if ort not in bewacht.get(datei, set()):
                g = unbewachbar_grund(datei, zeile)
                offen.append((datei, z, zeile.strip()[:70],
                              bool(TRAEGT.search(zeile)), g))
    print()
    print("== Reichweite: was dieses Register NICHT bewacht ==")
    traegt = [o for o in offen if o[3]]
    mit_grund = [o for o in traegt if o[4]]
    ohne_grund = [o for o in traegt if not o[4]]
    print(f"  {geprueft} Kennzahlen mit Befehl, {len(offen)} fettgedruckte Zahlen in "
          f"Tabellenzellen ohne einen")
    print(f"  davon TRAGEND (Zusage oder Vergleich): {len(traegt)}   "
          f"Zwischenstand: {len(offen) - len(traegt)}")
    print(f"  {zitiert} weitere stehen in BLOCKZITATEN und zaehlen nicht mit -- die Zahlen")
    print("  eines Zitats gehoeren dem Zitierten. *Ein Register, das seine eigene")
    print("  Arbeitsliste mitzaehlt, misst sich selbst.*")
    # **The load-bearing bucket, split once more** (2026-08-30). A load-bearing figure without
    # a command is not debt by that fact alone: most of them are a dated record that must not
    # get one. *What remains is the work list, and it is a great deal shorter.*
    print(f"     davon mit geschriebenem GRUND: {len(mit_grund)}   "
          f"OFFEN, also Arbeitsliste: {len(ohne_grund)}")
    nach_klasse = {}
    for o in mit_grund:
        nach_klasse[o[4][0]] = nach_klasse.get(o[4][0], 0) + 1
    if nach_klasse:
        print("     " + ", ".join(f"{k} {v}" for k, v in sorted(nach_klasse.items())))
    tot = unbewachbar_tot()
    for x in tot:
        befunde.append(f"UNBEWACHBAR-Register: {x}")
        print(f"  BEFUND  {x}")
    print()
    print("  **Nicht alle unbewachten Zahlen sind gleich viel wert.** Eine, die in einer")
    print("  ZUSAGE oder einem VERGLEICH steht, traegt eine Behauptung nach aussen; eine, die")
    print("  einen Zwischenstand beschreibt, traegt nichts. *Wer die naechsten zwoelf nach")
    print("  diesem Kriterium waehlt statt nach Aufwand, senkt das Risiko schneller als die")
    print("  Zahl.* Die Einteilung liest Stichwoerter und irrt in beide Richtungen -- sie")
    print("  sortiert eine Arbeitsliste, sie spricht nichts frei (W10).")
    if "--reichweite" in sys.argv:
        print()
        for d, z, zeile, tr, g in sorted(offen, key=lambda o: (o[4] is not None, not o[3], o[0])):
            marke = "TRAEGT" if tr else "  --  "
            if g:
                print(f"     {marke}  {d}:{z}  {zeile}")
                print(f"               GRUND ({g[0]}): {g[1]}")
            else:
                print(f"     {marke}  {d}:{z}  {zeile}")
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
