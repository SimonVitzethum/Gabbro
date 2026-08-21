#!/usr/bin/env python3
"""**Steht diese Regel auf dem TECHNISCHEN Grund oder auf dem tragenden?**

Am 2026-08-20 fiel dieselbe Klasse viermal an einem Tag:

    Eine Pruefung, die aus dem NAHELIEGENDEN Grund gebaut wurde, deckt nicht, was der
    TRAGENDE Grund verlangt.

Der schaerfste der vier: `N011` fing Geister im Speicher, weil ein Geist **keine Absenkung
hat** -- ein Grund ueber die Darstellung. Was die Regel halten muss, ist etwas anderes: ein
LINEARER Wert hat Speicher, aber keinen PFAD, und *„genau einmal verbraucht" ist eine Aussage
ueber einen Kontrollflusspfad.* Der schaerfere Grund traf den Fall, den die schwaechere Regel
uebersah -- ein `linear type` im Slot ging mit null Fehlern durch.

## Die billige Naeherung

Die systematische Antwort waere teuer. **Die billige ist ein Durchgang ueber die
ABSAGETEXTE**, denn jede Regel traegt ihren Grund im eigenen Wortlaut, und der ist entweder

  * eine Eigenschaft der **ABSENKUNG** -- *„hat keinen Speicher", „ist ein unbekannter Ruf",
    „die Breite laeuft ueber", „existiert zur Laufzeit nicht"*. **Das sind die Verdaechtigen.**
  * eine Eigenschaft der **ZUSAGE** -- *„genau einmal", „auf jedem Pfad", „der Rufer
    verlaesst sich darauf", „ordnet nichts"*.

Das ist keine Analyse, sondern eine Zaehlung -- und sie haette alle vier gefunden.

## Und was das NICHT heisst

**Ein Verdaechtiger ist kein Befund.** Die Liste sagt: *diese Regel begruendet sich ueber die
Darstellung, und es lohnt zu fragen, ob ihre Zusage weiter reicht.* Sie sagt nicht, dass ein
Fall durchgeht -- W10, nicht abgewiesen ist nicht bestaetigt.
"""
import pathlib
import re
import sys

WURZEL = pathlib.Path(__file__).resolve().parent.parent
CHECK = WURZEL / "crates" / "gabbro-check" / "src"

# **Woerter ueber die DARSTELLUNG.** Wer so begruendet, begruendet ueber das Erzeugnis.
ABSENKUNG = [
    "at run time", "no lowering", "erase", "erased", "erases", "no storage",
    "unknown to the graph", "the width", "byte", "bytes", "machine word",
    "the array would have no size", "cannot lie in", "shifts every field",
    "does not exist at", "would have no size", "the generator emits", "no representation",
]
# **`word` steht NICHT in der Liste, und das ist eine Korrektur an mir selbst.** Es traf
# `S001` und `S003`, deren Notizen von einem *Wort des Wortschatzes* sprechen -- eine
# Aussage ueber die Grammatik, nicht ueber die Darstellung. *Ein Wortzaehler, der auf
# Teilzeichenketten sitzt, misst die Sprache des Kommentars und nicht seinen Gegenstand.*
# **Woerter ueber die ZUSAGE.** Wer so begruendet, begruendet ueber das Programm.
ZUSAGE = [
    "exactly once", "every path", "on no path", "the caller", "promise", "promises",
    "orders nothing", "counterpart", "could never run", "consumed", "held", "rank",
    "before", "after", "invariant", "obligation", "relies", "guarantee", "never delivers",
    "is a statement about", "chain", "order", "must be able to end", "duty",
]


def texte():
    """(Kennung, Text) je Absage -- Meldung und Notizen zusammen."""
    aus = {}
    for p in sorted(CHECK.glob("*.rs")):
        # **`saetze.rs` NENNT Kennungen, es vergibt keine** -- und dieser Waechter erkennt
        # eine Absage an `"XNNN",` im Quelltext. *Ohne diese Zeile las er den SATZ, den ein
        # Pass schuldet, als den Absagetext, den er druckt.*
        #
        # **Zum zweiten Mal dieselbe Klasse aus derselben Datei, am selben Tag** -- in
        # `pruefe-kennungen.py` meldete sie 146 Doppelbelegungen, hier verschob sie die
        # Gruende: „ohne erkennbaren Grund" fiel von 44 auf 14, „tragend" stieg von 102 auf
        # 135. **Und diese Richtung ist die gefaehrliche: es sah aus wie ein Fortschritt, den
        # niemand verdient hat.**
        #
        # *Die Lehre ist allgemeiner als die Zeile:* wer Quellen nach `"XNNN"` durchsucht,
        # misst NENNUNGEN und nicht VERGABEN, und ein Register ueber Regeln nennt sie alle.
        if p.name == "saetze.rs":
            continue
        q = p.read_text(encoding="utf-8")
        # Jede Absage: die Kennung, dann bis zum naechsten `);` auf Absagenebene.
        for m in re.finditer(r'"([A-Z][0-9]{3})"\s*,', q):
            code = m.group(1)
            fenster = q[m.end(): m.end() + 4000]
            # Nur die Zeichenkettenteile -- Bezeichner interessieren nicht.
            # **`re.S` -- und ohne das las die Zaehlung die halben Notizen nicht.**
            #
            # Rust setzt eine lange Zeichenkette mit `\` am Zeilenende fort; ohne
            # `DOTALL` bricht das Muster dort ab, und alles nach der ersten Fortsetzung
            # fiel weg. *Der Waechter meldete `N011` als verdaechtig -- eine Regel, deren
            # Notiz „genau einmal verbraucht" ausdruecklich nennt.* **Ein Instrument, das
            # seinen Gegenstand nur halb liest, misst seine eigene Leseweite.**
            stuecke = re.findall(r'"((?:[^"\\]|\\.)*)"', fenster, re.S)
            t = " ".join(stuecke[:30]).lower()
            aus.setdefault(code, "")
            aus[code] += " " + t
    return aus


def einordnen(t: str):
    a = [w for w in ABSENKUNG if w in t]
    z = [w for w in ZUSAGE if w in t]
    if z:
        return "tragend", a, z
    if a:
        return "VERDAECHTIG", a, z
    return "unklar", a, z


def haupt() -> int:
    t = texte()
    verdacht, tragend, unklar = [], [], []
    for code in sorted(t):
        art, a, _ = einordnen(t[code])
        if art == "VERDAECHTIG":
            verdacht.append((code, a[:3]))
        elif art == "tragend":
            tragend.append(code)
        else:
            unklar.append(code)

    print("== Gruende: steht die Regel auf der ABSENKUNG oder auf der ZUSAGE? ==")
    print("-- Ein Verdaechtiger ist KEIN Befund. Er sagt: diese Regel begruendet sich ueber")
    print("-- die Darstellung, und es lohnt zu fragen, ob ihre Zusage weiter reicht.")
    print()
    print(f"   {len(verdacht)} verdaechtig · {len(tragend)} tragend · {len(unklar)} unklar")
    print()
    for code, w in verdacht:
        print(f"   VERDAECHTIG  {code}   ({', '.join(w)})")
    # **Die UNKLAREN sind der groessere Befund** (2026-08-20).
    #
    # Eine Regel, deren Absagetext den Grund in KEINER der beiden Sprachen sagt, sagt ihn
    # vielleicht gar nicht. *Das ist keine Fehlklassifikation, sondern die Frage eine Ebene
    # tiefer:* wer eine Absage liest und daraus nicht erkennt, ob sie ueber die Darstellung
    # oder ueber die Zusage begruendet, kann auch nicht pruefen, ob sie weit genug reicht.
    print()
    print(f"   {len(unklar)} unklar -- der Text sagt den Grund in KEINER der beiden Sprachen:")
    for i in range(0, len(unklar), 12):
        print("      " + " ".join(unklar[i:i + 12]))

    # **Die Sprechprobe: die vier bekannten Instanzen muessen herausfallen.**
    #
    # Der Waechter misst nichts, wenn er die Faelle nicht nennt, an denen die Klasse
    # gefunden wurde. Geprueft wird gegen die WORTLAUTE VON DAMALS -- nicht gegen die
    # heutigen, denn drei davon sind inzwischen nachgezogen.
    print()
    print("== Sprechprobe: findet die Zaehlung die vier bekannten Instanzen? ==")
    damals = {
        "N011 (2026-08-19)": "is a ghost type and cannot lie in a slot field "
                             "a ghost value does not exist at run time the generator erases it",
        "E009 (Konstruktor)": "the call effects are undecidable is unknown to the graph",
        "Geistloeschung":     "a ghost type has no lowering no byte no heap no cycle",
        "M104":              "leaves the width of the result type",
    }
    fehler = 0
    for name, text in damals.items():
        art, a, _ = einordnen(text.lower())
        if art == "VERDAECHTIG":
            print(f"   ok -- {name} faellt als verdaechtig ({', '.join(a[:2])})")
        else:
            print(f"   GESCHEITERT -- {name} wird als `{art}` gefuehrt")
            fehler = 1
    # Und die Gegenrichtung: eine Regel, die ueber die ZUSAGE begruendet, darf NICHT fallen.
    art, _, z = einordnen(
        "`w` is listed under consumes but is consumed on no path "
        "consumes is a promise to the caller: the value is gone afterwards".lower()
    )
    if art == "tragend":
        print(f"   ok -- eine Zusageregel (L101) faellt NICHT ({', '.join(z[:2])})")
    else:
        print(f"   GESCHEITERT -- L101 wird als `{art}` gefuehrt; der Waechter sagt zu jedem ja")
        fehler = 1
    if fehler:
        return 1

    print()
    print("== Und was das NICHT heisst ==")
    print("  Gezaehlt wird ueber eine GESCHLOSSENE Wortliste. Eine Regel, die ihren Grund")
    print("  mit anderen Woertern sagt, faellt hier nicht auf -- die Zaehlung verpflichtet,")
    print("  sie spricht nicht frei (W10). Und ein Verdaechtiger ist eine Frage, kein Fehler.")
    return 0


if __name__ == "__main__":
    sys.exit(haupt())
