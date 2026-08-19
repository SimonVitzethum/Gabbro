#!/usr/bin/env python3
"""**Widerrufene Saetze -- die Klasse, die dreimal von Hand gefunden wurde.**

`pruefe-todo.py` haelt `TODO.md` gegen sechs Klassen, darunter *stehengebliebene Zahl*. Er
sieht **genau eine Datei.** Am 2026-08-19 standen in `dokumente/PLAN.md` sechs Saetze, die
das Gegenteil des Gebauten sagten -- vier Abschnitte ueber dem Bauplan, der sie widerlegt.

    Zeile 1742  "Gleitkomma -- nicht im Kern"
    Zeile 1826  "M1 ist ueber Intervallen ganzer Zahlen gebaut"
    Zeile 1983  3D-Renderer: fuer immer draussen
    Zeile 2018  "hat keinen Bereich, den M101 vergleichen koennte"
    Zeile 2150  "opaque zum Beissen bringen -- eingeschoben"
    Zeile 2158  Punkt 5: nicht bauen

**Der Unterschied zu einer bloszen Ungenauigkeit:** ein widerrufener Satz sagt nicht *"hier
ist noch etwas offen"*, sondern *"das geht nie"*. Er verhindert Arbeit statt sie zu
verzoegern -- und er tut es leise, weil er wie ein Ergebnis aussieht.

**Die Ausnahme ist die Durchstreichung.** Der Ordner streicht durch, er loescht nicht:
`~~alt~~ **neu**` ist die vorhandene Form (aarch64, Festkomma, das Memo). Ein Vorkommen in
einem durchgestrichenen Absatz ist deshalb erlaubt -- ebenso eines in einem Block zwischen
`<!-- widerruf:aus -->` und `<!-- widerruf:an -->`, damit ein Widerrufsregister den
widerrufenen Satz ZITIEREN kann.

**Und die Grenze, damit die Zahl nicht mehr verspricht als sie misst:** der Waechter findet
nur, was jemand als widerrufen aufgeschrieben hat. *Er ist ein Gedaechtnis, kein Urteil.*

    ./pruefe-widerruf.py
"""
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent

# Je Eintrag vier Felder, und ohne alle vier wird er nicht angenommen (ZAHN 1):
#   muster  was nicht mehr dastehen darf
#   datum   wann es widerrufen wurde
#   grund   WAS es widerrufen hat -- eine Datei, ein Beispiel, eine Kennung
#   ersatz  was stattdessen gilt
WIDERRUFE = [
    dict(kennung="WF1",
         muster=r"[Gg]leitkomma[^.\n]{0,40}nicht im Kern"
                r"|kein[e]? Gleitkomma[^.\n]{0,20}im Kern"
                r"|[Nn]o floating\s*\n?\s*point in the core",
         datum="2026-08-18", grund="«F1», `typen.rs`: `Typ::Gleitkomma(FBereich)`",
         ersatz="`f32`/`f64` mit Bereich, NaN- und Unendlichbit -- `beispiele/26-gleitkomma.gab`"),
    dict(kennung="WF2",
         muster=r"M1 ist ueber Intervallen \*\*?ganzer\*\*? Zahlen"
                r"|M1 ist über Intervallen \*\*ganzer\*\* Zahlen"
                r"|M1 ist über Intervallen ganzer Zahlen",
         datum="2026-08-18", grund="`typen.rs`: `FBereich { breite, lo, hi, kann_nan, … }`",
         ersatz="M1 traegt beide Bereichsarten; `M101` vergleicht auch Gleitkommabereiche"),
    dict(kennung="WF3",
         muster=r"keinen Bereich, den `M101` vergleichen",
         datum="2026-08-18", grund="`m1.rs`: der Gleitkommazweig von `passt`",
         ersatz="`M101` vergleicht ihn, und `F001` prueft die zwei Bits daneben"),
    dict(kennung="WF4",
         muster=r"Gleitkomma[^\n]{0,60}f[uü]r immer drau[sß]en"
                r"|f[uü]r immer drau[sß]en[^\n]{0,60}Gleitkomma",
         datum="2026-08-18", grund="dieselbe Spalte der Drei-Spalten-Tabelle",
         ersatz="3D-Renderer: teilweise heute, ganz nach der Erweiterung"),
    dict(kennung="WD1",
         muster=r"`opaque`[^\n]{0,30}h[aä]lt nicht"
                r"|undurchsichtige[rn]? Typ[^\n]{0,40}keine Wirkung",
         datum="2026-08-18", grund="`D003` (die Rechnung) und `D004` (die Modulgrenze)",
         ersatz="`opaque` beisst; offen ist die TUER, nicht der Biss"),
    dict(kennung="WE1",
         muster=r"[Kk]ein Pass liest `?ensures`?"
                r"|`ensures` (?:wird von keinem Pass gelesen|liest niemand)"
                r"|Tippfehler in einem `ensures` f[aä]llt nicht"
                r"|`ensures`[^\n]{0,40}gez[aä]hlt, nie gehalten"
                r"|[Kk]ein Pass liest Pr[aä]dikate"
                r"|prueft auch keiner ihre NAMEN|prüft auch keiner ihre Namen",
         datum="2026-08-18", grund="`m1.rs`: `ensures_pruefen` -- `M109`/`M110`/`M111`",
         ersatz="die WOHLGEFORMTHEIT wird geprueft (Namen, `result`, Herstellbarkeit); "
                "was offen bleibt, ist die EINLOESUNG durch den Rumpf"),
    dict(kennung="WB1",
         muster=r"«B24»[^\n]{0,80}(?:ist offen|bleibt offen|blockiert|eine Entscheidung, und sie ist die einzige)"
                r"|[Ww]as blockiert, ist der IP-Kopf"
                r"|«B24» is (?:an )?open"
                r"|`format` weigert sich f[uü]r jede davon"
                r"|Netzwerkstack[^\n|]{0,40}blockiert an"
                r"|blockiert an \*\*einer\*\* Entscheidung",
         datum="2026-08-18", grund="`PFLICHTEN.md`:141/:155 -- entschieden; "
                                   "`beispiele/24-ip-kopf.gab` und `emit.rs`:1416 -- gebaut",
         ersatz="entschieden UND gebaut; seit 2026-08-19 auch im Pruefer (`N007`/`N008`)"),
    dict(kennung="WM1",
         muster=r"(?:Kennzahl|metric|kennzahl)[^\n]{0,60}(?:>=|≥)\s*1,9"
                r"|(?:>=|≥)\s*1,90\b|(?:>=|≥)\s*1,98\b|(?:>=|≥)\s*2,03\b"
                r"|steht (?:die Kennzahl|the metric)[^\n]{0,30}1,9",
         datum="2026-08-19", grund="`w` war an VERUS-Zeilen gemessen; Gabbro beweist in "
                                   "Isabelle/HOL, und dessen zehn Theorien tragen NULL W",
         ersatz="unbekannt, > 0,5 -- die untere Schranke ist ein Argument (W > 0), "
                "die obere hat heute niemand"),
    dict(kennung="WD2",
         muster=r"`opaque` zum Bei[sß]en bringen[^\n]{0,30}\*\*eingeschoben\*\*",
         datum="2026-08-18", grund="`m1.rs`:745, Gift 79 und vier Sprechproben",
         ersatz="gebaut; Punkt 3 der Reihenfolge ist zu"),
]

# Welche Dateien der Waechter liest. TODO.md und DONE.md stehen mit drin: ein widerrufener
# Satz ist dort genauso teuer, und `pruefe-todo.py` sieht diese Klasse nicht.
DATEIEN = (sorted(W.glob("dokumente/*.md"))
           + [W / "TODO.md", W / "DONE.md", W / "README.md"]
           # **Und die Beispiele.** Ihre Kommentare sind Prosa, die gelesen wird wie ein
           # Dokument -- `22-bootstrecke.gab` traegt fuenf Zeilen Befundtext ueber `ensures`.
           # *Ein widerrufener Satz ist dort genauso teuer und faellt sonst niemandem auf.*
           + sorted(W.glob("beispiele/*.gab")))

AUS = re.compile(r"<!--\s*widerruf:aus\s*-->.*?<!--\s*widerruf:an\s*-->", re.S)


def absaetze(text):
    """(Zeilennummer, Absatztext) -- Absaetze sind durch Leerzeilen getrennt."""
    zeile, puffer, start = 1, [], 1
    for z in text.split("\n"):
        if z.strip() == "":
            if puffer:
                yield start, "\n".join(puffer)
            puffer, start = [], zeile + 1
        else:
            if not puffer:
                start = zeile
            puffer.append(z)
        zeile += 1
    if puffer:
        yield start, "\n".join(puffer)


def suche(text, muster):
    """Lebende Treffer: nicht in einem `widerruf:aus`-Block, nicht durchgestrichen."""
    # Der ausgenommene Block wird laengengleich ersetzt, damit die Zeilennummern stimmen.
    text = AUS.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), text)
    treffer = []
    for zeile, absatz in absaetze(text):
        for m in re.finditer(muster, absatz):
            if "~~" in absatz:
                continue  # durchgestrichen -- der Ordner loescht nicht, er streicht durch
            versatz = absatz[:m.start()].count("\n")
            treffer.append((zeile + versatz, m.group(0)[:70].replace("\n", " ")))
    return treffer


def lauf(dateien, widerrufe):
    befunde = []
    for e in widerrufe:
        for d in dateien:
            if not d.exists():
                continue
            for zeile, text in suche(d.read_text(), e["muster"]):
                befunde.append((e["kennung"], d.relative_to(W), zeile, text))
    return befunde


def main():
    # ZAHN 1 -- kein Eintrag ohne alle vier Felder.
    for e in WIDERRUFE:
        for f in ("muster", "datum", "grund", "ersatz"):
            if not e.get(f):
                print("FEHLER: Eintrag %s ohne `%s`" % (e["kennung"], f))
                return 2

    befunde = lauf(DATEIEN, WIDERRUFE)

    print("== Widerrufene Saetze: %d Eintraege, %d Dateien ==" % (len(WIDERRUFE), len(DATEIEN)))
    for e in WIDERRUFE:
        eigene = [b for b in befunde if b[0] == e["kennung"]]
        marke = "%d LEBENDE" % len(eigene) if eigene else "zu"
        print("  %-5s %-10s %s" % (e["kennung"], marke, e["ersatz"]))
        for _, datei, zeile, text in eigene:
            print("        %s:%d  %s" % (datei, zeile, text))

    # ZAHN 2 (R14) -- der Waechter weist nach, dass er messen kann. Beide Richtungen:
    # der eingesetzte Satz musz fallen, der durchgestrichene nicht.
    probe = W / "dokumente" / "PLAN.md"
    roh = probe.read_text()
    gift = roh + "\n\nGleitkomma ist nicht im Kern, und dabei bleibt es.\n"
    sauber = roh + "\n\n~~Gleitkomma ist nicht im Kern~~ -- gefallen 2026-08-18.\n"
    faellt = len(suche(gift, WIDERRUFE[0]["muster"])) > len(suche(roh, WIDERRUFE[0]["muster"]))
    haelt = len(suche(sauber, WIDERRUFE[0]["muster"])) == len(suche(roh, WIDERRUFE[0]["muster"]))
    print("\n== Sprechprobe (R14) ==")
    print("  eingesetzter Satz faellt:      %s" % ("ja" if faellt else "NEIN"))
    print("  durchgestrichener bleibt frei: %s" % ("ja" if haelt else "NEIN"))
    if not (faellt and haelt):
        print("== WIDERRUF: der Waechter misst nicht ==")
        return 2

    if befunde:
        print("\n== WIDERRUF: %d lebende Vorkommen ==" % len(befunde))
        print("   Durchstreichen mit Datum, nicht loeschen -- oder den Eintrag zuruecknehmen,")
        print("   wenn der Widerruf selbst falsch war.")
        return 1
    print("\n== WIDERRUF: ALL PASS -- kein widerrufener Satz steht lebend da ==")
    print("   Und was das NICHT heiszt: der Waechter kennt %d Widerrufe. Gegen einen Satz," % len(WIDERRUFE))
    print("   den niemand als ueberholt erkannt hat, hilft er nicht.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
