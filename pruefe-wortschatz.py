#!/usr/bin/env python3
"""Deckt die Wortschatztabelle in SYNTAX.md die Terminale der EBNF?

Zweite blinde Stelle desselben Waechters: er prueft die NICHTTERMINALE auf
Geschlossenheit und behauptet daneben einen "geschlossenen Wortschatz", ohne die
TERMINALE je anzusehen. Gefunden 2026-08-14 von einem Pruefagenten: 27 echte
Schluesselwoerter standen in der EBNF und nicht in der Tabelle.
"""
import re, sys, pathlib

d = pathlib.Path(sys.argv[1]).read_text()
m = re.search(r"```\n(  Struktur.*?)```", d, re.S)
# Die Spaltenkoepfe stehen gross am Zeilenanfang -- ohne sie zu entfernen zaehlt der
# Pruefer "blauf" (aus "Ablauf") als totes Wort. Erster Fund des Pruefers war er selbst.
roh = re.sub(r"^\s*[A-ZÄÖÜ]\w*", "", m.group(1), flags=re.M) if m else ""
vok = set(re.findall(r"\b[a-z_][a-z0-9_]+\b", roh))   # Wortgrenzen: sonst "elf" aus "Self"
ebnf = "\n".join(re.findall(r"```ebnf\n(.*?)```", d, re.S))
# Ein-Zeichen-Terminale stammen aus Zeichenbereichen ("a" … "z") und sind keine Woerter.
term = {t for t in re.findall(r'"([a-z_][a-z0-9_]*)"', ebnf) if len(t) > 1}

fehlt = sorted(term - vok)          # in der Grammatik, nicht im Wortschatz
tot   = sorted(vok - term)          # im Wortschatz, nirgends in der Grammatik

print(f"  Wortschatz: {len(term)} EBNF-Terminale, {len(vok)} Tabellenwoerter")
if fehlt:
    print(f"    NICHT IN DER TABELLE ({len(fehlt)}): " + ", ".join(fehlt))
if tot:
    print(f"    TOTE WOERTER ({len(tot)}): " + ", ".join(tot))
sys.exit(1 if (fehlt or tot) else 0)
