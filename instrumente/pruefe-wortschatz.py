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
roh_tabelle = m.group(1) if m else ""
roh = re.sub(r"^\s*[A-ZÄÖÜ]\w*", "", roh_tabelle, flags=re.M)
vok = set(re.findall(r"(?<!@)\b[a-z_][a-z0-9_]+\b", roh))  # Wortgrenzen: sonst "elf" aus "Self";
                                                     # `(?<!@)`: `@version` ist EIN Wort, nicht zwei
# Die Tabelle muss dieselben zwei Sonderformen fuehren koennen, die die EBNF-Seite seit
# G6 sieht: `@version` (fuehrendes `@` faellt aus der Wortgrenze) und `O` (ein einzelner
# Grossbuchstabe). Ohne diese Zeile kann die Tabelle den Befund gar nicht beantworten --
# der Waechter haette dann eine Meldung ohne moegliche Erwiderung.
vok |= set(re.findall(r"@[a-z_][a-z0-9_]*", roh))
vok |= {w for w in re.findall(r"(?<![\w@])([A-Z])(?![\w])", roh)}
# Grossgeschriebene Woerter der Tabelle (`Self`, `Some`, `None`) -- die
# Kleinbuchstabenregex oben sieht sie nicht, und ohne diese Zeile meldet der
# Waechter sie als "nicht in der Tabelle", obwohl sie danebenstehen.
# Nur aus den Tabellenzeilen selbst, ohne den Klammerkommentar -- sonst zaehlt der
# Waechter Prosa aus der Fussnote als Wortschatzwort.
vok |= set(re.findall(r"\b[A-Z][a-z][A-Za-z]*\b", re.sub(r"\([^)]*\)", "", roh)))
ebnf_roh = "\n".join(re.findall(r"```ebnf\n(.*?)```", d, re.S))
# **Kommentare zuerst heraus.** Die Regelregex unten sucht das `;` am ZEILENENDE; steht
# dahinter ein `(* … *)`, findet sie es nicht und `.*?` laeuft bis zum naechsten
# Zeilenende-Semikolon -- sie VERSCHLUCKT die Folgeregel, still und ohne Meldung.
# Gefunden 2026-08-15: elf Regeln waren so verschmolzen, darunter `program` selbst; von
# `program` aus war dann NICHTS erreichbar, und die Erreichbarkeitspruefung meldete 112
# Tote statt des einen Waechterfehlers. **Dritte blinde Stelle desselben Waechters** --
# und dieselbe Klasse wie G6: das Werkzeug sah an seinem eigenen Rand nicht hin.
ebnf = re.sub(r"\(\*.*?\*\)", "", ebnf_roh, flags=re.S)
# **G6, geschlossen.** Bis 2026-08-15 lautete die Regel: nimm Terminale der Form
# `[a-z_][a-z0-9_]*` mit Laenge > 1. Damit fielen ZWEI echte Terminale durch das Netz --
# `O` (Grossbuchstabe, `costexpr`) und `@version` (fuehrendes `@`) --, und der Waechter
# behauptete einen geschlossenen Wortschatz, ohne sie je angesehen zu haben. Dieselbe
# blinde Stelle wie zweimal zuvor, nur an einem anderen Rand.
#
# Die Ausnahme ist jetzt MECHANISCH statt implizit: Zeichenmaterial steht in genau diesen
# Regeln, und nur dort werden Ein-Zeichen-Terminale weggelassen. Alles andere zaehlt --
# gross, klein oder mit `@`.
ZEICHENREGELN = {"letter", "digit", "hexdigit", "char", "quote", "newline", "hex", "bin"}
zeichenmaterial = set()
for k, v in re.findall(r"^\s*([a-z][a-z0-9_]*)\s*=(.*?);\s*$", ebnf, re.M | re.S):
    if k in ZEICHENREGELN:
        zeichenmaterial |= set(re.findall(r'"([^"]*)"', v))
term = {t for t in re.findall(r'"(@?[A-Za-z_][A-Za-z0-9_]*)"', ebnf)
        if t not in zeichenmaterial and (len(t) > 1 or t.isupper())}

# Erreichbarkeit: eine definierte, aber von `program` aus nie erreichte Regel ist ein
# stiller Toter -- der Geschlossenheitspruefer sieht sie nicht, weil er die Gegenrichtung prueft.
prod = {}
for k, v in re.findall(r"^\s*([a-z][a-z0-9_]*)\s*=(.*?);\s*$", ebnf, re.M | re.S):
    prod.setdefault(k, "")            # mehrere Definitionen VEREINIGEN -- dict() nahm die letzte,
    prod[k] += " " + v                # und genau daran fiel `item` zweimal auf
erreicht, rand = set(), ["program"]
while rand:
    r = rand.pop()
    if r in erreicht or r not in prod: continue
    erreicht.add(r)
    rand += re.findall(r"\b([a-z][a-z0-9_]+)\b", re.sub(r'"[^"]*"', '', prod[r]))
LEX = {"comment"}   # lexikalisch, steht nicht in der Grammatik
tot_regel = sorted(set(prod) - erreicht - LEX)
if tot_regel:
    print(f"    UNERREICHBAR VON program ({len(tot_regel)}): " + ", ".join(tot_regel))

# **Sonderformen (G6):** Terminale, die ausdruecklich KEINE Wortschatzwoerter sind. Sie
# stehen in einer eigenen Tabellenzeile und werden hier aus dem Abgleich genommen -- aber
# gezaehlt und benannt. Der Unterschied zu vorher ist nicht die Ausnahme, sondern dass sie
# sichtbar ist: bis 2026-08-15 fielen genau diese zwei aus der Terminalregex heraus, und
# der Waechter behauptete Geschlossenheit ueber einer Menge, die er nie gesehen hatte.
m_s = re.search(r"^\s*Sonderform\s+(.*?)(?:\(|$)", roh_tabelle, re.M)
sonder = set(m_s.group(1).split()) if m_s else set()
vok -= sonder
term -= sonder

fehlt = sorted(term - vok)          # in der Grammatik, nicht im Wortschatz
tot   = sorted(vok - term)          # im Wortschatz, nirgends in der Grammatik

print(f"  Wortschatz: {len(term)} EBNF-Terminale, {len(vok)} Tabellenwoerter"
      + (f" + {len(sonder)} Sonderformen ({', '.join(sorted(sonder))})" if sonder else ""))
# **Der Zaehler ueber den Ausnahmen, mitgefuehrt ab drei.** Eine benannte Ausnahme ist eine
# Zusage; drei sind eine Liste; **fuenf sind ein Muster und verlangen eine eigene Regel**.
# Ein Ausnahmefach, das waechst, ohne dass jemand die Zahl ansieht, wird zur zweiten
# Grammatik -- dieselbe Bewegung wie ein Wortschatz, dessen Rand niemand prueft.
if len(sonder) >= 5:
    print(f"    !! {len(sonder)} SONDERFORMEN -- das ist kein Ausnahmefach mehr, sondern ein")
    print( "       Muster. Es verlangt eine eigene Regel: WAS macht ein Terminal zu einer")
    print( "       Sonderform, und warum ist die Menge geschlossen?")
elif sonder:
    print(f"    ({len(sonder)} von 5 -- ab fuenf verlangt die Klasse eine eigene Regel)")
if fehlt:
    print(f"    NICHT IN DER TABELLE ({len(fehlt)}): " + ", ".join(fehlt))
if tot:
    print(f"    TOTE WOERTER ({len(tot)}): " + ", ".join(tot))
# **Die Sprechprobe, und sie ruft sich selbst.**
#
# Bis zum 2026-08-20 hatte dieser Waechter keine -- gefunden von `pruefe-waechter.py` beim
# ersten Lauf. *Ein Waechter, der nicht rot werden kann, misst nichts* (R14), und gerade
# dieser hier hat seinen eigenen Rand schon DREIMAL uebersehen (G6, die verschmolzenen
# Regeln, die Spaltenkoepfe). **Wer dreimal am eigenen Rand vorbeisah, schuldet die Probe.**
#
# Sie schiebt ein erfundenes Terminal in eine KOPIE der Grammatik und verlangt, dass es als
# „nicht in der Tabelle" faellt. Die andere Richtung ist der Lauf darueber: er meldet nichts.
if "--probe" not in sys.argv:
    import subprocess, tempfile, os
    kopie = d.replace("```ebnf\n", '```ebnf\nzzprobe = "zzsprechprobe" ;\n', 1)
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as f:
        f.write(kopie)
        name = f.name
    try:
        r = subprocess.run([sys.executable, __file__, name, "--probe"],
                           capture_output=True, text=True, timeout=60)
        gefangen = "zzsprechprobe" in r.stdout
    except subprocess.TimeoutExpired:
        gefangen = False
        r = None
    finally:
        os.unlink(name)
    print()
    if gefangen:
        print("    Sprechprobe: ok (ein erfundenes Terminal faellt als „nicht in der Tabelle\")")
    else:
        print("    SPRECHPROBE GESCHEITERT: ein erfundenes Terminal geht durch --")
        print("    dieser Waechter kann nicht rot werden und misst damit nichts.")
        sys.exit(1)

sys.exit(1 if (fehlt or tot or tot_regel) else 0)
