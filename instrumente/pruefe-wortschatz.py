#!/usr/bin/env python3
"""Deckt die Wortschatztabelle in SYNTAX.md die Terminale der EBNF?

Zweite blinde Stelle desselben Waechters: er prueft die NICHTTERMINALE auf
Geschlossenheit und behauptet daneben einen "geschlossenen Wortschatz", ohne die
TERMINALE je anzusehen. Gefunden 2026-08-14 von einem Pruefagenten: 27 echte
Schluesselwoerter standen in der EBNF und nicht in der Tabelle.
"""
import re, sys, pathlib

# **TOOTH 0 -- THE SUBJECT HAS TO BE THERE** (2026-08-31). Until today the first statement
# of this file was `pathlib.Path(sys.argv[1]).read_text()`: without an argument an
# `IndexError`, over a tree without `dokumente/` a `FileNotFoundError` -- both with return
# code **1**, both a traceback, and in a chain both look like a gap in the vocabulary.
# *A crash is not a refusal -- a NAMED refusal is*, and a missing subject says the SETUP
# has to change, not the tree.
if len(sys.argv) < 2 or sys.argv[1].startswith("--"):
    print("ABBRUCH: kein Dateiargument -- dieser Waechter liest `dokumente/SYNTAX.md`.",
          file=sys.stderr)
    print("  Ohne Gegenstand wurde NICHTS gemessen; sein Argument steht in"
          " `pruefe-waechter.py:ARGUMENTE`.", file=sys.stderr)
    sys.exit(2)
_ziel = pathlib.Path(sys.argv[1])
if not _ziel.is_file():
    print(f"ABBRUCH: {_ziel} fehlt -- der Gegenstand dieses Waechters ist nicht hier.",
          file=sys.stderr)
    print("  Es wurde NICHTS gemessen: ohne Grammatik gibt es weder Terminal noch"
          " Tabellenwort.", file=sys.stderr)
    sys.exit(2)

d = _ziel.read_text()
# **The anchor reads a ROW LABEL, and a row label is written in a language** (2026-09-01).
# `  Struktur` is the first row of the vocabulary table; it is how this tool finds the table
# at all. Translate that one word and `roh_tabelle` goes empty -- every terminal then counts
# as missing from the table. *The whole vocabulary hangs on one German noun.*
#
# Both spellings stand here, and the German one STAYS: a tool that reads only the new
# spelling has the same hole, mirrored, from the first file that has not moved yet.
m = re.search(r"```\n(  (?:Struktur|Structure).*?)```", d, re.S)
# Die Spaltenkoepfe stehen gross am Zeilenanfang -- ohne sie zu entfernen zaehlt der
# Pruefer "blauf" (aus "Ablauf") als totes Wort. Erster Fund des Pruefers war er selbst.
#
# **The label has to be ONE word, and that is a constraint on the DOCUMENT** -- this line is
# why. A two-word English label (`Special form`) would leave its second word standing, and
# `form` would enter the vocabulary as a table word out of nowhere. The optional group below
# takes that specific case; anything longer belongs in one word.
roh_tabelle = m.group(1) if m else ""
roh = re.sub(r"^\s*[A-ZÄÖÜ]\w*(?:\s+forms?\b)?", "", roh_tabelle, flags=re.M)
# **The parenthetical is a COMMENT of the table, not a row of it** (2026-09-01). Today it
# holds a German aside pointing at footnote G6, and it contributes nothing BY ACCIDENT:
# every word in it happens to be capitalised or one letter long. Its English form
# (*"not vocabulary words -- see footnote G6"*) would put four lowercase words into `vok`,
# and each would surface as a DEAD WORD in a table that never gained a row.
# *An accident is not a rule*, so the parenthesis comes out for every pass now, not just
# for the capitalised one below.
roh = re.sub(r"\([^)]*\)", "", roh)
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
m_s = re.search(r"^\s*(?:Sonderform|Special(?:\s+forms?)?)\s+(.*?)(?:\(|$)", roh_tabelle, re.M)
sonder = set(m_s.group(1).split()) if m_s else set()
vok -= sonder
term -= sonder

# **Two empty sets cover each other completely, and that is not coverage** (2026-08-31).
# Measured over an empty tree: no vocabulary table matched, no EBNF block was found, `fehlt`
# and `tot` both came out empty -- and this file exited 0 with the line `Wortschatz: 0 EBNF
# terminals, 0 table words`. **A closed vocabulary over nothing.** That is W17 word for word:
# not a wrong verdict, a POSITIVE verdict about nothing, and it looks like a result.
#
# The `--probe` branch is exempt: the speech test runs this same file over a COPY that is
# supposed to be readable, and it reads the globals, not the return code.
if "--probe" not in sys.argv and not (term and vok):
    print(f"ABBRUCH: {len(term)} EBNF-Terminale gegen {len(vok)} Tabellenwoerter -- "
          "mindestens eine Menge ist LEER.")
    print("  Zwei leere Mengen decken einander, und das ist kein geschlossener Wortschatz,")
    print("  sondern eine Datei, die dieses Werkzeug nicht lesen konnte. NICHTS gemessen.")
    sys.exit(2)

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
# speech_test: begin
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
        # 2, not 1: the last sentence says NOTHING was measured, so the return code says it
        # too. Reading it as a finding would send someone looking through SYNTAX.md for a
        # gap that this run never looked for.
        sys.exit(2)

    # **THE COUNTER-DIRECTION: the same grammar with ENGLISH row labels** (2026-09-01).
    #
    # The probe above proves the tool can go red. It says nothing about the language of the
    # table, and the language of the table is what the two patterns above hang on. So the
    # same file is read once more with every row label translated, and the demand is that
    # **both readings produce the same two numbers**.
    #
    # *This is the half that has to exist BEFORE `SYNTAX.md` moves.* Afterwards it is too
    # late to find out: an anchor that misses makes `roh_tabelle` empty, the empty-set latch
    # fires, and a translation looks like a broken grammar.
    ETIKETTEN = [("Struktur", "Structure"), ("Vertraege", "Contracts"),
                 ("Wirkungen", "Effects"), ("Ablauf", "Control"), ("Zeiger", "Pointers"),
                 ("Bibliothek", "Library"), ("Domaenen", "Domains"), ("Typen", "Types"),
                 ("Eingebaut", "Builtin"), ("Sonderform", "Special")]
    englisch = d
    for de, en in ETIKETTEN:
        englisch = englisch.replace("\n  %s " % de, "\n  %s " % en)
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as f:
        f.write(englisch)
        name_en = f.name
    try:
        r2 = subprocess.run([sys.executable, __file__, name_en, "--probe"],
                            capture_output=True, text=True, timeout=60)
        m2 = re.search(r"Wortschatz: (\d+) EBNF-Terminale, (\d+) Tabellenwoerter", r2.stdout)
    except subprocess.TimeoutExpired:
        m2 = None
    finally:
        os.unlink(name_en)
    gleich = bool(m2) and (int(m2.group(1)), int(m2.group(2))) == (len(term), len(vok))
    if gleich:
        print("    Gegenrichtung: ok (dieselbe Grammatik mit ENGLISCHEN Zeilenetiketten "
              "gibt dieselben %d / %d)" % (len(term), len(vok)))
    else:
        gemessen = ("%s / %s" % m2.groups()) if m2 else "gar nichts -- die Tabelle war weg"
        print("    GEGENRICHTUNG GESCHEITERT: mit englischen Zeilenetiketten misst dieser")
        print("    Waechter %s statt %d / %d." % (gemessen, len(term), len(vok)))
        print("    Die Muster haengen an einem DEUTSCHEN Etikett, und `SYNTAX.md` wandert.")
        sys.exit(2)

# speech_test: end
sys.exit(1 if (fehlt or tot or tot_regel) else 0)
