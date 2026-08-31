#!/usr/bin/env python3
"""Findet Bereichspflichten in einem Rust-Baum und schlaegt eine Klasse vor (K/V1/V2/V3/F/N).

**KEIN MESSGERAET.** Gefahren am 2026-08-14, Ergebnis in MESSUNGEN.md als UNGUELTIG
berichtet: er besteht die Sprechprobe des Protokolls (drei bekannte Fundstellen) und liegt
trotzdem in 3 von 5 handgeprueften N-Stellen falsch. Was ihm fehlt -- Bereichsrechnung ueber
`1 << x`, Boolesche Ketten statt `if`, dokumentierte Vorbedingungen als F -- ist zusammen
genau M1+V1--V3, angewandt auf Rust. Er bleibt hier als **Finder von Kandidaten**.

Das Protokoll steht in MESSUNGEN.md und ist VOR diesem Skript geschrieben und committet.
Dieses Skript aendert es nicht; wo es etwas nicht entscheiden kann, kippt es nach N.

    ./instrumente/zaehle-narrow.py [BAUM]        Standard: ~/Dokumente/SEL4Lake/SEL4Lake
    ./instrumente/zaehle-narrow.py --sprechprobe Nur die drei bekannten Fundstellen pruefen

DER ZAEHLER IST EINE HEURISTIK UEBER ZEILEN, kein Rust-Parser. Er gilt nur als Messgeraet,
wenn er die drei Stellen findet, die der Ordner schon kennt -- s. `sprechprobe()`.
"""
import re
import sys
import pathlib
from collections import Counter, defaultdict

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.py`.
# `sys.path` gets the tool's own directory because this file is also LOADED by
# `abnahme.py` (via `importlib`), and then `sys.path[0]` is the working directory.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

# --- Die drei Sprechproben aus dem Protokoll. Findet der Zaehler sie nicht, ist die Zahl
# --- ungueltig -- nicht ungenau, ungueltig.
SPRECHPROBEN = [
    ("crates/caprock-sched/src/lib.rs", "leading_zeros"),
    ("kernel/src/colors.rs", "leading_zeros"),
    ("crates/caprock-hal/src/cache_decode.rs", "leading_zeros"),
]

BAUM = pathlib.Path.home() / "Dokumente" / "SEL4Lake" / "SEL4Lake"
ORDNER = ["kernel", "crates", "programs"]

# Ein Name, wie ihn eine Bedingung nennen kann: `n`, `self.x`, `a.b.c`, `x[i]`.
NAME = r"(?:[A-Za-z_][A-Za-z0-9_]*)(?:\s*\.\s*[A-Za-z_][A-Za-z0-9_]*|\s*\[[^\]\[]*\])*"
ZAHL = r"(?:0x[0-9A-Fa-f_]+|0b[01_]+|[0-9][0-9_]*)"

# Ausdruecklich behandelte Operationen -- keine Pflicht, kein Mensch (Spalte K).
BEHANDELT = re.compile(
    r"\b(?:checked_sub|saturating_sub|wrapping_sub|overflowing_sub|abs_diff"
    r"|checked_div|checked_rem|saturating_div|wrapping_div|checked_add"
    r"|saturating_add|wrapping_add|NonZero)"
)


def entkerne(text):
    """Kommentare und Zeichenketten raus -- sonst zaehlt der Zaehler Prosa.

    Zeilenzahlen bleiben erhalten: jedes entfernte Zeichen wird durch ein Leerzeichen
    ersetzt, jedes Zeilenende bleibt stehen.
    """
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
        elif c == "/" and i + 1 < n and text[i + 1] == "*":
            tiefe = 0
            while i < n:
                if text[i : i + 2] == "/*":
                    tiefe += 1
                    out.append("  ")
                    i += 2
                elif text[i : i + 2] == "*/":
                    tiefe -= 1
                    out.append("  ")
                    i += 2
                    if tiefe == 0:
                        break
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
        elif c == '"':
            out.append(" ")
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    out.append(" ")
                    i += 1
                if i < n:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
            out.append(" ")
            i += 1
        elif c == "'" and i + 2 < n and text[i + 2] == "'":
            out.append("   ")
            i += 3
        else:
            out.append(c)
            i += 1
    return "".join(out)


class Funktion:
    def __init__(self, name, params, zeilen, erste_zeile):
        self.name = name
        self.params = params
        self.zeilen = zeilen          # Liste der Rumpfzeilen
        self.erste_zeile = erste_zeile  # 1-basiert, Zeile der ersten Rumpfzeile


def funktionen(text):
    """Schneidet die Funktionsruempfe samt Parameternamen heraus."""
    zeilen = text.split("\n")
    out = []
    i = 0
    kopf = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^>{;]*>)?\s*\(")
    while i < len(zeilen):
        m = kopf.search(zeilen[i])
        if not m:
            i += 1
            continue
        # Signatur einsammeln, bis die runde Klammer zu ist.
        sig = zeilen[i][m.end() - 1 :]
        j = i
        tiefe = sig.count("(") - sig.count(")")
        while tiefe > 0 and j + 1 < len(zeilen):
            j += 1
            sig += " " + zeilen[j]
            tiefe += zeilen[j].count("(") - zeilen[j].count(")")
        params = set(re.findall(r"(?:^|[,(])\s*(?:mut\s+)?([a-z_][A-Za-z0-9_]*)\s*:", sig))
        params.add("self")
        # Rumpf: vom ersten `{` nach der Signatur bis zur passenden Klammer.
        k = j
        while k < len(zeilen) and "{" not in zeilen[k]:
            if ";" in zeilen[k]:
                break
            k += 1
        if k >= len(zeilen) or "{" not in zeilen[k]:
            i = j + 1
            continue
        anfang = k
        tiefe = 0
        rumpf = []
        while k < len(zeilen):
            tiefe += zeilen[k].count("{") - zeilen[k].count("}")
            rumpf.append(zeilen[k])
            if tiefe <= 0 and k > anfang - 1 and "{" in "".join(rumpf):
                break
            k += 1
        # Defekt 2 der Eichung: **ein Verschlussparameter ist ein Parameter.** Die Pflicht
        # wandert dort genauso zum Aufrufer wie bei einer Funktion; wer ihn uebersieht,
        # zaehlt jede Stelle in einem `|a, b| …` faelschlich nach N.
        for z in rumpf:
            for verschluss in re.finditer(r"\|\s*([^|]{1,200}?)\s*\|", z):
                inneres = verschluss.group(1)
                if ":" not in inneres and "," not in inneres and not inneres.strip():
                    continue
                params |= set(
                    re.findall(r"(?:^|,)\s*(?:mut\s+)?([a-z_][A-Za-z0-9_]*)\s*:", inneres)
                )
        out.append(Funktion(m.group(1), params, rumpf, anfang + 1))
        i = k + 1
    return out


AS_TYP = re.compile(
    r"\s+as\s+(?:u8|u16|u32|u64|usize|i8|i16|i32|i64|isize)\s*$"
)


def ohne_cast(t):
    """`pd as usize` ist derselbe Ort wie `pd`. Ohne diese Zeile schneidet der Zaehler
    den Operanden als `usize` und findet keine Pruefung mehr -- Defekt 1 der Eichung."""
    vorher = None
    while vorher != t:
        vorher = t
        t = AS_TYP.sub("", t).strip()
    return t


def _operand_links(z, i):
    """Der Operand links von Stelle i -- ueber Klammern hinweg, ohne Regex."""
    j = i
    while j > 0 and z[j - 1] in " \t":
        j -= 1
    # `x as u64 - 1`: der Cast gehoert zum Operanden, nicht zwischen ihn und den Operator.
    for wort in ("usize", "isize", "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"):
        marke = " as " + wort
        if z[:j].rstrip().endswith(wort) and marke in z[:j]:
            j = z[:j].rstrip().rfind(marke)
            break
    ende = j
    while j > 0:
        c = z[j - 1]
        if c in ")]":
            auf, zu = ("(", ")") if c == ")" else ("[", "]")
            tiefe = 0
            while j > 0:
                j -= 1
                if z[j] == zu:
                    tiefe += 1
                elif z[j] == auf:
                    tiefe -= 1
                    if tiefe == 0:
                        break
        elif c.isalnum() or c in "_.:":
            j -= 1
        else:
            break
    return z[j:ende].strip()


def _operand_rechts(z, i):
    """Der Operand rechts von Stelle i -- Klammern, Methodenaufrufe, `as T` faellt weg."""
    j = i
    while j < len(z) and z[j] in " \t":
        j += 1
    anfang = j
    while j < len(z):
        c = z[j]
        if c in "([":
            auf, zu = (c, ")" if c == "(" else "]")
            tiefe = 0
            while j < len(z):
                if z[j] == auf:
                    tiefe += 1
                elif z[j] == zu:
                    tiefe -= 1
                    if tiefe == 0:
                        j += 1
                        break
                j += 1
        elif c.isalnum() or c in "_.:":
            j += 1
        else:
            break
    return z[anfang:j].strip()


def stellen(rumpf):
    """Alle Bereichspflichten eines Rumpfes: (art, zeilennr_im_rumpf, links, rechts).

    Operanden werden ueber balancierte Klammern geschnitten, nicht ueber ein Muster:
    `31 - self.bitmap.leading_zeros()` und `u64::BITS - (n - 1).leading_zeros()` sind
    genau die Formen, an denen ein Muster scheitert -- und genau die drei Sprechproben.
    """
    out = []
    for nr, z in enumerate(rumpf):
        if BEHANDELT.search(z):
            continue
        for i, c in enumerate(z):
            if c == "-":
                if i + 1 < len(z) and z[i + 1] in ">=-":
                    continue
                if i > 0 and z[i - 1] in "-<":
                    continue
                links = _operand_links(z, i)
                if not links:              # unaeres Minus
                    continue
                rechts = _operand_rechts(z, i + 1)
                if rechts:
                    out.append(("sub", nr, links, rechts))
            elif c == "/":
                if i + 1 < len(z) and z[i + 1] in "/*=":
                    continue
                if i > 0 and z[i - 1] in "/*":
                    continue
                links, rechts = _operand_links(z, i), _operand_rechts(z, i + 1)
                if links and rechts:
                    out.append(("div", nr, links, rechts))
            elif c == "%":
                if i + 1 < len(z) and z[i + 1] == "=":
                    continue
                links, rechts = _operand_links(z, i), _operand_rechts(z, i + 1)
                if links and rechts:
                    out.append(("rem", nr, links, rechts))
    return out


def zahlwert(t):
    """Nur ZAHLEN. Ein benannter `const` hat fuer diesen Zaehler keinen Wert -- und ohne
    Wert kann er nicht pruefen, ob eine Schranke traegt. Kippregel: dann nach N."""
    t = t.strip().replace("_", "")
    try:
        if t.startswith("0x"):
            return int(t, 16)
        if t.startswith("0b"):
            return int(t, 2)
        return int(t)
    except ValueError:
        return None


def vergleiche_gegen(zeile, name):
    """Alle `name OP zahl` und `zahl OP name` einer Zeile, als (OP, wert) mit OP aus der
    Sicht von `name`."""
    out = []
    kopf = re.escape(name)
    for m in re.finditer(rf"{kopf}\s*(>=|<=|==|!=|>|<)\s*({ZAHL})", zeile):
        w = zahlwert(m.group(2))
        if w is not None:
            out.append((m.group(1), w))
    spiegel = {">=": "<=", "<=": ">=", ">": "<", "<": ">", "==": "==", "!=": "!="}
    for m in re.finditer(rf"({ZAHL})\s*(>=|<=|==|!=|>|<)\s*{kopf}", zeile):
        w = zahlwert(m.group(1))
        if w is not None:
            out.append((spiegel[m.group(2)], w))
    return out


def ist_konstant(t):
    return bool(re.fullmatch(ZAHL, t)) or bool(re.fullmatch(r"[A-Z][A-Z0-9_]*", t))


def grundname(t):
    """Der Kopf eines Ortes -- `self.bitmap[i]` -> `self.bitmap`, `pd as usize` -> `pd`."""
    t = ohne_cast(t.strip())
    t = re.sub(r"\s*\[[^\]]*\]\s*$", "", t).strip()
    t = re.sub(r"^\((.*)\)$", r"\1", t).strip()
    return ohne_cast(t)


def geschrieben_zwischen(rumpf, von, bis, name):
    """Stirbt der Fakt? Jedes Schreiben auf eine beteiligte Stelle toetet ihn."""
    kopf = re.escape(grundname(name))
    muster = re.compile(rf"{kopf}\s*(?:\[[^\]]*\])?\s*(?:=[^=]|\+=|-=|\*=|/=|&=|\|=)")
    for z in rumpf[von + 1 : bis]:
        if muster.search(z):
            return True
    return False


def schleifengrenze_zwischen(rumpf, von, bis):
    """Kippregel 3: eine Schleife zwischen Pruefung und Stelle toetet den Fakt."""
    tiefe = 0
    for z in rumpf[von : bis + 1]:
        if re.search(r"\b(?:for|while|loop)\b", z):
            tiefe += 1
    if tiefe == 0:
        return False
    # Steht die Stelle noch im selben Rumpf wie die Pruefung? Naeherung ueber die
    # Einrueckung: tiefer eingerueckt heisst weiter innen.
    ein_pruef = len(rumpf[von]) - len(rumpf[von].lstrip())
    ein_stelle = len(rumpf[bis]) - len(rumpf[bis].lstrip())
    return ein_stelle > ein_pruef


VERLAESST = re.compile(r"\b(?:return|continue|break|panic!|unreachable!|todo!|abort)\b|\?;")


def zweigende(rumpf, i):
    """Wo endet der Block, der in Zeile i mit `{` aufgeht? (-1 = kein Block)"""
    if "{" not in rumpf[i]:
        return -1
    tiefe = 0
    for j in range(i, len(rumpf)):
        tiefe += rumpf[j].count("{") - rumpf[j].count("}")
        if tiefe <= 0 and j >= i:
            return j
    return len(rumpf) - 1


def zweig_verlaesst(rumpf, i, ende):
    """Verlaesst der Zweig ab Zeile i seinen Weg immer? (return/continue/break/panic)

    **Das ist dieselbe Regel, die der Uebersetzer als `endet_immer` fuehrt** -- ein Zaehler,
    der sie nicht kennt, misst eine andere Sprache als der Pruefer. Defekt 4 der Eichung,
    und der teuerste: `if c < 2 { return None; }` ist die haeufigste Form im ganzen Baum.
    """
    if ende < i:
        return False
    return any(VERLAESST.search(z) for z in rumpf[i : ende + 1])


BEZEICHNER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
VERGLEICH = re.compile(r"(?:[><!=]=|[><])")
NEGIERT = {">=": "<", ">": "<=", "<=": ">", "<": ">=", "==": "!=", "!=": "=="}
WAECHTER = re.compile(r"\b(?:if|while|assert!|debug_assert!|assert_eq!|assert_ne!|matches!)\b")


def pruefung_im_rumpf(rumpf, nr, *orte):
    """Steht VOR der Stelle ueberhaupt eine Pruefung, die einen der Namen nennt?

    Der Unterschied zwischen „keine Pruefung" (Spalte F -- die Pflicht wandert zum
    Aufrufer, `requires` traegt sie) und „eine Pruefung, die nicht traegt" (Spalte N --
    hier braucht es `narrow` oder eine Aussage, die die Sprache nicht hat).
    """
    namen = set()
    for o in orte:
        namen |= set(BEZEICHNER.findall(o))
    namen -= {"as", "u8", "u16", "u32", "u64", "usize", "i8", "i16", "i32", "i64", "isize"}
    if not namen:
        return False
    for z in rumpf[:nr]:
        if not WAECHTER.search(z) or not VERGLEICH.search(z):
            continue
        if namen & set(BEZEICHNER.findall(z)):
            return True
    return False


def klassiere(f, art, nr, links, rechts):
    """Die sechs Spalten des Protokolls, Kippregel: immer nach N."""
    rumpf = f.zeilen

    # --- K (Defekt 3 der Eichung): die saettigenden Redewendungen. `len - frei.min(len)`
    # --- kann nicht unterlaufen, und zwar durch Konstruktion, nicht durch eine Pruefung.
    if art == "sub":
        kern_l = grundname(ohne_cast(links))
        if re.search(r"\.\s*min\s*\(", rechts) and kern_l and kern_l in rechts:
            return "K"
        if re.search(r"\.\s*max\s*\(", links) and grundname(ohne_cast(rechts)) in links:
            return "K"

    # --- K: beide Operanden fest, oder ein Nenner, der die Null ausschliesst.
    if art in ("div", "rem"):
        if ist_konstant(rechts) and rechts not in ("0", "0x0", "0b0"):
            return "K"
    else:
        if ist_konstant(links) and ist_konstant(rechts):
            return "K"

    # Die Groesse, um die es geht: beim Teilen der Nenner, beim Abziehen die linke Seite.
    gepruefte = rechts if art in ("div", "rem") else links
    gegen = links if art in ("div", "rem") else rechts
    kopf_g = re.escape(grundname(gepruefte))
    kopf_a = re.escape(grundname(gegen))
    k_links = zahlwert(links)
    k_rechts = zahlwert(rechts)

    # --- V2 vor V1 auswerten waere bequem; die Kippregel verlangt die TEUERSTE Spalte,
    # --- also wird beides gesucht und die teurere genommen.
    treffer = None

    # V1 -- Groesse gegen Konstante, **und die Konstante muss die Pflicht tragen**.
    # Die Kippregel („im Zweifel nach N") gilt auch hier: `if a >= 1` traegt `a - 5` nicht,
    # und ein benannter `const` als Schranke hat fuer diesen Zaehler keinen Wert -- also N.
    def v1_traegt(op, wert):
        if art in ("div", "rem"):
            # Der Nenner muss die Null ausschliessen.
            return (op in (">", "!=") and wert == 0) or (op == ">=" and wert >= 1)
        if k_rechts is not None:            # `a - K`: es braucht `a >= K`
            return (op == ">=" and wert >= k_rechts) or (op == ">" and wert >= k_rechts - 1) \
                or (op == "!=" and wert == 0 and k_rechts <= 1)
        if k_links is not None:             # `K - b`: es braucht `b <= K`
            return (op == "<=" and wert <= k_links) or (op == "<" and wert <= k_links + 1)
        return False

    for i in range(nr - 1, -1, -1):
        z = rumpf[i]
        if not WAECHTER.search(z):
            continue
        # Steht die Stelle IM Zweig, gilt die Bedingung; steht sie DAHINTER und der Zweig
        # verlaesst immer, gilt ihre Verneinung.
        ende = zweigende(rumpf, i)
        drin = i <= nr <= ende if ende >= i else False
        if not drin:
            if not zweig_verlaesst(rumpf, i, ende) or nr <= ende:
                continue
        getroffen = False
        for op, wert in vergleiche_gegen(z, grundname(gepruefte)):
            if not drin:
                op = NEGIERT[op]
            if v1_traegt(op, wert):
                getroffen = True
                break
        # Die Form „frueh zurueck": `if n == 0 { return … }` schliesst die Null aus.
        if not getroffen and re.search(
            rf"\bif\s+{kopf_g}\s*==\s*0\s*\{{[^}}]*\b(?:return|continue|break|panic!|unreachable!)",
            z,
        ):
            getroffen = art in ("div", "rem") or (k_rechts is not None and k_rechts <= 1)
        if not getroffen:
            continue
        if geschrieben_zwischen(rumpf, i, nr, gepruefte):
            break
        if schleifengrenze_zwischen(rumpf, i, nr):
            break
        treffer = "V1"
        break

    # V2 -- die beiden Stellen gegeneinander.
    if not ist_konstant(gegen) and art == "sub":
        v2 = re.compile(
            rf"\b(?:if|while|assert!|debug_assert!)\s*\(?\s*{kopf_g}\s*(?:>=|>)\s*{kopf_a}\b"
            rf"|\b(?:if|while|assert!|debug_assert!)\s*\(?\s*{kopf_a}\s*(?:<=|<)\s*{kopf_g}\b"
        )
        v2_frueh = re.compile(
            rf"\bif\s+{kopf_g}\s*<\s*{kopf_a}\s*\{{[^}}]*\b(?:return|continue|break|panic!)"
        )
        v2_neg = re.compile(
            rf"\b(?:if|while)\s*\(?\s*{kopf_g}\s*(?:<|<=)\s*{kopf_a}\b"
            rf"|\b(?:if|while)\s*\(?\s*{kopf_a}\s*(?:>|>=)\s*{kopf_g}\b"
        )
        for i in range(nr - 1, -1, -1):
            ende = zweigende(rumpf, i)
            drin = i <= nr <= ende if ende >= i else False
            # Die Verneinung: `if a < b { return … }` sagt danach `a >= b`.
            # `a <= b` verneint zu `a > b` -- traegt `a - b` ebenfalls.
            if not drin and zweig_verlaesst(rumpf, i, ende) and nr > ende:
                if v2_neg.search(rumpf[i]):
                    if geschrieben_zwischen(rumpf, i, nr, gepruefte) or geschrieben_zwischen(
                        rumpf, i, nr, gegen
                    ):
                        break
                    if schleifengrenze_zwischen(rumpf, i, nr):
                        break
                    treffer = "V2" if treffer is None else treffer
                    break
            if not drin:
                continue
            if v2.search(rumpf[i]) or v2_frueh.search(rumpf[i]):
                if geschrieben_zwischen(rumpf, i, nr, gepruefte) or geschrieben_zwischen(
                    rumpf, i, nr, gegen
                ):
                    break
                if schleifengrenze_zwischen(rumpf, i, nr):
                    break
                treffer = "V2" if treffer is None else treffer
                break

    if treffer:
        return treffer

    # V3 -- die Stelle steht in einem `match`-Zweig und der Wert ist dessen Bindung.
    v3 = re.compile(rf"=>|\b(?:Some|Ok)\s*\(\s*{kopf_g}\s*\)")
    for i in range(nr - 1, max(-1, nr - 8), -1):
        if re.search(rf"\b[A-Z][A-Za-z0-9_]*\s*\(\s*{kopf_g}\s*\)\s*=>", rumpf[i]) or re.search(
            rf"\b(?:Some|Ok)\s*\(\s*{kopf_g}\s*\)\s*=>", rumpf[i]
        ):
            return "V3"
    del v3

    # F -- **keine Pruefung im Rumpf**, und ein Operand ist ein Parameter. Das Protokoll
    # sagt „keine Pruefung", nicht „keine Pruefung, die traegt": steht im Rumpf eine
    # Pruefung, die die Stelle nicht traegt, ist es N. Genau das ist
    # `31 - self.bitmap.leading_zeros()` -- die Pruefung `if self.bitmap == 0` steht da,
    # sie traegt nur nicht (aus `bitmap != 0` folgt `lz <= 31` erst ueber eine Aussage
    # ueber `leading_zeros`, und die hat die Sprache nicht).
    if pruefung_im_rumpf(rumpf, nr, gepruefte, gegen):
        return "N"
    for t in (gepruefte, gegen):
        kopf = grundname(t).split(".")[0].split("[")[0]
        if kopf in f.params:
            return "F"

    return "N"


def lauf(baum, zeige_n=False):
    zaehlung = Counter()
    je_datei = defaultdict(Counter)
    n_stellen = []
    f_stellen = []
    dateien = 0
    for ordner in ORDNER:
        wurzel = baum / ordner
        if not wurzel.is_dir():
            continue
        for pfad in sorted(wurzel.rglob("*.rs")):
            teile = set(pfad.parts)
            if "target" in teile or ".claude" in teile:
                continue
            dateien += 1
            roh = pfad.read_text(errors="replace")
            text = entkerne(roh)
            rel = pfad.relative_to(baum)
            for f in funktionen(text):
                for art, nr, links, rechts in stellen(f.zeilen):
                    spalte = klassiere(f, art, nr, links, rechts)
                    zaehlung[spalte] += 1
                    je_datei[str(rel).split("/")[1] if "/" in str(rel) else str(rel)][
                        spalte
                    ] += 1
                    zeile = f.erste_zeile + nr
                    eintrag = (str(rel), zeile, art, links, rechts, f.name)
                    if spalte == "N":
                        n_stellen.append(eintrag)
                    elif spalte == "F":
                        f_stellen.append(eintrag)
    return zaehlung, je_datei, n_stellen, f_stellen, dateien


def sprechprobe(baum):
    """Der Zaehler muss die drei bekannten Stellen finden -- sonst ist die Zahl ungueltig."""
    ok = True
    for rel, marke in SPRECHPROBEN:
        pfad = baum / rel
        if not pfad.is_file():
            print(f"  FEHLT: {rel}")
            ok = False
            continue
        text = entkerne(pfad.read_text(errors="replace"))
        gefunden = False
        for f in funktionen(text):
            for art, nr, links, rechts in stellen(f.zeilen):
                if marke in f.zeilen[nr]:
                    spalte = klassiere(f, art, nr, links, rechts)
                    print(
                        f"  {rel}:{f.erste_zeile + nr}  {art}  "
                        f"`{links}` / `{rechts}`  ->  {spalte}"
                    )
                    gefunden = True
        if not gefunden:
            print(f"  NICHT GEFUNDEN: {rel} ({marke})")
            ok = False
    return ok


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    baum = pathlib.Path(args[0]) if args else BAUM
    if not baum.is_dir():
        print(f"Baum nicht gefunden: {baum}")
        return 2

    print(f"== Sprechprobe des Klassierers ({baum}) ==")
    gueltig = sprechprobe(baum)
    if not gueltig:
        print("\n== UNGUELTIG: der Zaehler findet die bekannten Stellen nicht ==")
        return 1
    if "--sprechprobe" in sys.argv:
        return 0

    zaehlung, je_datei, n_stellen, f_stellen, dateien = lauf(baum)
    gesamt = sum(zaehlung.values())
    print(f"\n== Zaehlung ueber {dateien} Dateien, {gesamt} Bereichspflichten ==\n")
    for spalte in ("K", "V1", "V2", "V3", "F", "N"):
        anteil = 100.0 * zaehlung[spalte] / gesamt if gesamt else 0.0
        print(f"  {spalte:<3} {zaehlung[spalte]:>5}   {anteil:5.1f} %")

    print(f"\n  N = {zaehlung['N']}, F = {zaehlung['F']}")
    print()
    print("  !! DIESE ZAHLEN SIND KEINE MESSUNG. !!")
    print("  Eine Handstichprobe (MESSUNGEN.md, 2026-08-14) fand in 3 von 5 N-Stellen")
    print("  einen Fehler des Zaehlers, alle in dieselbe Richtung. Er findet KANDIDATEN;")
    print("  die Latte `<= 24` entscheidet er nicht. Das Messgeraet dafuer ist der")
    print("  Uebersetzer selbst -- und der braucht die Bereiche in Gabbro.")

    print("\n== N -- jede Stelle, die `narrow` braucht ==")
    for datei, zeile, art, links, rechts, fn in n_stellen:
        print(f"  {datei}:{zeile}  {fn}()  {art}  `{links}` gegen `{rechts}`")

    print("\n== F -- Pruefung liegt beim Aufrufer, braucht `requires` ==")
    for datei, zeile, art, links, rechts, fn in f_stellen[:40]:
        print(f"  {datei}:{zeile}  {fn}()  {art}  `{links}` gegen `{rechts}`")
    if len(f_stellen) > 40:
        print(f"  … und {len(f_stellen) - 40} weitere")

    print("\n== Verteilung je Kiste ==")
    for kiste in sorted(je_datei, key=lambda k: -sum(je_datei[k].values()))[:20]:
        c = je_datei[kiste]
        print(
            f"  {kiste:<24} gesamt {sum(c.values()):>4}  "
            f"N {c['N']:>3}  F {c['F']:>3}  V1 {c['V1']:>3}  V2 {c['V2']:>3}  "
            f"V3 {c['V3']:>3}  K {c['K']:>3}"
        )
    # Kein Urteil im Rueckgabewert: der Zaehler faellt nur, wenn seine Sprechprobe faellt.
    abschnitt.fertig()
    return 0


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
