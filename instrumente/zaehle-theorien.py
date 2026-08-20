#!/usr/bin/env python3
"""**Eine Isar-Datei dieses Ordners ist zu einem grossen Teil Fliesstext -- und die Zahl sagt
es nicht.**

Am 2026-08-19 buchte der Ordner: *„Zehn Theorien, 1 639 Zeilen, 48 Saetze, 86
Beweisschritte."* **Fuer die Amortisationszahl ist es gleich, was davon Prosa ist; fuer jeden
Vergleich mit einer Verus- oder seL4-Zeilenzahl nicht.** Wer eine Isar-Datei dieses Ordners
gegen eine Verus-Zeilenzahl haelt, vergleicht zwei verschiedene Dinge -- *dieselbe
Verwechslung, an der die Kennzahl `1,90` am 2026-08-19 zurueckgezogen wurde, eine Ebene
tiefer.*

    ./instrumente/zaehle-theorien.py [--je-datei]

DAS MASS -- vier Spalten, und die Grenze zwischen ihnen ist mechanisch
----------------------------------------------------------------------
    Geruest   `theory` · `imports` · `begin` · `end` · Leerzeilen
    Prosa     `(* … *)` · `text ‹…›` · `section`/`subsection`
    Modell    `definition` · `fun` · `datatype` · `type_synonym` · `abbreviation` · `record`
    Beweis    `lemma`/`theorem`/`corollary` samt ihrem Beweis

**Und was das NICHT heisst:** die Einteilung liest ZEILENANFAENGE. Ein `text`-Block, der ein
Modell erklaert, zaehlt als Prosa, und eine `definition` mit einem erklaerenden Kommentar
dahinter zaehlt ganz als Modell. *Die Zahl ist eine Naeherung mit einer benannten Kante, kein
Parser* (W10).

DIE ZWEITE HAELFTE: WER HAT DEN SCHRITT GESUCHT?
-------------------------------------------------
Am 2026-08-17 lief dieser Ordner **zweimal an einem Tag** in eine Beweissuche: erst ein
`metis` (9 Minuten, 6,3 GB), dann ein `blast` (12 Minuten, 4,8 GB). `./instrumente/pruefe-beweise.sh`
haelt seither bei 3 GB an -- **aber der Wachhund greift erst, wenn die Suche schon laeuft.**

*Die andere Haelfte ist eine Zaehlung, und sie steht hier:* jeder `metis`-, `blast`- und
`smt`-Aufruf im Baum ist ein **eingefrorenes Suchergebnis**, und ihre Zahl darf nicht
stillschweigend wachsen. **`sledgehammer`, `try0`, `nitpick` und `quickcheck` haben in einer
eingecheckten Theorie gar nichts zu suchen** -- das sind Suchbefehle und keine Beweise.

*Dass heute keiner dasteht, ist ein Befund und kein Freibrief:* die Zahl daneben sagt, ueber
wie vielen Zeilen er erhoben wurde (W17).
"""
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
BEWEISE = W / "beweise"

# **Ratsche, keine Zielzahl.** Jeder Aufruf ist eine Suche, die einmal lief und deren
# Ergebnis jetzt im Baum steht. Sie darf fallen, nicht steigen.
MARKE_EINGEFROREN = 31        # metis + blast + smt
VERBOTEN = ("sledgehammer", "try0", "nitpick", "quickcheck")

# **Die dritte Haelfte: welche Theorie steht in KEINEM Register?** (2026-08-20)
#
# `gabbro schablonen` fuehrt **Erzeugerpflichten** -- *„eine Beweispflicht, die der Erzeuger
# schuldet"*. `Intervall_Aussen.thy` handelt vom PRUEFER und passt dort nicht hinein; damit
# gibt es **zwei Vertrauensflaechen und nur eine Buchung** (`TODO.md`, Stufe 5). Der Ordner
# fuehrte das als Prosa im `durch:`-Feld -- und eine Flaeche, die nur in Prosa steht, waechst
# unbemerkt.
#
# **Gemessen wird die Verknuepfung, nicht das Urteil.** Ob ein zweites Register gebaut werden
# soll, ist eine Entscheidung und steht im TODO. *Was hier steht, ist die Zahl, ohne die man
# sie nicht treffen kann.*
#
# **Ratsche, keine Zielzahl**: sie darf fallen, nicht steigen. Heute 2 --
#   * `Intervall_Aussen.thy`  -- handelt vom PRUEFER, und dafuer gibt es kein Register,
#   * `Table_Induktion.thy`   -- IST eine Schablone (`table.induktion`, S7), und der
#     Registereintrag nennt seine Datei nicht. *Die andere Richtung derselben Luecke:
#     nicht die Flaeche fehlt, sondern die Zeile, die sie verknuepft.*
MARKE_OHNE_REGISTER = 2
REGISTER = "crates/gabbro-check/src/schablonen.rs"
EINGEFROREN = ("metis", "blast", "smt")

MODELL = re.compile(r"^\s*(definition|fun|primrec|datatype|type_synonym|abbreviation|record|"
                    r"inductive|locale|instantiation|typedecl|consts|axiomatization)\b")
SATZ = re.compile(r"^\s*(lemma|theorem|corollary|proposition)\b")
UEBERSCHRIFT = re.compile(r"^\s*(section|subsection|subsubsection|chapter|paragraph)\b")
GERUEST = re.compile(r"^\s*(theory|imports|begin|end)\b\s*$|^\s*(theory|imports)\b")
SCHRITT = re.compile(r"^\s*(apply|by|proof|qed|next|then|hence|thus|moreover|ultimately|"
                     r"show|have|obtain|fix|assume|case|from|with|also|finally|using|"
                     r"unfolding)\b")


def klassifiziere(text):
    """Vier Spalten je Zeile. Gibt (geruest, prosa, modell, beweis, saetze, schritte)."""
    g = p = mo = b = 0
    saetze = schritte = 0
    im_kommentar = False
    im_text = 0            # Schachtelung von \<open> … \<close> innerhalb eines `text`-Blocks
    block = None           # "modell" | "beweis" | None
    for z in text.split("\n"):
        roh = z.rstrip()
        # (1) Blockkommentar `(* … *)`
        if im_kommentar:
            p += 1
            if "*)" in roh:
                im_kommentar = False
            continue
        if roh.lstrip().startswith("(*"):
            p += 1
            if "*)" not in roh:
                im_kommentar = True
            continue
        # (2) `text ‹…›` / `txt ‹…›`
        if im_text:
            p += 1
            im_text += roh.count("\\<open>") - roh.count("\\<close>")
            im_text = max(im_text, 0)
            continue
        if re.match(r"^\s*(text|txt|notepad)\b", roh):
            p += 1
            tiefe = roh.count("\\<open>") - roh.count("\\<close>")
            im_text = max(tiefe, 0)
            continue
        # (3) Ueberschrift und Geruest
        if UEBERSCHRIFT.match(roh):
            p += 1
            continue
        if not roh.strip():
            g += 1
            block = None
            continue
        if GERUEST.match(roh) or roh.strip() in ("begin", "end"):
            g += 1
            continue
        # (4) Modell und Beweis
        if MODELL.match(roh):
            block = "modell"
        elif SATZ.match(roh):
            block = "beweis"
            saetze += 1
        if block == "modell":
            mo += 1
        elif block == "beweis":
            b += 1
            if SCHRITT.match(roh):
                schritte += 1
        else:
            g += 1
    return g, p, mo, b, saetze, schritte


def taktiken(text):
    """Suchbefehle und eingefrorene Suchergebnisse -- ausserhalb von Kommentaren gezaehlt."""
    ohne = re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)
    verboten = {w: len(re.findall(r"\b%s\b" % w, ohne)) for w in VERBOTEN}
    frost = {w: len(re.findall(r"\b%s\b" % w, ohne)) for w in EINGEFROREN}
    return verboten, frost


def ohne_register(namen, registertext):
    """Welche Theorien nennt das Schablonenregister NICHT? -- reine Textmessung.

    Gelesen wird der Dateiname (`Foo.thy`), weil das die einzige Verknuepfung ist, die es
    heute gibt: das Register nennt seine Theorien in Prosa. *Damit ist diese Zaehlung eine
    UNTERE Schranke der Buchungsluecke -- ein Eintrag, der die Theorie nur ueber ihren
    Schablonennamen meint, zaehlt hier als gebucht* (W10).
    """
    genannt = set(re.findall(r"([A-Za-z_]+)\.thy", registertext))
    return sorted(n for n in namen if n not in genannt)


def sprechprobe():
    """R14, in beide Richtungen -- an einer ERFUNDENEN Theorie."""
    gift = ("theory G\n  imports Main\nbegin\n\n"
            "lemma x: \"True\"\n  sledgehammer\n\nend\n")
    sauber = ("theory G\n  imports Main\nbegin\n\n"
              "text \\<open>Prosa\\<close>\n\n"
              "definition d :: nat where \"d = 0\"\n\n"
              "lemma x: \"True\"\n  by simp\n\nend\n")
    v_gift, _ = taktiken(gift)
    v_sauber, _ = taktiken(sauber)
    _, p_s, m_s, b_s, sa, _ = klassifiziere(sauber)
    # **Und die Registerhaelfte, in beide Richtungen** -- an einem ERFUNDENEN Register.
    r_gift = ohne_register(["A", "B"], "-- A.thy steht hier")        # B fehlt -> 1 Befund
    r_sauber = ohne_register(["A", "B"], "A.thy und B.thy stehen hier")
    return (sum(v_gift.values()) == 1, sum(v_sauber.values()) == 0,
            p_s == 1 and m_s == 1 and b_s == 2 and sa == 1,
            r_gift == ["B"] and r_sauber == [])


def main():
    g_ok, s_ok, k_ok, r_ok = sprechprobe()
    print("== Sprechprobe des Zaehlers ==")
    print("  ein `sledgehammer` faellt auf:   %s" % ("ja" if g_ok else "NEIN"))
    print("  eine saubere Theorie bleibt frei: %s" % ("ja" if s_ok else "NEIN"))
    print("  die vier Spalten treffen:         %s" % ("ja" if k_ok else "NEIN"))
    print("  eine Theorie ohne Register faellt: %s" % ("ja" if r_ok else "NEIN"))
    if not (g_ok and s_ok and k_ok and r_ok):
        print("== THEORIEN: der Zaehler misst nicht ==")
        return 1

    dateien = sorted(BEWEISE.glob("*.thy"))
    if not dateien:
        print("== THEORIEN: 0 Theorien gefunden -- es wurde NICHTS gemessen ==")
        return 1
    S = [0] * 6
    v_alle, f_alle = {w: 0 for w in VERBOTEN}, {w: 0 for w in EINGEFROREN}
    je = []
    for d in dateien:
        t = d.read_text(encoding="utf-8", errors="replace")
        z = klassifiziere(t)
        v, f = taktiken(t)
        for i in range(6):
            S[i] += z[i]
        for w in VERBOTEN:
            v_alle[w] += v[w]
        for w in EINGEFROREN:
            f_alle[w] += f[w]
        je.append((d.name, z, sum(f.values())))
    g, p, mo, b, saetze, schritte = S
    zeilen = g + p + mo + b

    print()
    print("== %d Theorien, %d Zeilen, %d Saetze, %d Beweisschritte =="
          % (len(dateien), zeilen, saetze, schritte))
    print("   Geruest   %5d   %4.1f %%   theory/imports/begin/end und Leerzeilen"
          % (g, 100.0 * g / zeilen))
    print("   Prosa     %5d   %4.1f %%   Kommentare, `text`-Bloecke, Ueberschriften"
          % (p, 100.0 * p / zeilen))
    print("   Modell    %5d   %4.1f %%   Definitionen, Datentypen, Abkuerzungen"
          % (mo, 100.0 * mo / zeilen))
    print("   Beweis    %5d   %4.1f %%   Saetze samt ihren Beweisen"
          % (b, 100.0 * b / zeilen))
    print("   **Modell + Beweis = %d Zeilen (%.1f %%)** -- das ist die Haelfte, die einer"
          % (mo + b, 100.0 * (mo + b) / zeilen))
    print("   Verus-Zeilenzahl gegenuebersteht. Der Rest ist Text ueber den Beweis.")

    if "--je-datei" in sys.argv:
        print()
        for name, (g1, p1, m1, b1, s1, sc1), fr in je:
            print("   %-28s %4d Z   Prosa %3d  Modell %3d  Beweis %3d   %d Saetze, %d eingefroren"
                  % (name, g1 + p1 + m1 + b1, p1, m1, b1, s1, fr))

    # -- Die dritte Haelfte: die Buchung ------------------------------------------------
    reg = (W / REGISTER)
    print()
    if not reg.is_file():
        print("== THEORIEN: %s nicht gefunden -- die Registerhaelfte wurde NICHT gemessen =="
              % REGISTER)
        return 1
    fehlend = ohne_register([d.stem for d in dateien], reg.read_text())
    print("== Buchung: %d von %d Theorien nennt das Schablonenregister NICHT =="
          % (len(fehlend), len(dateien)))
    for n in fehlend:
        print("   %s" % n)
    print("   `gabbro schablonen` fuehrt ERZEUGERpflichten. Eine Theorie ueber den PRUEFER")
    print("   passt dort nicht hinein -- damit gibt es zwei Vertrauensflaechen und eine")
    print("   Buchung. *Ob ein zweites Register die Antwort ist, ist eine ENTSCHEIDUNG und")
    print("   steht im TODO; diese Zahl ist die, ohne die man sie nicht treffen kann.*")
    if len(fehlend) > MARKE_OHNE_REGISTER:
        print("== THEORIEN: %d ohne Register gegen die Marke %d =="
              % (len(fehlend), MARKE_OHNE_REGISTER))
        print("   **Die Marke ist eine Ratsche**: sie darf fallen, nicht steigen. Eine neue")
        print("   ungebuchte Theorie waechst sonst still in die Vertrauensflaeche hinein.")
        return 1

    print()
    frost = sum(f_alle.values())
    verb = sum(v_alle.values())
    print("== Suche: %d Suchbefehle, %d eingefrorene Suchergebnisse ==" % (verb, frost))
    print("   verboten     " + ", ".join("%s %d" % (w, v_alle[w]) for w in VERBOTEN))
    print("   eingefroren  " + ", ".join("%s %d" % (w, f_alle[w]) for w in EINGEFROREN)
          + "   (Marke %d)" % MARKE_EINGEFROREN)
    if verb:
        print("== THEORIEN: %d Suchbefehl(e) in einer eingecheckten Theorie ==" % verb)
        print("   `sledgehammer`/`try0`/`nitpick` sind Suchbefehle und keine Beweise. Der")
        print("   Wachhund in `pruefe-beweise.sh` greift erst, wenn die Suche schon LAEUFT.")
        return 1
    if frost > MARKE_EINGEFROREN:
        print("== THEORIEN: %d eingefrorene Suchergebnisse gegen die Marke %d =="
              % (frost, MARKE_EINGEFROREN))
        print("   Am 2026-08-17 kosteten ein `metis` und ein `blast` zusammen 21 Minuten und")
        print("   11 GB. **Die Marke ist eine Ratsche**: sie darf fallen, nicht steigen.")
        return 1
    print("== THEORIEN: kein Suchbefehl, %d eingefroren -- keine neue ==" % frost)
    print("   Und was das NICHT heisst: gezaehlt wird ueber %d Zeilen in %d Theorien, und"
          % (zeilen, len(dateien)))
    print("   die Einteilung liest ZEILENANFAENGE. Ein `text`-Block ueber ein Modell zaehlt")
    print("   als Prosa. *Die Zahl ist eine Naeherung mit einer benannten Kante* (W10).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
