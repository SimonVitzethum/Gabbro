#!/usr/bin/env python3
"""**Keine Kennung zweimal.** Der Waechter gegen eine Fehlerklasse, die ich an einem Tag
dreimal begangen habe.

Am 2026-08-14 habe ich beim Bau von `locks shared` die Kennungen `K003` und `S001`/`S002`
vergeben, ohne nachzusehen, wer sie schon hat: `kosten.rs` fuehrt `K003` seit Pass 9 fuer
unbekannte Aufrufkosten, `schleifen.rs` fuehrt `S001`/`S002` seit Pass 6 fuer die
Schleifenmarke und den durchfallenden `else`-Zweig.

**Warum das mehr ist als Kosmetik:** die Giftproben pruefen auf **Kennungen**
(`-- erwartet: CODE`). Eine doppelt vergebene Kennung macht jede solche Probe mehrdeutig --
sie faellt gruen, waehrend die gemeinte Regel ausgefallen ist. *Genau die Bewegung, gegen die
der ganze Ordner gebaut ist.*

**Die Regel, mechanisch:** eine Kennung darf in beliebig vielen ZEILEN stehen (dieselbe Regel
an mehreren Stellen ist normal), aber nur in **einer Datei**. Die Datei ist die Regel.

Sprechprobe in beide Richtungen, und sie faehrt in JEDEM Lauf. `--sprechprobe`
faehrt nur sie und sonst nichts.
"""
import collections
import pathlib
import re
import sys

WURZEL = pathlib.Path(__file__).resolve().parent.parent

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import korpus  # noqa: E402

KENNUNG = re.compile(r'"([A-Z][0-9]{3})"')

# --- Lane 182: source trust (homoglyphs and bidi) -------------------------------------
#
# Gabbro's promise is that a HUMAN reads a body ("written by hand and read by a
# person"); a program that reads differently to a human than to the parser breaks
# exactly that premise (Trojan Source, CVE-2021-42574). The lexer refuses four
# classes (`P060`-`P063`, `lex.rs::quelltext_pruefe`); this guardian is the same
# check over the tree's own sources, so a poisoned file cannot sit here unnoticed.
#
# What is scanned: every `.gab` (except the poison corpus `beispiele/gift/`, which
# carries poison ON PURPOSE -- the same exclusion `korpus.py` makes), every `.lean`
# and every `.rs`, minus the build and worktree directories. Identifier runs are
# checked on `.gab` code only (strings and `--` comments skipped, as the lexer
# skips them); bidi and invisible characters are refused ANYWHERE, comments and
# strings included. `.rs`/`.lean` legitimately carry Greek and math symbols in
# comments and strings, so only the bidi/invisible classes apply to them.
# `P064` is booked with the lane and stays unissued.

_BIDI = {
    0x202A, 0x202B, 0x202C, 0x202D, 0x202E,
    0x2066, 0x2067, 0x2068, 0x2069,
    0x200E, 0x200F, 0x061C,
}
_UNSICHTBAR = {0x200B, 0x200C, 0x200D}
_UMLAUTE = set("äöüÄÖÜß")
_AUSGENOMMEN = {"target", ".git", ".lake", ".claude", "__pycache__", "gift"}


def _schrift(o):
    # **Character for character `lex.rs::schrift` (and `schrift` in
    # `LexerVertrauen.lean`, whose `0` for ASCII non-letters is only the
    # spelling of "neutral" there).** ASCII letters are family 1, every other
    # ASCII character falls through to 13 -- and `_laufzeichen` below keeps
    # only 1..12, so spaces and punctuation break runs on all three sides.
    if 65 <= o <= 90 or 97 <= o <= 122:
        return 1
    if 0xC0 <= o <= 0xFF or 0x100 <= o <= 0x24F or 0x1E00 <= o <= 0x1EFF:
        return 1  # Latin (covers the umlauts)
    if 0x370 <= o <= 0x3FF or 0x1F00 <= o <= 0x1FFF:
        return 2  # Greek
    if 0x400 <= o <= 0x4FF or 0x500 <= o <= 0x52F \
            or 0x2DE0 <= o <= 0x2DFF or 0xA640 <= o <= 0xA69F:
        return 3  # Cyrillic
    if 0x530 <= o <= 0x58F:
        return 4  # Armenian
    if 0x590 <= o <= 0x5FF:
        return 5  # Hebrew
    if 0x600 <= o <= 0x6FF or 0x750 <= o <= 0x77F:
        return 6  # Arabic
    if 0x900 <= o <= 0x97F:
        return 7  # Devanagari
    if 0xE00 <= o <= 0xE7F:
        return 8  # Thai
    if 0x10A0 <= o <= 0x10FF:
        return 9  # Georgian
    if 0x1100 <= o <= 0x11FF or 0xAC00 <= o <= 0xD7AF:
        return 10  # Hangul
    if 0x3040 <= o <= 0x309F or 0x30A0 <= o <= 0x30FF:
        return 11  # Hiragana / Katakana
    if 0x3400 <= o <= 0x4DBF or 0x4E00 <= o <= 0x9FFF:
        return 12  # Han
    return 13


def _erlaubt(c):
    return (c.isascii() and (c.isalpha() or c.isdigit() or c == "_")) or c in _UMLAUTE


def _laufzeichen(c):
    """A run character -- character for character the rule of
    `lex.rs::ist_laufzeichen` and `LexerVertrauen.lean::istLaufWeiter`: `_`,
    ASCII letters and digits, and the twelve script families. Anything else
    (exotic numbers, punctuation, format) breaks a run on all three sides."""
    if c == "_" or (c.isascii() and (c.isalpha() or c.isdigit())):
        return True
    return 1 <= _schrift(ord(c)) <= 12


def _laeufe(code):
    """Identifier-like runs of code (strings and `--` comments skipped).

    Yields `(run, attached_to_digit, line)`; a run starting right behind a digit
    belongs to the number neighbourhood (`L003`/`L006` own it) and is marked,
    not judged.
    """
    out = []
    i, n = 0, len(code)
    vorher_ziffer = False
    while i < n:
        c = code[i]
        if c == '"':
            j = code.find('"', i + 1)
            k = code.find("\n", i + 1)
            i = (j + 1) if j != -1 and (k == -1 or j < k) else (k if k != -1 else n)
            vorher_ziffer = False
            continue
        if c == "-" and i + 1 < n and code[i + 1] == "-":
            k = code.find("\n", i)
            i = n if k == -1 else k
            vorher_ziffer = False
            continue
        if c.isalpha() or c == "_":
            angehaengt = vorher_ziffer
            j = i + 1
            while j < n and _laufzeichen(code[j]):
                j += 1
            out.append((code[i:j], angehaengt, code[:i].count("\n") + 1))
            vorher_ziffer = False
            i = j
            continue
        vorher_ziffer = c.isascii() and c.isdigit()
        i += 1
    return out


def quellvertrauen_text(text, mit_laeufen):
    """Findings as `(line, code, detail)` -- the same four classes as the lexer.

    `P060` (bidi) and `P063` (invisible) run over the raw text, comments and
    strings included; `P061`/`P062` run over identifier-like runs of code only.
    U+FEFF passes exactly once, as the first character of the file (BOM).
    """
    befunde = []
    for lnr, zeile in enumerate(text.split("\n"), 1):
        for pos, c in enumerate(zeile):
            o = ord(c)
            if o in _BIDI:
                befunde.append((lnr, "P060", "bidi U+%04X" % o))
            elif o in _UNSICHTBAR:
                befunde.append((lnr, "P063", "invisible U+%04X" % o))
            elif o == 0xFEFF and not (lnr == 1 and pos == 0):
                befunde.append((lnr, "P063", "invisible U+FEFF"))
    if mit_laeufen:
        for lauf, angehaengt, zeile in _laeufe(text):
            if all(_erlaubt(c) for c in lauf) or angehaengt:
                continue
            arten = {_schrift(ord(c)) for c in lauf if c.isalpha()}
            code = "P062" if len(arten) >= 2 else "P061"
            befunde.append((zeile, code, "identifier `%s`" % lauf))
    return befunde


def quellvertrauen(wurzel=None):
    """`(scanned, findings)` over the tree's `.gab`/`.lean`/`.rs` sources."""
    wurzel = wurzel or WURZEL
    befunde = []
    geprueft = 0
    for q in sorted(wurzel.rglob("*.gab")) + sorted(wurzel.rglob("*.lean")) \
            + sorted(wurzel.rglob("*.rs")):
        rel = q.relative_to(wurzel)
        if _AUSGENOMMEN & set(rel.parts):
            continue
        try:
            text = q.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        geprueft += 1
        for lnr, code, detail in quellvertrauen_text(text, q.suffix == ".gab"):
            befunde.append((str(rel), lnr, code, detail))
    return geprueft, befunde


def sprechprobe_quellvertrauen():
    """Both directions: poison of every class is seen, clean text passes."""
    gift = (
        "-- \u202e\n"
        + "const p\u0430ss : u32 = 1;\n"
        + "const \u0430 : u32 = 1;\n"
        + "const\u200bA : u32 = 1;\n"
    )
    sauber = (
        "module m {\n"
        "const Gr\u00f6\u00dfe : u32 = 1; -- Gr\u00f6\u00dfe \u03c3 \u2192\n"
        'assume a "x";\n'
        "}\n"
    )
    codes = {c for _, c, _ in quellvertrauen_text(gift, True)}
    alle_vier = {"P060", "P061", "P062", "P063"} <= codes
    rein = quellvertrauen_text(sauber, True) == []
    # **The counter-direction must not take its yardstick from the subject:** the
    # clean text is fixed, not "whatever the tree holds today".
    print("== Sprechprobe Quellenvertrauen ==")
    print(f"  Gift aller vier Klassen gesehen: {'ja' if alle_vier else 'NEIN: %s' % sorted(codes)}")
    print(f"  sauberer Text geht durch:        {'ja' if rein else 'FALSCHER ALARM'}")
    return alle_vier and rein


def erhebe(zusatz=None):
    """Kennung -> Menge der Dateien, die sie vergeben.

    **An UNTRACKED `.rs` scratch file under `crates/` used to count too** (found by the
    `K100` walk audit, 2026-09-04: dropping one that reuses `"N001"` flips this guardian
    from `ALL PASS` to a false double-issue). `korpus.verfolgt()` keeps the population to
    what `git` actually knows about.
    """
    karte = collections.defaultdict(set)
    for q in sorted((WURZEL / "crates").rglob("*.rs")):
        if "/tests/" in str(q):
            continue          # Tests NENNEN Kennungen, sie vergeben keine
        if not korpus.verfolgt(q, WURZEL):
            continue
        # **Dasselbe fuer das Passregister** (seit 2026-08-21): `saetze.rs` fuehrt je Satz
        # die Kennungen auf, mit denen er absagt -- es NENNT sie, es vergibt sie nicht.
        # *Ohne diese Zeile meldete dieser Waechter 146 Doppelbelegungen, und keine davon
        # war eine.*
        if q.name == "saetze.rs":
            continue
        text = q.read_text()
        if zusatz and q.name == zusatz[0]:
            text += zusatz[1]
        for m in KENNUNG.finditer(text):
            karte[m.group(1)].add(q.name)
    return karte


def befunde(karte):
    return sorted((k, sorted(v)) for k, v in karte.items() if len(v) > 1)


def sprechprobe():
    """**Both directions -- and the second one does NOT take its yardstick from the subject.**

    The guardian has to SEE an artificial double issue and to LET THROUGH the same
    identifier once the poison is gone.

    Until 2026-08-31 the counter-direction read *"the real state reports nothing"*, and that
    is exactly the trap `pruefe-todo.py` has already paid for once: a REAL double issue would
    have made the probe fall, the guardian would have aborted with `2` -- **and swallowed the
    finding while doing so.** *A probe that takes its yardstick from its subject does not
    measure the subject.* So the question is only about `K001`: a double issue with the
    poison, none without it -- whatever else stands in the tree.
    """
    gift = befunde(erhebe(("namen.rs", '\nlet _ = "K001";\n')))
    sauber = befunde(erhebe())
    gesehen = any(k == "K001" for k, _ in gift)
    frei = not any(k == "K001" for k, _ in sauber)
    print("== Sprechprobe ==")
    print(f"  kuenstliche Doppelbelegung K001: {'gesehen' if gesehen else 'UEBERSEHEN'}")
    print(f"  ohne das Gift ist K001 frei:     {'ja' if frei else 'FALSCHER ALARM'}")
    return gesehen and frei


def main():
    # **THE SPEECH TEST RUNS EVERY TIME** (2026-08-31). Until today it sat behind a flag,
    # and `abnahme.py` calls this tool with no arguments at all -- **so the regular run
    # never once checked whether this guardian can go red.** Of all 28 guardians it was the
    # only one whose probe had to be ordered; every other runs it unasked. *A speech test
    # you have to request is indistinguishable from none* (R14).
    if not sprechprobe():
        # 2, not 1: a guardian that fails its own probe has measured NOTHING -- what it
        # says about the identifiers afterwards is not a statement about them.
        print("\n! Der Waechter misst nicht, was er behauptet. ABBRUCH.")
        return 2
    if not sprechprobe_quellvertrauen():
        print("\n! Der Waechter misst nicht, was er behauptet. ABBRUCH.")
        return 2
    if "--sprechprobe" in sys.argv:
        return 0

    karte = erhebe()
    # **`0 issued ... ALL PASS` was a GREEN run until 2026-08-31** (measured over an empty
    # tree). Every identifier belonged to exactly one file because there were none -- the
    # statement is true, empty, and it looks like a result. *That is W17, and this workshop
    # has already paid for the sentence once, with `zaehle-b3.py`.*
    if not karte:
        print("ABBRUCH: keine einzige Kennung erhoben -- es wurde NICHTS gemessen.")
        print("  `jede Kennung gehoert genau einer Datei` ist ueber der leeren Menge wahr")
        print("  und sagt nichts. Eine leere Grundgesamtheit ist eine Absage (W1, W17).")
        return 2
    b = befunde(karte)
    print(f"== Kennungen: {len(karte)} vergeben ==")
    # **The second half rides along, and its return code rides with it.** Source trust
    # (lane 182) lives in this file because it already walks every identifier-issuing
    # source; a finding below counts exactly like a double issue above.
    geprueft, qv = quellvertrauen()
    print(f"== Quellenvertrauen: {geprueft} .gab/.lean/.rs-Dateien geprueft ==")
    # **No population, no verdict** (W17, same as above): a trust statement over zero
    # files is true, empty, and looks like a result.
    if geprueft == 0:
        print("ABBRUCH: keine einzige Quelldatei erhoben -- es wurde NICHTS gemessen.")
        return 2
    if not b:
        letters = collections.Counter(k[0] for k in karte)
        print("  " + ", ".join(f"{c}: {n}" for c, n in sorted(letters.items())))
        print("== KENNUNGEN: ALL PASS -- jede Kennung gehoert genau einer Datei ==")
    else:
        for k, dateien in b:
            print(f"  !! {k} wird in {len(dateien)} Dateien vergeben: {', '.join(dateien)}")
        print(f"\n== KENNUNGEN: {len(b)} DOPPELBELEGUNGEN ==")
        print("  Eine Giftprobe mit `-- erwartet: <Kennung>` ist damit mehrdeutig: sie faellt")
        print("  gruen, waehrend die gemeinte Regel ausgefallen sein kann.")
    if not qv:
        print("== QUELLENVERTRAUEN: ALL PASS -- kein Bidi, kein unsichtbares Zeichen, "
              "kein fremdes Schriftbild ==")
        return 1 if b else 0
    for rel, lnr, code, detail in qv[:20]:
        print(f"  !! {rel}:{lnr} [{code}] {detail}")
    if len(qv) > 20:
        print(f"  ... und {len(qv) - 20} weitere")
    print(f"\n== QUELLENVERTRAUEN: {len(qv)} BEFUNDE ==")
    return 1


if __name__ == "__main__":
    sys.exit(main())
