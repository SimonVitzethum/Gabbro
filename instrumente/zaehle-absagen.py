#!/usr/bin/env python3
"""**Die Absageformen des ERZEUGERS, aufgeschluesselt -- und je Form ihr Zustand.**

`C001` entsteht in `emit.rs` an genau EINER Stelle (`fn weigere`). Was zaehlt, sind ihre
**Aufrufer**: jeder von ihnen sagt eine andere Form ab, und die Frage des
Vollstaendigkeitsplans lautet je Form:

> **Weist der PRUEFER dieselbe Form schon vorher ab?**

Faellt die Antwort ueberall auf „ja", dann ist `C001` fuer ein angenommenes Programm
**unerreichbar** -- und das ist die Aussage, die eine Korpuszahl nicht treffen kann
(`dokumente/PLAN-VOLLSTAENDIGKEIT.md` §2, Falle 80).

DIE ZAEHLUNG, UND WARUM SIE NICHT `grep C001` IST
--------------------------------------------------
`grep -c 'C001' emit.rs` zaehlt die Kommentare mit -- 22 statt 135. `grep -c 'weigere('`
zaehlt die Definition mit -- 136 statt 135. **Beide Zahlen standen schon in einem Plan**
(`PLAN-VOLLSTAENDIGKEIT.md`: erst 22, dann 136/127).

Dieses Werkzeug klammert von `weigere(` aus und liest das DRITTE Argument; steht dort ein
Bezeichner statt eines Textes, folgt es dem `let <name> = match … { … }` davor und nimmt
jeden Zweig einzeln, **aber nur die Zweige, deren WERT ein Text ist** -- die anderen senken
ab und kehren zurueck. *Eine Weigerung hinter einer Fallunterscheidung ist so viele Formen,
wie die Unterscheidung Textzweige hat.*

**Gemessen am 2026-08-31: 135 Aufrufe, davon 134 mit eigenem Text und einer hinter einem
`match` mit fuenf Textzweigen -- 139 Absagestellen und 130 verschiedene FORMEN.**

DIE ZUSTAENDE
-------------
    vom Pruefer   der Pruefer weist dieselbe Form ab; der Erzeuger sieht sie nie
    UNGEDECKT     der Pruefer nimmt die Form AN, und der Erzeuger sagt sie ab
    ungemessen    kein Korpusprogramm erreicht die Stelle -- und das ist keine Auskunft

**`UNGEDECKT` ist die ganze Frage.** Alles andere ist Buchhaltung.

WAS `--korpus` MISST UND WAS ES NICHT MISST
--------------------------------------------
`--korpus` faehrt `gabbro emit` ueber JEDE `.gab` des Baumes und trennt, was `emit`
ohnehin zusammen ausgibt: `emittiere_mit` laeuft auch dann, wenn der Pruefer Fehler fand.
Eine Datei mit **null Pruefer-Fehlern und einem `C001`** ist damit eine gemessene
`UNGEDECKT`-Zelle -- kein Argument, ein Programm.

> **Aber die Umkehrung gilt NICHT.** Eine Form, die kein Korpusprogramm erreicht, ist
> `ungemessen` und nicht gedeckt. *Der Korpus ist von der Sprache nach aussen geschrieben*
> (Falle 80); wer aus seinem Schweigen eine Deckung liest, hat die Frage gegen eine
> bequemere getauscht. Die Tafel druckt die drei Mengen darum getrennt, und
> `messung/ABSAGEFORMEN.md` traegt je Form das Urteil, das ein Mensch dazugeschrieben hat.

    ./instrumente/zaehle-absagen.py              die Formen, aus `emit.rs`
    ./instrumente/zaehle-absagen.py --korpus     dazu der gemessene Zustand je Form
    ./instrumente/zaehle-absagen.py --json       maschinenlesbar
"""
import json
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
EMIT = W / "crates" / "gabbro-check" / "src" / "emit.rs"
ZEICHEN = re.compile(r"'(?:\\.|[^\\'])'")
KOPF = re.compile(r"^(Fehler|Warnung|error|warning):\s*\[([A-Z][0-9]{3})\]\s*(\S+?):(\d+):(\d+):\s*(.*)$")
# **One deadline per file, and an expiry is an ABORT and not an empty result.**
# A hang reads as "still running", never as a finding -- on 2026-08-20 twenty-one runs of
# `pruefe-emission.sh` stood side by side for that reason (W17).
FRIST = 120


def ohne_kommentare(quelle):
    """The source with every comment blanked to spaces -- SAME length, newlines kept.

    Without this the brace scanner walks into a comment: `emit.rs` quotes `SPRACHE.md`
    with plain `"` inside `//` lines, and one such quote flips the string flag and makes
    the next `{` invisible. *Measured: 13 phantom arms out of one `match`.*
    """
    aus = []
    i = 0
    n = len(quelle)
    while i < n:
        c = quelle[i]
        # **A char literal carries a quote, and `emit.rs` has one**: `.replace('"', "\\\"")`
        # at line 3976. Read as the start of a string it swallows the next 2 000 lines --
        # and the brace scanner then finds arms that are not there. A lifetime (`'a`) has
        # no closing tick and is left alone by the same pattern.
        if c == "'" and ZEICHEN.match(quelle, i):
            stueck = ZEICHEN.match(quelle, i).group(0)
            aus.append(" " * len(stueck))
            i += len(stueck)
        elif c == '"':
            j = i + 1
            while j < n:
                if quelle[j] == "\\":
                    j += 2
                    continue
                if quelle[j] == '"':
                    break
                j += 1
            aus.append(quelle[i : j + 1])
            i = j + 1
        elif quelle.startswith("//", i):
            j = quelle.find("\n", i)
            j = n if j < 0 else j
            aus.append(" " * (j - i))
            i = j
        elif quelle.startswith("/*", i):
            j = quelle.find("*/", i + 2)
            j = n - 2 if j < 0 else j
            stueck = quelle[i : j + 2]
            aus.append("".join(ch if ch == "\n" else " " for ch in stueck))
            i = j + 2
        else:
            aus.append(c)
            i += 1
    return "".join(aus)


def _klammer_zu(text, offen):
    """Index of the `)` closing the `(` at `offen` -- string literals skipped."""
    tiefe = 0
    instr = False
    esc = False
    i = offen
    while i < len(text):
        c = text[i]
        if instr:
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                instr = False
        elif c == '"':
            instr = True
        elif c == "(":
            tiefe += 1
        elif c == ")":
            tiefe -= 1
            if tiefe == 0:
                return i
        i += 1
    raise ValueError("unbalanced")


def _teile(rumpf):
    """Split an argument list on TOP-LEVEL commas."""
    teile = []
    tiefe = 0
    instr = False
    esc = False
    cur = ""
    for c in rumpf:
        if instr:
            cur += c
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                instr = False
            continue
        if c == '"':
            instr = True
            cur += c
            continue
        if c in "([{":
            tiefe += 1
        if c in ")]}":
            tiefe -= 1
        if c == "," and tiefe == 0:
            teile.append(cur)
            cur = ""
        else:
            cur += c
    if cur.strip():
        teile.append(cur)
    return teile


def _text_aus(literal):
    """A Rust string literal (possibly `\\`-continued) as one line of text."""
    literal = re.sub(r"\\\s*\n\s*", "", literal)
    stuecke = re.findall(r'"((?:[^"\\]|\\.)*)"', literal)
    text = " ".join(stuecke)
    text = text.replace('\\"', '"').replace("\\\\", "\\")
    return re.sub(r"\s+", " ", text).strip()


def _zweige_von(quelle, bis, name):
    """The string arms of the `let <name> = match … {` block that ends before `bis`.

    A refusal behind a match is as many forms as the match has arms. Without this the
    tool would count one form and the table would be short by four.
    """
    kopf = quelle.rfind(f"let {name} = match", 0, bis)
    if kopf < 0:
        return []
    auf = quelle.find("{", quelle.find("match", kopf))
    tiefe = 0
    instr = False
    esc = False
    i = auf
    while i < len(quelle):
        c = quelle[i]
        if instr:
            if esc:
                esc = False
            elif c == "\\":
                esc = True
            elif c == '"':
                instr = False
        elif c == '"':
            instr = True
        elif c == "{":
            tiefe += 1
        elif c == "}":
            tiefe -= 1
            if tiefe == 0:
                break
        i += 1
    aus = []
    for anfang, ende in _arme(quelle, auf, i):
        koerper = quelle[anfang:ende].strip().strip(",").strip()
        if koerper.startswith("{") and koerper.endswith("}"):
            koerper = koerper[1:-1].strip()
        # **Only an arm whose VALUE is a text is a refusal.** The others walk the domain
        # and `return` -- taking their `format!` templates would count the emitted C as a
        # refused form, and the table would grow by twelve rows that say nothing.
        if not re.fullmatch(r'"(?:[^"\\]|\\.)*"(?:\s*"(?:[^"\\]|\\.)*")*', koerper, re.S):
            continue
        aus.append((quelle[:anfang].count("\n") + 1, _text_aus(koerper)))
    return aus


def _ende_text(quelle, i):
    """Index just past the string literal that starts at `i`."""
    j = i + 1
    while j < len(quelle):
        if quelle[j] == "\\":
            j += 2
            continue
        if quelle[j] == '"':
            return j + 1
        j += 1
    return j


def _zu(quelle, offen):
    """Index of the bracket closing the one at `offen` -- strings skipped."""
    paare = {"(": ")", "[": "]", "{": "}"}
    ende = paare[quelle[offen]]
    tiefe = 0
    i = offen
    while i < len(quelle):
        c = quelle[i]
        if c == '"':
            i = _ende_text(quelle, i)
            continue
        if c == quelle[offen]:
            tiefe += 1
        elif c == ende:
            tiefe -= 1
            if tiefe == 0:
                return i
        i += 1
    raise ValueError("unbalanced")


def _arme(quelle, auf, zu):
    """The `(begin, end)` of every arm VALUE inside the match body `quelle[auf:zu]`."""
    aus = []
    i = auf + 1
    while i < zu:
        c = quelle[i]
        if c == '"':
            i = _ende_text(quelle, i)
            continue
        if c in "([{":
            i = _zu(quelle, i) + 1
            continue
        if quelle.startswith("=>", i):
            j = i + 2
            while j < zu and quelle[j].isspace():
                j += 1
            if quelle[j] == "{":
                e = _zu(quelle, j) + 1
            else:
                e = j
                while e < zu:
                    if quelle[e] == '"':
                        e = _ende_text(quelle, e)
                        continue
                    if quelle[e] in "([{":
                        e = _zu(quelle, e) + 1
                        continue
                    if quelle[e] == ",":
                        break
                    e += 1
            aus.append((j, e))
            i = e
            continue
        i += 1
    return aus


def formen(quelle=None):
    """Every `weigere(…)` CALL SITE with the form it refuses. Sorted by line."""
    quelle = ohne_kommentare(quelle if quelle is not None else EMIT.read_text())
    aus = []
    for m in re.finditer(r"\bweigere\s*\(", quelle):
        if quelle[max(0, m.start() - 3) : m.start()] == "fn ":
            continue
        zeile = quelle[: m.start()].count("\n") + 1
        zu = _klammer_zu(quelle, m.end() - 1)
        teile = _teile(quelle[m.end() : zu])
        if len(teile) < 3:
            continue
        dritt = teile[2].strip()
        if '"' in dritt:
            aus.append((zeile, _text_aus(dritt), "direkt"))
        else:
            zweige = _zweige_von(quelle, m.start(), dritt.lstrip("&"))
            if not zweige:
                aus.append((zeile, f"<{dritt}>", "unaufgeloest"))
            for z, t in zweige:
                aus.append((z, t, f"Zweig von `{dritt}`"))
    return sorted(aus)


def korpuslauf(wurzel=None, gabbro=None):
    """Per `.gab` file: the checker codes and the `C001` texts, apart.

    `gabbro emit` runs `emittiere_mit` even when the checker found errors, so ONE run
    yields both halves. Zero checker errors beside a `C001` is a measured `UNGEDECKT`.
    """
    wurzel = wurzel or W
    befehl = None
    # **A binary older than its sources measures a tree that no longer exists** (2026-08-31).
    # This tool preferred `target/release/gabbro`; here it was ELEVEN DAYS old, with 44 source
    # files newer than it. The table then read 4 UNGEDECKT on the server (debug, current) and
    # 51 here (release, stale) -- *from byte-identical sources*.
    #
    # Third instance of one family: `rsync -a` hands `cargo` a mixture, `rglob` walks into
    # foreign worktrees, and a stale binary answers for a checker nobody built. **The demand
    # is the one `pruefe-beweise.sh` already makes: nothing older than any source.**
    juengste = max((q.stat().st_mtime for q in (wurzel / "crates").rglob("*.rs")), default=0)
    veraltet = []
    for k in (gabbro, wurzel / "target" / "release" / "gabbro", wurzel / "target" / "debug" / "gabbro"):
        if k is None or not pathlib.Path(k).exists():
            continue
        if pathlib.Path(k).stat().st_mtime < juengste:
            veraltet.append(str(k))
            continue
        befehl = [str(k)]
        break
    # **When the CLOCK says stale, ask the CONTENT -- do not forge the timestamp.**
    # `git merge` and the mutation run both rewrite unchanged sources, and every one of them
    # is younger than the build afterwards; a pure time comparison then aborts over a tree
    # that is current. *`cargo` reckons by CONTENT, this latch reckons by TIME, and neither
    # is wrong* -- the same two notions of "current" that `pruefe-beweise.sh` books for
    # Isabelle. So: let it build once, and leave the verdict to the tool that knows the
    # content. **A `touch` on the binary would be the wrong cure** -- it hides exactly the
    # mixture the latch stands against.
    if befehl is None and veraltet:
        gebaut = subprocess.run(["cargo", "build", "--offline", "-q"], cwd=wurzel,
                                capture_output=True, text=True)
        if gebaut.returncode == 0:
            # `cargo` has just certified the build against the CONTENT. It may or may not
            # have relinked -- both mean the same thing, so take the YOUNGEST candidate and
            # do not ask the clock a second time.
            frisch = [k for k in veraltet if pathlib.Path(k).exists()]
            if frisch:
                befehl = [max(frisch, key=lambda k: pathlib.Path(k).stat().st_mtime)]
                veraltet = []
    if befehl is None and veraltet:
        raise SystemExit(
            "ABBRUCH: jedes gefundene Binaerprogramm ist AELTER als die Quellen -- "
            + ", ".join(veraltet)
            + "\n  Ein veraltetes Binaerprogramm antwortet fuer einen Pruefer, den niemand "
            "gebaut hat.\n  `cargo build` und noch einmal. *Nichts wurde gemessen.*"
        )
    # **A missing binary is not a missing measurement.** `cargo run` builds it -- slower, and
    # it never turns "nothing was measured" into a green run (W1). The same fallback
    # `zaehle-fragmente.py` carries.
    if befehl is None:
        befehl = ["cargo", "run", "-q", "--bin", "gabbro", "--"]
    aus = {}
    # **`rglob` from the repo root walks into every agent worktree** (2026-08-31). Measured on
    # the day this tool was built: 13 629 of 14 078 `.gab` files in the tree live under
    # `.claude/worktrees/`, some of them ten days stale. The table then read 2 398 emitting
    # files locally and 825 on the server -- and gave 45 UNGEDECKT against 4, *from the same
    # sources*. The server was right by accident: the worktrees are excluded from the rsync.
    #
    # Same class as `zaehle-b3.py`, which followed a path pointing beside its own worktree.
    # *A tool whose verdict depends on which OTHER trees happen to lie around measures the
    # disk, not the language.*
    #
    # **And the exclusion is RELATIVE to the root, which cost a measurement the same night.**
    # The first form matched the absolute path -- and the root of an agent IS
    # `…/.claude/worktrees/agent-X`, so inside one every file matched and the corpus went to
    # zero -- *418 found, 0 left after the filter.* `pruefe-grammatiktafel.py` then aborted with 2
    # instead of naming its four cells, **and an abort inside an acceptance run looks like the
    # finding it was supposed to report.** A filter that reads the absolute path measures where
    # the tree LIES, not what is in it.
    aus_bau = ("target", ".claude", ".lake")
    for d in sorted(pathlib.Path(wurzel).rglob("*.gab")):
        if any(teil in aus_bau for teil in d.relative_to(wurzel).parts[:-1]):
            continue
        try:
            r = subprocess.run(befehl + ["emit", str(d)], cwd=wurzel,
                               capture_output=True, text=True, timeout=FRIST)
        except subprocess.TimeoutExpired:
            raise SystemExit(
                f"ABBRUCH: `gabbro emit {d}` ueberschritt {FRIST} s -- es wurde NICHTS "
                "gemessen, und eine halbe Tafel ist keine."
            )
        codes, c001 = [], []
        for zeile in r.stderr.split("\n"):
            k = KOPF.match(zeile)
            if not k or k.group(1) not in ("Fehler", "error"):
                continue
            if k.group(2) == "C001":
                c001.append(re.sub(r"\s+", " ", k.group(6).replace("no lowering: ", "", 1)).strip())
            else:
                codes.append(k.group(2))
        aus[str(d.relative_to(wurzel))] = {"codes": sorted(set(codes)), "c001": c001}
    return aus


def zustaende(gemessen):
    """Form text -> (`UNGEDECKT` | `nur mit Pruefer-Fehler` , the files that showed it)."""
    karte = {}
    for datei, e in gemessen.items():
        for t in e["c001"]:
            eintrag = karte.setdefault(t, {"ungedeckt": [], "mit_fehler": []})
            (eintrag["ungedeckt"] if not e["codes"] else eintrag["mit_fehler"]).append(datei)
    return karte


def sprechprobe():
    """**Der Auszaehler an sich selbst -- in beide Richtungen.**

    Er hat sich beim Bau dreimal geirrt, und jedes Mal sah die Zahl plausibel aus: ein
    Anfuehrungszeichen in einem `//`-Kommentar, das Zeichenliteral `'"'`, und `match`-Zweige,
    die absenken statt abzusagen. *Ein Zaehler ohne Probe ist eine Behauptung.*

    Gemessen wird an einem ERFUNDENEN Quelltext, nicht am echten -- sonst wandert die Probe
    mit ihrem Gegenstand.
    """
    gift = (
        'fn f() {\n'
        '    // ein Kommentar mit einem " darin, und SPRACHE.md sagt "so"\n'
        '    let c = \'"\';\n'
        '    weigere(absagen, s.span, "zzsprechprobe eine erfundene Form");\n'
        '    let grund = match &x.d {\n'
        '        D::A(o) => { senke(o); return; }\n'
        '        D::B(_) => "zzzweig ein Textzweig",\n'
        '    };\n'
        '    weigere(absagen, s.span, grund);\n'
        '}\n'
    )
    gefunden = {t for _, t, _ in formen(gift)}
    proben = [
        ("eine Absage wird gefunden", "zzsprechprobe eine erfundene Form" in gefunden),
        ("ein TEXTZWEIG hinter einem `match` zaehlt einzeln", "zzzweig ein Textzweig" in gefunden),
        ("ein Zweig, der ABSENKT, zaehlt NICHT", len(gefunden) == 2),
        ("ein Quelltext ohne Weigerung ergibt null", not formen("fn f() { g(); }\n")),
    ]
    return proben


def main():
    # **TOOTH 0 -- THE SUBJECT HAS TO BE THERE** (2026-08-31). Over a tree without
    # its subject this tool died of a `FileNotFoundError`: return code **1**, a
    # traceback, and in a chain that reads like a finding. *A crash is not a refusal
    # -- a NAMED refusal is*, and a missing subject says the SETUP has to change.
    if not EMIT.is_file():
        print(f"ABBRUCH: {EMIT.relative_to(W)} fehlt -- es wurde NICHTS gemessen.",
              file=sys.stderr)
        print("  Ohne den Erzeuger gibt es keine Absageform, und `0 Formen` waere ein"
              " Urteil ueber nichts (W1, W17).", file=sys.stderr)
        return 2
    # `--json` yields MACHINE-READABLE output; the probe then belongs on the error channel,
    # or it stands in the middle of the document somebody is reading in.
    kanal = sys.stderr if "--json" in sys.argv else sys.stdout
    print("== Sprechprobe des Auszaehlers ==", file=kanal)
    proben = sprechprobe()
    for was, ok in proben:
        print(f"  {'ok         ' if ok else 'GESCHEITERT'}  {was}", file=kanal)
    if not all(ok for _, ok in proben):
        print("\n! Der Auszaehler misst nicht, was er behauptet. ABBRUCH.", file=kanal)
        # **Every refusal in this file ends with 2, not 1** (2026-08-31). This counter joined
        # `abnahme.py` that day, so its return code is now read as a VERDICT -- and the sixth
        # requirement applies: `1` means the TREE has to change, `2` means the SETUP does.
        # Every site below says NOTHING WAS MEASURED, so every one of them is a `2`.
        return 2
    print(file=kanal)
    alle = formen()
    texte = sorted({t for _, t, _ in alle})
    gemessen = korpuslauf() if "--korpus" in sys.argv else None
    karte = zustaende(gemessen) if gemessen else {}

    if "--json" in sys.argv:
        print(json.dumps({"stellen": alle, "korpus": gemessen}, indent=1))
        return 0

    print(f"== {len(alle)} Absagestellen, {len(texte)} verschiedene FORMEN, in {EMIT.name} ==")
    print()
    for zeile, text, art in alle:
        marke = ""
        if karte.get(text, {}).get("ungedeckt"):
            marke = "UNGEDECKT  "
        elif text in karte:
            marke = "mit Fehler "
        elif gemessen is not None:
            marke = "ungemessen "
        print(f"  {zeile:>5}  {marke}{text[:110]}")

    if gemessen is None:
        print()
        print("  (`--korpus` misst dazu, welche Form ein Programm mit NULL Pruefer-Fehlern")
        print("   ausloest -- das ist die gemessene `UNGEDECKT`-Menge.)")
        return 0

    ung = sorted(t for t, e in karte.items() if e["ungedeckt"])
    print()
    print(f"== {len(gemessen)} Dateien gefahren -- "
          f"{sum(1 for e in gemessen.values() if not e['codes'])} ohne Pruefer-Fehler ==")
    print(f"== {len(ung)} FORMEN gemessen UNGEDECKT · "
          f"{len(karte) - len(ung)} nur neben einem Pruefer-Fehler gesehen · "
          f"{len(texte) - len(karte)} vom Korpus nie erreicht ==")
    print()
    for t in ung:
        print(f"  UNGEDECKT  {t[:100]}")
        for d in karte[t]["ungedeckt"]:
            print(f"             {d}")
    print()
    print("  **Ungemessen ist nicht gedeckt.** Der Korpus ist von der Sprache nach aussen")
    print("  geschrieben; sein Schweigen ueber eine Form ist keine Auskunft ueber sie")
    print("  (Falle 80). Das Urteil je Form steht in `messung/ABSAGEFORMEN.md`.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
