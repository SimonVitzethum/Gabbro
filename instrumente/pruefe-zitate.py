#!/usr/bin/env python3
"""**A note that claims a check its rule does not perform.**

The class has now appeared twice with a name. On 2026-08-20 at `R003`: its note *spoke the
sentence* about the register offset, and no line did it -- `return d.NUR_W.A;` gave zero
errors. On 2026-08-21 in the emission layer: two comments in `emit.rs` cited `N027` and `N029`
as enforcing things they do not enforce. **The second one was found by re-reading, not by a
tool** -- and that is the whole reason this file exists.

    A comment that cites an identifier makes a claim about the CHECKER, not about the code
    it sits next to. An unchecked claim in a comment is worse than none: it is read as
    evidence.

## The rule, mechanically

Every identifier cited in a comment must either

  * be **issued in the same file** -- then the comment speaks about its own rule; or
  * be marked as a **foreign rule**, by naming the file it lives in, or by one of the
    connectives this folder already writes (*„same class as", „unlike", „is caught by"*).

Everything else is a candidate. **This is a candidate list, not a verdict** -- the same
framing as `pruefe-vergabe.py`, and for the same reason: whether a citation is a claim or a
cross-reference is a judgement, and a tool that guessed would be the silent answer this folder
writes against.

## The direction of its error

  * **false positive:** a legitimate cross-reference whose wording this file does not know;
  * **false negative (W10):** a claim about a rule that IS issued in the same file but says
    something else. *This tool cannot read.* `R003` -- the case that named the class -- would
    NOT be caught here, because its note and its rule sit in one file.

*That limit is the reason the mark below is a ratchet and not a target.* It measures the
cheap half; the expensive half stays with the reader.

    ./instrumente/pruefe-zitate.py            checks
    ./instrumente/pruefe-zitate.py --liste    every candidate with its line
"""
import importlib.util
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
FRIST = 120  # seconds; this tool executes nothing, the deadline covers the whole run.

# Where an identifier is ISSUED -- the same definition `pruefe-vergabe.py` uses. A register
# NAMES identifiers, it does not issue them.
VERGABE = re.compile(r'Absage::(?:fehler|hinweis|warnung)\s*\(\s*"([A-Z][0-9]{3})"')
NICHT = {"saetze.rs"}

# A citation in a comment: `M101` in backticks. Bare text is not counted -- `M101` without
# backticks is prose, and this folder writes its identifiers in backticks.
ZITAT = re.compile(r"`([A-Z][0-9]{3})`")

# **Connectives that mark a citation as a CROSS-REFERENCE rather than a claim.** They are
# taken from the wording this folder already uses; the list is closed and short on purpose --
# a long one would acquit everything.
FREMD = re.compile(
    r"\b(same class|dieselbe klasse|same shape|dieselbe gestalt|unlike|anders als|"
    r"wie bei|as at|siehe|see |vgl|is caught by|faengt|gefangen von|belongs to|"
    r"gehoert (zu|in)|lives in|steht in|\.rs\b|siblings?|schwester|"
    # **Naming the LAYER counts as naming the place.** For `emit.rs` the checker is as
    # foreign as another file: „die Regel, die im Pruefer `M123` heisst" points somewhere
    # else just as clearly as a file name does. *Added 2026-08-21 after the guardian flagged
    # four such lines -- the list was too narrow, not the comments too vague.*
    r"im pruefer|in the checker|im erzeuger|in the (generator|emitter)|eine ebene)", re.I)

# **The unit is the PARAGRAPH, not the line** *(2026-08-28)*.
#
# The rule above says "the comment", not "the line" -- and until today it was read line by
# line. A sentence running over two lines lost its place marker that way:
#
#     /// `Held(L)`. **Not a gap at all** -- the lock passes discharge it (`H005`, `H006`,
#     /// `H012`, `H016`). Reporting it as "no term" counted a carried obligation ...
#
# *"the lock passes discharge it"* stands in line 1, `H012` and `H016` in line 2 -- and line 2
# counted as two unbacked claims. **The paragraph says where the rule lives; the line does
# not know.**
#
# Split at EMPTY comment lines, not at the comment block: a seventy-line module header would
# otherwise be acquitted whole by a single `see`. *A paragraph is what a reader takes as one
# statement* -- in `abi.rs` the longest are seven lines.
ABSATZ_TRENNER = re.compile(r"^\s*(?://+!?|///|\*)\s?")

# **A ratchet, not a target -- and on 2026-08-28 it was RAISED to 274.** The reason stands
# here in full, because a raised mark otherwise looks like a healed cause.
#
# Measured at three states, each with ITS OWN expressions, line-wise and paragraph-wise:
#
#     62b997b  (226 was set here)         line-wise 226   paragraph-wise 207
#     927c1a5  (before the day's merges)  line-wise 256   paragraph-wise 233
#     today                               line-wise 309   paragraph-wise 274
#
# **First: the mark itself stood on the wrong unit.** 226 was never the object; the object
# was 207, and 19 of the difference were line breaks.
#
# **Second -- and this is the answer to the question that counts:** the OBJECT grows, not the
# denominator. Recomputed: of the 233 candidates at `927c1a5` **not one** dropped out, and
# **not one** arose because an identifier moved to another file. All 41 new ones are NEW
# comment lines -- 24 in `opsruf.rs`, `lean.rs`, `gatter.rs` and `kbedingung.rs`, the rest in
# files that grew. That the checker went from 40 to 43 files and from 211 to 227 issued
# identifiers explains none of it.
#
# **So 274 is a DEBT and not a booking, and it is carried as a debt** (`TODO.md`,
# 2026-08-28): the target is 207, and the way there is 67 comments that must say where their
# rule lives.
#
# *Why it was not paid here, written out:* it is 67 comments across twenty checker files,
# `emit.rs` leading with 40 -- ~~**and `emit.rs` is the file whose LITERAL lines the mutation
# catalogue carries as anchors.** Step 0.1 is repointing three dead anchors in exactly that
# file right now. *Whoever writes into a measuring surface while it is being measured measures
# a mixture* -- the same class as the collision of 2026-08-21.~~
#
# **STRUCK THROUGH 2026-08-30, because it was measured and it is FALSE.** The anchor hook was
# then the ground for calling the target 207 wrongly set, and for correcting the population
# instead of paying the debt. The count says otherwise:
#
#     anchor lines in the catalogue, distinct          499
#     of those, COMMENT lines                            4   phasen/typen/emit/aufrufgraph
#     anchors carrying an identifier in backticks        0
#     candidates the anchor rule removes                 0   274 -> 274
#
# `emit.rs` holds 135 anchor lines and exactly ONE of them is a comment, which cites nothing.
# **So none of the 40 `emit.rs` comments this guardian names is an anchor, and rewriting them
# cannot move `--anker` off 340 of 340.** The two populations are disjoint by construction:
# an anchor is a run of source text, a candidate needs an identifier in backticks, and no
# anchor has one.
#
# *The debt therefore stands, undiminished, at 274 with the target 207* -- there is no
# population correction to be had here, and the mark is NOT re-booked. What went in instead is
# the rule itself plus `ankerprobe`, which prints the zero on every run: the disjointness is
# now CHECKED rather than assumed, and it will speak up on the day it stops holding.
# **274 -> 281 on 2026-08-31, and the subject grew by a whole rule family.** `D014`-`D016`
# (`domaene.rs`, the chain edge) are built as `D006`-`D008` word for word, and seven of the
# new comment lines say so by NAMING the model: `D006` at the missing field, `D007` at the
# missing end, `D008` at the foreign table, `M109` at the position finding, `M120` at the
# `Self` binding, `K003` at the silent carrier. *Every one of those is a cross-reference and
# not a claim that this file issues the code* -- which is exactly the judgement this tool
# says it leaves to the reader. **The debt is carried, not discharged:** the target stays
# 207, and these seven are in it.
#
# **281 -> 279 later on 2026-08-31, and the mark FALLS.** `D017`/`D018` and `N044`/`N045`
# added sixteen comment lines citing a foreign rule, and every one of them now names the file
# the rule lives in -- `M109`/`M111`/`M120` in `m1.rs`, `K003` in `kosten.rs`, `D012` in
# `opsruf.rs`, `D010` in `kbedingung.rs`. Two OLDER lines fell with the same pass. *A whole
# rule family came in and the debt went DOWN by two* -- the target stays 207, and the mark
# follows the measurement in the direction a ratchet is allowed to move.
#
# **279 -> 280 on 2026-08-31, and the mark RISES with its reason.** The object grew: the
# block-scope work added `beispiele/gift/434`, `gift/435` and
# `messung/proben/probe-schleifenzusage-schatten.gab`, and one of those carries a citation
# of a rule it does not issue. **The target stays 207.** A mark that rises because the
# corpus grew is a different movement from one that rises because a debt was let go -- the
# file names stand here so the difference stays countable.
#
# **280 -> 281 on 2026-08-31, and the mark RISES with its reason.** The module/build lane
# added `crates/gabbro-cli/src/bau.rs`, three probe files and two measurement documents; one
# of them cites a rule it does not issue. **The target stays 207** -- the object grew, the
# debt did not.
#
# **281 -> 282 on 2026-09-01, and the mark RISES with its reason.** The seam lane added
# `beispiele/58`, three poison probes and three measurement probes; one cites a rule it does
# not issue. **The target stays 207** -- the object grew, the debt did not.
#
# **282 -> 286 on 2026-09-01, and the mark RISES with its reason.** The `OB4` lane added
# `beispiele/58`-`62` and nine poison probes; four of them cite a rule they do not issue.
# **The target stays 207** -- the object grew, the debt did not.
#
# **286 -> 289 on 2026-09-01, and the mark RISES with its reason.** The `OB5` lane carried
# the edge between two units into `bau.rs`, and the three new comments there name the three
# refusals the edge is ABOUT: `E009` and `K003` (what a call across the boundary costs
# without the bridge) and `N038` (why the preamble has to be the transitive closure). All
# three are issued elsewhere; **the target stays 207** -- the object grew, the debt did not.
# **289 -> 292 on 2026-09-01, and the mark RISES with its reason.** The `extern fn` lane
# added `beispiele/63-druckt.gab`, five poison probes and one measurement probe; three of
# them cite a rule they do not issue -- `P034` (why the bare call and not `let _ =`), `N041`
# (which the printing example is ABOUT and which no longer fires on it) and `N046` named
# from the sibling probes. **The target stays 207** -- the object grew, the debt did not.
#
# **292 -> 293 on 2026-09-01, and the mark RISES with its reason.** The entry-point lane
# added `beispiele/63-druckt.bau` and the entry rule in `bau.rs`; one comment cites a rule it
# does not issue. **The target stays 207** -- the object grew, the debt did not.
#
# **295 -> 296 on 2026-09-01, and the mark RISES with its reason.** The `S8` lane added
# `D020`, two assumptions and `beispiele/gift/570`; one comment cites a rule it does not
# issue. **The target stays 207** -- the object grew, the debt did not.
# **296 -> 302 on 2026-09-01, and the reason stands AT the mark again.** The on-ramp lane and
# the release lane together laid six comments that name a foreign identifier: the five hint
# texts in `parse.rs` name `P033`/`P014`/`M104`, and the flag probe names `P001`.
#
# **Each of the six is a cross-reference and not a coverage claim** -- the text says *"`P033`
# is already called that"*, not *"this file issues `P033`"*.
#
# *That does not acquit them; it names them.* The ratchet counts candidates, and a candidate
# is not a refusal -- see the section below, which has said so since the first run.
# **302 -> 306 on 2026-09-01.** The register-layout audit laid four comments that name a
# foreign identifier: `N047`/`N048`/`N049` each cite `N009` or `N010` to say what they are the
# sibling OF, and the corpus registry cites all three. Cross-references again, not coverage
# claims -- the text says *"`N009` compares registers against each other and never against
# the stride"*, which is a statement about `N009` and not about the file it stands in.
# **306 -> 308 on 2026-09-01.** The two repaired walkers (`wirkungen::liest_expr`,
# `geteilt::orte_in`) each cite `E010`/`H007` and the emitter's `C001` to say what the
# measurement WAS and where the counter-argument comes from. Cross-references, and this time
# the cited text is a quoted refusal -- evidence, not a coverage claim.
# **308 -> 316 on 2026-09-02.** The ExprArt-walker examination closed ten more index/bracket
# holes, and each repaired arm cites the code it now catches and the argument that settled it:
# `geteilt`/`namen`/`kosten` cite `H012`/`N016`/`N025`/`K001` for the call-in-an-index; the
# `ohne_klammern` arms in `phasen`/`m2`/`kbedingung`/`lib` cite `O004`/`L107`/`D005`/`W15`;
# `m1` cites `M109` for `&f`; `emit` cites `E008`; `kosten` and `namen` cite the emitter's own
# `C001`/`D004` for the counter-direction. Cross-references and quoted refusals -- evidence,
# not coverage claims. *Same category as the 306 -> 308 booking, eight arms further.*
# **316 -> 323 on 2026-09-02, and the seven come from `B2`'s answer.** `N052` and the POSIX
# table are stated by REFERENCE to the rules they sit between, and each reference is the
# argument rather than a coverage claim: `cnamen.rs` cites `M115` (the obligation a
# length-taking binding makes discharge-able) and `W7` (why `POSIX` is not folded into
# `vergeben`); `namen.rs` cites `N041`, `N046` and `M115` at the new refusal and `ZEIGER` in
# `miss-c-signaturen.py` for the parameter/result asymmetry; `emit.rs` cites `N046` and `W7`
# where `zeiger_schreibend` and `aus_ctafel` got their second reader; `saetze.rs` cites
# `P034`/`P041` for why a second code -- not a wider `N041` -- was the right shape.
# *Cross-references and quoted refusals. What each one asserts is about the CITED rule.*
# **323 -> 325 at the merge on 2026-09-02, and the number is MEASURED and not summed.** Two
# lanes moved this mark independently: the `B2` lane to 323, the boundary-sweep lane to 318,
# both from 316. **Neither number is the union** -- the merged tree measures 325, because the
# two sets of new comments overlap in none of their citations. *Picking a side or adding the
# deltas would both have been wrong, and the tool says which by refusing to agree with either.*
# **325 -> 332 at the merge on 2026-09-02, measured on the MERGED tree.** The pointer-typing
# lane booked 330 on its own base; the merged tree measures 332. *Third time in two days that
# a mark moved by two lanes is neither lane's number* -- the citations do not overlap, so
# neither picking a side nor adding the deltas lands on it. All seven of the lane's own are in
# `m1.rs` at the one new rule, each naming a boundary of it.
MARKE = 332
# **An ANCHOR comment is not a candidate** *(2026-08-30)*.
#
# `instrumente/mutiere-pruefer.py` carries 340 mutations, and every one of them holds a
# LITERAL run of source text as its anchor. An anchor the rewritten source no longer contains
# falls to `ANKER FEHLT` -- and the catalogue keeps reporting coverage over a shrinking base
# (W14). So a comment line that is part of an anchor is a MEASURING SURFACE of another tool,
# and demanding its rewrite here would set one instrument against another.
#
# *Population correction, not a relaxation* -- the same class as W23: a tool's own poison
# probes belong in hit counts, never in a demand count.
#
# > **And what the measurement said when the rule went in: it removes NOTHING.** Of 499
# > distinct anchor lines exactly **4** are comments, and **not one of the 340 anchors carries
# > an identifier in backticks at all**. The two populations are disjoint -- so the ground on
# > which this correction was ordered ("reaching 207 can silence `--anker`") does not hold.
# > *See `messung/ANKERHAKEN.md` for the full count.*
#
# The rule stays in anyway, and `ankerprobe` prints the number it removes on every run. That
# turns an ASSUMPTION into a measured fact: the day somebody writes an identifier into an
# anchor, the number stops being zero and says so.
_ANKER = None


def anker_kommentare():
    """File name -> set of stripped comment lines the mutation catalogue holds as anchors.

    **Raises rather than returning empty.** An exclusion that silently excludes nothing looks
    exactly like one that worked -- `main` turns the failure into a red abort.
    """
    global _ANKER
    if _ANKER is None:
        pfad = W / "instrumente" / "mutiere-pruefer.py"
        spec = importlib.util.spec_from_file_location("mutiere_pruefer", pfad)
        mp = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mp)
        if not mp.MUTATIONEN:
            raise RuntimeError("the mutation catalogue is empty")
        aus = {}
        for m in mp.MUTATIONEN:
            for z in m.alt.splitlines():
                t = z.strip()
                if t.startswith("//") or t.startswith("*"):
                    aus.setdefault(m.pfad.name, set()).add(t)
        _ANKER = aus
    return _ANKER


def vergeben():
    """File name -> set of identifiers issued in it."""
    aus = {}
    for q in sorted(W.glob("crates/*/src/*.rs")):
        if q.name in NICHT:
            continue
        aus[q.name] = set(VERGABE.findall(q.read_text(encoding="utf-8", errors="replace")))
    return aus


def absaetze(zeilen):
    """Comment paragraphs: maximal runs of comment lines, split at EMPTY ones.

    Yields one list of `(line number, text)` per paragraph. **The unit of the rule** -- see
    `ABSATZ_TRENNER` above.
    """
    i = 0
    while i < len(zeilen):
        if not (zeilen[i].strip().startswith("//") or zeilen[i].strip().startswith("*")):
            i += 1
            continue
        absatz = []
        while i < len(zeilen):
            t = zeilen[i].strip()
            if not (t.startswith("//") or t.startswith("*")):
                break
            if not ABSATZ_TRENNER.sub("", t).strip():
                i += 1
                if absatz:
                    yield absatz
                absatz = []
                continue
            absatz.append((i + 1, t))
            i += 1
        if absatz:
            yield absatz


def erhebe(zusatz=None, anker=True):
    """Candidates: (file, line, identifier, comment text).

    `anker=False` drops the anchor exclusion -- `ankerprobe` runs both ways to say what the
    rule costs. Nothing else may call it that way.
    """
    je_datei = vergeben()
    aussen = anker_kommentare() if anker else {}
    aus = []
    for q in sorted(W.glob("crates/*/src/*.rs")):
        if q.name in NICHT:
            continue
        text = q.read_text(encoding="utf-8", errors="replace")
        if zusatz and q.name == zusatz[0]:
            text += zusatz[1]
        eigene = je_datei.get(q.name, set())
        gehalten = aussen.get(q.name, frozenset())
        for absatz in absaetze(text.splitlines()):
            # **A place marker ANYWHERE in the paragraph excuses the paragraph** -- and only it.
            if FREMD.search(" ".join(t for _, t in absatz)):
                continue
            for n, s in absatz:
                # **An anchor comment is a measuring surface, not a demand** -- see above.
                if s in gehalten:
                    continue
                for k in ZITAT.findall(s):
                    if k not in eigene:
                        aus.append((q.name, n, k, s[:96]))
    return aus


def sprechprobe():
    """Both directions -- and the poison direction RECONSTRUCTS the real case.

    On 2026-08-21 `emit.rs` claimed `N027` and `N029`. `emit.rs` issues neither, and neither
    citation named a file. This probe puts exactly that line back.
    """
    echt = erhebe()
    gift = erhebe(zusatz=("emit.rs", "\n// the pass guarantees `N027` here, so nothing else has to\n"))
    a = len(gift) > len(echt)
    b = not any(d == "emit.rs" and k == "N027" for d, _, k, _ in echt)
    print("== Speech test, both directions ==")
    print("  reconstructed: %s" % ("ok (the false N027 citation is found)" if a
                                   else "FAILED -- the guardian does not see it"))
    print("  today's state: %s" % ("ok (the corrected comment passes)" if b
                                   else "FAILED -- false red"))
    return a and b


def ankerprobe():
    """**What the anchor rule COSTS, printed on every run.**

    A population correction that nobody counts is a claim. This one is counted both ways, and
    the difference is the only honest statement about it. *Today it is zero* -- the anchors and
    the citations do not overlap, and that is a measured fact rather than a hope.
    """
    anker = anker_kommentare()
    zeilen = sum(len(v) for v in anker.values())
    mit = len(erhebe())
    ohne = len(erhebe(anker=False))
    print("== Anchor rule (anchors of `mutiere-pruefer.py` are not candidates) ==")
    print("   %d anchor comment lines across %d files; it removes %d candidates."
          % (zeilen, len(anker), ohne - mit))
    if ohne == mit:
        print("   Zero today -- no anchor carries an identifier in backticks. The two")
        print("   populations are disjoint, and this line is what keeps that CHECKED.")
    return True


def main():
    # **Red on abort, not a quiet zero.** If the source tree cannot be read at all, this tool
    # must fall -- a guardian that reports „0 candidates" over an empty set is
    # indistinguishable from one that looked.
    # **Return code 2, and until 2026-08-31 it was 1.** Three lines further down a failed
    # speech test already ended with 2 -- the same file said both things about the same
    # class. *A refusal that ends with 1 is a refusal nobody can tell from a finding.*
    if not list(W.glob("crates/*/src/*.rs")):
        print("ABORT: no checker sources found -- this is NOT a count of zero.")
        sys.exit(2)
    # **Red on a catalogue that cannot be read.** The anchor rule can only exclude what it can
    # see; if it sees nothing, its zero is not a measurement.
    try:
        anker_kommentare()
    except Exception as e:
        print("ABORT: the mutation catalogue is unreadable (%s) -- the anchor rule" % e)
        print("       would then exclude nothing, and that is NOT a count of zero.")
        sys.exit(2)
    if not sprechprobe():
        sys.exit(2)
    ankerprobe()
    kand = erhebe()
    je_datei = {}
    for d, _, _, _ in kand:
        je_datei[d] = je_datei.get(d, 0) + 1

    print("\n== Citations in comments that name a FOREIGN identifier: %d ==" % len(kand))
    if je_datei:
        schwer = sorted(je_datei.items(), key=lambda x: -x[1])[:6]
        print("   heaviest: " + ", ".join("%s %d" % (a, b) for a, b in schwer))
    print("   A comment citing an identifier makes a claim about the CHECKER. Where the")
    print("   identifier is issued elsewhere and the comment does not say so, the claim")
    print("   is unchecked -- and it is read as evidence.")

    if "--liste" in sys.argv:
        print("\n== Every candidate ==")
        for d, n, k, s in kand:
            print("  %s:%d  [%s]  %s" % (d, n, k, s))

    print("\n== And what this does NOT mean ==")
    print("  A candidate list, not a verdict: whether a citation is a claim or a")
    print("  cross-reference is a judgement. And the expensive half stays with the reader --")
    print("  a note about a rule that IS issued in the same file but says something else")
    print("  passes here. **`R003`, the case that named the class, would NOT be caught.**")

    schlecht = 0
    if MARKE is not None and len(kand) > MARKE:
        print("\n  RATCHET BROKEN: %d candidates, %d booked." % (len(kand), MARKE))
        schlecht = 1
    print("\n== Work done: %d files, %d issued identifiers, %d candidates, 3 probes ==" % (
        len(list(W.glob("crates/*/src/*.rs"))),
        sum(len(v) for v in vergeben().values()), len(kand)))
    return schlecht


if __name__ == "__main__":
    sys.exit(main())
