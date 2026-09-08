#!/usr/bin/env python3
"""**Does the coverage theorem talk about THIS language?**

`programmlogik/Gabbro/Coverage.lean` proves a sentence about every form of the grammar:
carried by a general lemma, carried by the automation, assumed under a name, or refused
under a tag. The proof rests on `Form` and `Reason` -- and both are **hand-written mirrors**
of `crates/gabbro-check/src/lean.rs`. A mirror that drifts still typechecks. The theorem is
then green and about a language that is not Gabbro.

That is the `W7`/`W16` class this tree keeps finding: **two registers over one thing, and
only one of them read by a guard.** `PLAN.md` section 11.1 is the most recent instance --
`LeanReason::PassCounter` was declared, tagged, returned by the emitter, and stood in
neither `LeanReason::ALL` nor `zaehle-lean.py`'s `GRUENDE`.

WHAT THIS GUARD CHECKS
----------------------
1. **The population.** Every variant of `LeanReason` has a constructor of `Reason`, and
   every constructor of `Reason` has a variant -- name for name, in both directions.
2. **The order.** `Reason`'s constructors stand in the order of `LeanReason::ALL`, so the
   two lists can be read side by side.
3. **The tags.** For every variant, `LeanReason::tag()` and `Reason.tag` give the SAME
   string. A tag that drifts makes `every_refusal_has_an_emitter_tag` a claim about a tag
   nobody prints.
4. **The kinds.** `LeanReason::kind()` and `Reason.kind` agree, so `classify` assumes what
   the emitter assumes and refuses what the emitter refuses.
5. **The classifier is total in the SOURCE too.** Every constructor of `Form` appears in
   `classify`, and `classify` has no catch-all arm that could swallow a new one.
6. **Every carried form has a lemma.** A `Form` whose `classify` arm says `.carried` has an
   explicit arm in `Discharges` -- not the `_ => False` fallback.

WHAT THIS GUARD DOES **NOT** CHECK -- and this half is the honest one
--------------------------------------------------------------------
* **That `Form` is the whole grammar.** The refusal half (`Reason`) is mechanical because
  `lean.rs` names its refusals in one enum. The CARRIED half has no such enum: the emitter
  decides to carry a form by writing a term, at some fifty places in `lean.rs`, and there is
  no list to compare against. *A form the grammar admits, the emitter carries, and `Form`
  never names would pass every check above.* Closing that needs the emitter to name its
  carried decision points the way it names its refusals -- a change to `lean.rs`, not to
  this guard.
* **That the Lean file PROVES anything.** `lake build` does that; this guard reads text.
* **That the verdict is the RIGHT one.** It checks that a carried form has a lemma, not
  that the lemma says what the form needs. Only a reader can check that.
* **That `parse.rs` admits exactly the forms `Form` names.** The grammar side is checked by
  `pruefe-grammatiktafel.py` against the EBNF, and against `Form` by nobody.

    ./instrumente/pruefe-deckung.py           the judgement
    ./instrumente/pruefe-deckung.py --probe   only the speech test

Exit 0 green, 1 a finding, 2 an abort (nothing was measured).
"""
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
LEAN_RS = W / "crates" / "gabbro-check" / "src" / "lean.rs"
COVERAGE = W / "programmlogik" / "Gabbro" / "Coverage.lean"


def camel(name):
    """`PassCounter` -> `passCounter`, the spelling a Lean constructor takes."""
    return name[0].lower() + name[1:]


# ---------------------------------------------------------------- the Rust side

def rust_varianten(text):
    """The variants of `enum LeanReason`, in declaration order."""
    m = re.search(r"pub enum LeanReason \{(.*?)\n\}", text, re.S)
    if not m:
        return None
    return re.findall(r"^\s{4}([A-Z][A-Za-z0-9]*),\s*$", m.group(1), re.M)


def rust_alle(text):
    """`LeanReason::ALL`, in its own order."""
    m = re.search(r"pub const ALL: \[LeanReason; (\d+)\] = \[(.*?)\n    \];", text, re.S)
    if not m:
        return None, None
    return int(m.group(1)), re.findall(r"LeanReason::([A-Za-z0-9]+),", m.group(2))


def rust_marken(text):
    """`LeanReason::tag()` -- variant to string."""
    m = re.search(r"pub fn tag\(self\) -> &'static str \{\s*match self \{(.*?)\n        \}",
                  text, re.S)
    if not m:
        return None
    return dict(re.findall(r"LeanReason::([A-Za-z0-9]+) => \"([^\"]*)\"", m.group(1)))


def rust_arten(text, varianten):
    """`LeanReason::kind()` -- variant to `assumption`/`noTerm`/`noWiring`."""
    m = re.search(r"pub fn kind\(self\) -> Kind \{\s*match self \{(.*?)\n        \}",
                  text, re.S)
    if not m:
        return None
    koerper = m.group(1)
    arten = {}
    # Every arm but the catch-all names its variants explicitly.
    for arm in re.finditer(r"((?:\s*\|?\s*LeanReason::[A-Za-z0-9]+)+)\s*=> Kind::(\w+)",
                           koerper):
        art = {"Assumption": "assumption", "NoTerm": "noTerm",
               "NoWiring": "noWiring"}[arm.group(2)]
        for v in re.findall(r"LeanReason::([A-Za-z0-9]+)", arm.group(1)):
            arten[v] = art
    rest = re.search(r"_ => Kind::(\w+)", koerper)
    if rest:
        art = {"Assumption": "assumption", "NoTerm": "noTerm",
               "NoWiring": "noWiring"}[rest.group(1)]
        for v in varianten:
            arten.setdefault(v, art)
    return arten


# ---------------------------------------------------------------- the Lean side

def lean_gruende(text):
    """The constructors of `inductive Reason`, in declaration order."""
    m = re.search(r"inductive Reason where\n(.*?)\n  deriving", text, re.S)
    if not m:
        return None
    return re.findall(r"[|\s]([a-z][A-Za-z0-9]*)\b", m.group(1))


def lean_marken(text):
    """`Reason.tag` -- constructor to string."""
    m = re.search(r"def Reason\.tag : Reason → String\n(.*?)\n\n", text, re.S)
    if not m:
        return None
    return dict(re.findall(r"\| \.([A-Za-z0-9]+) => \"([^\"]*)\"", m.group(1)))


def lean_arten(text, gruende):
    """`Reason.kind` -- constructor to kind, catch-all resolved."""
    m = re.search(r"def Reason\.kind : Reason → Kind\n(.*?)\n\n", text, re.S)
    if not m:
        return None
    arten = {}
    rest = None
    for zeile in m.group(1).splitlines():
        treffer = re.match(r"\s*\|(.*?)=> \.(\w+)", zeile)
        if not treffer:
            continue
        namen = re.findall(r"\.([a-z][A-Za-z0-9]*)", treffer.group(1))
        if not namen:
            rest = treffer.group(2)
            continue
        for n in namen:
            arten[n] = treffer.group(2)
    if rest:
        for g in gruende:
            arten.setdefault(g, rest)
    return arten


def lean_formen(text):
    """The constructors of `inductive Form`, in declaration order."""
    m = re.search(r"inductive Form where\n(.*?)\n  deriving", text, re.S)
    if not m:
        return None
    return re.findall(r"^  \| ([a-z][A-Za-z0-9]*)", m.group(1), re.M)


def lean_urteile(text):
    """`classify` -- form to the verdict written for it. `None` where an arm is missing."""
    m = re.search(r"\ndef classify : Form → Verdict\n(.*?)\n\n", text, re.S)
    if not m:
        return None, False
    urteile = {}
    hat_auffang = False
    # **Only the arms at the OUTER level.** An arm's right-hand side may itself be a
    # `match` with arms of its own (`.refusedOrAssumed r => match r.kind with …`), and
    # those are over `Kind`, not over `Form`. A regex that read them as Form arms would
    # report the inner `| _ =>` as a catch-all over the enumeration -- a guard finding a
    # defect its own subject does not have.
    arme, puffer = [], ""
    for zeile in m.group(1).splitlines():
        if re.match(r"^  \| ", zeile) and "=>" in puffer:
            arme.append(puffer)
            puffer = zeile
        elif re.match(r"^  \| ", zeile):
            puffer = (puffer + " " + zeile.strip()).strip() if puffer else zeile
        elif zeile.strip() and puffer:
            puffer += " " + zeile.strip()
    if puffer:
        arme.append(puffer)
    for arm in arme:
        if re.match(r"^  \| _\b", arm):
            hat_auffang = True
            continue
        kopf, _, rumpf = arm.partition("=>")
        for n in re.findall(r"\.([a-z][A-Za-z0-9]*)", kopf):
            urteile[n] = rumpf.strip().split()[0] if rumpf.strip() else ""
    return urteile, hat_auffang


def lean_entlastungen(text):
    """`Discharges` -- the forms with an EXPLICIT arm (the `_ => False` fallback is not one)."""
    m = re.search(r"\ndef Discharges : Form → Prop\n(.*?)\n\n", text, re.S)
    if not m:
        return None
    return set(re.findall(r"^  \| \.([a-z][A-Za-z0-9]*) =>", m.group(1), re.M))


# ---------------------------------------------------------------- the judgement

def messe(lean_rs_text, coverage_text):
    """Returns (list of findings, list of counted things). A `None` field is an ABORT."""
    befunde = []
    varianten = rust_varianten(lean_rs_text)
    anzahl, alle = rust_alle(lean_rs_text)
    marken_r = rust_marken(lean_rs_text)
    gruende = lean_gruende(coverage_text)
    marken_l = lean_marken(coverage_text)
    formen = lean_formen(coverage_text)
    urteile, auffang = lean_urteile(coverage_text)
    entlastungen = lean_entlastungen(coverage_text)
    if not all([varianten, alle, marken_r, gruende, marken_l, formen, urteile is not None,
                entlastungen is not None]):
        return None, None
    arten_r = rust_arten(lean_rs_text, varianten)
    arten_l = lean_arten(coverage_text, gruende)
    if arten_r is None or arten_l is None:
        return None, None

    # 1. the population, both directions
    erwartet = [camel(v) for v in alle]
    fehlend = [v for v in erwartet if v not in gruende]
    ueberzaehlig = [g for g in gruende if g not in erwartet]
    for v in fehlend:
        befunde.append(f"`LeanReason` has {v} and `Reason` has not")
    for g in ueberzaehlig:
        befunde.append(f"`Reason` has {g} and `LeanReason` has not")
    if anzahl != len(alle):
        befunde.append(f"`LeanReason::ALL` says {anzahl} and holds {len(alle)}")
    if set(varianten) != set(alle):
        nur_enum = sorted(set(varianten) - set(alle))
        nur_alle = sorted(set(alle) - set(varianten))
        for v in nur_enum:
            befunde.append(f"`LeanReason::{v}` stands in the enum and not in `ALL`")
        for v in nur_alle:
            befunde.append(f"`LeanReason::{v}` stands in `ALL` and not in the enum")

    # 2. the order
    if not fehlend and not ueberzaehlig and gruende != erwartet:
        erste = next(i for i, (a, b) in enumerate(zip(gruende, erwartet)) if a != b)
        befunde.append(f"the order parts at position {erste}: "
                       f"`Reason` has {gruende[erste]}, `ALL` has {erwartet[erste]}")

    # 3. the tags
    for v in alle:
        g = camel(v)
        if g not in marken_l or v not in marken_r:
            continue
        if marken_r[v] != marken_l[g]:
            befunde.append(f"tag of {v}: `lean.rs` says \"{marken_r[v]}\", "
                           f"`Coverage.lean` says \"{marken_l[g]}\"")
    for v in alle:
        if v not in marken_r:
            befunde.append(f"`LeanReason::{v}` has no tag in `lean.rs`")
        if camel(v) not in marken_l:
            befunde.append(f"`Reason.{camel(v)}` has no tag in `Coverage.lean`")

    # 4. the kinds
    for v in alle:
        g = camel(v)
        if v in arten_r and g in arten_l and arten_r[v] != arten_l[g]:
            befunde.append(f"kind of {v}: `lean.rs` says {arten_r[v]}, "
                           f"`Coverage.lean` says {arten_l[g]}")

    # 5. the classifier is total in the source too
    if auffang:
        befunde.append("`classify` carries a `| _ =>` arm -- a new form would be swallowed")
    for f in formen:
        if f not in urteile:
            befunde.append(f"`Form.{f}` has no arm in `classify`")

    # 6. every carried form has a lemma
    for f in formen:
        if urteile.get(f) == ".carried" and f not in entlastungen:
            befunde.append(f"`Form.{f}` is carried and has no arm in `Discharges`")

    gezaehlt = [f"{len(alle)} refusal reasons", f"{len(formen)} forms",
                f"{sum(1 for f in formen if urteile.get(f) == '.carried')} carried",
                f"{len(entlastungen)} discharge lemmas"]
    return befunde, gezaehlt


# ---------------------------------------------------------------- the speech test

RS_PROBE = """
pub enum LeanReason {
    Alpha,
    Beta,
    Gamma,
}
impl LeanReason {
    pub fn kind(self) -> Kind {
        match self {
            LeanReason::Alpha => Kind::Assumption,
            _ => Kind::NoTerm,
        }
    }
    pub const ALL: [LeanReason; 3] = [
        LeanReason::Alpha,
        LeanReason::Beta,
        LeanReason::Gamma,
    ];
    pub fn tag(self) -> &'static str {
        match self {
            LeanReason::Alpha => "alpha",
            LeanReason::Beta => "beta",
            LeanReason::Gamma => "gamma",
        }
    }
"""

LEAN_PROBE = """
inductive Reason where
  | alpha | beta | gamma
  deriving DecidableEq, Repr

def Reason.tag : Reason → String
  | .alpha => "alpha"
  | .beta => "beta"
  | .gamma => "gamma"

def Reason.kind : Reason → Kind
  | .alpha => .assumption
  | _ => .noTerm

inductive Form where
  | eins
  | zwei
  | refusedOrAssumed (r : Reason)
  deriving DecidableEq, Repr

def classify : Form → Verdict
  | .eins => .carried
  | .zwei => .carriedByTactic
  | .refusedOrAssumed r => .refused r.tag

def Discharges : Form → Prop
  | .eins => EinsCarried
  | _ => False

"""


def sprechprobe():
    """Both directions, on a subject this run brings along.

    A guard that only shows what it catches has not shown that it stays quiet where
    nothing is wrong -- that half is the one `W10` keeps asking for.
    """
    proben = []
    heil_b, heil_z = messe(RS_PROBE, LEAN_PROBE)
    proben.append(("the matching pair stays quiet", heil_b == []))
    proben.append(("and it counted something", bool(heil_z)))

    # a variant that `Reason` does not have
    b, _ = messe(RS_PROBE.replace("    Gamma,\n", "    Gamma,\n    Delta,\n")
                 .replace("LeanReason; 3", "LeanReason; 4")
                 .replace("        LeanReason::Gamma,\n",
                          "        LeanReason::Gamma,\n        LeanReason::Delta,\n")
                 .replace('LeanReason::Gamma => "gamma",',
                          'LeanReason::Gamma => "gamma",\n'
                          '            LeanReason::Delta => "delta",'), LEAN_PROBE)
    proben.append(("a variant `Reason` does not have FALLS",
                   any("has delta and `Reason` has not" in x for x in b)))

    # a tag that drifted
    b, _ = messe(RS_PROBE, LEAN_PROBE.replace('| .beta => "beta"', '| .beta => "bета"'))
    proben.append(("a drifted tag FALLS", any(x.startswith("tag of Beta") for x in b)))

    # a kind that drifted
    b, _ = messe(RS_PROBE, LEAN_PROBE.replace("| .alpha => .assumption",
                                              "| .alpha => .noWiring"))
    proben.append(("a drifted kind FALLS", any(x.startswith("kind of Alpha") for x in b)))

    # a carried form with no discharge lemma
    b, _ = messe(RS_PROBE, LEAN_PROBE.replace("  | .zwei => .carriedByTactic",
                                              "  | .zwei => .carried"))
    proben.append(("a carried form without a lemma FALLS",
                   any("`Form.zwei` is carried and has no arm" in x for x in b)))

    # a form with no arm in `classify`
    b, _ = messe(RS_PROBE, LEAN_PROBE.replace("  | .zwei => .carriedByTactic\n", ""))
    proben.append(("a form with no verdict FALLS",
                   any("`Form.zwei` has no arm in `classify`" in x for x in b)))

    # a catch-all in `classify` -- the silent way a new form gets a verdict
    b, _ = messe(RS_PROBE, LEAN_PROBE.replace("  | .zwei => .carriedByTactic",
                                              "  | _ => .carriedByTactic"))
    proben.append(("a `| _ =>` in `classify` FALLS",
                   any("carries a `| _ =>` arm" in x for x in b)))

    # the order parting
    b, _ = messe(RS_PROBE, LEAN_PROBE.replace("| alpha | beta | gamma",
                                              "| beta | alpha | gamma"))
    proben.append(("a parted order FALLS", any("the order parts" in x for x in b)))

    # an unreadable subject is an ABORT and not a green
    b, z = messe("nothing here", LEAN_PROBE)
    proben.append(("an unreadable `lean.rs` is an ABORT", b is None and z is None))
    return proben


def main():
    nur_probe = "--probe" in sys.argv
    proben = sprechprobe()
    gefallen = [name for name, ok in proben if not ok]
    print("== speech test ==")
    for name, ok in proben:
        print(f"   {'ok  ' if ok else 'FAIL'} {name}")
    if gefallen:
        print(f"ABBRUCH: SPRECHPROBE GESCHEITERT ({len(gefallen)} of {len(proben)}) -- "
              "NOTHING measured.")
        return 2
    if nur_probe:
        print(f"== speech test green: {len(proben)} of {len(proben)} ==")
        return 0

    if not LEAN_RS.exists() or not COVERAGE.exists():
        fehlt = [str(p) for p in (LEAN_RS, COVERAGE) if not p.exists()]
        print(f"ABBRUCH: {', '.join(fehlt)} is missing -- NOTHING measured.")
        return 2
    befunde, gezaehlt = messe(LEAN_RS.read_text(encoding="utf-8"),
                              COVERAGE.read_text(encoding="utf-8"))
    if befunde is None:
        print("ABBRUCH: `lean.rs` or `Coverage.lean` did not yield the registers "
              "this guard reads -- NOTHING measured.")
        return 2
    print("== coverage: `Coverage.lean` against `lean.rs` ==")
    print("   " + ", ".join(gezaehlt))
    if befunde:
        print(f"! {len(befunde)} FINDING(S):")
        for b in befunde:
            print(f"   - {b}")
        print("   The two registers stand apart -- the theorem then speaks about a "
              "language that is not the one the checker checks.")
        return 1
    print("   UNCOVERED = 0 -- the two registers cover each other.")
    print("   NOT checked: that `Form` is the whole grammar. The emitter's CARRIED "
          "decisions stand in no list; see the header.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
