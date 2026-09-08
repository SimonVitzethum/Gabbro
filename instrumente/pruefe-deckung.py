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
7. **The carried population.** Every variant of `LeanCarried` -- the register of the
   emitter's CARRYING sites, added 2026-09-08 -- stands in `LeanCarried::ALL`, and every
   entry of `ALL` in the enum. Tags are present and unique.
8. **The carried correspondence, forward.** Every `Form` constructor a carrying site names
   in `LeanCarried::forms` exists in `Coverage.lean` and `classify` calls it `.carried`.
9. **The carried correspondence, backward.** Every form `classify` calls `.carried` is
   named -- by a carrying site, or by `CARRIED_BY_WIRING` with the emitter function that
   decides it and why there is no term. *No form may stand in both lists, and no wiring
   entry may name a form the classifier does not call carried.*

**Until 2026-09-08 checks 7 to 9 did not exist, and this header said why:** the refusal half
was mechanical because `lean.rs` named its refusals in one enum, and the CARRIED half had no
such enum -- the emitter carried a form by writing a term, at some fifty places, with no list
to compare against. *A form the grammar admits, the emitter carries, and `Form` never named
would pass every check.* It did: `LeanCarried` was written, and the correspondence named
**eight forms** the emitter had carried all along and `Form` had never mentioned -- the
reason `match`, `return f(a)`, `let ... else` at a call, `breaking`, `publishes`, `awaits`,
`locks`, and the `descendants`/`ancestors` domain. Six of the eight are the CARRIED half of
a form whose REFUSED half was in the register from the start.

**And a new carrying site cannot bypass the register**, which is a fact about the type and
not about discipline: `place_term`, `expr_term`, `pred_term`, `domain_of`, `stmt_term` and
`block_term` return a `Carried`, whose only constructor is `LeanCarried::term`. An `Ok(s)`
with a bare `String` does not compile. The same correspondence runs on the Rust side as
`cargo test -p gabbro-check --lib lean::deckung_tests`, so it is not only this script.

WHAT THIS GUARD DOES **NOT** CHECK -- and this half is the honest one
--------------------------------------------------------------------
* **That `parse.rs` admits exactly the forms `Form` names.** *This is the register that is
  still read by nobody.* The grammar side is checked by `pruefe-grammatiktafel.py` against
  the EBNF; the emitter's carried decisions are now checked against `Form` by checks 7 to 9;
  but that the PARSER admits exactly the forms these two lists talk about is a third
  register, and it has no guard. A form `parse.rs` accepts, `lean.rs` never sees a term for
  and `Form` never names would pass everything here.
* **That the MAPPING is the right one.** A carrying site names the `Form` whose lemma
  discharges it, and that judgement is a reader's. A site that named `store` where it should
  name `read` would pass: both are carried forms. What is mechanical is that the name exists
  and that nothing is left unnamed.
* **That the Lean file PROVES anything.** `lake build` does that; this guard reads text.
* **That the verdict is the RIGHT one.** It checks that a carried form has a lemma, not
  that the lemma says what the form needs. Only a reader can check that.

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


def rust_getragene(text):
    """The variants of `enum LeanCarried`, in declaration order."""
    m = re.search(r"pub enum LeanCarried \{(.*?)\n\}", text, re.S)
    if not m:
        return None
    return re.findall(r"^\s{4}([A-Z][A-Za-z0-9]*),\s*$", m.group(1), re.M)


def rust_getragene_alle(text):
    """`LeanCarried::ALL`, with the length the declaration claims."""
    m = re.search(r"pub const ALL: \[LeanCarried; (\d+)\] = \[(.*?)\n    \];", text, re.S)
    if not m:
        return None, None
    return int(m.group(1)), re.findall(r"LeanCarried::([A-Za-z0-9]+),", m.group(2))


def rust_getragene_marken(text):
    """`LeanCarried::tag()` -- decision to string."""
    m = re.search(r"pub fn tag\(self\) -> &'static str \{\s*match self \{"
                  r"(\s*LeanCarried::.*?)\n        \}", text, re.S)
    if not m:
        return None
    return dict(re.findall(r"LeanCarried::([A-Za-z0-9]+) => \"([^\"]*)\"", m.group(1)))


def rust_getragene_formen(text):
    """`LeanCarried::forms()` -- decision to the `Form` constructors it names.

    A `Subterm` arm names none, and that is not the same as naming nothing by accident:
    the arm says so in the source.
    """
    m = re.search(r"pub fn forms\(self\) -> CarriedForm \{\s*match self \{(.*?)\n        \}",
                  text, re.S)
    if not m:
        return None
    koerper = m.group(1)
    # An arm may run over several lines; join them by the `LeanCarried::` that starts one.
    arme = re.split(r"\n(?=\s*LeanCarried::)", koerper)
    aus = {}
    for arm in arme:
        k = re.match(r"\s*LeanCarried::([A-Za-z0-9]+)", arm)
        if not k:
            continue
        if "CarriedForm::Subterm" in arm:
            aus[k.group(1)] = []
        else:
            f = re.search(r"CarriedForm::Forms\(&\[(.*?)\]\)", arm, re.S)
            aus[k.group(1)] = re.findall(r"\"([A-Za-z0-9]+)\"", f.group(1)) if f else None
    return aus


def rust_verdrahtet(text):
    """`CARRIED_BY_WIRING` -- the carried forms that no term-writing site names."""
    m = re.search(r"pub const CARRIED_BY_WIRING: \[\(&str, &str, &str\); (\d+)\] = \[(.*?)\n\];",
                  text, re.S)
    if not m:
        return None, None
    return int(m.group(1)), re.findall(r"\(\s*\"([A-Za-z0-9]+)\",", m.group(2))


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

    # 7. the carried population -- the register of the emitter's CARRYING sites
    getragene = rust_getragene(lean_rs_text)
    g_anzahl, g_alle = rust_getragene_alle(lean_rs_text)
    g_marken = rust_getragene_marken(lean_rs_text)
    g_formen = rust_getragene_formen(lean_rs_text)
    v_anzahl, verdrahtet = rust_verdrahtet(lean_rs_text)
    if not all([getragene, g_alle, g_marken, g_formen, verdrahtet]):
        return None, None
    if g_anzahl != len(g_alle):
        befunde.append(f"`LeanCarried::ALL` says {g_anzahl} and holds {len(g_alle)}")
    if v_anzahl != len(verdrahtet):
        befunde.append(f"`CARRIED_BY_WIRING` says {v_anzahl} and holds {len(verdrahtet)}")
    for c in sorted(set(getragene) - set(g_alle)):
        befunde.append(f"`LeanCarried::{c}` stands in the enum and not in `ALL`")
    for c in sorted(set(g_alle) - set(getragene)):
        befunde.append(f"`LeanCarried::{c}` stands in `ALL` and not in the enum")
    for c in getragene:
        if c not in g_marken:
            befunde.append(f"`LeanCarried::{c}` has no tag")
        if g_formen.get(c) is None and c in g_formen:
            befunde.append(f"`LeanCarried::{c}` names neither forms nor `Subterm`")
        if c not in g_formen:
            befunde.append(f"`LeanCarried::{c}` has no arm in `forms`")
    doppelte = [m for m in set(g_marken.values()) if list(g_marken.values()).count(m) > 1]
    for m in sorted(doppelte):
        befunde.append(f"two carrying sites share the tag \"{m}\"")

    # 8. the carried correspondence, forward
    getragene_formen = {f for f in formen if urteile.get(f) == ".carried"}
    benannt = set()
    for c in getragene:
        for f in (g_formen.get(c) or []):
            benannt.add(f)
            if f not in formen:
                befunde.append(f"carrying site {g_marken.get(c, c)} names `{f}`, "
                               "which is no constructor of `Form`")
            elif f not in getragene_formen:
                befunde.append(f"carrying site {g_marken.get(c, c)} names `{f}`, "
                               f"which `classify` calls {urteile.get(f)} and not `.carried`")

    # 9. the carried correspondence, backward
    for f in sorted(getragene_formen - benannt - set(verdrahtet)):
        befunde.append(f"`Form.{f}` is carried and NO carrying site and no wiring entry "
                       "names it")
    for f in sorted(set(verdrahtet) & benannt):
        befunde.append(f"`{f}` stands in `CARRIED_BY_WIRING` and is named by a carrying "
                       "site as well -- two registers over one thing")
    for f in sorted(set(verdrahtet) - getragene_formen):
        befunde.append(f"`CARRIED_BY_WIRING` names `{f}`, which `classify` does not call "
                       "carried")

    unterterme = sum(1 for c in getragene if g_formen.get(c) == [])
    gezaehlt = [f"{len(alle)} refusal reasons", f"{len(formen)} forms",
                f"{len(getragene_formen)} carried",
                f"{len(entlastungen)} discharge lemmas",
                f"{len(getragene)} carrying sites ({unterterme} sub-term)",
                f"{len(verdrahtet)} carried by wiring"]
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
}

pub enum LeanCarried {
    Eins,
    Nichts,
}

impl LeanCarried {
    pub fn tag(self) -> &'static str {
        match self {
            LeanCarried::Eins => "eins",
            LeanCarried::Nichts => "nichts",
        }
    }

    pub fn forms(self) -> CarriedForm {
        match self {
            LeanCarried::Eins => CarriedForm::Forms(&["eins"]),
            LeanCarried::Nichts => CarriedForm::Subterm,
        }
    }

    pub const ALL: [LeanCarried; 2] = [
        LeanCarried::Eins,
        LeanCarried::Nichts,
    ];
}

pub const CARRIED_BY_WIRING: [(&str, &str, &str); 1] = [
    (
        "drei",
        "verdrahtung",
        "no term, an order",
    ),
];
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
  | drei
  | refusedOrAssumed (r : Reason)
  deriving DecidableEq, Repr

def classify : Form → Verdict
  | .eins => .carried
  | .drei => .carried
  | .zwei => .carriedByTactic
  | .refusedOrAssumed r => .refused r.tag

def Discharges : Form → Prop
  | .eins => EinsCarried
  | .drei => DreiCarried
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

    # a carrying site that names a form nobody carries
    b, _ = messe(RS_PROBE.replace('LeanCarried::Eins => CarriedForm::Forms(&["eins"])',
                                  'LeanCarried::Eins => CarriedForm::Forms(&["vier"])'),
                 LEAN_PROBE)
    proben.append(("a carrying site naming an unknown form FALLS",
                   any("names `vier`" in x for x in b)))

    # a carried form no carrying site and no wiring entry names -- the blind half, closed
    b, _ = messe(RS_PROBE, LEAN_PROBE.replace("  | .zwei => .carriedByTactic",
                                              "  | .zwei => .carried")
                                     .replace("  | .eins => EinsCarried",
                                              "  | .eins => EinsCarried\n  | .zwei => ZweiCarried"))
    proben.append(("a carried form nobody names FALLS",
                   any("`Form.zwei` is carried and NO carrying site" in x for x in b)))

    # a decision that stands in the enum and not in `ALL` -- `PLAN.md` 11.1's shape
    b, _ = messe(RS_PROBE.replace("    Nichts,\n}", "    Nichts,\n    Vier,\n}")
                 .replace('LeanCarried::Nichts => "nichts",',
                          'LeanCarried::Nichts => "nichts",\n'
                          '            LeanCarried::Vier => "vier",')
                 .replace("LeanCarried::Nichts => CarriedForm::Subterm,",
                          "LeanCarried::Nichts => CarriedForm::Subterm,\n"
                          "            LeanCarried::Vier => CarriedForm::Subterm,"),
                 LEAN_PROBE)
    proben.append(("a decision outside `ALL` FALLS",
                   any("stands in the enum and not in `ALL`" in x for x in b)))

    # a form in BOTH lists
    b, _ = messe(RS_PROBE.replace('"drei",\n        "verdrahtung",',
                                  '"eins",\n        "verdrahtung",'), LEAN_PROBE)
    proben.append(("a form in both lists FALLS",
                   any("two registers over one thing" in x for x in b)))

    # an unreadable subject is an ABORT and not a green
    b, z = messe("nothing here", LEAN_PROBE)
    proben.append(("an unreadable `lean.rs` is an ABORT", b is None and z is None))

    # and a `lean.rs` WITHOUT the carried register is an abort too, not a green half
    b, z = messe(RS_PROBE[:RS_PROBE.index("pub enum LeanCarried")], LEAN_PROBE)
    proben.append(("a `lean.rs` without the carried register is an ABORT",
                   b is None and z is None))
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
    print("   UNCOVERED = 0 -- the registers cover each other, refusals and carries.")
    print("   NOT checked: that `parse.rs` admits exactly the forms these lists name. "
          "That is the third register, and it has no guard; see the header.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
