#!/usr/bin/env python3
"""The recomputer: correspondence rerun from artifacts, per run, with a verdict.

Erhaltung C1 leaves this program open: `korrespondenz_sound` proves that a VALID
certificate IMPLIES correspondence, not that any run PRODUCES one. This file is
the second program -- it reads what a run left behind and recomputes the four
correspondence legs plus the alias, cost, and bound legs of `nachpruefer` (§10)
as data. No proofs here; the Lean shapes are mirrored as Boolean checks.

RUN ARTIFACTS -- three inputs, all required:
  --ledger PATH   the ledger sidecar (kostenledger shape): who carries the ops
                  count, both counts, the witness pairs, the alias load, the
                  run's site inventory, and the counted C statements:
                    {"carrier": "cerCo" | "produktion",
                     "opsGabbro": nat, "opsC": nat, "paare": nat,
                     "arithSites": [nat, ...], "gabbroSites": [nat, ...],
                     "cAnweisungen": nat}
  --cert PATH     the certificate rows (CorrCert shape):
                    {"sites": [{"gabbro": g, "c": c, "form": "<CForm>"}]}
  --c PATH        the emitted C. The recomputer can only see effects the image
                  NAMES, so each emitted evaluation site carries a marker:
                    /* gabbro-site <c-id> <form> */
                  The form token may be omitted; when present it must agree
                  with the certificate row for that C id.

CHECKS -- each a mirror of one Lean recomputation:
  [completeness]  every ledger site has a certificate row (mirrors `vollB`).
                  BEWEIS.md §4 says "exactly once"; the Lean shape checks
                  AT LEAST once, and this program follows the Lean shape.
  [order]         the C ids stand nondecreasing in certificate order, adjacent
                  check only (mirrors `geordnetCertB`; transitivity is the
                  Lean side's lift, not this program's).
  [closure]       every row form stands in the ruled list below (mirrors
                  `ruledB`). The list is WRITTEN OUT here, not imported: the
                  checkfat lesson (BEWEIS.md §4) says the recomputer carries
                  its OWN table. It names the same 19 `CForm` shapes as
                  `grammatik/Grammatik/Ziel.lean`.
  [no-extra]      every row's Gabbro site is in the ledger inventory (mirrors
                  `ohneExtraB`), every C marker has a certificate row, and
                  every certificate C id is marked in the image.
  [alias]         the image carries no address-arithmetic site (mirrors the
                  `aliasKept` leg of `nachpruefer`: `arithSites == []`).
  [cost]          under `cerCo` the C count IS the Gabbro count (mirrors
                  `costKept`); under `produktion` at least one green witness
                  pair ran (mirrors `costMeasured` -- zero pairs is not a
                  measurement).
  [bound]         the counted C statements stay at or under 17 (mirrors the
                  `senkungBegrenzt` leg of `nachpruefer`, which hardcodes the
                  measured maximum from `messung/ABSENKUNG-MESSUNG.md`).

VERDICT -- green/red PER RUN, with the work beside it (W17):
  exit 0  GREEN -- all legs recomputed over N sites, M rows, K markers.
  exit 1  RED -- every finding printed, each tagged with its leg.
  exit 2  ABORT -- an input is missing or unreadable, or this program's own
          speech test failed. Nothing was measured.

    ./instrumente/nachpruefer.py --ledger L --cert C --c E
    ./instrumente/nachpruefer.py --probe    # only the speech test
"""
import json
import locale
import os
import pathlib
import re
import signal
import sys
import tempfile

# Pinned locale: this tool parses JSON and its own markers, both locale-free,
# but whoever reads tool output and pins nothing measures their own language
# (2026-08-25: `Mehrfachdefinition von` vs `multiple definition`). Pin it here
# so the verdict lines read the same everywhere.
os.environ["LC_ALL"] = "C"
try:
    locale.setlocale(locale.LC_ALL, "C")
except locale.Error:
    pass

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402  -- the shared cut notice

WURZEL = pathlib.Path(__file__).resolve().parent.parent

# Every execution under a deadline. A hanger looks like "still running", not
# like a finding -- on 2026-08-20 twenty-one runs of `pruefe-emission.sh`
# stood side by side, the oldest for three and a half hours.
FRIST = 300

# The ruled list, written out, not imported: the recomputer carries its OWN
# table (BEWEIS.md §4, the checkfat lesson). The 19 `CForm` shapes named in
# `grammatik/Grammatik/Ziel.lean`; a certificate form outside this list is a
# [closure] finding, not a parse error.
REGELFORMEN = frozenset({
    "statisch", "extern", "zuweisung", "wenn", "schalter", "zaehlSchleife",
    "rueckgabe", "sprungAlsSchleifenende", "ruf", "literal", "name", "feld",
    "index", "wahlLesen", "atomar", "beschraenkt", "fluechtig", "noreturn",
    "asmEins",
})

# The measured maximum C statements per Gabbro primitive
# (`messung/ABSENKUNG-MESSUNG.md`); the Lean `nachpruefer` hardcodes the same
# number. Anything above it is a [bound] finding.
SCHRANKE = 17

# One emitted evaluation site, named by the image itself.
MARKIERUNG = re.compile(r"gabbro-site\s+(\d+)(?:\s+([A-Za-z]+))?")

TRAEGER = ("cerCo", "produktion")


def _ist_nat(x):
    return isinstance(x, bool) is False and isinstance(x, int) and x >= 0


def lade_ledger(pfad):
    """Read and validate the sidecar. Returns (ledger, error); error is None
    on success. A malformed sidecar is an ABORT, not a finding: the tool could
    not measure."""
    try:
        roh = pathlib.Path(pfad).read_text(encoding="utf-8")
    except OSError as e:
        return None, f"ledger unreadable: {pfad}: {e.strerror or e}"
    try:
        daten = json.loads(roh)
    except json.JSONDecodeError as e:
        return None, f"ledger is no JSON: {pfad}: {e}"
    if not isinstance(daten, dict):
        return None, f"ledger is no object: {pfad}"
    for feld in ("opsGabbro", "opsC", "paare", "cAnweisungen"):
        if not _ist_nat(daten.get(feld)):
            return None, f"ledger field '{feld}' is no nat: {daten.get(feld)!r}"
    for feld in ("arithSites", "gabbroSites"):
        wert = daten.get(feld)
        if not isinstance(wert, list) or not all(_ist_nat(v) for v in wert):
            return None, f"ledger field '{feld}' is no nat list: {wert!r}"
    if daten.get("carrier") not in TRAEGER:
        return None, f"ledger carrier is neither cerCo nor produktion: {daten.get('carrier')!r}"
    return daten, None


def lade_cert(pfad):
    """Read and validate the certificate rows. Same contract as lade_ledger."""
    try:
        roh = pathlib.Path(pfad).read_text(encoding="utf-8")
    except OSError as e:
        return None, f"certificate unreadable: {pfad}: {e.strerror or e}"
    try:
        daten = json.loads(roh)
    except json.JSONDecodeError as e:
        return None, f"certificate is no JSON: {pfad}: {e}"
    if not isinstance(daten, dict) or not isinstance(daten.get("sites"), list):
        return None, f"certificate carries no 'sites' list: {pfad}"
    for i, zeile in enumerate(daten["sites"]):
        if not isinstance(zeile, dict):
            return None, f"certificate row {i} is no object: {zeile!r}"
        if not _ist_nat(zeile.get("gabbro")) or not _ist_nat(zeile.get("c")):
            return None, (f"certificate row {i} carries no nat ids: "
                           f"{zeile!r}")
        if not isinstance(zeile.get("form"), str) or not zeile["form"]:
            return None, f"certificate row {i} carries no form: {zeile!r}"
    return daten["sites"], None


def lese_markierungen(pfad):
    """Map every C id the image names to its marker count and form tokens.
    Same abort contract as the loaders."""
    try:
        text = pathlib.Path(pfad).read_text(encoding="utf-8")
    except OSError as e:
        return None, f"emitted C unreadable: {pfad}: {e.strerror or e}"
    markiert = {}
    for treffer in MARKIERUNG.finditer(text):
        cid = int(treffer.group(1))
        form = treffer.group(2)
        eintrag = markiert.setdefault(cid, {"n": 0, "formen": set()})
        eintrag["n"] += 1
        if form:
            eintrag["formen"].add(form)
    return markiert, None


def pruefe(ledger, zeilen, markiert):
    """Recompute every leg. Returns the finding list; empty means green.
    Each finding carries its leg in brackets, so a probe that fails for the
    wrong reason cannot pass as a probe that failed for the right one."""
    befunde = []
    inventar = set(ledger["gabbroSites"])

    # [completeness] -- mirrors `vollB`: every ledger site owns a row.
    abgedeckt = {z["gabbro"] for z in zeilen}
    for g in sorted(inventar):
        if g not in abgedeckt:
            befunde.append(f"[completeness] Gabbro site {g} owns no row")

    # [order] -- mirrors `geordnetCertB`: adjacent C ids nondecreasing.
    for vorher, nachher in zip(zeilen, zeilen[1:]):
        if nachher["c"] < vorher["c"]:
            befunde.append(
                f"[order] C sites run backwards: {vorher['c']} before "
                f"{nachher['c']}")
            break

    # [closure] -- mirrors `geschlossenB`: every row form is ruled.
    for z in zeilen:
        if z["form"] not in REGELFORMEN:
            befunde.append(
                f"[closure] form {z['form']!r} (Gabbro site {z['gabbro']}) "
                f"stands in no ruled row")

    # [no-extra] -- mirrors `ohneExtraB`, plus both image directions.
    for z in zeilen:
        if z["gabbro"] not in inventar:
            befunde.append(
                f"[no-extra] row claims Gabbro site {z['gabbro']}, "
                f"outside the run inventory")
    cert_c = {z["c"] for z in zeilen}
    for cid in sorted(markiert):
        if cid not in cert_c:
            befunde.append(
                f"[no-extra] C site {cid} marked in the image, "
                f"no certificate row names it")
    for cid in sorted(cert_c):
        if cid not in markiert:
            befunde.append(
                f"[no-extra] certificate C site {cid} unmarked "
                f"in the image")
    # A marker form token that disagrees with its row mislabels the effect.
    form_je_c = {}
    for z in zeilen:
        form_je_c.setdefault(z["c"], set()).add(z["form"])
    for cid, eintrag in sorted(markiert.items()):
        for form in sorted(eintrag["formen"]):
            if cid in form_je_c and form not in form_je_c[cid]:
                befunde.append(
                    f"[no-extra] C site {cid} marked {form!r}, "
                    f"certificate says {sorted(form_je_c[cid])}")

    # [alias] -- mirrors the `aliasKept` leg: the list must be empty.
    if ledger["arithSites"]:
        befunde.append(
            f"[alias] image carries {len(ledger['arithSites'])} "
            f"address-arithmetic sites: {sorted(ledger['arithSites'])[:8]}"
            f"{' ...' if len(ledger['arithSites']) > 8 else ''}")

    # [cost] -- mirrors `costKept` and `costMeasured`.
    if ledger["carrier"] == "cerCo" and ledger["opsC"] != ledger["opsGabbro"]:
        befunde.append(
            f"[cost] carrier cerCo, but opsC {ledger['opsC']} != opsGabbro "
            f"{ledger['opsGabbro']}")
    if ledger["carrier"] == "produktion" and not ledger["paare"] > 0:
        befunde.append("[cost] carrier produktion, but zero witness pairs ran")

    # [bound] -- mirrors the `senkungBegrenzt` leg at the measured maximum.
    if ledger["cAnweisungen"] > SCHRANKE:
        befunde.append(
            f"[bound] {ledger['cAnweisungen']} C statements over the "
            f"measured maximum {SCHRANKE}")

    return befunde


def beurteile(ledger_pfad, cert_pfad, c_pfad):
    """Load all three artifacts and recompute. Returns (rc, befunde, arbeit)
    with rc 0 green, 1 red findings, 2 abort; arbeit is the work quantity for
    the verdict line (W17)."""
    ledger, fehler = lade_ledger(ledger_pfad)
    if fehler:
        return 2, [fehler], {}
    zeilen, fehler = lade_cert(cert_pfad)
    if fehler:
        return 2, [fehler], {}
    markiert, fehler = lese_markierungen(c_pfad)
    if fehler:
        return 2, [fehler], {}
    befunde = pruefe(ledger, zeilen, markiert)
    arbeit = {"sites": len(ledger["gabbroSites"]), "rows": len(zeilen),
              "markers": len(markiert), "pairs": ledger["paare"]}
    return (1 if befunde else 0), befunde, arbeit


def _lege_artefakte(verzeichnis, ledger, zeilen, c_text):
    """Write one run's three artifacts into scratch. Fixtures live in /tmp
    and never in the repo: a probe that writes beside its subject measures
    the mixture, not the subject."""
    verzeichnis = pathlib.Path(verzeichnis)
    ledger_pfad = verzeichnis / "ledger.json"
    cert_pfad = verzeichnis / "cert.json"
    c_pfad = verzeichnis / "emit.c"
    ledger_pfad.write_text(json.dumps(ledger), encoding="utf-8")
    cert_pfad.write_text(json.dumps({"sites": zeilen}), encoding="utf-8")
    c_pfad.write_text(c_text, encoding="utf-8")
    return str(ledger_pfad), str(cert_pfad), str(c_pfad)


def _gute_ledger(**mehr):
    ledger = {"carrier": "cerCo", "opsGabbro": 4, "opsC": 4, "paare": 0,
              "arithSites": [], "gabbroSites": [0, 1], "cAnweisungen": 4}
    ledger.update(mehr)
    return ledger


_GUTE_ZEILEN = [{"gabbro": 0, "c": 0, "form": "literal"},
                {"gabbro": 1, "c": 1, "form": "name"}]
_GUTES_C = ("int v = 1; /* gabbro-site 0 literal */\n"
            "int w = v; /* gabbro-site 1 name */\n")


def sprechprobe():
    """Both directions: the accept case must go green, every forged artifact
    must fall -- each on its own leg. Returns True only if all hold."""
    print("== Sprechprobe des Nachpruefers ==")
    ok = True
    with tempfile.TemporaryDirectory(prefix="nachpruefer-") as kratz:
        # Outside /tmp the fixtures would land beside the subject.
        assert kratz.startswith("/tmp"), kratz

        def fall(name, erwartet, ledger, zeilen, c_text):
            nonlocal ok
            ziel = pathlib.Path(kratz) / re.sub(r"\W+", "_", name)
            ziel.mkdir(parents=True, exist_ok=True)
            pfade = _lege_artefakte(ziel, ledger, zeilen, c_text)
            rc, befunde, _ = beurteile(*pfade)
            getroffen = any(f.startswith(erwartet) for f in befunde)
            gut = rc == 1 and getroffen
            ok = ok and gut
            print(f"  {name}: {'faellt' if gut else 'UEBERSEHEN'} "
                  f"({erwartet}, rc {rc})")
            for b in befunde:
                print(f"     {b}")
            return gut

        # The accept case: two sites, in order, over ruled forms, nothing more.
        sauber = pathlib.Path(kratz) / "sauber"
        sauber.mkdir(parents=True, exist_ok=True)
        pfade = _lege_artefakte(sauber, _gute_ledger(), list(_GUTE_ZEILEN),
                                _GUTES_C)
        rc, befunde, arbeit = beurteile(*pfade)
        sauber_ok = rc == 0 and not befunde
        ok = ok and sauber_ok
        print(f"  accept case goes green: "
              f"{'ja' if sauber_ok else 'FALSCHES ROT'} (rc {rc})")
        for b in befunde:
            print(f"     {b}")

        # Every forgery below must fall, each on its own leg.
        fall("dropped row (completeness)", "[completeness]",
             _gute_ledger(), [_GUTE_ZEILEN[0]], _GUTES_C)
        fall("backwards C ids (order)", "[order]",
             _gute_ledger(),
             [{"gabbro": 0, "c": 1, "form": "literal"},
              {"gabbro": 1, "c": 0, "form": "name"}],
             _GUTES_C)
        fall("unruled form (closure)", "[closure]",
             _gute_ledger(),
             [_GUTE_ZEILEN[0], {"gabbro": 1, "c": 1, "form": "Zauberei"}],
             _GUTES_C.replace("name */", "Zauberei */"))
        fall("foreign Gabbro site (no-extra)", "[no-extra]",
             _gute_ledger(),
             list(_GUTE_ZEILEN) + [{"gabbro": 99, "c": 2, "form": "ruf"}],
             _GUTES_C + "f(); /* gabbro-site 2 ruf */\n")
        fall("unmarked C effect (no-extra)", "[no-extra]",
             _gute_ledger(), list(_GUTE_ZEILEN),
             _GUTES_C + "f(); /* gabbro-site 2 ruf */\n")
        fall("row without image (no-extra)", "[no-extra]",
             _gute_ledger(), list(_GUTE_ZEILEN),
             "int v = 1; /* gabbro-site 0 literal */\n")
        fall("diverging counts under cerCo (cost)", "[cost]",
             _gute_ledger(opsC=9), list(_GUTE_ZEILEN), _GUTES_C)
        fall("zero pairs under produktion (cost)", "[cost]",
             _gute_ledger(carrier="produktion", paare=0),
             list(_GUTE_ZEILEN), _GUTES_C)
        fall("address arithmetic in image (alias)", "[alias]",
             _gute_ledger(arithSites=[7]), list(_GUTE_ZEILEN), _GUTES_C)
        fall("over the statement bound (bound)", "[bound]",
             _gute_ledger(cAnweisungen=18), list(_GUTE_ZEILEN), _GUTES_C)

        # The abort direction: a missing input measures nothing (rc 2).
        rc, befunde, _ = beurteile(str(pathlib.Path(kratz) / "fehlt.json"),
                                   str(pathlib.Path(kratz) / "cert.json"),
                                   str(pathlib.Path(kratz) / "emit.c"))
        abort_ok = rc == 2
        ok = ok and abort_ok
        print(f"  missing ledger aborts: "
              f"{'ja' if abort_ok else 'KEIN ABBRUCH'} (rc {rc})")

    print(f"== Sprechprobe: {'haelt' if ok else 'GESCHEITERT'} ==")
    return ok


def _mit_frist(arbeit):
    """Run `arbeit` under FRIST. A deadline that is not wired up is a
    comment, not a deadline."""
    if not hasattr(signal, "SIGALRM"):
        return arbeit()

    def _abgelaufen(_zeichen, _rahmen):
        raise TimeoutError(f"deadline {FRIST} s exceeded")

    vorher = signal.signal(signal.SIGALRM, _abgelaufen)
    signal.alarm(FRIST)
    try:
        return arbeit()
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, vorher)


def main():
    args = sys.argv[1:]
    if "--probe" in args or "--sprechprobe" in args:
        return 0 if sprechprobe() else 2

    def _nimm(name):
        return args[args.index(name) + 1] if name in args and \
            args.index(name) + 1 < len(args) else None

    ledger_pfad = _nimm("--ledger")
    cert_pfad = _nimm("--cert")
    c_pfad = _nimm("--c")
    fehlend = [n for n, p in (("--ledger", ledger_pfad),
                              ("--cert", cert_pfad),
                              ("--c", c_pfad)) if not p]
    if fehlend:
        print(f"ABBRUCH: missing inputs: {', '.join(fehlend)} -- "
              f"nothing was measured.", file=sys.stderr)
        print("  Usage: nachpruefer.py --ledger L --cert C --c E",
              file=sys.stderr)
        return 2

    # The speech test runs every time: a recomputer that cannot go red
    # measures nothing (R14). It fails with 2, not 1: what it says about the
    # run afterwards is then no statement about the run.
    print("== Sprechprobe des Nachpruefers ==")
    if not sprechprobe():
        print("\n! The recomputer does not measure what it claims. ABBRUCH.")
        return 2

    try:
        rc, befunde, arbeit = _mit_frist(
            lambda: beurteile(ledger_pfad, cert_pfad, c_pfad))
    except TimeoutError as e:
        print(f"ABBRUCH: {e} -- nothing was measured.", file=sys.stderr)
        return 2

    print("\n== Nachpruefung ==")
    if rc == 2:
        for b in befunde:
            print(f"  ABBRUCH: {b}")
        print("  Nothing was measured.", file=sys.stderr)
        return 2
    menge = (f"{arbeit['sites']} sites, {arbeit['rows']} rows, "
             f"{arbeit['markers']} C markers, {arbeit['pairs']} pairs")
    if not befunde:
        # The vacuous run corresponds (Erhaltung `korrespondenz_leer`) -- and
        # a green over nothing must SAY it is over nothing (W17).
        leer = " (VACUOUS -- no site, no row, no marker)" \
            if arbeit["sites"] == 0 and arbeit["rows"] == 0 \
            and arbeit["markers"] == 0 else ""
        print(f"  {menge} recomputed, no finding.{leer}")
        print(f"== NACHPRUEFER: GREEN -- {menge}{leer} ==")
        abschnitt.fertig()
        return 0
    for b in befunde:
        print(f"  !! {b}")
    print(f"== NACHPRUEFER: RED -- {len(befunde)} findings over {menge} ==")
    abschnitt.fertig()
    return 1


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
