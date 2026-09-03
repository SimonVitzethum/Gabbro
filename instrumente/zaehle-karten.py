#!/usr/bin/env python3
"""**Zwei Blicke auf dieselbe Karte, und nur einer war modulbewusst -- wie viele gibt es noch?**

Am 2026-08-17 fiel eine Giftprobe nicht, die fallen musste. Die Ursache: `typ_von_ort` schlug
den globalen Traeger ueber `suche` nach (modulbewusst, mit Kandidatenliste), `index_pruefen`
aber mit einem blanken `globale.get(...)`. **In jedem `module`-Block traf der zweite nie**, und
`M103` schwieg fuer jede Tabelle, die ueber ihren globalen Namen adressiert wird.

Behoben und mit Gift 76 belegt. **Was blieb, war die allgemeine Frage** -- und sie stand
seither als Satz im TODO, mit einer Zahl daneben, die niemand nachrechnen konnte:

> *„Gezaehlt: 13 direkte `.get(`-Blicke auf die Karten in `umgebung.rs`."*

**Die Zahl war 13 und ist heute 35** (2026-08-20). Nicht, weil jemand zweiundzwanzig neue
geschrieben haette, sondern weil `.contains_key(` denselben Blick tut und nie mitgezaehlt
wurde -- *eine Zaehlung, die eine der beiden Formen nicht kennt, misst ihre eigene Leseweite*
(W16).

    ./instrumente/zaehle-karten.py [--stellen]

DAS MASS
--------
`Umgebung` fuehrt Karten von einem QUALIFIZIERTEN Namen auf etwas. Der modulbewusste Weg
dorthin ist `suche(...)`: er baut aus `von` und `pfad` eine Kandidatenliste (eigenes Modul,
jedes umgebende, jede `use`-Zeile) und probiert sie der Reihe nach. **Jeder Blick, der die
Karte direkt befragt, hat diese Liste nicht** -- er trifft nur, wenn der Name schon
vollqualifiziert dasteht.

**Und was das NICHT heisst:** ein direkter Blick ist kein Fehler. Wo der Schluessel aus einer
Deklaration stammt, die selbst schon qualifiziert ist, trifft er richtig. *Diese Zaehlung
findet KANDIDATEN, sie spricht keinen frei und klagt keinen an* (W10) -- wie
`zaehle-narrow.py` und aus demselben Grund: was sie nicht entscheiden kann, kippt sie in die
Spalte, die Arbeit macht.
"""
import pathlib
import re
import sys

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.py`.
# `sys.path` gets the tool's own directory because this file is also LOADED by
# `abnahme.py` (via `importlib`), and then `sys.path[0]` is the working directory.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

W = pathlib.Path(__file__).resolve().parent.parent
SRC = W / "crates" / "gabbro-check" / "src"

# **Die gebuchte Marke.** Eine Ratsche, keine Zielzahl: sie darf fallen, nicht steigen. Ein
# neuer direkter Blick ist eine neue Stelle, an der `M103` in einem `module` schweigen kann.
#
# **35/31 -> 36/32 am 2026-08-20**, und die Ratsche hat den Schritt gemeldet, bevor jemand
# hinsah. Die neue Stelle ist `emit.rs:239` (`verbundwert`): sie liest den erklaerten
# Rueckgabetyp des Gerufenen, damit ein `let` OHNE Annotation als Verbund erkannt wird.
# *Sie erbt das Verhalten der Datei* -- `wert_ctyp` schlaegt zwoelf Zeilen weiter unten
# dieselbe Karte genauso nach, und `emit::Namen` ist ueberhaupt nach dem KURZEN Namen
# geschluesselt. **Der Erzeuger ist damit an dieser Karte durchgehend nicht modulbewusst**,
# und das ist ein Posten dieses Zaehlers, kein Nebenbefund dieser einen Zeile.
#
# **36/32 -> 40/36 on 2026-08-31, and nobody saw the step.** That is the finding,
# not the four sites: this counter stood OUTSIDE `abnahme.py`, so its red exit reached
# `master` and no collective run read it. *A guardian nobody drives is indistinguishable from
# one that does not exist* -- the sentence `abnahme.py` was built on, here against the
# boundary `abnahme.py` itself drew. The mark is pulled to the MEASURED state, because a mark
# below the state is a permanently red guardian and tells nobody anything new.
#
# The four are in `emit.rs` and `m1.rs` and they belong to whoever owns `crates/`; they are
# DEBT, not an achievement. `./instrumente/zaehle-karten.py --stellen` names every one.
#
# **40/36 -> 45/40 on 2026-09-03, and six sites carried the step.** `abnahme.py` had not read
# this counter in days; the six were each run down to a PROGRAM, not left as a count -- *"a
# count says a hole is possible; a program says it is there"* was the standing order.
#
# * **`domaene.rs::abbildungsfelder_pruefen` (`Umgebung::formate`) was the real `M103` shape,
#   and it FELL.** `walkknoten` stored the node-`format` name pre-qualified against the
#   `walk`'s OWN module; one enclosing module apart, `formate.get(&knoten)` missed and
#   `D020`'s own poison (`!m.gibtsnicht`) passed with `0 errors, 0 hints` -- the exact
#   sentence `walkknoten`'s doc already quotes about the pre-`D020` tree, reproduced by
#   nesting instead of by absence. Fixed: the map now carries the RAW name, read through the
#   new `Umgebung::suche_formate`, module-aware like `suche_global`. Poison:
#   `beispiele/gift/668-mapping-field-one-module-away.gab`. It no longer stands in this
#   count at all.
#
# * **Five sites in `emit::Namen::geraete` (the 2026-09-02 `at port` feature) are a
#   DIFFERENT shape, confirmed live, and NOT the `suche` one.** `Namen` carries no module
#   path anywhere, and `suche` needs one to build its candidate list -- there is nothing
#   here to hand it. Measured: two `device Foo`, one in each of two `module`s, different
#   register offsets, checked at `0 errors, 0 hints`, and the emitted
#   `Foo_R_in`/`Foo_R_out` for BOTH devices carried the SECOND device's offset -- the first
#   device's own accessor silently read and wrote the wrong port. Repaired at the one
#   COLLECTION site instead of at each read: a second `device` sharing a name now gets a
#   named `C001` refusal (`emit.rs`, next to `weigere`) rather than silently overwriting
#   the first. That refusal line is itself a direct, unqualified look at the same map --
#   the guard cannot tell a fix from a hole by text alone -- so it is the SIXTH site the
#   mark carries, not a seventh. Poison: `beispiele/gift/669-two-devices-share-a-name.gab`.
#   The five reads stay in the count, now safe *because* the sixth exists upstream of all
#   of them.
#
# * **`emit.rs::traegertyp` (`Namen::typen`) is the SAME shape as `geraete` -- confirmed
#   structurally, not independently reproduced with its own emitted-C example -- and is
#   OPEN DEBT, not fixed this round.** `namen.typen.insert(t.name.text.clone(), …)` is as
#   bare-keyed as `namen.geraete.insert(d.name.text.clone(), …)`; the same collision would
#   silently swap which module's `type` a cast or return narrows against. It merely
#   CONSOLIDATED three direct pre-mark reads (`vorzeichen`, `ctyp`'s own inline `.get`, a
#   `.contains_key` branch) into this one shared reader -- net two FEWER call sites against
#   an equally open map, not a new blind spot. Left for whoever next touches `Namen`.
#
# * `m1.rs:3823` (`Umgebung::funktionen`, inside a candidate `.any(|k| …)` loop) is
#   `BEWUSST` already and needed nothing.
#
# **The mark is pulled to this measured state**, same reasoning as 2026-08-31: a mark below
# it is a permanently red guardian. The five `geraete` reads and the `typen` reader are DEBT
# named here, not an achievement -- and lowering `Namen` to a module-aware structure, the
# way `Umgebung` already is, is the rewrite that would actually close them.
MARKE_DIREKT = 45
MARKE_UNQUALIFIZIERT = 40

# **Modulbewusst von Hand**: der Blick steht in einer Kandidatenschleife. Das ist der eine
# Fall, in dem ein direkter `.get(` richtig ist, ohne durch `suche` zu gehen.
BEWUSST = re.compile(r"kandidaten|find_map\(\|k\|")


def blicke(text, karten):
    """Ein Blick auf eine Karte: `.<karte>.get(` oder `.<karte>.contains_key(`.

    **Beide, seit 2026-08-20** -- `contains_key` tut denselben Blick und stand in keiner
    Zaehlung.
    """
    for i, z in enumerate(text.split("\n"), 1):
        for k in karten:
            for m in re.finditer(r"\.%s\s*\.\s*(get|contains_key)\s*\(" % re.escape(k), z):
                yield i, k, m.group(1), z.strip()


def karten_von(text):
    """Die Karten der `Umgebung` -- und welche davon ausserhalb ueberhaupt sichtbar sind."""
    alle = re.findall(r"^\s*(?:pub )?([a-z_]+): HashMap<", text, re.M)
    oeffentlich = re.findall(r"^\s*pub ([a-z_]+): HashMap<", text, re.M)
    return alle, oeffentlich


def messe():
    u = (SRC / "umgebung.rs").read_text(encoding="utf-8")
    alle, oeffentlich = karten_von(u)
    stellen = []
    dateien = 0
    for p in sorted(SRC.glob("*.rs")):
        if p.name == "umgebung.rs":
            continue
        t = p.read_text(encoding="utf-8")
        dateien += 1
        zeilen = t.split("\n")
        for nr, k, art, z in blicke(t, oeffentlich):
            umfeld = "\n".join(zeilen[max(0, nr - 3):nr])
            stellen.append((p.name, nr, k, art, bool(BEWUSST.search(umfeld)), z[:74]))
    return alle, oeffentlich, dateien, stellen


def sprechprobe():
    """R14, in beide Richtungen -- an einer ERFUNDENEN Quelle.

    *Ein Zaehler, der nur die eigenen Dateien liest, misst, wie gut sie zu ihm passen.*
    """
    karten = karten_von("    pub erfunden: HashMap<String, u8>,\n")[1]
    gift = list(blicke("        if u.erfunden.get(&n).is_some() {", karten))
    gift2 = list(blicke("        if u.erfunden.contains_key(&n) {", karten))
    sauber = list(blicke("        if u.suche_global(von, &n).is_some() {", karten))
    return karten == ["erfunden"], len(gift) == 1, len(gift2) == 1, not sauber


def main():
    # **TOOTH 0 -- THE SUBJECT HAS TO BE THERE** (2026-08-31). Over a tree without
    # its subject this tool died of a `FileNotFoundError`: return code **1**, a
    # traceback, and in a chain that reads like a finding. *A crash is not a refusal
    # -- a NAMED refusal is*, and a missing subject says the SETUP has to change.
    if not (SRC / "umgebung.rs").is_file():
        print("ABBRUCH: crates/gabbro-check/src/umgebung.rs fehlt -- es wurde NICHTS "
              "gemessen.", file=sys.stderr)
        return 2
    k_ok, g_ok, g2_ok, s_ok = sprechprobe()
    print("== Sprechprobe des Zaehlers ==")
    print("  Karte erkannt:            %s" % ("ja" if k_ok else "NEIN"))
    print("  direkter `.get(` faellt:  %s" % ("ja" if g_ok else "NEIN"))
    print("  `.contains_key(` faellt:  %s" % ("ja" if g2_ok else "NEIN"))
    print("  Weg ueber `suche` frei:   %s" % ("ja" if s_ok else "NEIN"))
    if not (k_ok and g_ok and g2_ok and s_ok):
        print("== KARTEN: der Zaehler misst nicht ==")
        # **Every refusal in this file ends with 2, not 1** (2026-08-31). This counter joined
        # `abnahme.py` that day, so its return code is now read as a VERDICT -- and the sixth
        # requirement applies: `1` means the TREE has to change, `2` means the SETUP does.
        # Every site below says NOTHING WAS MEASURED, so every one of them is a `2`.
        return 2

    alle, oeffentlich, dateien, stellen = messe()

    # **The speech test above proves the regex on an INVENTED line, not on the subject**
    # (2026-09-02). That is the right shape -- a counter that reads only its own files
    # measures how well they suit it -- but it leaves one end open: the pattern can be
    # perfect and still match nothing here, because the subject moved out from under it.
    #
    # The verdict below is a RATCHET, and a ratchet compares upward. Zero cards found means
    # zero sites found, zero is under every mark, and the run reports a record best at the
    # exact moment it stopped seeing its subject. *An empty population is worth nothing to
    # a ratchet, and looks like the best result it ever had.*
    #
    # A floor, therefore, on the real harvest and not on the invented one. `2`, because
    # this says the SETUP has to change, exactly as tooth 0 above does.
    if not alle or not oeffentlich or not dateien:
        print("ABBRUCH: %d Karten, %d oeffentlich, %d Passdateien -- es wurde NICHTS "
              "gemessen." % (len(alle), len(oeffentlich), dateien), file=sys.stderr)
        print("   Die Sprechprobe oben faehrt an einer ERFUNDENEN Zeile und bleibt davon "
              "gruen.", file=sys.stderr)
        return 2

    unqual = [s for s in stellen if not s[4]]
    print()
    print("== %d Karten in `umgebung.rs`, %d davon oeffentlich, %d Passdateien gelesen =="
          % (len(alle), len(oeffentlich), dateien))
    print("   direkte Blicke            %3d   (`.get(` und `.contains_key(`)" % len(stellen))
    print("   davon modulbewusst        %3d   in einer Kandidatenschleife"
          % (len(stellen) - len(unqual)))
    print("   davon UNQUALIFIZIERT      %3d   trifft nur einen vollqualifizierten Namen"
          % len(unqual))
    je_karte = {}
    for _, _, k, _, _, _ in stellen:
        je_karte[k] = je_karte.get(k, 0) + 1
    print("   je Karte: " + ", ".join("%s %d" % (k, n)
                                      for k, n in sorted(je_karte.items(), key=lambda x: -x[1])))
    if "--stellen" in sys.argv:
        print()
        for datei, nr, k, art, bewusst, z in stellen:
            print("   %-8s %s:%d  .%s.%s(   %s"
                  % ("bewusst" if bewusst else "UNQUAL", datei, nr, k, art, z))

    print()
    abschnitt.fertig()
    if len(stellen) > MARKE_DIREKT or len(unqual) > MARKE_UNQUALIFIZIERT:
        print("== KARTEN: %d direkte Blicke (%d unqualifiziert) gegen die Marke %d / %d =="
              % (len(stellen), len(unqual), MARKE_DIREKT, MARKE_UNQUALIFIZIERT))
        print("   **Die Marke ist eine Ratsche, keine Zielzahl.** Jeder neue direkte Blick ist")
        print("   eine neue Stelle, an der eine Pruefung in einem `module`-Block schweigen")
        print("   kann -- genau die Gestalt des Lochs in `M103` vom 2026-08-17.")
        return 1
    print("== KARTEN: %d direkte Blicke, %d unqualifiziert -- keine neue =="
          % (len(stellen), len(unqual)))
    print("   Und was das NICHT heisst: ein direkter Blick ist kein Fehler. Wo der Schluessel")
    print("   aus einer schon qualifizierten Deklaration stammt, trifft er richtig. Diese")
    print("   Zaehlung findet KANDIDATEN -- sie verpflichtet, sie spricht nicht frei (W10).")
    print("   **Wie viele der %d in einem `module` danebengreifen, ist ungemessen** und"
          % len(unqual))
    print("   braeuchte je Stelle eine Giftdatei mit `module`-Block.")
    return 0


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
