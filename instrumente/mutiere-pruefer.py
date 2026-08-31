#!/usr/bin/env python3
"""Mutationsprobe **auf den Pruefer selbst**.

Die Testsuite prueft zwei Richtungen: eine erwartete Absage faellt, ein sauberer Fall geht
durch. Beides sagt nichts ueber die Richtung, die am 2026-08-14 zwoelfmal offen stand:
**eine Regel, die gar nicht mehr greift.** Sechzehn Dateien mit echten Ueberlaeufen kamen
durch, und 48 gruene Proben merkten nichts davon.

Diese Probe stellt genau die Frage. Sie **beschaedigt eine Regel des Pruefers** und sieht
nach, ob irgendeine Probe faellt:

    ueberlebt  ->  **BEFUND.** Diese Regel hat keinen Test. Ihr Ausfall waere unbemerkt
                   geblieben -- also ist sie heute unbewacht.
    gefangen   ->  die Regel steht unter Beobachtung.
    ungueltig  ->  die Mutation uebersetzt nicht; sie sagt nichts und zaehlt nicht mit.

`README.md` verlangt genau das fuer die Annotationsemission (*„Mutationsprobe auf der
ANNOTATIONSEMISSION, nicht nur auf der Codeemission"*). Der Pruefer ist derselbe Fall: er
emittiert Absagen, und ein Erzeuger, der stillschweigend schwaechere Absagen ausgibt,
liefert ein gruenes Nichts.

**Die Quelle wird nur waehrend eines Laufs veraendert und danach byteweise
wiederhergestellt** -- gegen Hash geprueft. Bei jedem Abbruch ebenso.

    ./instrumente/mutiere-pruefer.py              alle Mutationen
    ./instrumente/mutiere-pruefer.py --schnell    nur die Sprechprobe des Geruests
    ./instrumente/mutiere-pruefer.py --anker      nur der Ankerstand -- ohne Bau, ohne sauberen Baum
"""
import hashlib
import pathlib
import subprocess
import sys
import tempfile

WURZEL = pathlib.Path(__file__).resolve().parent.parent

# **Jede Ausfuehrung mit Frist.** Ein Haenger sieht aus wie „laeuft noch", nicht wie
# ein Befund -- am 2026-08-20 standen deswegen einundzwanzig Laeufe von
# `pruefe-emission.sh` nebeneinander, der aelteste seit dreieinhalb Stunden.
FRIST = 900
CHECK = WURZEL / "crates" / "gabbro-check" / "src"


# **Die Emissionsflaechen -- und die Bezugsgroesse, die 32/32 sonst verschweigt.**
# `32 von 32` ist ein Verhaeltnis ueber DER FLAECHE, die es beschaedigen kann. Wo nichts
# emittiert wird, kann nichts mutieren -- und eine Gesamtzahl liest sich dann wie Deckung.
FLAECHEN = {
    "pruefer": "Der Pruefer (Absagen). Gebaut, mutierbar.",
    # **Not zero any more since 2026-08-21** («P6»). `gabbro pflichten --isabelle` writes a
    # unit's obligation register as an Isabelle theory, and `instrumente/pruefe-p6-beweis.sh`
    # lets Isabelle read it. The warning that stood here as the REASON for the zero is
    # therefore not discharged but has become APPLICABLE: it is the yardstick of the seven
    # mutations below.
    #
    # > *A duty that vanishes is noticed; one that gets weaker is not.*
    #
    # **And the reference size stays small and named:** of 47 counted obligations exactly ONE
    # stands closed today (`./instrumente/zaehle-p6.py`). What the emitter does not emit it
    # cannot weaken either -- these mutations cover the surface it HAS, not the one it ought
    # to have.
    "annotation": "Die ANNOTATIONSEMISSION -- der Wunschform-Kanal. Gebaut seit 2026-08-21 "
                  "(`gabbro pflichten --isabelle`, «P6»), also mutierbar: ein Erzeuger, der "
                  "stillschweigend abgeschwaechte Vertraege ausgibt, liefert einen gruenen "
                  "Beweis ueber eine schwaechere Aussage, und ohne diese Proben faengt ihn "
                  "keine.",
    # **Seit 2026-08-17 nicht mehr null.** Ein Fragment ist durchgestochen -- .gab -> C ->
    # cc -Werror -> ausgefuehrt -> verglichen (`pruefe-emission.sh`). Die Flaeche ist damit
    # beschaedigbar geworden, und das ist der ganze Unterschied: was 0 Mutationen hat, ist
    # nicht gedeckt, sondern unbeschaedigbar.
    # **This number is NOT maintained here either** -- and until 2026-08-30 it was.
    #
    # The sentence read *"TWO translation units built and mutable (one example and fragment
    # F7, the ghost erasure); eight fragments unchecked"*. It was written on 2026-08-17 and
    # never followed the thing it described: on 2026-08-30 `pruefe-emission.sh` builds and
    # runs **23** units, five of them fragments, and **five** fragments are the ones nobody
    # runs -- of which exactly ONE still emits at all (`messung/W24-FRAGMENTE.md`).
    #
    # > **A second register over the same thing** (W7), and the `schablone` row three lines
    # > down already carries the cure in words -- it refuses to hold a number at all. A stale
    # > number beside a live catalogue does not read as stale: it reads as a measurement.
    #
    # So this row asks the harness instead of remembering it.
    "code": lambda: emissionsflaeche_satz(),
    # **Diese Zahl wird NICHT hier gepflegt.** Sie stand hier als "16, keine bewiesen",
    # waehrend `gabbro schablonen` 19 mit 4 bewiesenen meldete -- zwei Register ueber
    # derselben Sache, und das ist die Fehlerklasse, gegen die W7 steht. Wer sie hier
    # nachfuehrt, baut das zweite Register wieder auf.
    "schablone": "Die Erzeuger-Schablonen (Zahl: `gabbro schablonen`). Ueberwiegend ENTWORFEN -- "
                 "was kein Code ist, kann keine Mutation fangen.",
}


class Mutation:
    def __init__(self, name, datei, alt, neu, regel, flaeche="pruefer"):
        self.name = name
        # **Ein Pfad mit `/` nennt seine Kiste** (2026-08-20).
        #
        # Bis heute stand hier nur `CHECK / datei`, und `CHECK` ist `gabbro-check/src`.
        # **Damit war der ganze PARSER unbeschaedigbar** -- 193 von 193 sagte nichts ueber
        # `gabbro-syntax`, und die Zahl las sich trotzdem wie Deckung.
        #
        # > Aufgefallen erst, als eine Mutation den Tiefenwaechter in `parse.rs` treffen
        # > sollte und die Datei nicht gefunden wurde. *Eine Flaeche, die kein Werkzeug
        # > erreicht, faellt in keiner Statistik auf -- sie fehlt einfach.*
        self.pfad = (WURZEL / "crates" / datei) if "/" in datei else (CHECK / datei)
        self.alt = alt
        self.neu = neu
        self.regel = regel
        self.flaeche = flaeche


# Jede Mutation beschaedigt GENAU EINE Regel. Der Text daneben sagt, welche -- wer eine
# Mutation ueberleben sieht, weiss damit sofort, was heute unbewacht ist.
MUTATIONEN = [
    # -- m1.rs: «B33», die fluechtige Stelle ---------------------------------------------
    Mutation(
        "register-verengt-sich-wieder",
        "m1.rs",
        "        if let (ExprArt::Ort(o), Some(wert)) = (&a.art, self.u.konst_wert(&self.modul, b)) {\n"
        "            if !fa {",
        "        if let (ExprArt::Ort(o), Some(wert)) = (&a.art, self.u.konst_wert(&self.modul, b)) {\n"
        "            if true {",
        "«B33» -- V1 verengt eine Registerstelle wieder; `if d.ST.IDX < 8` deckt "
        "`T.slots[d.ST.IDX]`, und zwischen den zwei volatilen Lesungen darf die Hardware "
        "schreiben, was sie will",
    ),
    Mutation(
        "registerbeziehung-lebt-wieder",
        "m1.rs",
        "        if let (ExprArt::Ort(oa), ExprArt::Ort(ob)) = (&a.art, &b.art) {\n"
        "            if fa || fb {",
        "        if let (ExprArt::Ort(oa), ExprArt::Ort(ob)) = (&a.art, &b.art) {\n"
        "            if false {",
        "«B33» in der zweiten Schreibrichtung -- V2 macht aus einem Registervergleich "
        "wieder einen Beziehungsfakt",
    ),
    # -- gruppe.rs: the rank resolved in the wrong module (2026-08-24) --------------------
    #
    # `konst_wert("", …).unwrap_or(0)` -- empty module path, and the failure became a `0`
    # that stands nowhere in the source. Two locks with different ranks both read `0`.
    Mutation(
        "gruppenrang-aus-der-wurzel",
        "gabbro-check/src/gruppe.rs",
        "            let rang = u.konst_wert(modul, &l.rang);",
        "            let rang = Some(u.konst_wert(\"\", &l.rang).unwrap_or(0));",
        "`U005` -- der Rang wird wieder von der WURZEL aufgeloest und faellt auf 0 zurueck; "
        "zwei verschiedene Raenge gelten dann als gleich und ein richtiges Programm faellt",
    ),
    # -- wirkungen.rs: the frame under an incomplete hull (2026-08-24) --------------------
    #
    # `E009` set the hint and RETURNED, so `E008` was switched off for the whole function --
    # and the reason propagated upward: one unresolvable edge deep down left every caller's
    # frame unchecked. Ten corpus sites carried it.
    Mutation(
        "rahmen-faellt-unter-unvollstaendiger-huelle-aus",
        "gabbro-check/src/wirkungen.rs",
        "                 contains must be declared -- a lower bound refutes, it just cannot confirm\",\n            ),\n        );\n    }",
        "                 contains must be declared -- a lower bound refutes, it just cannot confirm\",\n            ),\n        );\n        return;\n    }",
        "`E008` -- eine unaufloesbare Kante schaltet den Rahmen wieder fuer die ganze "
        "Rufkette ab; die untere Schranke wird weggeworfen, obwohl sie widerlegt",
    ),
    # -- schleifen.rs: `by consuming` without a `consumes` (2026-08-24) -------------------
    #
    # The pass register booked it on 2026-08-21 and nothing followed: for `unvisited` and
    # `consuming`, pass 6 says nothing about termination at all.
    Mutation(
        "consuming-ohne-consumes-geht-durch",
        "gabbro-check/src/schleifen.rs",
        "        if !verbraucht {",
        "        if false {",
        "`S008` -- `by consuming` darf wieder ohne `consumes` stehen; die Zusage, dass die "
        "Domaene schrumpft, haette dann keinen Traeger",
    ),
    # -- m3.rs: the address space (2026-08-24) -------------------------------------------
    #
    # **The pass register booked it: the address space is checked nowhere.** `Typ` drops
    # `Raum` at construction, so only the DECLARATION still carries it -- and until today
    # nothing compared it. A `ptr<normal, rw>` reached a `ptr<mmio, rw>` parameter with zero
    # errors.
    Mutation(
        "adressraum-egal-am-rufort",
        "gabbro-check/src/m3.rs",
        "                    if ist != soll {",
        "                    if false {",
        "`R008` -- der Adressraum darf wieder wechseln; ein `normal`-Zeiger geht an einen "
        "`mmio`-Parameter, und der Erzeuger senkt beide verschieden ab",
    ),
    # -- phasen.rs: the step in a `return` (2026-08-24) -----------------------------------
    #
    # `fluss` handled `let` and the bare call and stopped there. The SAME lie written two ways
    # measured differently -- caught in a `let`, silent in a `return`.
    Mutation(
        "phasenschritt-im-return-unsichtbar",
        "gabbro-check/src/phasen.rs",
        "            StmtArt::Return(Some(e)) => {",
        "            StmtArt::Return(Some(e)) if false => {",
        "`O004` -- ein Phasenschritt im `return` wird wieder uebersehen; dieselbe Zusage im "
        "`let` faellt, im `return` nicht",
    ),
    # -- m3.rs: the syntactic half of the alias question (2026-08-24) ----------------------
    #
    # `messung/RACE.md` listed form `A1` among the four that NOTHING carries, and
    # `gabbro alias` had counted the site since 2026-08-21 without any pass refusing it.
    Mutation(
        "syntaktischer-alias-geht-wieder-durch",
        "gabbro-check/src/m3.rs",
        "                    if geschriebene.iter().any(|g| *g == ort) {",
        "                    if false {",
        "`R007` -- derselbe Zeiger darf wieder an zwei schreibbare Zeigerparameter gehen; "
        "der Gerufene rechnet mit zwei Namen, die er fuer verschieden halten darf",
    ),
    # -- pflichten.rs: the device promise (2026-08-24, «B26») -----------------------------
    #
    # **A clause that parses and is dropped is the folder's most-paid-for shape.** Until today
    # `RegDecl::requires` was read by no pass at all. Counting it is the whole fix -- and
    # without an anchor the counting could be removed again in silence.
    Mutation(
        "geraetezusage-wird-nicht-gezaehlt",
        "gabbro-check/src/pflichten.rs",
        "                    if r.requires.is_some() {",
        "                    if false {",
        "«B26» -- ein `requires` am Register verschwindet wieder still; die Klausel parst "
        "und niemand zaehlt sie",
    ),
    # -- kosten.rs: the branch prefix (2026-08-24) ---------------------------------------
    #
    # **Found while WRITING the soundness argument, not by a tool** (`messung/K001.md`).
    # `WennStmt::zweige` is flat, so a run taking arm `i` has evaluated conditions `0..=i`.
    # Dropping the prefix makes an `else if` chain measure less than the same body written as
    # sequential `if`s -- an UNDER-count, and on an upper bound that is the only direction
    # that matters.
    Mutation(
        "zweigkette-verliert-praefix",
        "gabbro-check/src/kosten.rs",
        "                    praefix = praefix.plus(self.ausdruck(bed));",
        "                    praefix = Kosten::Zahl(0).plus(self.ausdruck(bed));",
        "`K001` -- die `else if`-Kette zaehlt wieder nur die eigene Bedingung je Zweig; "
        "dieselbe Bedeutung sequentiell geschrieben misst dann mehr",
    ),
    # -- m1.rs: `refines`, the head form of P6 (2026-08-24) -------------------------------
    #
    # **Three anchors for three rules, and the reason stands in `messung/VERFEINERUNG.md`:**
    # the refinement obligation is the strongest statement this language makes about a body.
    # A rule about it with nothing mutating against it would not be covered -- it would be
    # UNDAMAGEABLE, and that is the state the surface `annotation` sat in for weeks.
    Mutation(
        "refines-auch-an-spec-fn",
        "m1.rs",
        "        if f.klasse != Some(FnKlasse::Impl) {",
        "        if false {",
        "`M130` -- eine `spec fn` duerfte `refines` tragen; sie IST die Aussage, und die "
        "Pflicht haette keinen Rumpf, der sie schuldet",
    ),
    Mutation(
        "refines-nennt-ins-leere",
        "m1.rs",
        "        let Some(&stellen) = self.spec_fns.get(&genannt) else {",
        "        let Some(&stellen) = self.spec_fns.get(&genannt).or(Some(&f.parameter.len())) else {",
        "`M131` -- `refines` duerfte eine Spezifikation nennen, die es nicht gibt; der "
        "Beweiser nimmt die genannte Aussage dann an",
    ),
    Mutation(
        "refines-ungleiche-stelligkeit",
        "m1.rs",
        "        if stellen != f.parameter.len() {",
        "        if false {",
        "`M132` -- Spezifikation und Rumpf duerften verschiedene Stelligkeit tragen; die "
        "erzeugte Pflicht truege ungebundene Variablen",
    ),
    # -- m3.rs: die Registerklasse ------------------------------------------------------
    Mutation(
        "klasse-w-darf-gelesen-werden",
        "m3.rs",
        "fn darf_lesen_reg(k: RegKlasse) -> bool {\n    !matches!(k, RegKlasse::Schreiben)",
        "fn darf_lesen_reg(k: RegKlasse) -> bool {\n    let _ = k;\n    true",
        "R005 -- ein `class w`-Register darf wieder gelesen werden; genau so stand es bis "
        "zum 2026-08-20 im Ordner als ERLEDIGT",
    ),
    Mutation(
        "klasse-r-darf-geschrieben-werden",
        "m3.rs",
        "fn darf_schreiben_reg(k: RegKlasse) -> bool {\n    matches!(",
        "fn darf_schreiben_reg(k: RegKlasse) -> bool {\n    let _ = k;\n    return true;\n    #[allow(unreachable_code)]\n    matches!(",
        "R006 -- ein `class r`-Register darf wieder geschrieben werden",
    ),
    Mutation(
        "feldklasse-erbt-immer",
        "m3.rs",
        "                .map(|(n, _, k)| (n.text.clone(), k.unwrap_or(r.klasse)))",
        "                .map(|(n, _, k)| { let _ = k; (n.text.clone(), r.klasse) })",
        "«B23» -- die Klasse je Feld faellt weg, jedes Feld erbt wieder die des Registers; "
        "`FSTS.FRI` ist damit schreibbar, weil `FSTS` es ist",
    ),
    # -- typen.rs: die Bereichsarithmetik ------------------------------------------------
    Mutation(
        "bereich-passt-immer",
        "typen.rs",
        "        self.min >= ziel.min && self.max <= ziel.max",
        "        let _ = ziel; true",
        "M101 -- ein Wert passt immer in sein Ziel",
    ),
    Mutation(
        "breite-passt-immer",
        "typen.rs",
        "        let (lo, hi) = grenzen(self.breite, self.vorzeichen);\n"
        "        self.min >= lo && self.max <= hi\n    }\n\n    /// **Ein Bereich, der KEINEN Wert",
        "        let (lo, hi) = grenzen(self.breite, self.vorzeichen);\n"
        "        let _ = (lo, hi);\n        true\n    }\n\n    /// **Ein Bereich, der KEINEN Wert",
        "M104 -- kein Ueberlauf verlaesst je die Breite",
    ),
    # **Zwei Regeln aus der Rezension vom 2026-08-20.** Beide waren ABSTUERZE oder stille
    # Ja-Aussagen, also gehoeren sie hierher: was keine Mutation faengt, ist ungedeckte
    # Flaeche, egal wie frisch der Test daneben ist.
    # **Drei Regeln aus der dritten Rezension.** Alle drei waren "eine Klasse richtig
    # diagnostiziert, eine Instanz behoben" -- darum zielen sie auf die GEMEINSAME Stelle.
    # **Die dritte Rezension, zweite Haelfte.** Jede dieser Mutationen macht genau EINE
    # Umgehung wieder auf -- und jede lag einen syntaktischen Schritt neben einer
    # bestehenden Giftprobe.
    Mutation(
        "m2-steigt-nicht-in-argumente",
        "m2.rs",
        "    for x in crate::alle_ausdruecke(e) {\n        if let ExprArt::Ruf(r) = &x.art {",
        "    for x in [e] {\n        if let ExprArt::Ruf(r) = &x.art {",
        "L104 -- ein geschachtelter `consumes`-Ruf wird wieder unsichtbar: "
        "`aussen(wecken(p)); wecken(p);` ist ein Double-Free mit gruenem Haken",
    ),
    Mutation(
        "m2-nimmt-jede-position",
        "m2.rs",
        "        let wird_verbraucht = sig.get(i).is_some_and(|n| verbraucht.contains(n));",
        "        let wird_verbraucht = !sig.is_empty() && !verbraucht.is_empty();",
        "an einer Rufstelle gilt wieder JEDES lineare Argument als verbraucht, sobald der "
        "Gerufene irgendeinen Parameter verbraucht -- in beide Richtungen falsch",
    ),
    Mutation(
        "verbrauch-in-der-schleife-zaehlt-einmal",
        "m2.rs",
        "            let vor_schleife: Option<BTreeMap<_, _>> =\n                matches!(&s.art, StmtArt::Schleife(_)).then(|| zust.clone());",
        "            let vor_schleife: Option<BTreeMap<String, (Zustand, Span, bool, bool)>> = None;",
        "L108 -- ein Schleifenrumpf verbraucht wieder `genau einmal`, obwohl er oft laeuft",
    ),
    Mutation(
        "im-zweig-geborener-wert-faellt-heraus",
        "m2.rs",
        "    if endet_hier {\n        return; // wer den Zweig mit `return` verlaesst",
        "    if true {\n        return; // wer den Zweig mit `return` verlaesst",
        "L109 -- ein linearer Wert, der im Zweig geboren wird und ihn nicht verlaesst, "
        "faellt wieder an der Vereinigung heraus",
    ),
    Mutation(
        "mass-darf-sich-nur-bewegen",
        "kosten.rs",
        "        BinOp::Minus => k >= 1,",
        "        BinOp::Minus | BinOp::Plus => k >= 0,",
        "K009 -- ein STEIGENDES Rekursionsmass geht wieder durch; `g(n + 1, m)` "
        "terminiert nicht und wird abgesenkt",
    ),
    Mutation(
        "sperrabdruck-wird-summiert",
        "gruppe.rs",
        "        for k in crate::unterbloecke(s) {\n            schreibstellen(k, traeger, gehalten, aus);",
        "        for k in crate::unterbloecke(s).into_iter().take(0) {\n            schreibstellen(k, traeger, gehalten, aus);",
        "U003 -- die Schreibstellen INNERHALB eines `locks`-Blocks werden nicht mehr "
        "gefunden, also hat die Gruppe keinen Abdruck mehr: zwei "
        "`locks`-Bloecke NACHEINANDER sehen aus wie zwei gehaltene Sperren, und zwischen "
        "ihnen ist die Gruppe offen",
    ),
    Mutation(
        "can-fail-darf-schreiben",
        "namen.rs",
        '                        StmtArt::Zuweisung(z) => ("an assignment", z.ziel.span),',
        '                        StmtArt::Publish(_) if false => ("an assignment", s.span),',
        "N027 -- ein `can_fail`-Block darf wieder schreiben und sperren, obwohl das `check` "
        "keinen Vertrag traegt und zehn der zwoelf Paesse ihn nie sehen",
    ),
    Mutation(
        "schritt-in-locks-bleibt-unsichtbar",
        "phasen.rs",
        "            for inner in crate::unterbloecke(k) {\n                if im_block(inner, u, modul, schritte) {",
        "            for inner in crate::unterbloecke(k).into_iter().take(0) {\n                if im_block(inner, u, modul, schritte) {",
        "O006 -- ein Phasenschritt in einem `locks { }` innerhalb einer Schleife wird "
        "wieder unsichtbar",
    ),
    Mutation(
        "v006-endet-an-der-klammer",
        "paarung.rs",
        "                danach_namen.extend(spaeter_aussen.iter().cloned());",
        "                danach_namen.truncate(danach_namen.len());",
        "V006 -- ein `if` um das release-Speichern macht die Regel wieder stumm; die "
        "Sichtbarkeitsordnung endet dann an einer Klammer",
    ),
    Mutation(
        "konstante-verliert-ihren-wert",
        "m1.rs",
        "                        self.u.konst_wert_von_namen(&self.modul, &o.basis.text),",
        "                        None::<i128>,",
        "eine benannte Konstante loest wieder auf den vollen Bereich ihres Typs auf: "
        "`x + 8` geht durch, `x + RESERVE` faellt an M104 -- ein Pruefer, der das Benennen "
        "bestraft, erzieht zur magischen Zahl",
    ),
    Mutation(
        "tiefenwaechter-fehlt-am-modul",
        "gabbro-syntax/src/parse.rs",
        "        self.tiefer(|p| p.moduledecl_innen(oeffentlich))",
        "        self.moduledecl_innen(oeffentlich)",
        "300 verschachtelte `module` toeten den Pruefer mit einem Stapelueberlauf, waehrend "
        "40 verschachtelte Klammern ein sauberes `P038` geben -- der Waechter sass an drei "
        "von sechs Rekursionsstellen",
    ),
    Mutation(
        "bereichsarithmetik-laeuft-selbst-ueber",
        "typen.rs",
        "        match x.checked_mul(y) {",
        "        match Some(x.wrapping_mul(y)) {",
        "die Domaene, auf der der Ueberlaufbeweis ruht, rechnet wieder umlaufend: zwei "
        "blanke `u64` multipliziert geben im Freigabebau `u64 in -36893488147419103231 .. 0` "
        "-- eine negative Untergrenze auf einem vorzeichenlosen Typ",
    ),
    Mutation(
        "ausdruckslaeufer-steigt-nicht-in-den-index",
        "lib.rs",
        "        ExprArt::Ort(o) | ExprArt::Alt(o) => aus.extend(ausdruecke_im_ort(o)),",
        "        ExprArt::Ort(_) | ExprArt::Alt(_) => {}",
        "ein Ruf in Indexposition wird wieder unsichtbar: `t.slots[schreibt()].x` unter "
        "`effects { pure }` faellt nicht mehr an E008, und der Erzeuger setzt `pure` "
        "darueber -- die Klasse, an der `-O1` einmal 65 Rufe geloescht hat",
    ),
    Mutation(
        "praedikatlaeufer-vergisst-folgt-und-quantor",
        "lib.rs",
        "            PredArt::Quantor(q) => geh(&q.rumpf, aus),",
        "            PredArt::Quantor(_) => {}",
        "ein Ruf im Rumpf eines Quantors wird wieder unsichtbar. **Die erste Fassung "
        "dieser Mutation strich `Folgt` aus dem Muster und machte das `match` damit "
        "nicht-erschoepfend -- sie BAUTE nicht und zaehlte als `ungueltig`.** Genau das "
        "ist der Preis eines `match` ohne `_`-Zweig, und genau darum ist er richtig: der "
        "Uebersetzer laesst die Luecke gar nicht erst entstehen",
    ),
    Mutation(
        "unbekannter-name-faellt-nicht",
        "m1.rs",
        '                Absage::fehler("M119", o.basis.span, format!("`{n}` is declared nowhere"))\n                    .mit_notiz(',
        '                Absage::hinweis("M119", o.basis.span, format!("`{n}` is declared nowhere"))\n                    .mit_notiz(',
        "M119 -- ein Tippfehler schaltet die Indexpruefung wieder ab: `t.slots[j].x` mit "
        "unbekanntem `j` gibt null Fehler, wo `i` ein M103 gaebe",
    ),
    Mutation(
        "globaler-fakt-ueberlebt-den-ruf",
        "m1.rs",
        "        self.u.suche_global(&self.modul, schluessel).is_none()",
        "        !self.u.globale.contains_key(schluessel)",
        "in jeder Datei mit `module` gilt jede globale Groesse wieder als lokal, also "
        "loescht `aufruf_toetet_fakten` nie -- ein Fakt ueberlebt einen Ruf, der ihn "
        "schreibt",
    ),
    Mutation(
        "umlauf-rechnet-doch-signiert",
        "emit.rs",
        "        BinOp::Plus | BinOp::Minus | BinOp::Mal | BinOp::SchiebLinks",
        "        BinOp::Minus | BinOp::SchiebLinks",
        "`u16 wrapping` mal `u16 wrapping` geht wieder ohne Cast ins C; die ganzzahlige "
        "Aufwertung hebt beide Seiten auf `int`, und dort ist der Ueberlauf UNDEFINIERT -- "
        "Gabbro sagt `definiert`, das Erzeugnis meint etwas anderes",
        "code",
    ),
    Mutation(
        "ein-feld-des-static-zaehlt-nicht",
        "m1.rs",
        "                        Some(ist_zeiger) => z.ziel.suffixe.is_empty() || !ist_zeiger,",
        "                        Some(_) => z.ziel.suffixe.is_empty(),",
        "M118 fasst wieder nur den `static` selbst; `punkt.a = 5` auf einem "
        "unveraenderlichen Verbund geht durch, und der Erzeuger schreibt `static const` "
        "daneben",
    ),
    Mutation(
        "const-landet-auf-dem-zeigerziel",
        "emit.rs",
        '                (false, true) => ("", "const "),',
        '                (false, true) => ("const ", ""),',
        "aus dem konstanten ZEIGER wird ein Zeiger auf konstantes Ziel; `cc` weist damit "
        "ein Programm ab, das Gabbro richtig findet",
        "code",
    ),
    Mutation(
        "static-ohne-mut-darf-schreiben",
        "m1.rs",
        "                if statisch_unveraenderlich {",
        "                if false && statisch_unveraenderlich {",
        "M118 -- auf ein `static` ohne `mut` zu schreiben faellt wieder nirgends; der "
        "Erzeuger schreibt `static const` daneben, und `gcc` ist die einzige Instanz",
    ),
    Mutation(
        "prozent-im-assembler-bleibt-einfach",
        "emit.rs",
        "        if c == '%' && zs.peek() != Some(&'[') {",
        "        if false && c == '%' && zs.peek() != Some(&'[') {",
        "der Assemblertext geht woertlich in einen ERWEITERTEN `__asm__`-Block; `%eax` "
        "statt `%%eax`, und `cc` lehnt die Uebersetzungseinheit ab. Bei `asm` liest die "
        "Sprache den Inhalt ausdruecklich NICHT -- der C-Uebersetzer ist die einzige "
        "Pruefung, die es gibt",
        "code",
    ),
    Mutation(
        "leerer-bereich-geht-durch",
        "m1.rs",
        "if b.min > b.max {",
        "if false && b.min > b.max {",
        "M117 -- ein Bereich ohne jeden Wert wird nicht mehr abgesagt; aus dem Leeren "
        "folgt jede Aussage, also auch dass ein Divisor nicht null ist",
    ),
    Mutation(
        "leerer-bereich-rechnet-doch",
        "typen.rs",
        "    pub fn ist_leer(&self) -> bool {\n        self.min > self.max",
        "    pub fn ist_leer(&self) -> bool {\n        false && self.min > self.max",
        "der Riegel hinter M117 faellt weg -- `a.min / b.max` teilt bei `5 .. 0` durch die "
        "Null und der Pruefer stirbt an einer Deklaration",
    ),
    Mutation(
        "nenner-nie-null",
        "typen.rs",
        "    pub fn enthaelt_null(&self) -> bool {\n        self.min <= 0 && self.max >= 0",
        "    pub fn enthaelt_null(&self) -> bool {\n        false && self.min <= 0 && self.max >= 0",
        "M102 -- der Nenner schliesst die Null immer aus",
    ),
    Mutation(
        "subtraktion-zu-eng",
        "typen.rs",
        "(a.min.checked_sub(b.max), a.max.checked_sub(b.min))",
        "(a.min.checked_sub(b.min), a.max.checked_sub(b.min))",
        "die Untergrenze der Subtraktion (Unterlauf wird unsichtbar)",
    ),
    Mutation(
        "addition-zu-eng",
        "typen.rs",
        "(a.min.checked_add(b.min), a.max.checked_add(b.max))",
        "(a.min.checked_add(b.min), a.max.checked_add(b.min))",
        "die Obergrenze der Addition",
    ),
    Mutation(
        "literal-immer",
        "typen.rs",
        "    if a.literal {\n        return Some((b.breite, b.vorzeichen));",
        "    if a.literal || a.min == a.max {\n        return Some((b.breite, b.vorzeichen));",
        "U10 -- ein Punktbereich nimmt wieder fremde Breite an",
    ),
    Mutation(
        "schieben-ohne-vorzeichen",
        "typen.rs",
        "    let ecken = [\n        a.min << b.min,\n        a.min << b.max,\n"
        "        a.max << b.min,\n        a.max << b.max,\n    ];",
        "    let ecken = [a.max << b.min, a.max << b.max];",
        "U8 -- schiebe_links vergisst den negativen Operanden",
    ),
    # -- m1.rs: die Faktenmenge ----------------------------------------------------------
    Mutation(
        "fakten-sterben-nie",
        "m1.rs",
        "    fn schreiben_toetet_fakten(&self, ziel: &Ort, lage: &mut Lage) {\n"
        "        let Some(k) = schluessel_von(ziel) else {",
        "    fn schreiben_toetet_fakten(&self, ziel: &Ort, lage: &mut Lage) {\n"
        "        if true {\n            return;\n        }\n"
        "        let Some(k) = schluessel_von(ziel) else {",
        "SPRACHE.md 3.2 -- ein Fakt stirbt bei keinem Schreiben mehr",
    ),
    Mutation(
        "unterblock-toetet-nicht",
        "m1.rs",
        "    fn geschriebenes_toeten(&mut self, b: &Block, aussen: &mut Lage) {\n"
        "        let mut ziele = Vec::new();",
        "    fn geschriebenes_toeten(&mut self, b: &Block, aussen: &mut Lage) {\n"
        "        if true {\n            let _ = (b, aussen);\n            return;\n        }\n"
        "        let mut ziele = Vec::new();",
        "U1 -- ein Schreiben im Unterblock toetet den aeusseren Fakt nicht",
    ),
    Mutation(
        "aufruf-toetet-nicht",
        "m1.rs",
        "    fn aufruf_toetet_fakten(&self, lage: &mut Lage) {\n        lage.fakten.retain",
        "    fn aufruf_toetet_fakten(&self, lage: &mut Lage) {\n"
        "        if true {\n            return;\n        }\n        lage.fakten.retain",
        "U4/U5 -- ein Aufruf toetet keinen nichtlokalen Fakt",
    ),
    Mutation(
        "index-ungeprueft",
        "m1.rs",
        # **Der Anker brach am 2026-08-17**, als der Kartenblick modulbewusst wurde --
        # das Geruest meldete `ANKER FEHLT` und schloss die Mutation AUS, statt sie still
        # als gefangen zu zaehlen. *Genau dafuer ist die Meldung da.*
        "    fn index_pruefen(&mut self, o: &Ort, lage: &Lage) {",
        "    fn index_pruefen(&mut self, o: &Ort, lage: &Lage) {\n"
        "        if true {\n            let _ = (o, lage);\n            return;\n        }",
        "M103/M4 -- kein Index wird gegen seine Schranke geprueft",
    ),
    Mutation(
        "v1-tot",
        "m1.rs",
        "        for f in &lage.fakten {\n            if let Fakt::Bereich {",
        "        for f in &lage.fakten[..0] {\n            if let Fakt::Bereich {",
        "V1 -- kein Fakt verengt je einen Bereich",
    ),
    Mutation(
        "v2-tot",
        "m1.rs",
        "    fn beziehung(&self, a: &Ort, b: &Ort, lage: &Lage) -> Option<i128> {\n"
        "        let (ka, kb) = (schluessel_von(a)?, schluessel_von(b)?);",
        "    fn beziehung(&self, a: &Ort, b: &Ort, lage: &Lage) -> Option<i128> {\n"
        "        if true {\n            let _ = (a, b, lage);\n            return None;\n        }\n"
        "        let (ka, kb) = (schluessel_von(a)?, schluessel_von(b)?);",
        "V2 -- eine Beziehung zweier Stellen traegt nie",
    ),
    Mutation(
        "v3-tot",
        "m1.rs",
        "                        innen.lokal.insert(binder.text.clone(), nutzlast);",
        "                        let _ = nutzlast;\n"
        "                        innen.lokal.insert(binder.text.clone(), Typ::Unbekannt);",
        "V3 -- der match-Binder traegt seine Nutzlast nicht mehr",
    ),
    Mutation(
        "endet-immer-stimmt-immer",
        "m1.rs",
        "    fn endet_immer(&self, b: &Block) -> bool {\n        let Some(letzte) = b.anweisungen.last()",
        "    fn endet_immer(&self, b: &Block) -> bool {\n"
        "        if true {\n            let _ = b;\n            return true;\n        }\n"
        "        let Some(letzte) = b.anweisungen.last()",
        "U6/V1-Verneinung -- jeder Zweig gilt als verlassend",
    ),
    Mutation(
        "index-nicht-im-schluessel",
        "m1.rs",
        "                    indizes.push(inner.basis.text.clone());",
        "                    let _ = &inner.basis.text;",
        "U3 -- der Fakt ueber a[i] ueberlebt das Schreiben von i",
    ),
    Mutation(
        "let-verdeckt-nicht",
        "m1.rs",
        '                lage.fakten\n                    .retain(|f| !nennt_namen(f, &l.name.text));\n',
        '',
        "U2 -- eine neue Bindung erbt den Fakt ihres Vorgaengers",
    ),
    Mutation(
        "wrapping-ueberall",
        "m1.rs",
        "                if !ziel.laeuft_um() {\n"
        "                    self.passt_wert(",
        "                if ziel.laeuft_um() {\n"
        "                    self.passt_wert(",
        "jede Zuweisung gilt als `wrapping`",
    ),
    # -- namen.rs, schleifen.rs, wirkungen.rs --------------------------------------------
    Mutation(
        "doppelte-namen-egal",
        "namen.rs",
        "    if let Some(erste) = gesehen.get(name) {",
        "    if false {\n        let erste = &span;",
        "N001 -- zwei Deklarationen desselben Namens sind keine mehr",
    ),
    Mutation(
        "bits-duerfen-ueberlappen",
        "namen.rs",
        "            if tief <= *h2 && *t2 <= hoch {",
        "            if false && tief <= *h2 && *t2 <= hoch {",
        "N003/D2 -- Registerfelder duerfen sich ueberschneiden",
    ),
    Mutation(
        "marke-egal",
        "schleifen.rs",
        "    if marken.iter().any(|m| m == &ziel.text) {\n        return;\n    }",
        "    if true || marken.iter().any(|m| m == &ziel.text) {\n        return;\n    }",
        "H001 -- `leave`/`next` zielen auf beliebige Namen",
    ),
    Mutation(
        "let-else-darf-durchfallen",
        "schleifen.rs",
        '            if !crate::endet_immer(&l.sonst, lg.div) {',
        '            if false && !crate::endet_immer(&l.sonst, lg.div) {',
        "U7/S002 -- der `else`-Zweig darf durchfallen",
    ),
    Mutation(
        "effects-fail-open",
        "wirkungen.rs",
        "            if f.klasse != Some(FnKlasse::Spec) {\n"
        "                absagen.schiebe(\n                    Absage::fehler(\n"
        "                        \"E001\",",
        "            if false && f.klasse != Some(FnKlasse::Spec) {\n"
        "                absagen.schiebe(\n                    Absage::fehler(\n"
        "                        \"E001\",",
        "SPRACHE.md 7 -- `effects` ist wieder fail-open",
    ),
    Mutation(
        "kapazitaet-egal",
        "umgebung.rs",
        "                        laenge: self.kapazitaeten.get(t).copied(),",
        "                        laenge: None,",
        "A3 -- eine Tabelle mit `count N` gibt ihrem Slotfeld keine Laenge",
    ),
    # **The error that stood for three days, put back as a mutation** (2026-08-31).
    #
    # Until 2026-08-20 this site computed `levels x node length`: 2 048, where the leaf set
    # of a four-level `walk` over 512-entry nodes holds 512^4 = 68 719 476 736. **Seven
    # orders of magnitude**, and it was the EMITTER that found it, not a probe --
    # `saetze.rs::kosten.domaenenschranke` wrote exactly that down as its own gap.
    #
    # *Since 2026-08-31 it falls:* the `mappings of` probe in `rechenwerk.rs` walks `e` from
    # 1 to 4 over `l = 2`, and the two readings already part at `e = 3` (16 against 12). The
    # second falling probe is a CONSEQUENCE of the same rule: without the power nothing
    # overflows any more, so `K003` stays away.
    Mutation(
        "walkschranke-wieder-ein-pfad",
        "umgebung.rs",
        "                            if let Some(n) = (l as u128).checked_pow(e as u32) {",
        "                            if let Some(n) = (l as u128).checked_mul(e as u128) {",
        "the bound of `mappings of` is `levels x node length` again instead of "
        "`node length ^ levels` -- one descent path, handed out as the leaf set",
    ),
    # **The walk's IDENTITY hangs on its cost number again** (2026-08-31).
    #
    # `walkschranken` answers "how large is the leaf set"; the resolver asks "does this
    # `walk` exist". With the cost map back in that seat, `walk W levels 0`, `node : [Pte; 0]`
    # and a leaf count past `u128` all say **`N040`: `W` names no type** at a declaration
    # three lines above -- two of the three being ordinary typos, not corners.
    Mutation(
        "walkname-haengt-an-der-zahl",
        "umgebung.rs",
        "                            Traegerart::Walk => self.walknamen.contains(*k),",
        "                            Traegerart::Walk => self.walkschranken.contains_key(*k),",
        "W16 -- the existence of a `walk` TYPE is decided by the cost map again, so a "
        "declaration whose leaf count is 0 or past `u128` is reported as an unknown name",
    ),
    # **THE OTHER FOUR DOMAIN BOUNDS, one mutation each** (2026-08-31).
    #
    # `walkschranke-wieder-ein-pfad` above puts back the historic error of ONE domain. The
    # sentence `kosten.domaenenschranke` speaks about five, and its own reservation says so:
    # *"Every other domain bound in this pass has exactly the same shape and exactly as
    # little checking."* These four close that sentence.
    #
    # **Each one is an OFF-BY-ONE and not a removal, and that is the whole point.** A bound
    # that is GONE is already refused by `K003` and caught by two poison probes since long
    # ago. A bound that is WRONG is what the 2 048 against 512^4 was -- present, plausible,
    # and seven orders of magnitude short. *The probe reads the number out of the `K001`
    # text, so one off is enough to part the readings.*
    Mutation(
        "count-schranke-um-eins-daneben",
        "domaene.rs",
        "            .map(|n| n as i128)",
        "            .map(|n| n as i128 - 1)",
        "K001 -- the bound of `slots of` and of `index into T` is the table's `count` minus "
        "one, so the last slot costs nothing",
    ),
    Mutation(
        "elems-schranke-um-eins-daneben",
        "domaene.rs",
        "                return Some(*n as i128);",
        "                return Some(*n as i128 - 1);",
        "K001 -- the bound of `elems of` is the array length minus one; same class as "
        "`elems-laesst-den-letzten-aus` in the emitter, one layer up",
    ),
    Mutation(
        "queue-schranke-um-eins-daneben",
        "domaene.rs",
        "                gefunden = laenge.map(|n| n as i128);",
        "                gefunden = laenge.map(|n| n as i128 - 1);",
        "K001 -- the bound of `queue` is the single field array minus one, so a full queue "
        "costs less than it runs",
    ),
    # **This one is NOT an off-by-one, because the read path itself is what is unmeasured.**
    # `index into T` names its table in the TYPE, and until 2026-08-17 nobody read it -- no
    # example had ever triggered the site, since the corpus carries `descendants of` only
    # inside predicates, where no cost pass runs. *A bound never triggered is not covered,
    # it is unbreakable.* With the guard gone the bound is missing, and `K003` takes over --
    # which is exactly what it looked like before the site was found.
    Mutation(
        "index-into-tabelle-verloren",
        "domaene.rs",
        '            crate::typen::Typ::Benannt { ref name, .. } if name.starts_with("index into ") => {',
        '            crate::typen::Typ::Benannt { ref name, .. } if false && name.starts_with("index into ") => {',
        "K001 -- an `index into T` no longer names its table, so a `traverse` over it has "
        "no bound and falls back to `K003`",
    ),
    # -- domaene.rs: die KETTENkante (2026-08-31) ----------------------------------------
    #
    # `chain(a, b) in` is the one domain that names its edge AT THE WALK, and until this day
    # nobody read the two names. **Three rules, three mutations** -- and each of them is the
    # state the checker was in yesterday, so a survivor here would say the rule went back to
    # where it came from. `messung/DOMAENENNAMEN.md`.
    Mutation(
        "kettenkante-nimmt-irgendein-feld",
        "domaene.rs",
        "    let Some((_, typ)) = felder.iter().find(|(n, _)| *n == kante.text) else {",
        "    let Some((_, typ)) = felder.iter().find(|(n, _)| *n == kante.text)"
        ".or(felder.first()) else {",
        "D014 -- a chain edge that names no field silently takes the FIRST slot field "
        "instead, so `chain(gibtsnicht, auchnicht)` stands again",
    ),
    Mutation(
        "kettenkante-braucht-kein-ende",
        "domaene.rs",
        '    let Some(ziel) = name.strip_prefix("option index into ") else {',
        '    let Some(ziel) = name.strip_prefix("option index into ").or(Some(kurz)) else {',
        "D015 -- a chain edge no longer has to be `option index into`, so a `bool` is an "
        "edge again and a chain has no end",
    ),
    Mutation(
        "kettenkante-darf-hinaus",
        "domaene.rs",
        "    if kurzname(ziel) != kurz {",
        "    if false && kurzname(ziel) != kurz {",
        "D016 -- a chain edge may point into a FOREIGN table, so the walk leaves its own "
        "table at the first step",
    ),
    Mutation(
        "index-erbt-nicht",
        "umgebung.rs",
        "                    .find_map(|k| self.kapazitaeten.get(&k).copied())\n"
        "                    .map(|n| IntBereich::genau(32, false, 0, n as i128 - 1 + sonderwert))",
        "                    .find_map(|k| self.kapazitaeten.get(&k).copied())\n"
        "                    .map(|_| IntBereich::voll(32, false))",
        "A3 -- `index into T` erbt die Schranke aus `count` nicht",
    ),
    # **«C1», 2026-08-19.** `option index into T` reicht bis `N`, `index into T` bis `N-1` --
    # der Unterschied IST der Sonderwert. Ohne ihn ist ein Optionswert von einem gueltigen
    # Index nicht zu unterscheiden, und `h.slots[frei]` greift einen Slot hinter das Feld.
    Mutation(
        "option-ohne-sonderwert",
        "umgebung.rs",
        "                let sonderwert = i128::from(*optional);",
        "                let sonderwert = 0;",
        "der Bereich eines `option index into T` enthaelt den Sonderwert nicht mehr",
    ),
    Mutation(
        "rumpf-egal",
        "wirkungen.rs",
        "    for (ort, span) in &taten.schreibt {",
        "    for (ort, span) in &taten.schreibt[..0] {",
        "E005 -- der Rumpf darf jede Wirkungsliste ueberschreiten",
    ),
    Mutation(
        "sperre-egal",
        "wirkungen.rs",
        "    for (ort, span, geteilt) in &taten.sperrt {",
        "    for (ort, span, geteilt) in &taten.sperrt[..0] {",
        "E006 -- ein `locks`-Block braucht keine erklaerte Sperre",
    ),
    Mutation(
        "erzeuger-zeigt-auf-den-falschen-typ",
        "emit.rs",
        "                _ if u.tabellen.iter().any(|x| *x == n) => n,",
        '                _ if u.tabellen.iter().any(|x| *x == n) => "uint32_t".into(),',
        "C-Emission -- ein Pfad auf eine Tabelle wird wieder `uint32_t` statt der Struktur",
        "code",
    ),
    Mutation(
        # **Die Lizenzbedingung.** LIZENZ-ZUSATZ.md knuepft die zusaetzliche Erlaubnis an
        # den Hinweis im erzeugten C. Eine Bedingung, die niemand prueft, ist eine Bitte.
        "erzeuger-ohne-lizenzhinweis",
        "emit.rs",
        "/* Generated by Gabbro -- https://github.com/SimonVitzethum/Gabbro",
        "/* generated",
        "C-Emission -- der Lizenzhinweis faellt aus dem erzeugten C",
        "code",
    ),
    Mutation(
        "vorfahren-ohne-schranke",
        "domaene.rs",
        '            | Domaene::VorfahrenVon(o)\n',
        '',
        "K003 -- `ancestors of` erbt die Schranke von `descendants of` nicht mehr",
    ),
    Mutation(
        # **Die Luecke, die der Bau von `ancestors of` aufgedeckt hat**, und sie lag bei
        # `descendants of` schon vorher: der Tabellenname aus `index into T` ist
        # unqualifiziert, die Kapazitaetentabelle schluesselt qualifiziert.
        "indextyp-nennt-seine-tabelle-nicht",
        "domaene.rs",
        '            crate::typen::Typ::Benannt { ref name, .. } if name.starts_with("index into ") => {',
        '            crate::typen::Typ::Benannt { ref name, .. } if name.starts_with("XXindex into ") => {',
        "K003 -- ein `index into T` benennt seine Tabelle nicht mehr",
    ),
    Mutation(
        "rangordnung-egal",
        "geteilt.rs",
        '            let Some(alt) = alt else { continue };\n            if *alt >= neu {\n                absagen.schiebe(\n                    Absage::fehler(\n                        "H006",',
        '            let Some(alt) = alt else { continue };\n            if false && *alt >= neu {\n                absagen.schiebe(\n                    Absage::fehler(\n                        "H006",',
        "H006 -- die Sperrordnung darf absteigen",
    ),
    Mutation(
        # **Die lockernde Fassung**, und sie ist die wahrscheinlichere: gleicher Rang gilt
        # als in Ordnung. Zwei Sperren desselben Rangs haben aber keine Ordnung -- wer sie
        # verschachtelt, kann es in zwei Richtungen tun, und genau daraus entsteht die
        # Verklemmung.
        "rangordnung-gleich-erlaubt",
        "geteilt.rs",
        '            let Some(alt) = alt else { continue };\n            if *alt >= neu {\n                absagen.schiebe(\n                    Absage::fehler(\n                        "H006",',
        '            let Some(alt) = alt else { continue };\n            if *alt > neu {\n                absagen.schiebe(\n                    Absage::fehler(\n                        "H006",',
        "H006 -- gleicher Rang gilt als Ordnung",
    ),
    Mutation(
        "gruppe-invariante-egal",
        "gruppe.rs",
        "            if treffer.len() < 2 {",
        "            if treffer.len() < 0 {",
        "U007 -- eine Gruppen-Invariante darf einen einzigen Traeger nennen",
    ),
    Mutation(
        "gruppe-austritt-egal",
        "gruppe.rs",
        "                    for e in &ev[i..j] {",
        "                    for e in &ev[i..i] {",
        "U006 -- ein Austritt im Zwischenzustand faellt nicht auf",
    ),
    Mutation(
        # **Die lockernde Fassung**: nur `return` gilt als Austritt. `let … else` -- die
        # einzige Fehlerfortpflanzung der Sprache und der stillste der drei Wege hinaus --
        # rutscht durch. Genau die Fassung, die jemand schreibt, der an `return` denkt.
        "gruppe-austritt-nur-return",
        "gruppe.rs",
        '                aus.push(Ereignis::Austritt("let … else", s.span));',
        "                let _ = s.span;",
        "U006 -- `let … else` ist kein Austritt",
    ),
    Mutation(
        "gruppe-abdruck-egal",
        "gruppe.rs",
        "            if !fehlend.is_empty() {",
        "            if false && !fehlend.is_empty() {",
        "U003 -- zwei Traeger einer Gruppe schreiben und nur eine Sperre halten",
    ),
    Mutation(
        # **Die lockernde Fassung**: es genuegt, IRGENDEINE Sperre der Gruppe zu halten.
        # Genau die Fassung, die ein Mensch schreiben wuerde, der die Ordnung fuer
        # nebensaechlich haelt -- und die V4 nicht faengt.
        "gruppe-eine-reicht",
        "gruppe.rs",
        "                    if !hier.contains(s) && !fehlend.contains(s) {",
        "                    if hier.is_empty() && !fehlend.contains(s) {",
        "U003 -- eine gehaltene Sperre deckt die ganze Gruppe",
    ),
    Mutation(
        "lesen-egal",
        "wirkungen.rs",
        "    for (ort, span) in &taten.liest {",
        "    for (ort, span) in &taten.liest[..0] {",
        "E010 -- der Rumpf darf jede Stelle lesen, ohne sie zu nennen (Lesart A)",
    ),
    Mutation(
        # **Die gefaehrlichere der beiden**, weil sie nicht abschaltet, sondern LOCKERT:
        # jedes Lesen gilt als gedeckt, sobald IRGENDEINE `reads`-Zeile dasteht. Eine
        # Funktion mit `reads a` duerfte dann `b` lesen -- und die Absage bleibt still.
        "lesen-praefixlos",
        "wirkungen.rs",
        "        if !leserechte.iter().any(|e| deckt(e, ort)) {",
        "        if leserechte.is_empty() {",
        "E010 -- eine `reads`-Zeile deckt jede andere Stelle mit",
    ),
    Mutation(
        "modul-egal",
        "umgebung.rs",
        "    pub fn funktion(&self, von: &str, pfad: &Pfad) -> Option<&Signatur> {\n"
        "        self.suche(&self.funktionen, von, &pfad.text())",
        # **Deterministisch**: die HashMap-Reihenfolge ist es nicht, und eine Mutation, die
        # mal den richtigen und mal den falschen Eintrag trifft, ueberlebt zufaellig.
        # Sortiert und der letzte Treffer -- so faellt die Wahl immer gleich aus.
        "    pub fn funktion(&self, von: &str, pfad: &Pfad) -> Option<&Signatur> {\n"
        "        let _ = von;\n"
        "        let kurz = kurzname(&pfad.text()).to_string();\n"
        "        let mut treffer: Vec<&String> = self\n"
        "            .funktionen\n            .keys()\n"
        "            .filter(|k| kurzname(k) == kurz)\n            .collect();\n"
        "        treffer.sort();\n"
        "        return treffer.last().and_then(|k| self.funktionen.get(*k));\n"
        "        #[allow(unreachable_code)]\n"
        "        self.suche(&self.funktionen, von, &pfad.text())",
        "U11 -- Signaturen werden wieder nach blankem Namen aufgeloest",
    ),
    Mutation(
        "kosten-egal",
        "kosten.rs",
        '                z.gerechnet += 1;\n                if n > zusage {',
        '                z.gerechnet += 1;\n                if false && n > zusage {',
        "K001 -- ein Rumpf darf jede Kostenzusage ueberschreiten",
    ),
    Mutation(
        "haltezeit-egal",
        "kosten.rs",
        "                        if n > *zusage {",
        "                        if false && n > *zusage {",
        "K002 -- ein `locks`-Block darf seine `held`-Zusage ueberschreiten",
    ),
    Mutation(
        "haltezeit-darf-symbolisch-sein",
        "kosten.rs",
        "                    None => absagen.schiebe(haltezeit_ist_keine_zahl(l, wort, h.span)),",
        "                    None => {}",
        "K010 -- eine `held`-Zusage darf wieder ein Symbol sein, faellt damit aus der Karte "
        "und schaltet `K002` still ab. Genau der Zustand vom 2026-08-20: 0 Fehler ueber "
        "einer unbewachten Sperre",
    ),
    Mutation(
        "traversierung-kostenlos",
        "kosten.rs",
        '                (Kosten::Zahl(rumpf), Some(n)) => Kosten::Zahl(rumpf).mal(n, Some(t.span)),',
        '                (Kosten::Zahl(rumpf), Some(_)) => Kosten::Zahl(rumpf),',
        "eine Traversierung zaehlt nicht Rumpfkosten x Domaenenschranke",
    ),
    Mutation(
        "pure-neben-allem",
        "wirkungen.rs",
        "    if w.liste.len() > 1 {",
        "    if false && w.liste.len() > 1 {",
        "E002 -- `pure` darf neben jeder anderen Wirkung stehen",
    ),
    # -- geteilt.rs: die geteilte Sperrnahme, aus dem Papiertest vom 2026-08-14 ----------
    Mutation(
        "geteilt-darf-schreiben",
        "geteilt.rs",
        "        let Some(platz) = sp.schuetzt.iter().find(|p| beruehrt(p, &ort)) else {\n"
        "            continue;\n        };",
        "        let Some(platz) = sp.schuetzt.iter().find(|p| beruehrt(p, &ort) && false) else {\n"
        "            continue;\n        };",
        "H001 -- unter geteilter Sperre darf geschrieben werden (die tragende Regel)",
    ),
    Mutation(
        "geteilt-braucht-keine-zahl",
        "geteilt.rs",
        "                        Some(sp) if !sp.hat_geteilte_zeit => absagen.schiebe(",
        "                        Some(sp) if !sp.hat_geteilte_zeit && false => absagen.schiebe(",
        "H002 -- geteilt nehmen ohne `shared held`; die Latenzaussage verliert ihren Zweig",
    ),
    Mutation(
        "hochstufung-ist-erlaubt",
        "geteilt.rs",
        "                    if offen.contains(&name) {",
        "                    if false && offen.contains(&name) {",
        "H003 -- geteilt gehalten und exklusiv nachgenommen: der Deadlock faellt durch",
    ),
    Mutation(
        "luege-in-die-gefaehrliche-richtung",
        "wirkungen.rs",
        "        if !*geteilt && geteilte.iter().any(|e| deckt(e, ort)) {",
        "        if false && geteilte.iter().any(|e| deckt(e, ort)) {",
        "E007 -- exklusiv nehmen und geteilt erklaeren; der Aufrufer rechnet falsch",
    ),
    Mutation(
        "geteilte-haltezeit-egal",
        "kosten.rs",
        '                        (self.geteilte_haltezeiten, "shared held", "K004")',
        '                        (self.haltezeiten, "shared held", "K004")',
        "K004 -- die geteilte Haltezeit wird gegen die EXKLUSIVE Zahl geprueft",
    ),
    Mutation(
        "zeuge-an-der-aufrufgrenze-egal",
        "geteilt.rs",
        "        if *geteilt || !offen.iter().any(|o| o == sperre) {",
        "        if true || !offen.iter().any(|o| o == sperre) {",
        "H005 -- eine EXKLUSIVE Held-Forderung darf unter geteilter Nahme gerufen werden",
    ),
    Mutation(
        "staerke-des-zeugen-egal",
        "geteilt.rs",
        "        if *geteilt || !offen.iter().any(|o| o == sperre) {",
        "        if !offen.iter().any(|o| o == sperre) {",
        "H005 -- die Staerke des Zeugen entscheidet nicht mehr: auch `shared` faellt",
    ),
    Mutation(
        "divergenz-endet-nicht",
        "schleifen.rs",
        '    if lg.div.iter().any(|d| *d == a.text) {',
        '    if false && lg.div.iter().any(|d| *d == a.text) {',
        "S002 -- ein `else`-Zweig, der auf einem `-> never`-Aufruf endet, gilt als durchfallend",
    ),
    Mutation(
        "alles-divergiert",
        "schleifen.rs",
        "            if nie || div {",
        "            if true {",
        "S002 -- JEDE Funktion gilt als divergierend, also endet jeder Zweig",
    ),
    Mutation(
        "paarung-je-funktion",
        "paarung.rs",
        '    let alle_erwartet: BTreeSet<(String, String)> = je_funktion\n        .iter()\n',
        '    let alle_erwartet: BTreeSet<(String, String)> = je_funktion\n        .iter()\n        .take(1)\n',
        "V001 -- die Paarung sieht nur die EIGENE Funktion, nicht die vereinigte Menge",
    ),
    Mutation(
        "verwaistes-awaits-egal",
        "paarung.rs",
        '            if !alle_publiziert.contains(&(at.clone(), o.clone())) {',
        '            if false && !alle_publiziert.contains(&(at.clone(), o.clone())) {',
        "V002 -- ein `awaits` ohne Gegenstueck darf stehen (liest gueltigen Muell)",
    ),
    Mutation(
        "relaxed-darf-tragen",
        "paarung.rs",
        '        for (o, span, erklaert) in &h.relaxed_mit_last {',
        '        for (o, span, erklaert) in h.relaxed_mit_last.iter().take(0) {',
        "V004 -- `relaxed` darf eine Nutzlast tragen, die es nicht ordnet",
    ),
    Mutation(
        "kein-tor-wird-gebunden",
        "paarung.rs",
        '                if o.suffixe.is_empty() && l.lastfrei.contains(&o.basis.text) {',
        '                if false && l.lastfrei.contains(&o.basis.text) {',
        "V009 -- keine schlichte Atomlesung gilt mehr als Tor, also findet der Finder "
        "keine fehlende Paarung mehr",
    ),
    Mutation(
        "fremder-schreiber-egal",
        "paarung.rs",
        '            if wer.iter().any(|w| erreichbar.contains(w)) {',
        '            if true {',
        "V010 -- die Nutzlast darf von einem Schreiber kommen, den der Veroeffentlicher "
        "nie erreicht",
    ),
    Mutation(
        "linear-darf-fallen",
        "m2.rs",
        "                (Zustand::Lebt, true) => absagen.schiebe(",
        "                (Zustand::Verbraucht, true) => absagen.schiebe(",
        "L101 -- ein linearer Wert unter `consumes` darf fallengelassen werden (affin statt linear)",
    ),
    Mutation(
        "geliehenes-darf-sterben",
        "m2.rs",
        "                (Zustand::Verbraucht, false) => absagen.schiebe(",
        "                (Zustand::Lebt, false) => absagen.schiebe(",
        "L102 -- ein geliehener Wert darf verbraucht werden",
    ),
    Mutation(
        "zweige-duerfen-abweichen",
        "m2.rs",
        "        if uneins {",
        "        if false && uneins {",
        "L103 -- die Zweige duerfen einen linearen Wert verschieden behandeln",
    ),
    Mutation(
        "doppelverbrauch-egal",
        "m2.rs",
        "            if *z == Zustand::Verbraucht {\n                absagen.schiebe(\n                    Absage::fehler(\n                        \"L104\",",
        "            if false {\n                absagen.schiebe(\n                    Absage::fehler(\n                        \"L104\",",
        "L104 -- ein linearer Wert darf zweimal verbraucht werden",
    ),
    Mutation(
        "schreiben-ohne-recht-egal",
        "m3.rs",
        "    if !z.darf_schreiben() {",
        "    if false && !z.darf_schreiben() {",
        "R002 -- ein `r`-Zeiger darf beschrieben werden",
    ),
    Mutation(
        "lesen-ohne-recht-egal",
        "m3.rs",
        "    if !z.darf_lesen() {",
        "    if false && !z.darf_lesen() {",
        "R003 -- ein `w`-Zeiger darf gelesen werden",
    ),
    Mutation(
        "ops-traeger-darf-in-dma",
        "m3.rs",
        "                if z.raum == Raum::Dma {",
        "                if false && z.raum == Raum::Dma {",
        "R001 -- ein `ops`-Traeger darf im `dma`-Raum liegen (das Geraet umgeht die Grammatik)",
    ),
    Mutation(
        "eigen-darf-alles-nicht",
        "m3.rs",
        "            .any(|r| matches!(r, Recht::Schreiben | Recht::LesenSchreiben | Recht::Eigen(_)))",
        "            .any(|r| matches!(r, Recht::Schreiben | Recht::LesenSchreiben))",
        "R002 -- `own` traegt kein Schreibrecht mehr (falscher Alarm an jedem own-Zeiger)",
    ),
    Mutation(
        "by-ops-egal",
        "kbedingung.rs",
        "                    if text.split(['.', '[']).any(|x| x == feld) {",
        "                    if false && text.split(['.', '[']).any(|x| x == feld) {",
        "D002 -- ein `by ops`-Feld darf von Hand geschrieben werden (B29 wieder schreibbar)",
    ),
    Mutation(
        "by-ops-trifft-alles",
        "kbedingung.rs",
        "                    if text.split(['.', '[']).any(|x| x == feld) {",
        "                    if true {",
        "D002 -- `by ops` trifft JEDES Feld (falscher Alarm an jedem Nachbarfeld)",
    ),
    # -- schablonen.rs: die Ratsche ------------------------------------------------------
    #
    # **565 Zeilen ohne eine einzige Mutation, bis zum 2026-08-17.** Damit war die groesste
    # unbeschaedigbare Flaeche des Pruefers ausgerechnet die, auf der das ganze
    # Amortisierungsargument ruht -- und in ihr war ZAHN 2 seit dem 16.8. stumpf, ohne dass
    # ein Test es haette sagen koennen. *Eine Ratsche, die niemand beschaedigen kann, ist
    # eine Zusage.*
    Mutation(
        "ratsche-zahn-eins-stumpf",
        "schablonen.rs",
        "        .filter(|s| s.fundstelle.trim().is_empty())",
        "        .filter(|_s| false)",
        "RATSCHE Zahn 1 -- ein Eintrag ohne Fundstelle faellt nicht mehr auf",
        "schablone",
    ),
    Mutation(
        "ratsche-zahn-zwei-stumpf",
        "schablonen.rs",
        "pub fn marke_gerissen_in(liste: &[Schablone]) -> bool {\n    liste.len() > zulaessig_in(liste)",
        "pub fn marke_gerissen_in(liste: &[Schablone]) -> bool {\n    let _ = liste;\n    false",
        "RATSCHE Zahn 2 -- das Register darf beliebig wachsen (der Fehler vom 16.8.)",
        "schablone",
    ),
    Mutation(
        "ein-beweis-kauft-alles",
        "schablonen.rs",
        "    MARKE_OHNE_BEWEIS + bewiesen_in(liste)",
        "    if bewiesen_in(liste) > 0 { usize::MAX } else { MARKE_OHNE_BEWEIS }",
        "RATSCHE Zahn 2 -- der erste Beweis hebt die Marke ganz auf statt um EINEN Platz",
        "schablone",
    ),

    # -- lib.rs: die Passliste -----------------------------------------------------------
    #
    # `SPRACHE.md` Teil III sagt: **die Spezifikation IST die Passliste.** Laeuft ein Pass
    # still nicht, ist die Spezifikation nicht durchgesetzt -- und bis zum 2026-08-17 konnte
    # das niemand bemerken: 241 Zeilen, 0 Mutationen.
    Mutation(
        "ein-pass-laeuft-nicht",
        "lib.rs",
        "    gruppe::pass(baum, absagen);",
        "    let _ = &gruppe::pass;",
        "Passliste -- Pass 10 (Gruppe) faellt still aus; U001-U007 schweigen",
    ),
    Mutation(
        "die-paarung-faellt-aus",
        "lib.rs",
        "    paarung::pass(baum, absagen);",
        "    let _ = &paarung::pass;",
        "Passliste -- Pass 7 (Paarung) faellt still aus; V001-V004 schweigen",
    ),
    # -- aufrufgraph.rs: 268 Zeilen, an denen DREI Posten haengen ------------------------
    #
    # `H005`, die Aufrufwirkungen (`E008`) und die Trennung an der Klasse *Phase* -- alle drei
    # ruhen auf einer transitiven Huelle, die bis zum 2026-08-17 keine einzige Mutation trug.
    # Die Huelle war geprueft; die SAMMELSEITE nicht: alle sieben Proben riefen ausschliesslich
    # auf der obersten Rumpfebene.
    Mutation(
        "huelle-bleibt-flach",
        "aufrufgraph.rs",
        '        lauf.pfad.insert(name.to_string());\n',
        '        lauf.pfad.insert(name.to_string());\n        if true {\n            return (k.eigen.iter().cloned().collect(), None, false);\n        }\n',
        "E008 -- `effects` deckt wieder nur die ERSTE Ebene",
    ),
    Mutation(
        "zyklus-schweigt",
        "aufrufgraph.rs",
        '            return (BTreeSet::new(), Some(format!("cycle over `{name}`")), true);',
        '            return (BTreeSet::new(), None, true);',
        "R16 -- ein Zyklus liefert eine untere Schranke und nennt sich nicht mehr so",
    ),
    Mutation(
        "privat-ist-oeffentlich",
        "namen.rs",
        "        if offen.get(ziel).copied().unwrap_or(true) {\n            return true;\n        }",
        "        if true {\n            return true;\n        }",
        "N025 -- `pub` ist wieder Zierde; ein privates Item kommt ueber die Modulgrenze",
    ),
    Mutation(
        "ungleichheit-verengt-nicht",
        "m1.rs",
        "                if wert == b.min {\n                    (wert + 1, i128::MAX)",
        "                if false {\n                    (wert + 1, i128::MAX)",
        "M104 -- eine Ungleichheit am unteren Rand verengt nicht mehr; `if n == 0 {…} n - 1` faellt wieder",
    ),
    Mutation(
        "ungleichheit-verengt-die-mitte",
        "m1.rs",
        "                } else {\n                    return None;\n                }\n            }\n            _ => return None,",
        "                } else {\n                    (wert + 1, i128::MAX)\n                }\n            }\n            _ => return None,",
        "M1 -- ein Loch in der MITTE gilt als untere Schranke; das ist UNSOUND, nicht bloss grob",
    ),
    Mutation(
        "restrict-auch-bei-zwei-zeigern",
        "emit.rs",
        "            if zeigerziel(&zq.ziel).as_deref() == Some(traeger.as_str()) {\n                return false;\n            }",
        "            if false && zeigerziel(&zq.ziel).as_deref() == Some(traeger.as_str()) {\n                return false;\n            }",
        "OPT1 -- `restrict` auch bei ZWEI Zeigern desselben Traegers; H2a des Satzes faellt, und das ist UB",
        flaeche="code",
    ),
    Mutation(
        "asm-ohne-arch-egal",
        "namen.rs",
        "        if f.arch.is_none() {",
        "        if false && f.arch.is_none() {",
        "A001 -- ein `asm`-Rumpf ohne `arch` kommt durch; auf einer anderen Maschine tut er still etwas anderes",
    ),
    Mutation(
        "asm-operand-frei",
        "namen.rs",
        "            if !f.parameter.iter().any(|p| p.name.text == n.text) {",
        "            if false && !f.parameter.iter().any(|p| p.name.text == n.text) {",
        "A004 -- ein `asm`-Operand darf wieder einen Namen nennen, den es nicht gibt",
    ),
    Mutation(
        "asm-nicht-volatile",
        "emit.rs",
        '        a2.push_str("    __asm__ __volatile__(\\n");',
        '        a2.push_str("    __asm__ (\\n");',
        "OPT3 -- der Assemblerblock verliert `__volatile__` und darf wegoptimiert werden",
        flaeche="code",
    ),
    Mutation(
        "until-praedikat-unsichtbar",
        "lib.rs",
        "            Schleife::Retry(r) => r.bis.iter().collect(),",
        "            Schleife::Retry(_) => Vec::new(),",
        "E008 -- ein Ruf im `until` einer `retry`-Schleife wird wieder unsichtbar",
    ),
    Mutation(
        "attribut-ohne-rufpruefung",
        "emit.rs",
        "    if ruft_irgendwas(b) {\n        return \"\";\n    }",
        "    if false && ruft_irgendwas(b) {\n        return \"\";\n    }",
        "OPT2 -- `pure` wird auch an eine Funktion gehaengt, die einen FREMDEN Rumpf ruft",
        flaeche="code",
    ),
    Mutation(
        "rahmen-endet-am-aufruf",
        "wirkungen.rs",
        "            if !weltnamen.iter().any(|k| k == grund) {\n                continue; // kein bekannter Weltzustand -- der Pass sagt nichts\n            }",
        "            if true {\n                continue; // kein bekannter Weltzustand -- der Pass sagt nichts\n            }",
        "E008 -- der Rahmen endet wieder an der Aufrufgrenze: `writes a` deckt jedes fremde `writes`",
    ),
    Mutation(
        "verbrauchen-deckt-nicht-mehr",
        "wirkungen.rs",
        '        if art == "writes" {',
        '        if false && art == "writes" {',
        "E008 -- `consumes X` deckt `writes X` nicht mehr; `consumes` stuende dann nie fuer sich",
    ),
    Mutation(
        "zweimal-own-egal",
        "m3.rs",
        "                if gesehen.iter().any(|g| *g == ort) {",
        "                if false && gesehen.iter().any(|g| *g == ort) {",
        "R004 -- zwei `own`-Parameter duerfen wieder denselben Ort bekommen",
    ),
    Mutation(
        "wachhund-ohne-namen-schweigt",
        "schleifen.rs",
        '        absagen.schiebe(\n            Absage::hinweis(\n                "S007",',
        '        if true {\n            return;\n        }\n        absagen.schiebe(\n            Absage::hinweis(\n                "S007",',
        "S007 -- der dritte Zustand schweigt wieder; ein unbekannter Wachhundname geht durch",
    ),
    Mutation(
        "gerufener-ohne-effects-egal",
        "aufrufgraph.rs",
        '        let mut offen = if k.hat_effects {\n            None\n        } else {\n            Some(format!("`{name}` declares no `effects`"))\n        };',
        '        let mut offen = None;',
        "E009 -- ein Gerufener ohne `effects` macht die Menge nicht mehr zur unteren Schranke",
    ),
    Mutation(
        "held-ist-immer-geteilt",
        "aufrufgraph.rs",
        "        PredArt::Held { sperre, geteilt, .. } => aus.push((sperre.text.clone(), *geteilt)),",
        "        PredArt::Held { sperre, geteilt, .. } => { let _ = geteilt; aus.push((sperre.text.clone(), true)) }",
        "H005 -- eine EXKLUSIVE Sperrforderung gilt als geteilt (der geteilte Block laesst sie durch)",
    ),
    Mutation(
        "match-zweige-unsichtbar",
        "lib.rs",
        '        StmtArt::Match(m) => m.zweige.iter().map(|z| &z.rumpf).collect(),',
        '        StmtArt::Match(m) => {\n            let _ = m;\n            Vec::new()\n        }',
        "E008 -- Rufe in `match`-Zweigen sind unsichtbar (delete_leaf ruft dort dreimal)",
    ),
    Mutation(
        "locks-block-versteckt-rufe",
        "lib.rs",
        '        StmtArt::Sperrt(x) => vec![&x.rumpf],',
        '        StmtArt::Sperrt(x) => {\n            let _ = x;\n            Vec::new()\n        }',
        "E008 -- ein `locks`-Block versteckt seine Rufe, und genau dort sitzt H005",
    ),
    Mutation(
        "schleifenrumpf-versteckt-rufe",
        "lib.rs",
        '        StmtArt::Schleife(sch) => vec![match sch.as_ref() {\n            Schleife::Traverse(x) => &x.rumpf,\n            Schleife::Retry(x) => &x.rumpf,\n            Schleife::Forever(x) => &x.rumpf,\n        }],',
        '        StmtArt::Schleife(sch) => match sch.as_ref() {\n            Schleife::Traverse(_) => Vec::new(),\n            Schleife::Retry(x) => vec![&x.rumpf],\n            Schleife::Forever(x) => vec![&x.rumpf],\n        },',
        "E008 -- ein `traverse`-Rumpf versteckt seine Rufe (revoke ruft dort delete_leaf)",
    ),
    Mutation(
        "some-ist-ein-ruf",
        "aufrufgraph.rs",
        '            // `Some`/`None` sind Konstruktoren, keine Aufrufe (s. «B35»).\n            if n.text != "Some" && n.text != "None" && !r.ist_verbundwert() {',
        '            // `Some`/`None` sind Konstruktoren, keine Aufrufe (s. «B35»).\n            if true {',
        "B35 -- `Some`/`None` gelten als unbekannte Gerufene; jede option-Huelle wird untere Schranke",
    ),
    # -- manifest.rs: die Ratsche, die als Vorbild zitiert wurde -------------------------
    #
    # `schablonen.rs` nennt die Axiomschicht als das Beispiel einer Ratsche, DIE ES SCHON
    # GIBT. Sie hatte bis zum 2026-08-17 keinen Test und keine Mutation -- also genau die
    # Lage, die dort ueber die Schablonen beklagt wird, eine Datei weiter. Und die erste
    # Probe fand sofort etwas: `gabbro annahmen beispiele/*.gab` meldete 15, wo 14 stehen.
    Mutation(
        "menge-ist-wieder-liste",
        "manifest.rs",
        "        match aus.iter().find(|a| a.name == e.name) {\n            None => aus.push(e),",
        "        match None::<&Eintrag> {\n            None => aus.push(e),",
        "SYNTAX.md §12 -- die Annahmenmenge zaehlt Duplikate wieder mit (15 statt 14)",
    ),
    Mutation(
        "widerspruch-schweigt",
        "manifest.rs",
        "                if vorher.art != e.art || vorher.klasse != e.klasse || vorher.aussage != e.aussage {",
        "                if false && (vorher.art != e.art || vorher.klasse != e.klasse || vorher.aussage != e.aussage) {",
        "SYNTAX.md §12 -- derselbe Name mit anderem Inhalt gilt als Duplikat statt als Widerspruch",
    ),
    Mutation(
        "annahme-im-modul-verloren",
        "manifest.rs",
        "            ItemArt::Modul(m) => sammle_items(&m.items, out),",
        "            ItemArt::Modul(m) => { let _ = m; }",
        "SYNTAX.md §12 -- eine Annahme in einem verschachtelten Modul faellt aus dem Manifest",
    ),
    Mutation(
        "nicht-falsifizierbar-ohne-grund",
        "manifest.rs",
        "        AnnahmeKlasse::NichtFalsifizierbar(t) => Klasse::NichtFalsifizierbar {\n            grund: t.text.clone(),\n        },",
        "        AnnahmeKlasse::NichtFalsifizierbar(t) => { let _ = t; Klasse::NichtFalsifizierbar {\n            grund: String::new(),\n        } },",
        "SYNTAX.md §12 -- `unfalsifiable` verliert seinen Grund; eine Annahme ohne Rechenschaft",
    ),

    # -- korpus.rs: der Schneider, an dem Tor P2 haengt -----------------------------------
    Mutation(
        "schneider-verliert-den-vorspann",
        "korpus.rs",
        "                inhalt = \"\\n\".repeat(nr);",
        "                inhalt = String::new();",
        "Tor P2 -- Absagen zeigen auf Zeilen, die es in der Markdown-Datei nicht gibt",
    ),
    Mutation(
        "eine-skizze-gilt-als-einheit",
        "korpus.rs",
        "    if !verworfen.leer() {\n        return false; // der Lexer stolpert -- das ist kein Programm, sondern eine Skizze",
        "    if false && !verworfen.leer() {\n        return false; //",
        "Tor P2 -- ein Ausschnitt mit `…` zaehlt als Uebersetzungseinheit (W9, falsche Richtung)",
    ),
    Mutation(
        "eine-einheit-faengt-mit-irgendwas-an",
        "korpus.rs",
        "        gabbro_syntax::lex::Art::Wort(k) => gabbro_syntax::parse::faengt_item_an(k),",
        "        gabbro_syntax::lex::Art::Wort(k) => { let _ = k; true }",
        "Tor P2 -- ein Block, der mit einer Anweisung anfaengt, gilt als Uebersetzungseinheit",
    ),
    # -- emit.rs: die Geistloeschung -----------------------------------------------------
    #
    # Sie sitzt an DREI Orten gleichzeitig -- Signatur, Rufort, `let`-Bindung -- und zwei der
    # drei Fehlformen sind still. Die gefaehrlichste ist die dritte: laesst man die ganze
    # `let`-Anweisung verschwinden statt nur ihrer Bindung, uebersetzt das C anstandslos und
    # der Bootschritt findet nicht statt. `pruefe-emission.sh` bekam in der Gegenprobe `6`
    # statt `123456`.
    Mutation(
        "geist-let-verschwindet-ganz",
        "emit.rs",
        "        StmtArt::Let(l) if geist_wert(&l.wert, u) => {\n            aus.push_str(&format!(\"{e}{};\\n\", ausdruck(&l.wert, u, absagen)))\n        }",
        "        StmtArt::Let(l) if geist_wert(&l.wert, u) => { let _ = l; }",
        "C-Absenkung -- eine Bindung an einen Geist nimmt den RUF mit; der Schritt entfaellt still",
        "code",
    ),
    Mutation(
        "geist-parameter-bleibt-stehen",
        "emit.rs",
        "        if ist_geist(&p.typ, u) {\n            continue; // erased -- see above\n        }",
        "        if false && ist_geist(&p.typ, u) {\n            continue;\n        }",
        "C-Absenkung -- ein Geistparameter steht im C und braucht eine Darstellung, die es nicht gibt",
        "code",
    ),
    Mutation(
        "geist-rueckgabe-bleibt-stehen",
        "emit.rs",
        "        Some(t) if ist_geist(t, u) => \"void\".into(),",
        "        Some(t) if false && ist_geist(t, u) => \"void\".into(),",
        "C-Absenkung -- ein Geistrueckgabetyp wird abgesenkt statt geloescht",
        "code",
    ),
    Mutation(
        "ruf-behaelt-die-geistargumente",
        "emit.rs",
        "        .filter(|(i, _)| !geist.as_ref().is_some_and(|g| *g.get(*i).unwrap_or(&false)))",
        "        .filter(|(i, _)| { let _ = i; true })",
        "C-Absenkung -- der Rufort uebergibt einen Geist, den es zur Laufzeit nicht gibt",
        "code",
    ),
    # -- «B26»: `return e;` -- the bound reason, and the channel it goes out through -------
    #
    # Three passes were wrong about one shape at once (2026-08-30), and the first two were
    # HIDING the third: `M119` refused the program before the emitter ever saw it, so the
    # miscompile below stood behind a guard nobody had asked for. *An accident that holds is
    # indistinguishable from a rule until it stops.*
    # **The first version of this mutation was INVALID**, in the same silent way as
    # the body-channel one earlier that day (its name carries a German function word, so it
    # cannot be quoted in a comment here): it put `if false` on the `match` arm, which
    # left the `match` no longer exhaustive (`E0004`). The tree did not compile, the run
    # counted the mutation OUT OF THE DENOMINATOR, and 344 of 344 read like completeness.
    # *An invalid mutation is a shrunken population.*
    #
    # The arm stands now and yields `None` -- exactly the state before the repair: `e` at the
    # fallible register unbound, `M119` says so, and `return e;` never reaches the emitter.
    #
    # (Translated from German on 2026-08-30, and it is a HEAL and not a rewrite: `instrumente/`
    # carries English comments by CLAUDE.md, and these eight lines had pushed `MARKE_PY` from
    # 1072 to 1080 without the mark being moved. The ratchet arrived red at `master`.)
    Mutation(
        "grundbindung-am-register-faellt-weg",
        "m1.rs",
        "                            let t = crate::m3::ort_register(o, &self.geraete, &self.griffe)?;",
        "                            let t = crate::m3::ort_register(o, &self.geraete, &self.griffe).filter(|_| false)?;",
        "M1 -- `e` am fehlbaren Register bleibt ungebunden; `M119` sagt es, und `return e;` erreicht den Erzeuger nie",
        "pruefer",
    ),
    Mutation(
        "n034-sieht-nur-den-geschriebenen-grund",
        "namen.rs",
        "                        if o.suffixe.is_empty() && gebunden.iter().any(|n| *n == o.basis.text) {",
        "                        if false && o.suffixe.is_empty() && gebunden.iter().any(|n| *n == o.basis.text) {",
        "N034 -- ein Rumpf, der seinen Grund ueber die Bindung zurueckgibt, gilt als einer, der nie scheitert",
        "pruefer",
    ),
    Mutation(
        "gebundener-grund-geht-durch-den-erfolgskanal",
        "emit.rs",
        "                        \"{e}*_grund = {};\\n{e}return false;\\n\",\n"
        "                        ausdruck(x, u, absagen)\n"
        "                    ));\n"
        "                }\n"
        "                // **`return None` / `return Some(i)`**",
        "                        \"{e}*_wert = {};\\n{e}return true;\\n\",\n"
        "                        ausdruck(x, u, absagen)\n"
        "                    ));\n"
        "                }\n"
        "                // **`return None` / `return Some(i)`**",
        "C-Absenkung -- der gebundene Grund geht durch `*_wert` mit `true`: das Geraet log, und das C meldet Erfolg",
        "code",
    ),
    Mutation(
        "fremder-tag-ohne-vorwaertsdeklaration",
        "emit.rs",
        "        for f in &namen.fremde {\n            aus.push_str(&format!(\"struct {f};\\n\"));\n        }",
        "        for f in &namen.fremde {\n            let _ = f;\n        }",
        "C-Absenkung -- der Tag steht erst in der Parameterliste; seine Sichtbarkeit endet am Semikolon",
        "code",
    ),
    # -- emit.rs: die drei OFFENEN Ausfaelle ----------------------------------------------
    #
    # Der ganze Entwurf des Erzeugers ist "weigere dich beim Namen statt zu raten" -- und davon
    # gab es bis zum 2026-08-17 drei Ausnahmen, alle drei uebersetzbar, zwei davon still
    # falsch. Gefunden am Korpus, dieselbe Klasse wie der Tabellenzeiger vom Vortag.
    # `option-wird-vergroebert` stand hier vom Vormittag des 2026-08-17 bis zum Nachmittag
    # desselben Tages. **Sie ist mitsamt ihrer Regel entfallen**: die Absage, die sie
    # beschaedigte, gibt es nicht mehr, weil F8 die Darstellung entschieden hat. Ihre Sorge
    # traegt jetzt `sonderwert-ist-null` -- dieselbe Frage, andere Form. *Eine Mutation geht
    # nur mit ihrer Regel, nicht durch Umformulierung.*
    Mutation(
        "ausdruck-faellt-offen-auf-null",
        "emit.rs",
        # **Der Anker ist am 2026-08-21 umgezogen, und der Umzug ist der Befund.** Er stand
        # auf `_ => { weigere(…, "expression form") }` -- dem Sammelzweig, der drei Formen
        # unter EINEM Satz zusammenzog. Der Zweig ist ausgeschrieben; die Mutation zeigt
        # jetzt auf `old(place)`, weil dort die Probe steht.
        "        ExprArt::Alt(_) => {\n"
        "            weigere(\n"
        "                absagen,\n"
        "                e.span,\n"
        "                \"`old(place)` outside a compare-exchange",
        "        ExprArt::Alt(_) => {\n"
        "            let _ = absagen;\n"
        "            return \"0\".into();\n"
        "            #[allow(unreachable_code)]\n"
        "            weigere(\n"
        "                absagen,\n"
        "                e.span,\n"
        "                \"`old(place)` outside a compare-exchange",
        "C-Absenkung -- eine unbekannte Ausdrucksform wird zu null statt abgelehnt",
        "code",
    ),
    Mutation(
        "option-konstruktor-wird-ein-ruf",
        "emit.rs",
        "    if name == \"Some\" || name == \"None\" {",
        "    if false && (name == \"Some\" || name == \"None\") {",
        "C-Absenkung -- `None` wird als Ruf `None()` ausgegeben; dass -Werror ihn faengt, ist Glueck",
        "code",
    ),
    # -- emit.rs: F8 -- Sonderwert, Sperre, Austritt ---------------------------------------
    #
    # Drei Absenkungen, die keine Uebersetzungen sind sondern Entscheidungen. Die dritte ist
    # die, gegen die C8 bezahlt hat: ein Rueckkehrpfad aus einem `locks`-Block, der die Sperre
    # stehen laesst -- und das C uebersetzt anstandslos.
    Mutation(
        "sperre-bleibt-beim-return-liegen",
        "emit.rs",
        "            for freigabe in austritt.freigaben.iter().rev() {\n                aus.push_str(&format!(\"{e}{freigabe};\\n\"));\n            }",
        "            for freigabe in austritt.freigaben.iter().rev() {\n                let _ = freigabe;\n            }",
        "C-Absenkung -- ein `return` aus einem `locks`-Block laesst die Sperre stehen (C8)",
        "code",
    ),
    Mutation(
        "sonderwert-ist-null",
        "emit.rs",
        "            aus.push_str(&format!(\"#define {}_NONE ({})\\n\", t.name.text, laenge));",
        "            aus.push_str(&format!(\"#define {}_NONE (0*{})\\n\", t.name.text, laenge));",
        "C-Absenkung -- der Sonderwert kollidiert mit Slot 0; `None` und der erste Eintrag sind gleich",
        "code",
    ),
    Mutation(
        "sperre-ohne-prototypen",
        "emit.rs",
        "            aus.push_str(&format!(\n                \"\\nvoid {n}_nimm(void);\\nvoid {n}_gib(void);\\n\",\n                n = l.name.text\n            ));",
        "            let _ = &l.name;",
        "C-Absenkung -- eine Sperre wird genommen, ohne dass ihr Primitiv erklaert ist",
        "code",
    ),
    Mutation(
        "match-bindet-den-index-nicht",
        "emit.rs",
        "        aus.push_str(&format!(\"{e}        uint32_t {} = {hilf};\\n\", b.text));",
        "        let _ = b;",
        "C-Absenkung -- der `Some`-Zweig bekommt seinen Index nicht gebunden",
        "code",
    ),
    Mutation(
        "toter-parameter-bleibt-laut",
        "emit.rs",
        "            aus.push_str(&format!(\"    (void){};\\n\", p.name.text));",
        "            let _ = &p.name;",
        "C-Absenkung -- ein ungelesener Parameter laesst `cc -Wextra` das Erzeugnis ablehnen",
        "code",
    ),
    Mutation(
        "zuweisungsoperator-egal",
        "emit.rs",
        "            zuw_op(&z.op),",
        "            { let _ = &z.op; \"=\" },",
        "C-Absenkung -- `x += 1` wird `x = 1`; der Operator stand im Baum und wurde nicht angesehen",
        "code",
    ),
    Mutation(
        "narrow-schranke-inklusiv",
        "emit.rs",
        '            let oben = if bereich.exklusiv { "<" } else { "<=" };',
        '            let oben = "<=";',
        "code",
    ),
    Mutation(
        "narrow-prueft-nicht",
        "emit.rs",
        "            aus.push_str(&format!(\"{e}if (!({bedingung})) {{\\n\"));",
        "            aus.push_str(&format!(\"{e}if (0) {{ /* {bedingung} */\\n\"));",
        "C-Absenkung -- der `else`-Zweig eines `narrow` kann nie genommen werden",
        "code",
    ),
    Mutation(
        "never-ist-gewoehnlich",
        "emit.rs",
        "        Some(TypExpr::Never(_)) => \"_Noreturn void\".into(),",
        "        Some(TypExpr::Never(_)) => \"void\".into(),",
        "C-Absenkung -- eine nicht zurueckkehrende Funktion sieht fuer den C-Uebersetzer durchfallend aus",
        "code",
    ),
    # -- emit.rs: `retry` und `format` (F10) -----------------------------------------------
    Mutation(
        "budget-ist-schleifenzaehler",
        "emit.rs",
        "                    if c > 0 && n / c > 0 {\n                        aus.insert(r.span.von, n / c);",
        "                    if c > 0 && n > 0 {\n                        aus.insert(r.span.von, n);",
        "C-Absenkung -- `bounded N ops` wird als Durchgangszahl gelesen statt als Operationsbudget",
        "code",
    ),
    Mutation(
        "on-exceeded-darf-zurueckkehren",
        "emit.rs",
        # **Der Anker war seit dem 2026-08-20 MEHRDEUTIG** -- `forever` prueft dieselbe
        # Zusage. Der Ankerpruefer hat es gesagt, bevor der Lauf lief; er zeigt jetzt auf den
        # `retry`-Fall, den die Zeile darueber eindeutig macht.
        "    let ausgang = &r.bei_ueberschreitung.text;\n"
        "    if !u.funktionen.get(ausgang).is_some_and(|s| s.nie_rueck) {",
        "    let ausgang = &r.bei_ueberschreitung.text;\n"
        "    if false && !u.funktionen.get(ausgang).is_some_and(|s| s.nie_rueck) {",
        "C-Absenkung -- `on_exceeded` darf auf etwas zeigen, das zurueckkehrt; die Schleife dreht weiter",
        "code",
    ),
    # -- Die Emission vom 2026-08-20 ------------------------------------------------------
    #
    # Sieben Entscheidungen und fuenf Erzeugerfehler, und **ohne diese Mutationen waere die
    # neue Flaeche unbeschaedigbar**. Was 0 Mutationen hat, ist nicht gedeckt.
    Mutation(
        "baumkante-laeuft-am-elter-hinunter",
        "emit.rs",
        "if (!{h} && {basis}[{k}].{kind} != {n}u) {{ {k} = {basis}[{k}].{kind}; {h} = false; continue; }}",
        "if (!{h} && {basis}[{k}].{elter} != {n}u) {{ {k} = {basis}[{k}].{elter}; {h} = false; continue; }}",
        "C-Absenkung -- der Abstieg laeuft an `parent` statt an `child`; «B41b» nennt drei Kanten, und welche wohin geht, ist die ganze Aussage",
        "code",
    ),
    Mutation(
        "wurzel-ist-ihr-eigener-nachfahre",
        "emit.rs",
        "if ({k} == {r}) break;",
        "if (0 && {k} == {r}) break;",
        "C-Absenkung -- die Wurzel wird mitbesucht; ein Knoten ist kein Nachfahre seiner selbst",
        "code",
    ),
    Mutation(
        "vorfahr-faengt-bei-sich-selbst-an",
        "emit.rs",
        "for (uint32_t {v} = {basis}[{wurzel}].{elter}; {v} != {n}u;",
        "for (uint32_t {v} = {wurzel}; {v} != {n}u;",
        "C-Absenkung -- die Kette faengt beim Knoten selbst an; er waere sein eigener Vorfahr",
        "code",
    ),
    Mutation(
        "marke-wird-wie-ein-geist-geloescht",
        "emit.rs",
        "            } else if t.linear && t.rumpf.is_none() && t.parameter.is_none() {",
        "            } else if false && t.rumpf.is_none() && t.parameter.is_none() {",
        "C-Absenkung -- ein `linear type` ohne Rumpf traegt keine Bytes mehr; `ghost` waere damit eine Verzierung",
        "code",
    ),
    Mutation(
        "parametersicht-bleibt-global",
        "emit.rs",
        # **The ANCHOR moved on 2026-08-31, the subject did not.** `eigene_sicht` gained
        # the collection of unread `let` bindings, and it now sits between `let mut lokal`
        # and the parameter loop. *A dead anchor measures nothing, and `--anker` said so in
        # the same run.*
        "    for p in &f.parameter {\n        let name = &p.name.text;",
        "    for p in f.parameter.iter().take(0) {\n        let name = &p.name.text;",
        "C-Absenkung -- ein Parameter verdeckt die globale Ablesung seines Namens nicht mehr; ein Punkt steht, wo ein Pfeil hingehoert",
        "code",
    ),
    Mutation(
        "format-feld-wird-wieder-ein-pfeil",
        "emit.rs",
        "    if let Some(fmt) = u.formatwerte.get(&o.basis.text) {",
        "    if let Some(fmt) = None::<&String> {",
        "C-Absenkung -- ein `format`-Feld wird ein Feldzugriff statt eines Bytelesers",
        "code",
    ),
    Mutation(
        "cas-schleife-ohne-schranke",
        "emit.rs",
        "if ({i} >= (uint32_t)({gaenge})) {{ {ausgang}(); }}",
        "if (0 && {i} >= (uint32_t)({gaenge})) {{ {ausgang}(); }}",
        "C-Absenkung -- «C4b»: eine unbeschraenkte CAS-Schleife ist genau das, was diese Sprache verbietet",
        "code",
    ),
    Mutation(
        "acht-byte-leser-ohne-seinen-vier-byte-leser",
        "emit.rs",
        "                    if b == 8 {\n                        leser.insert(lesewort(4, gross));",
        "                    if false {\n                        leser.insert(lesewort(4, gross));",
        "C-Absenkung -- `gabbro_le64` ruft `gabbro_le32`, und der Sammler zaehlt wieder nur die GENANNTEN Leser statt der gebrauchten",
        "code",
    ),
    Mutation(
        "gabbro-kern-ohne-prototyp",
        "emit.rs",
        "    if baum_hat_accumulates(baum) {",
        "    if false && baum_hat_accumulates(baum) {",
        "C-Absenkung -- ein FREMDER Rumpf wird gerufen und nirgends erklaert; C11 macht daraus eine implizite Deklaration",
        "code",
    ),
    Mutation(
        "verbund-steht-wieder-an-seinem-platz",
        "emit.rs",
        "        if let ItemArt::Typ(t) = &item.art {\n            if namen.verbunde.contains(&t.name.text) {",
        "        if let ItemArt::Typ(t) = &item.art {\n            if false && namen.verbunde.contains(&t.name.text) {",
        "C-Absenkung -- ein spaet erklaerter Verbund steht im C hinter seinem ersten Gebrauch",
        "code",
    ),
    Mutation(
        "let-else-nimmt-jede-funktion",
        "namen.rs",
        "                    if !k.contains_key(&n) {",
        "                    if false && !k.contains_key(&n) {",
        "N028 -- ein `else`-Zweig ueber einer Funktion ohne `or <reason>` faellt nicht mehr auf; er koennte nie laufen",
    ),
    Mutation(
        "scheiternder-ruf-ausserhalb-eines-let-else",
        "namen.rs",
        "                if let Some(r) = k.get(&n) {",
        "                if let Some(r) = None::<&String> {",
        "N029 -- ein Ruf auf eine scheiternde Funktion ausserhalb eines `let … else`; der Grund faellt unbemerkt auf den Boden",
    ),
    Mutation(
        "ungelesene-bindung-bekommt-kein-void",
        "emit.rs",
        "                    if u.ungelesene_lets.contains(&l.name.text) {",
        "                    if false && u.ungelesene_lets.contains(&l.name.text) {",
        "die `(void)r2;`-Zeile fuer eine `let`-Bindung ohne Leser faellt weg; das erzeugte C "
        "traegt `unused variable` und `cc -Wall -Werror` weist die Einheit zurueck. "
        "`pruefe-emission.sh` Stufe 9 faengt es an `messung/proben/probe-let-ohne-leser.gab`.",
        "code",
    ),
    Mutation(
        "skalar-traegt-wieder-jedes-feld",
        "umgebung.rs",
        "            Typ::Ganzzahl(_) | Typ::Umlaufend(_) | Typ::Gleitkomma(_) | Typ::Wahrheit => {\n"
        "                Feldurteil::KeineFelder\n"
        "            }",
        "            Typ::Ganzzahl(_) | Typ::Umlaufend(_) | Typ::Gleitkomma(_) | Typ::Wahrheit => {\n"
        "                Feldurteil::Unklar\n"
        "            }",
        "M134 -- ein Feldzugriff auf eine ZAHL geht wieder durch; der Erzeuger schreibt "
        "`m->op` auf ein `uint64_t`, und `cc` bricht ab. Die zweite Haelfte (ein Feldname, "
        "den der Verbund nicht hat) bleibt wach -- genau EINE Giftprobe faellt (411).",
    ),
    Mutation(
        "c-vergibt-den-namen-nicht-mehr",
        "cnamen.rs",
        "    if EINGEBAUT.binary_search(&name).is_ok() {",
        "    if false && EINGEBAUT.binary_search(&name).is_ok() {",
        "N041 -- die Klasse `Eingebaut` faellt aus: `exit`, `abort`, `malloc` gehen wieder "
        "durch, der Erzeuger schreibt `_Noreturn void exit(void);`, und `cc` weist die "
        "Uebersetzungseinheit zurueck. Die beiden anderen Klassen bleiben wach -- genau EINE "
        "Giftprobe faellt (408).",
    ),
    Mutation(
        "zwei-erzeugernamen-duerfen-gleich-sein",
        "namen.rs",
        "        if gruppe.len() < 2 {",
        "        if gruppe.len() < 3 {",
        "N042 -- die Doppelung wird erst ab DREI gleichen Namen gemeldet, also nie: der "
        "Erzeuger schreibt `Eintrag_gueltig` zweimal, der Pruefer schweigt, und `cc` sagt "
        "*Redefinition*. Der Rest des Passes bleibt wach -- ~~genau EINE Giftprobe faellt "
        "(413)~~ **FUENF fallen (413, 417, 418, 419, 420), nachgemessen 2026-08-31**. Die "
        "alte Zahl stammt vom Tag, an dem 413 die einzige Probe der Regel war; die vier "
        "neuen decken die drei STILLEN Sorten ab, bei denen `cc` gar nichts sagt. *Eine "
        "Mutation, die mehr faellt als ihr Text behauptet, sieht aus wie eine, die weniger "
        "faellt* -- W25: eine Zahl belegt ihren Nenner, nicht ihre Beschriftung.",
    ),
    Mutation(
        "der-anhang-des-erzeugers-zaehlt-nicht-mehr",
        "erzeugernamen.rs",
        "    v.push(Gebildet { name, span, muster, was, angehaengt: true });",
        "    v.push(Gebildet { name, span, muster, was, angehaengt: false });",
        "N042 -- kein gebildeter Name gilt mehr als gebildet, also greift der Schnitt "
        "`mindestens eine Seite ist ein Anhang` nie: die ganze Regel schweigt, waehrend "
        "`geltungsbereich` und `N041` daneben unversehrt bleiben. ~~Genau EINE Giftprobe "
        "faellt (413)~~ **FUENF fallen (413, 417, 418, 419, 420), nachgemessen 2026-08-31** "
        "-- dieselbe Berichtigung wie eine Mutation weiter oben, und aus demselben Grund.",
    ),
    # **Two arms of the enumeration on their OWN**, so that not every `N042` mutation knocks
    # over the same five probes. Both were hand-set on 2026-08-31, BUILT, and measured:
    # exactly ONE probe stops falling, and it is the one belonging to that arm.
    Mutation(
        "die-bootstrecke-bildet-ihren-eintritt-nicht",
        "erzeugernamen.rs",
        '                format!("gabbro_boot_{n}"),',
        '                format!("gabbro_boot__{n}"),',
        "N042 -- der blosse Name einer `boot`-Strecke faellt aus der Aufzaehlung, und damit "
        "genau der Name, an dem die MASCHINE anfaengt: `void gabbro_boot_{b}(void);` neben "
        "`extern fn gabbro_boot_{b}()` wird ein Symbol, und `cc -Werror` uebersetzt es. "
        "Die Schritte `_s{i}` und `_{setzt}` bleiben wach -- genau EINE Giftprobe faellt "
        "(420), nachgemessen 2026-08-31.",
    ),
    Mutation(
        "der-pruefkoerper-heisst-nicht-mehr-so",
        "erzeugernamen.rs",
        '                format!("pruefe_{}", c.name.text),',
        '                format!("pruefe__{}", c.name.text),',
        "N042 -- `check c` bildet `pruefe_{c}` nicht mehr. Es ist der einzige erzeugte Name "
        "mit AEUSSERER Bindung, den der Erzeuger auch DEFINIERT: daneben ein "
        "`extern fn pruefe_{c}()`, und der Binder holt das Archivglied des Schreibers nie -- "
        "sein Aufruf wird vom Pruefkoerper beantwortet. Der Rest der Aufzaehlung bleibt "
        "wach -- genau EINE Giftprobe faellt (418), nachgemessen 2026-08-31.",
    ),
    Mutation(
        "baumkante-braucht-ihr-feld-nicht",
        "kbedingung.rs",
        "            let Some(typ) = felder.get(k.text.as_str()) else {",
        "            let Some(typ) = felder.get(k.text.as_str()).or_else(|| felder.values().next()) else {",
        "D006 -- eine `tree`-Kante darf ein Feld nennen, das der Slot nicht hat",
    ),
    Mutation(
        "baumkante-muss-nicht-enden-koennen",
        "kbedingung.rs",
        "                TypExpr::Index { tabelle, optional: true, .. } if tabelle.text == t.name.text => {}",
        "                _ if true => {}\n                #[allow(unreachable_patterns)]\n                TypExpr::Index { tabelle, optional: true, .. } if tabelle.text == t.name.text => {}",
        "D007/D008 -- eine Kante darf ein `u32` sein oder in eine fremde Tabelle zeigen; enden koennen muss sie dann nicht mehr",
    ),
    Mutation(
        "nominale-typen-sind-austauschbar",
        "namen.rs",
        "                        if hat == erwartet {",
        "                        if true || hat == erwartet {",
        "N030 -- ein `linear ghost`-Zeuge passt wieder an jede Stelle; der Wecker nimmt einen fremden Grund, und `Lost wakeup` ist zurueck",
    ),
    Mutation(
        "beobachter-braucht-keine-sonde",
        "namen.rs",
        "        match annahmen.get(&b.text) {\n            Some(true) => {}",
        "        match annahmen.get(&b.text) {\n            Some(_) => {}",
        "N031 -- «V9»: `observed by` nimmt die Paarungspflicht ab, ohne einen Falsifikator zu verlangen; das Schlupfloch bekommt einen Namen darauf",
    ),
    Mutation(
        "check-rumpf-hat-wieder-keinen-leser",
        "m1.rs",
        "            if let ItemArt::Check(c) = &item.art {\n                self.modul = modul.to_string();",
        "            if let ItemArt::Check(c) = &item.art {\n                let _ = c;\n                self.modul = modul.to_string();\n                if true { return; }",
        "M1 liest den `can_fail`-Rumpf nicht mehr -- der eine Ort, an dem eine falsifizierbare Aussage steht, hat wieder keinen Typpass",
    ),
    Mutation(
        "formatklausel-darf-nennen-was-sie-will",
        "namen.rs",
        "                if felder.contains(n.as_str())",
        "                if true || felder.contains(n.as_str())",
        "N032 -- die `where`-Klausel eines `format` darf wieder einen Namen nennen, den es nicht gibt; PFLICHTEN.md F10 baut auf ihr auf",
    ),
    # **The report line of a `check`** (2026-08-31). If this one survives, `measures` may
    # name into the void again -- and with it `N021` and `N022` go silent, because both find
    # their quantity by matching a name against this list. *The damage is not the missing
    # `N043`; it is the two refusals that stop falling without saying so.*
    Mutation(
        "measures-darf-nennen-was-es-will",
        "namen.rs",
        "                if sichtbar.contains(&m.basis.text) {",
        "                if true || sichtbar.contains(&m.basis.text) {",
        "N043 -- `measures` darf wieder einen Namen nennen, den es nicht gibt; damit "
        "schweigen `N021` und `N022` ueber diese Groesse mit",
    ),
    Mutation(
        "bootschritt-darf-nennen-was-er-will",
        "namen.rs",
        "            if !bekannt.contains(&n) {",
        "            if false && !bekannt.contains(&n) {",
        "N033 -- ein Bootschritt darf wieder eine Funktion nennen, die es nicht gibt",
    ),
    Mutation(
        "bootstrecke-darf-in-jeder-ordnung-stehen",
        "namen.rs",
        "                if hier != von {",
        "                if false && hier != von {",
        "O007 -- die Schritte einer Bootstrecke duerfen wieder in jeder Reihenfolge stehen; «B37» ist zurueck an der Stelle, an der es herkam",
    ),
    Mutation(
        "format-liest-immer-klein",
        "emit.rs",
        "        (4, true) => \"gabbro_be32\",",
        "        (4, true) => \"gabbro_le32\",",
        "C-Absenkung -- `endian big` wird klein gelesen; jedes Feld ist byteverdreht",
        "code",
    ),
    Mutation(
        "format-versatz-waechst-nicht",
        "emit.rs",
        '            versatz += breite;\n            i_feld += 1;',
        '            versatz += 0 * breite;\n            i_feld += 1;',
        "code",
    ),
    Mutation(
        "where-klausel-faellt-weg",
        "emit.rs",
        "        aus.push_str(&format!(\"    if (!({p})) return false;\\n\"));",
        "        let _ = p;",
        "C-Absenkung -- die `where`-Klauseln pruefen nichts; danach braucht jeder Zugriff wieder eine Laengenpruefung",
        "code",
    ),
    Mutation(
        "format-ohne-laengenpruefung",
        "emit.rs",
        "    if (v->len < {versatz}u) return false;\\n\"",
        "    if (0 && v->len < {versatz}u) return false;\\n\"",
        "C-Absenkung -- ein Puffer kuerzer als der Kopf gilt als gueltig",
        "code",
    ),
    Mutation(
        "untere-schranke-faellt-immer-weg",
        "emit.rs",
        "            let bedingung = if untere_ist_null && vorzeichenlos {",
        "            let bedingung = if untere_ist_null {",
        "C-Absenkung -- die untere `narrow`-Pruefung faellt auch fuer vorzeichenbehaftete Werte weg",
        "code",
    ),
    # -- emit.rs: `traverse` und `if` ------------------------------------------------------
    Mutation(
        # **Zweimal derselbe Anker seit dem 2026-08-20**: `elems of` senkt seit Stufe 3 in
        # derselben Form ab wie `slots of`, und der Ankerpruefer meldete MEHRDEUTIG. *Eine
        # mehrdeutige Mutation misst die erste Fundstelle und liest sich wie beide.* Also je
        # Domaene eine, mit der Zeile darueber als Unterscheidung.
        "traversierung-laesst-den-letzten-slot-aus",
        "emit.rs",
        "let feld = if u.tabellenglobal.contains(&o.basis.text) {",
        "let feld = if !u.tabellenglobal.contains(&o.basis.text) {",
        "C-Absenkung -- `slots of` greift mit dem falschen Zugriffszeichen auf den Traeger",
        "code",
    ),
    Mutation(
        # **Neu am 2026-08-20 mit «B12»:** `elems of` bindet einen INDEX und laeuft ueber das
        # Feld selbst. Laesst die Schleife den letzten Eintrag aus, ist die Domaene
        # unvollstaendig -- und `msg_kopiert` spraeche dann ueber ein Wort zu wenig.
        # **Die erste Fassung dieser Mutation MUTIERTE NICHTS** (2026-08-20): sie haengte ein
        # `let _ = 0;` an und war damit ein No-op -- sie ueberlebte den Lauf und las sich wie
        # eine unbewachte Regel. *Eine Mutation, die nichts aendert, ist die Umkehrung von
        # W17: Misserfolg ohne Arbeit, und sie beschuldigt eine Regel, die in Ordnung ist.*
        # **`uint32_t` -> `uint64_t` on 2026-08-31**: the index of an ARRAY is not the index
        # word of a TABLE, and the narrowing made `F06` fall at `cc -Werror=type-limits`.
        # *The anchor became unambiguous on the way -- `slots of` keeps `uint32_t`, so the
        # two domains no longer read alike.*
        "elems-laesst-den-letzten-aus",
        "emit.rs",
        "            let feld = ort(o, u, absagen);\n            let v = &x.variable.text;\n"
        "            aus.push_str(&format!(\n"
        "                \"{e}for (uint64_t {v} = 0; {v} < (uint64_t)",
        "            let feld = ort(o, u, absagen);\n            let v = &x.variable.text;\n"
        "            aus.push_str(&format!(\n"
        "                \"{e}for (uint64_t {v} = 0; {v} + 1 < (uint64_t)",
        "C-Absenkung -- die `elems of`-Schleife laesst den letzten Eintrag aus",
        "code",
    ),
    Mutation(
        # **Umgezogen am 2026-08-20**: der Pfeil stand hart da, und eine bei NAMEN
        # adressierte Tabelle ist kein Zeiger. Jetzt entscheidet `tabellenglobal`, und die
        # Mutation dreht die Entscheidung um -- der Punkt kommt an den Zeiger.
        "traversierung-nimmt-den-punkt",
        "emit.rs",
        "            let feld = if u.tabellenglobal.contains(&o.basis.text) {",
        "            let feld = if !u.tabellenglobal.contains(&o.basis.text) {",
        "C-Absenkung -- die Domaene greift durch den Zeiger mit `.` statt `->` und umgekehrt",
        "code",
    ),
    Mutation(
        # **Der Anker ist umgezogen, weil die Lesart entschieden ist** (2026-08-20, Stufe 3).
        # Bis dahin wurden `by consuming` UND `by decreasing` abgelehnt, mit *„was es fuer
        # den Lauf heisst, ist nicht entschieden"*. Jetzt laeuft `by decreasing` wie
        # `by unvisited` -- und nur `by consuming` bleibt abgelehnt, weil die ENTNAHME
        # erzeugter Code ist. Die Mutation dreht genau diesen Rest um.
        # *Der Anker traegt die Absagezeile mit*, weil `if matches!(…, Verbrauchend)` seit
        # «B12» an ZWEI Domaenen steht -- und ein mehrdeutiger Anker misst die erste
        # Fundstelle und liest sich wie beide.
        # **Stufe 4, 2026-08-20:** der Fehlerkanal an einer `impl fn`. Die Mutation nimmt das
        # `*_wert =` weg -- genau der Zustand, in dem der Erzeuger bis zu diesem Tag war:
        # `f(7)` meldete Erfolg und liess den Wert des Rufers unberuehrt.
        "fehlerkanal-schreibt-den-wert-nicht",
        "emit.rs",
        "aus.push_str(&format!(\"{e}*_wert = {t};\\n{e}return true;\\n\"));",
        "aus.push_str(&format!(\"{e}return true;\\n\"));",
        "C-Absenkung -- eine Funktion mit Fehlerkanal gibt ihr Ergebnis nicht heraus",
        "code",
    ),
    Mutation(
        # Und die andere Haelfte desselben Fundes: der Rueckgabewert ist der ERFOLG. Steht
        # dort der Wert, meldet `f(0)` Misserfolg -- fuer eine gueltige Null.
        "fehlerkanal-meldet-den-wert-als-erfolg",
        "emit.rs",
        "                    if austritt.fehlerkanal {",
        "                    if false && austritt.fehlerkanal {",
        "C-Absenkung -- der Wert wird als Erfolgsmerker zurueckgegeben",
        "code",
    ),
    Mutation(
        # **Stufe 5, 2026-08-20:** die geschlossene Wortmenge von `ops`. Faellt die Pruefung,
        # nimmt `opdecl` wieder jedes Wort -- und aus einem Namen faellt keine Wirkung.
        "ops-nimmt-jedes-wort",
        # *Die erste Fassung schnitt den `_`-Zweig des `match` heraus und war damit
        # UNGUELTIG -- ein nicht erschoepfendes `match` uebersetzt nicht.* Diese hier stellt
        # den Zustand vor dem 2026-08-20 wieder her: `identlist` statt `opnamen`.
        "gabbro-syntax/src/parse.rs",
        "                    ops.extend(self.opnamen()?);",
        "                    ops.extend(self.identlist()?);",
        "Parser -- `ops` nimmt wieder beliebige Woerter",
        # **Hier stand `"pass"`, und das ist keine Flaeche** (gefunden 2026-08-21). Die
        # Aufstellung je Flaeche zaehlt `m.flaeche == name` ueber `FLAECHEN`; ein Name, der
        # dort nicht steht, faellt aus JEDER Zeile heraus. Die Summe der Flaechen war damit
        # 239, die Gesamtzahl 240 -- *und niemand hat die zwei Zahlen je nebeneinander
        # gelegt.* Dieselbe Klasse wie die Kiste im Pfad einen Tag vorher: **eine Flaeche,
        # die kein Werkzeug erreicht, fehlt nicht laut, sie fehlt still.**
        "pruefer",
    ),
    Mutation(
        # **Die Verneinung, gebaut weil ein Programm sie brauchte.** Faellt das `!` weg, ist
        # jede Bedingung des Empfangswegs umgedreht -- und `cc` sagt nichts.
        "verneinung-verschwindet",
        "emit.rs",
        "ExprArt::Unaer(UnOp::Nicht, x) => format!(\"!({})\", ausdruck(x, u, absagen)),",
        "ExprArt::Unaer(UnOp::Nicht, x) => format!(\"({})\", ausdruck(x, u, absagen)),",
        "C-Absenkung -- die logische Verneinung faellt weg, jede Bedingung ist umgedreht",
        "code",
    ),
    Mutation(
        "verbrauchen-laeuft-wie-besuchen",
        "emit.rs",
        "            if matches!(x.abstieg, Abstieg::Verbrauchend) {\n"
        "                weigere(\n                    absagen,\n                    s.span,\n"
        "                    \"`by consuming` -- the run form is the same walk PLUS the removal, and \\",
        "            if false && matches!(x.abstieg, Abstieg::Verbrauchend) {\n"
        "                weigere(\n                    absagen,\n                    s.span,\n"
        "                    \"`by consuming` -- the run form is the same walk PLUS the removal, and \\",
        "C-Absenkung -- `by consuming` senkt ohne die Entnahme ab und leert nichts",
        "code",
    ),
    Mutation(
        # **Der Anker ist umgezogen, weil die Absage weg ist** (2026-08-20). `forever` senkt
        # ab; zu messen ist jetzt die GEPRUEFTE BEZUGNAHME auf den Wachhund.
        "forever-wachhund-wird-ein-kommentar",
        "emit.rs",
        "static void (*const {marke}_wachhund)(void) __attribute__((unused)) = {ausgang};",
        "/* on_exceeded {marke} = {ausgang} */",
        "C-Absenkung -- `on_exceeded` wird ein Kommentar statt einer Bezugnahme; der "
        "C-Uebersetzer liest die Klausel nicht mehr nach",
        "code",
    ),
    Mutation(
        "if-zweig-ohne-austritt",
        "emit.rs",
        "                for k in &rumpf.anweisungen {\n                    anweisung(k, aus, u, absagen, tiefe + 1, austritt);\n                }\n            }\n            if let Some(sonst) = &w.sonst {",
        "                for k in &rumpf.anweisungen {\n                    anweisung(k, aus, u, absagen, tiefe + 1, &Austritt::default());\n                }\n            }\n            if let Some(sonst) = &w.sonst {",
        "C-Absenkung -- ein `return` aus einem `if` im `locks`-Block laesst die Sperre stehen",
        "code",
    ),
    Mutation(
        "sonderwert-ohne-wortgrenze",
        "emit.rs",
        "        Some(&n) if n < WORTGRENZE => {",
        "        Some(&n) if n < WORTGRENZE || true => {",
        "C-Absenkung -- der Sonderwert wird nicht gegen das Indexwort geprueft (Option_Sonderwert.thy M-1)",
        "code",
    ),
    # -- emit.rs: das Geraet -----------------------------------------------------------
    Mutation(
        "register-ohne-volatile",
        "emit.rs",
        "                \"(*(volatile {breite} *)({}{pfeil}basis + {versatz}))\",",
        "                \"(*({breite} *)({}{pfeil}basis + {versatz}))\",",
        "C-Absenkung -- ein Registerzugriff darf wegoptimiert werden",
        "code",
    ),
    # **Repointed 2026-08-28 -- the gate moved, the mutation stayed behind.** The anchor read
    #
    #     ~~`    if !matches!(d.raum, Raum::Mmio) {`~~
    #
    # back when ONE refusal covered `at normal` and `at dma` together. That sentence was
    # split in two on 2026-08-26 (`emit.rs`: *"two refusals under one text was the older
    # mistake; they are two now"*), and `at dma` LOWERS since then -- under the named
    # assumption `dma_kohaerent`, and refused without one. **The gate this mutation wants is
    # therefore the ASSUMPTION gate**, not the address-space test: `if false && ...` lets
    # `at dma` lower with no assumption named anywhere, and that is the barrier-free
    # lowering M3 does not build.
    Mutation(
        "dma-wird-abgesenkt",
        "emit.rs",
        "    if matches!(d.raum, Raum::Dma) && !u.annahmen.contains(ANNAHME_DMA) {",
        "    if false && matches!(d.raum, Raum::Dma) && !u.annahmen.contains(ANNAHME_DMA) {",
        "C-Absenkung -- `at dma` wird ohne die benannte Annahme `dma_kohaerent` abgesenkt; "
        "welche Barriere ein DMA-Zugriff braucht, ist eine Aussage ueber das Speichermodell, "
        "und M3 baut sie ausdruecklich nicht",
        "code",
    ),
    Mutation(
        "registerversatz-egal",
        "emit.rs",
        "                        reg.insert(r.name.text.clone(), (v, intty(&r.typ)));",
        "                        reg.insert(r.name.text.clone(), (0 * v, intty(&r.typ)));",
        "C-Absenkung -- jedes Register liegt an Versatz 0; alle treffen dasselbe Wort",
        "code",
    ),
    Mutation(
        "annahmen-fahren-nicht-mit",
        "emit.rs",
        "        aus.push_str(\"\\n/* Proved under the following assumptions (SYNTAX.md 12).\\n\");",
        "        aus.push_str(\"\\n/*\\n\");",
        "SYNTAX.md 12 -- die Annahmenmenge steht nicht im Erzeugnis; die Zusage bleibt im Werkzeug",
        "code",
    ),
    Mutation(
        "unfalsifizierbar-ohne-grund-im-c",
        "emit.rs",
        "                    format!(\"UNFALSIFIABLE -- {grund}\")",
        "                    { let _ = grund; format!(\"UNFALSIFIABLE\") }",
        "SYNTAX.md 12 -- eine nicht falsifizierbare Annahme faehrt ohne ihren Grund mit",
        "code",
    ),
    Mutation(
        "bitlage-darf-herausragen",
        "emit.rs",
        "            if hi >= breite {",
        "            if false && hi >= breite {",
        "C-Absenkung -- eine Bitlage jenseits der Registerbreite wird maskiert statt abgelehnt",
        "code",
    ),
    Mutation(
        "bitfeld-ohne-verschiebung",
        "emit.rs",
        "                        return format!(\"(({wort} >> {lo}) & {maske}u)\");",
        "                        return format!(\"(({wort} >> 0) & {maske}u)\");",
        "C-Absenkung -- jedes Bitfeld wird ab Bit 0 gelesen",
        "code",
    ),
    # -- emit.rs: FALLE 4 -----------------------------------------------------------------
    Mutation(
        "mirrors-vergisst-den-zustand",
        "emit.rs",
        "                 \\x20   {wort} = ({breite})((_s & ({breite})~({breite}){geaendert}u) | ({breite}){neu}u);\\n\"",
        "                 \\x20   {wort} = ({breite})((0*_s & ({breite})~({breite}){geaendert}u) | ({breite}){neu}u);\\n\"",
        "FALLE 4 -- ein nicht mitgeschriebenes Zustandsbit wird geloescht; die Einheit schaltet sich mitten im Betrieb ab",
        "code",
    ),
    Mutation(
        "uebergang-maskiert-nicht",
        "emit.rs",
        "            let maske = 1u128 << lo;",
        "            let maske = 1u128;",
        "FALLE 4 -- der Uebergang aendert Bit 0 statt des benannten Bits",
        "code",
    ),
    Mutation(
        "requires-wird-zusicherung",
        "emit.rs",
        "        aus.push_str(\"/* requires: a caller obligation, not a generated assertion */\\n\");",
        "        aus.push_str(\"\\n\");",
        "SPRACHE -- die Vorbedingung eines Uebergangs verschwindet spurlos aus dem Erzeugnis",
        "code",
    ),
    Mutation(
        "none-nimmt-die-falsche-tabelle",
        "emit.rs",
        "        Some(TypExpr::Index { tabelle, optional: true, .. }) => Some(tabelle.text),",
        "        Some(TypExpr::Index { tabelle, .. }) => Some(tabelle.text),",
        "C-Absenkung -- ein `index into T` gilt als Option, und `= None` schreibt in ein Feld, "
        "das keinen Sonderwert hat",
        "code",
    ),
    # -- emit.rs: «C4»/«C5» -- der Tausch, das `const`, das Feld, der Griff ---------------
    #
    # Die erste ist die, gegen die der Katalog schon zwei Eintraege fuehrt: ein `=` auf einem
    # `_Atomic` ist in C `seq_cst`, also eine ANDERE Ordnung als die deklarierte. *Ein
    # Differenztest kann das an einem Faden nicht zeigen -- diese Mutation kann es.*
    Mutation(
        "tausch-nimmt-die-vorgabeordnung",
        "emit.rs",
        "{e}        &{ziel}, &{h}, ({typ})({}), {speichern}, {laden});\\n{e}}}\\n",
        "{e}        &{ziel}, &{h}, ({typ})({}), memory_order_seq_cst, memory_order_seq_cst);"
        "\\n{e}}}\\n",
        "C-Absenkung -- der Tausch nimmt seq_cst statt der deklarierten Ordnung",
        "code",
    ),
    Mutation(
        "tausch-ohne-erwarteten-wert",
        "emit.rs",
        '{e}bool {};\\n{e}{{\\n{e}    {typ} {h} = ({typ})({erwartet});\\n',
        '{e}bool {};\\n{e}{{\\n{e}    {typ} {h} = ({typ})0;\\n',
        "C-Absenkung -- der erwartete Wert der `when`-Bedingung faellt weg; der Tausch "
        "vergleicht gegen null",
        "code",
    ),
    Mutation(
        "const-nimmt-wieder-den-schwachen-auswerter",
        "emit.rs",
        "            } else if let Some(w) = namen.konstwert.get(&k.name.text).copied() {",
        "            } else if let Some(w) = None::<i128> {",
        "C-Absenkung -- `u64::max` faellt wieder auf den schwaecheren der zwei Auswerter "
        "zurueck (W7)",
        "code",
    ),
    Mutation(
        "feldlaenge-wird-geraten",
        "emit.rs",
        '            aus.push_str(&format!("    {el} {}[{n}];\\n", f.name.text));',
        '            aus.push_str(&format!("    {el} {}[1];\\n", f.name.text));',
        "C-Absenkung -- die Laenge eines Feldtyps wird geraten statt abgelesen",
        "code",
    ),
    # **Repointed 2026-08-28 -- a pure repoint, the same sabotage.** The anchor read
    #
    #     ~~`            "({name}){{ (volatile uint8_t *)(uintptr_t){} }}",`~~
    #
    # until the handle learned to carry EVERY declared parameter (2026-08-25, `Virtq(base,
    # n)`): the base became a NAMED member and the further parameters follow it. `0*` on the
    # base expression still points the handle at null instead of at its declared base, and
    # `rechenwerk.rs` asserts that whole line.
    Mutation(
        "geraetegriff-ohne-basis",
        "emit.rs",
        '            "({name}){{ .basis = (volatile uint8_t *)(uintptr_t){}{rest} }}",',
        '            "({name}){{ .basis = (volatile uint8_t *)(uintptr_t)0*{}{rest} }}",',
        "C-Absenkung -- der Geraetegriff zeigt auf null statt auf seine erklaerte Basis",
        "code",
    ),
    # -- emit.rs: «C3b» -- RCU, und der Unterschied zur Sperre ist das, was FEHLT ----------
    Mutation(
        "rcu-ohne-prototypen",
        "emit.rs",
        '                "void {n}_lese_start(void);\\nvoid {n}_lese_ende(void);\\n"',
        '                "/* {n} */\\n"',
        "C-Absenkung -- ein RCU-Lesebereich wird betreten, ohne dass sein Primitiv erklaert ist",
        "code",
    ),
    Mutation(
        "lesebereich-bleibt-beim-return-offen",
        "emit.rs",
        '            innen.freigaben.push(format!("{n}_lese_ende()"));',
        "            let _ = &innen;",
        "C-Absenkung -- ein `return` aus einem `observes` laesst den Lesebereich offen; "
        "die Gnadenfrist haengt genau daran",
        "code",
    ),
    # -- emit.rs: «C3a/c» -- `reason`, `group`, und der Speicher einer Tabelle -------------
    #
    # Zwei Absenkungen und eine gezogene Linie. Die dritte Mutation ist die interessanteste:
    # sie nimmt der Tabelle ihren eigenen Speicher, und dann steht wieder ein Pfeil auf einem
    # Typnamen im Erzeugnis -- die Form, die bis zum 2026-08-19 an `cc` delegiert war.
    Mutation(
        "reason-erfindet-seine-zahlen",
        "emit.rs",
        "                    f.wert,\n                    kommentartext(&f.text.text)",
        "                    0,\n                    kommentartext(&f.text.text)",
        "C-Absenkung -- die Fehlerwerte kommen nicht mehr aus der Quelle; zwei Faelle "
        "tragen dieselbe Zahl",
        "code",
    ),
    Mutation(
        "gruppe-erzeugt-doch-etwas",
        "emit.rs",
        "        ItemArt::Gruppe(_) => {}",
        '        ItemArt::Gruppe(g) => aus.push_str(&format!("\\nstatic int {};\\n", g.name.text)),',
        "C-Absenkung -- eine `group` kostet zur Laufzeit etwas; sie ist eine Beweisaussage "
        "und darf nichts erzeugen",
        "code",
    ),
    Mutation(
        "tabelle-ohne-eigenen-speicher",
        "emit.rs",
        "    if u.tabellenglobal.contains(&o.basis.text) {\n"
        '        t = format!("{}_speicher", o.basis.text);',
        "    if false && u.tabellenglobal.contains(&o.basis.text) {\n"
        '        t = format!("{}_speicher", o.basis.text);',
        "C-Absenkung -- eine ueber ihren Namen adressierte Tabelle wird wieder ein Pfeil auf "
        "einen Typnamen",
        "code",
    ),
    # -- emit.rs: «C2» -- der markierte Wert -----------------------------------------------
    #
    # Drei Stellen tragen die Absenkung, und jede kann still danebengehen: der `switch` liest
    # die MARKE (nicht den Wert), jeder Zweig liest das Glied SEINER Variante, und es gibt
    # keinen Sammelzweig. *Der dritte ist der unscheinbarste und der teuerste: ein `default:`
    # legt `-Wswitch` still, also genau den zweiten Leser von `D005`.*
    Mutation(
        "markiertes-match-liest-den-wert",
        "emit.rs",
        '    aus.push_str(&format!("{e}switch ({gegenstand}.marke) {{\\n"));',
        '    aus.push_str(&format!("{e}switch ({gegenstand}.marke + 0*1) {{\\n"));',
        "C-Absenkung -- der `switch` liest nicht mehr die Marke selbst",
        "code",
    ),
    Mutation(
        "variantenzweig-liest-fremdes-glied",
        "emit.rs",
        '                        "{e}    {c} {} = {gegenstand}.last.{};\\n",\n'
        "                        b.text, v.name.text",
        '                        "{e}    {c} {} = {gegenstand}.last.{};\\n",\n'
        "                        b.text, varianten[0].name.text",
        "C-Absenkung -- ein Zweig liest ein FREMDES Glied der Vereinigung; die Marke sagt "
        "dann nichts mehr",
        "code",
    ),
    Mutation(
        "markiertes-match-bekommt-einen-sammelzweig",
        "emit.rs",
        # **Der Anker ist am 2026-08-20 umgezogen** -- hinter dem `switch` steht jetzt der
        # `__builtin_unreachable`-Zweig fuer den Fall, dass jeder Arm zurueckkehrt, und die
        # alte Textstelle gibt es nicht mehr. `--anker` hat es gesagt, bevor der Lauf lief.
        'aus.push_str(&format!("{e}}}\\n"));\n    // **Wenn JEDER Zweig zurueckkehrt',
        'aus.push_str(&format!("{e}default: break;\\n{e}}}\\n"));\n    // **Wenn JEDER Zweig zurueckkehrt',
        "C-Absenkung -- der `switch` bekommt einen Sammelzweig und legt `-Wswitch` still, "
        "also den zweiten Leser von D005",
        "code",
    ),
    Mutation(
        "markiertes-match-muss-nicht-erschoepfen",
        "emit.rs",
        "    if m.zweige.len() != varianten.len()\n"
        "        || !varianten\n"
        "            .iter()\n"
        "            .all(|v| m.zweige.iter().any(|z| z.variante.text == v.name.text))\n"
        "    {",
        "    if false {",
        "C-Absenkung -- ein `match` ohne jede Variante wird ein `switch`, der durchfaellt "
        "und NICHTS tut",
        "code",
    ),
    # -- emit.rs / m1.rs: «C1» -- der Sonderwert, ausgeschrieben ---------------------------
    #
    # Der Beweis lag seit dem 2026-08-17 in `beweise/Option_Sonderwert.thy` und **kein
    # Erzeuger benutzte ihn**. Seit «C1» steht er im C -- und damit muss beschaedigbar sein,
    # was ihn traegt: der Wert selbst, die Nutzlastpruefung und der Typ des `Some`-Binders.
    Mutation(
        "none-wird-null",
        "emit.rs",
        '        "None" => Some(format!("{tab}_NONE")),',
        '        "None" => Some(format!("0*{tab}_NONE")),',
        "C-Absenkung -- `None` senkt zu 0 ab und ist von `Some(0)` nicht zu unterscheiden",
        "code",
    ),
    Mutation(
        "some-gegen-den-optionstyp",
        "m1.rs",
        "            (true, Some(nutzlast)) => self.passt(quelle, &nutzlast, span, was),",
        "            (true, Some(nutzlast)) => {\n"
        "                let _ = nutzlast;\n"
        "                self.passt(quelle, ziel, span, was)\n"
        "            }",
        "`Some(N)` wird gegen den OPTIONSTYP geprueft, also passt der Sonderwert hinein",
    ),
    Mutation(
        "some-binder-ohne-nutzlast",
        "m1.rs",
        "                            innen.lokal.insert(binder.text.clone(), nutz);",
        "                            innen.lokal.insert(binder.text.clone(), Typ::Unbekannt);",
        "V3 an der Option -- der `Some`-Binder traegt seinen Indexbereich nicht mehr",
    ),
    Mutation(
        "bank-ohne-schritt",
        "emit.rs",
        "i * {schritt}u + {off}u);",
        "i * 0u + {off}u);",
        "C-Absenkung -- jeder Eintrag einer `bank` liegt an derselben Adresse",
        "code",
    ),
    # **The SETTER, and until 2026-08-28 it had no mutation.** That day's full run let the
    # reader mutation directly above survive: its assertion stood over the whole output, and since
    # 2026-08-26 the setter carries the same address arithmetic -- it satisfied the assertion
    # alone. The probe is healed first (`rechenwerk.rs`, stride per BLOCK), and only then comes
    # this line: *a mutation added before its probe raises nothing but the denominator.*
    Mutation(
        "bank-schreiber-ohne-schritt",
        "emit.rs",
        "i * {schritt}u + {off}u) = x;",
        "i * 0u + {off}u) = x;",
        "C-Absenkung -- jeder Schreibzug in eine `bank` trifft denselben Eintrag",
        "code",
    ),
    Mutation(
        "transset-nimmt-nur-den-ersten",
        "emit.rs",
        "        geaendert |= g2;\n        neu |= n2;",
        "        geaendert = g2;\n        neu = n2;",
        "C-Absenkung -- ein `transset` setzt nur das letzte Bit; die uebrigen Orte fallen weg",
        "code",
    ),
    Mutation(
        "release-wird-abgesenkt",
        "emit.rs",
        "                Some(Ordnung::Relaxed) | None\n                    if matches!(a.obermenge, None | Some(Nutzlast::Nichts(_))) =>",
        "                _ if true =>",
        "C-Absenkung -- ein `release`-Atomic wird ohne Begruendung der Sichtbarkeit abgesenkt",
        "code",
    ),
    Mutation(
        "check-ohne-behauptung",
        "emit.rs",
        '        "\\n/* check {}\\n * claim: {}\\n",\n        kommentartext(&c.name.text),\n        kommentartext(&c.claim.text)',
        '        "\\n/* check {}\\n * claim: {}\\n",\n        kommentartext(&c.name.text),\n        kommentartext("")',
        "code",
    ),
    Mutation(
        "check-ohne-gegenprobe",
        "emit.rs",
        "        rumpf_aus.push_str(&format!(\n            \" * counterprobe: \\\"{}\\\" expects {}\\n\",",
        "        let _ = (was, erwartet);\n        rumpf_aus.push_str(&format!(\n            \"{}{}\",",
        "C-Absenkung -- die Gegenprobe faellt weg; eine Probe, die nicht rot werden kann, misst nichts",
        "code",
    ),
    # -- «B14b»: ein ausgepackter Ort ist kein Ruf ---------------------------------------
    Mutation(
        "ausgepackter-ort-gilt-als-ruf",
        "aufrufgraph.rs",
        "                if let Some(r) = l.als_ruf() {\n                    nimm(r, aus);\n                }",
        # **«B8», 2026-08-21: `pfad: Pfad` became `ziel: CallTarget`**, and this replacement
        # snippet BUILDS a `Ruf` by hand. Until it was carried along, the mutation did not
        # compile and counted as `ungueltig` -- it said nothing, and the quota ran over a
        # denominator smaller by one. *Exactly the decay of the measuring apparatus this
        # file's header warns about, only at a replacement snippet instead of an anchor.*
        "                nimm(&Ruf { ziel: CallTarget::Path(Pfad { teile: vec![l.name.clone()], span: l.name.span }), argumente: vec![], marken: vec![], span: l.name.span }, aus);",
        "B14b -- ein ausgepackter Ort gilt als Ruf; jede Huelle darueber wird untere Schranke",
    ),
    # -- «B7»: der Verbundkonstruktor ------------------------------------------------------
    #
    # **Die erste ist die Sprechprobe zur bewiesenen Schablone.** `Verbund_Konstruktor.thy`
    # waehlt `deckt fs zs <-> map fst zs = fs` -- die REIHENFOLGE -- ausdruecklich gegen die
    # Mengenfassung, und fuehrt unter M-2 als eigene Grenze: *nicht gezeigt ist, dass der
    # ERZEUGER `deckt` herstellt.* Diese Mutation ist genau diese Grenze, beschaedigt.
    Mutation(
        "verbundmarken-nur-als-menge",
        "m1.rs",
        "                if gegeben != felder {",
        "                let (mut g, mut f) = (gegeben.clone(), felder.clone());\n"
        "                g.sort(); f.sort();\n"
        "                if g != f {",
        "B7 -- die Marken gelten nur als MENGE; `P(b: …, a: …)` geht durch, "
        "und der Leser sieht die Deklaration, wo keine ist",
    ),
    Mutation(
        "konstruktor-gilt-als-aufruf",
        "aufrufgraph.rs",
        '                if n.text != "Some" && n.text != "None" && !r.ist_verbundwert() {\n                    aus.push((p.text(), args));',
        '                if n.text != "Some" && n.text != "None" {\n                    aus.push((p.text(), args));',
        "und jede Huelle darueber untere Schranke",
    ),
    # -- «B24»: die Kachelung IST die Wortgrenze ---------------------------------------------
    #
    # Ohne den Abbruch bei vollem Wort liest der Erzeuger alle aufeinanderfolgenden Bitfelder
    # gleicher Breite als EIN Wort -- und meldet am zweiten Byte des IP-Kopfs eine
    # Ueberlappung, die keine ist.
    Mutation(
        "bitgruppe-endet-nicht-am-vollen-wort",
        "emit.rs",
        "            if belegt == voll_hier {\n                break;\n            }",
        "            if false {\n                break;\n            }",
        "B24 -- die Bitgruppe frisst das naechste Wort mit; der IP-Kopf faellt an einer "
        "Ueberlappung, die keine ist",
    ),
    Mutation(
        "bitlage-jenseits-des-wortes-geht-durch",
        "emit.rs",
        "            if hi < lo || hi >= bits as u128 {",
        "            if hi < lo {",
        "B24 -- eine Bitlage jenseits der Wortbreite wird gelesen statt abgesagt; "
        "die Maske greift ins Leere",
    ),
    # -- `opaque` beisst ---------------------------------------------------------------------
    #
    # **Ohne diese Zeile wird ein undurchsichtiger Typ wieder als sein TRAEGER gerechnet**, und
    # `a & b` auf zwei Gleitkommawoertern ergibt Unsinn, den niemand meldet.
    Mutation(
        "undurchsichtig-rechnet-wie-der-traeger",
        "m1.rs",
        "            if let Typ::Benannt { name, undurchsichtig: true, .. } = t {",
        "            if let Typ::Benannt { name, undurchsichtig: false, .. } = t {",
        "D003 -- die Undurchsichtigkeit dreht sich um; wo die Breiten aufgehen, geht der "
        "Unsinn wieder durch",
    ),
    # -- Die parametrische Kostenzusage ------------------------------------------------------
    #
    # **Bis 2026-08-18 stand dort ein `return`**, und jede nicht-konstante `costs`-Zeile fiel
    # lautlos weg. Nimmt man den Vergleich gegen die kleinste Belegung heraus, ist die Zusage
    # wieder eine Zeile ohne Wirkung.
    Mutation(
        "parametrische-zusage-faellt-wieder-weg",
        "kosten.rs",
        "        let zusage_min = zusage.fest;",
        "        let zusage_min = i128::MAX;",
        "K001 -- eine parametrische Zusage wird wieder beliebig gross gelesen; "
        "`costs <= 0 * n` geht durch",
    ),
    Mutation(
        "negativer-faktor-gilt-als-schranke",
        "kosten.rs",
        "            if k < 0 {\n                return None;\n            }",
        "            if false {\n                return None;\n            }",
        "K005 -- ein negativer Faktor macht die Zusage bei wachsender Eingabe KLEINER; "
        "das ist keine Schranke",
    ),
    # -- `accumulates`: die Darstellung von `min`/`and` -------------------------------------
    #
    # **C nullt statische Felder, und null ist nicht das Neutrale von `min`.** Der erste Lauf
    # lieferte 0 statt 3, weil 61 unberuehrte Zellen mitzaehlten. `min` und `and` speichern
    # darum das KOMPLEMENT -- nimmt man die Umkehr heraus, ist das Ergebnis wieder falsch.
    Mutation(
        "min-akkumulator-ohne-umkehr",
        "emit.rs",
        '                MergeOp::Min => ("z = (z > v) ? z : v;", true),',
        '                MergeOp::Min => ("z = (z < v) ? z : v;", false),',
        "accumulates -- `min` speichert nicht mehr das Komplement; die unberuehrten Zellen "
        "ziehen jedes Ergebnis auf null",
    ),
    # -- Die Indexschranke an einer GLOBALEN Tabelle ----------------------------------------
    #
    # **Der Blick auf die Karte war unqualifiziert, und `M103` schwieg in jedem
    # `module`-Block.** Die erste getragene Klempnereiklasse traf genau die Form nicht, fuer
    # die sie da ist -- Kernzustand ohne Zeiger.
    Mutation(
        "indexschranke-sucht-unqualifiziert",
        "m1.rs",
        "                self.u\n                    .suche_global(&self.modul, &o.basis.text)\n                    .cloned()",
        "                self.u.globale.get(&o.basis.text).cloned()",
        "M103 -- der Traeger wird unqualifiziert gesucht; eine globale Tabelle in einem "
        "`module` hat wieder keine Indexschranke",
    ),
    # -- K11.2.3: die Ordnung im erzeugten C ------------------------------------------------
    #
    # **Die Absenkung von `release`/`acquire` ruht auf A10 -- und ihre einzige strukturelle
    # Zusage ist, dass die Ordnung im C die der Quelle ist.** Faellt die, erzeugt der Ordner
    # ein Programm, das die Quelle nicht sagt, und kein Differenztest zeigt es: ein Rennen
    # laesst sich durch Ausfuehrung nicht widerlegen.
    Mutation(
        "veroeffentlichung-nimmt-die-vorgabeordnung",
        "emit.rs",
        # **The anchor was pulled along on 2026-08-31, not the rule**: since `verenge` the
        # value stands as `{w}` in that line and no longer as `{}`. An anchor that does not
        # follow a rebuild falls under `ungueltig`, and the quota keeps reading as if it
        # covered it.
        "atomic_store_explicit(&{ziel}, {w}, {ordnung});",
        "{ziel} = {w}; /* {ordnung} */",
        "K11.2.3 -- die Veroeffentlichung wird ein `=`, also seq_cst statt der deklarierten "
        "Ordnung; das erzeugte Programm sagt etwas anderes als die Quelle",
    ),
    Mutation(
        "laden-nimmt-die-speicherordnung",
        "emit.rs",
        "            let Some((typ, _, ordnung)) = u.atomics.get(&quelle) else {",
        "            let Some((typ, ordnung, _)) = u.atomics.get(&quelle) else {",
        "K11.2.3 -- ein Laden mit `memory_order_release`; das gibt es in C11 nicht",
    ),
    # -- K11.2.1: `protects` beisst ---------------------------------------------------------
    #
    # **Die erste ist die tragende.** Ohne sie prueft der Ordner wieder nur die DISZIPLIN
    # einer genommenen Sperre und nicht, dass sie genommen wird -- der Zustand, in dem
    # `beispiele/05` eine `protects`-Klausel trug, die niemand einhielt.
    Mutation(
        "protects-beisst-nicht-mehr",
        "geteilt.rs",
        "        if da.iter().any(|d| d == &sperre) {\n            return;\n        }",
        "        if true {\n            return;\n        }",
        "K11.2.1 -- jeder Zugriff auf einen geschuetzten Platz gilt als gedeckt; "
        "`protects` ist wieder Zierde",
    ),
    Mutation(
        "nie-genommene-sperre-schweigt",
        "geteilt.rs",
        "        if !ueberhaupt_genommen.contains(name)",
        "        if false && !ueberhaupt_genommen.contains(name)",
        "K11.2.1 -- eine Sperre, die niemand nimmt, faellt nicht mehr auf; genau so stand "
        "`lock BERICHT` im eigenen Korpus",
    ),
    # -- «B37»: die Ordnung auf einer Geistmarke -------------------------------------------
    #
    # **Die erste ist die wichtigste.** Ohne `O003` erzwingt der lineare Wert wieder nur eine
    # Kette und nicht WELCHE -- alle 720 Reihenfolgen der sechs Bootschritte gingen durch, und
    # `order`/`advances` waeren Zeremonie.
    Mutation(
        "phasenschritt-trifft-jede-stufe",
        "phasen.rs",
        "    if ist != sch.von {",
        "    if false {",
        "B37 -- ein Schritt trifft jede Stufe; zwei vertauschte Bootschritte fallen nicht mehr",
    ),
    Mutation(
        "phasenordnung-ist-nur-eine-liste",
        "phasen.rs",
        "        if a >= b {",
        "        if false {",
        "B37 -- `advances` darf rueckwaerts gehen; aus der Ordnung wird wieder eine Liste",
    ),
    Mutation(
        "phasenstrecke-darf-aufhoeren",
        "phasen.rs",
        "            if letzte != eigen.nach {",
        "            if false {",
        "B37 -- ein Rumpf muss sich nicht mehr zu seiner Zusage zusammensetzen",
    ),
    # K11.1: die Zweige muessen sich einigen -- und ein Zweig, der ENDET, gehoert nicht dazu.
    Mutation(
        "phasenzweige-muessen-sich-nicht-einigen",
        "phasen.rs",
        "        if k != erster {",
        "        if false {",
        "K11.1 -- zwei Zweige duerfen die Marke auf verschiedene Stufen bringen",
    ),
    Mutation(
        "phasenschritt-in-der-schleife-geht-durch",
        "phasen.rs",
        '                if enthaelt_schritt(s, u, modul, schritte) {',
        '                if false {',
        "die Schleife oft",
    ),
    Mutation(
        "endender-zweig-zaehlt-mit",
        "phasen.rs",
        '                    if !crate::endet_immer(r, &[]) {\n                        zweige.push((k, r.span));\n                    }\n                }\n                // **Ein `if` ohne `else`',
        '                    zweige.push((k, r.span));\n                }\n                // **Ein `if` ohne `else`',
        "der haeufigste saubere Fall faellt",
    ),
    # -- K100.4: die Kreuzprobe des Uebersetzungszeugnisses --------------------------------
    #
    # **Das Zeugnis ist eine ZWEITE Lesung derselben Datei.** Sein Wert haengt daran, dass es
    # meldet, was es nicht einordnen kann -- schluckt es das, deckt es sich mit dem Erzeuger
    # per Konstruktion und misst nichts mehr.
    Mutation(
        "zeugnis-schluckt-unbekannte-items",
        "zeugnis.rs",
        'andere => e.unzugeordnet.push(format!("item `{}`", art_name(andere))),',
        "andere => { let _ = andere; }",
        "K100.4 -- das Zeugnis verschweigt Items, die es nicht einordnet; "
        "die Vertrauensflaeche ist dann groesser als gebucht",
    ),
    Mutation(
        # **Anchor moved on 2026-08-31, and the damage is the same one.** `breaking` lowers
        # since that day, so the arm books it with `zaehle` instead of pushing it onto
        # `unzugeordnet`. Dropping the `zaehle` call is the identical failure: a statement
        # falls SILENTLY out of the certificate -- neither counted nor reported as unknown.
        "zeugnis-schluckt-unbekannte-anweisungen",
        "zeugnis.rs",
        '                zaehle(e, "breaking");\n                block(&b.rumpf, e, geister);',
        "                block(&b.rumpf, e, geister);",
        "K100.4 -- dasselbe eine Ebene tiefer: eine Anweisung faellt still aus der Buchung",
    ),
    Mutation(
        "verbund-ohne-marken-geht-durch",
        "m1.rs",
        "        let gefunden = r.path().and_then(|p| self.u.verbundfelder(&self.modul, p)).cloned();",
        "        let gefunden = if r.ist_verbundwert() { r.path().and_then(|p| self.u.verbundfelder(&self.modul, p)).cloned() } else { None };",
        "B7 -- `P(1, 2)` ohne Feldnamen faellt nicht mehr; zwei gleichtypige Felder "
        "sind vertauschbar, ohne dass ein Typ dagegen spricht",
    ),
    # -- Die Zusage eines FREMDEN Rumpfes, als Posten im Zeugnis (2026-08-21) -------------
    #
    # **Vier Mutationen, weil der Posten vier Stellen hat, an denen er still sterben kann:**
    # die Unterscheidung wirksam/vorhanden, die zwei Sammelstellen in M1 (Bereich und
    # Beziehung) und der Abdruck im Zeugnis. *Eine Buchung, die nur an einer davon haengt,
    # sieht vollstaendig aus.*
    Mutation(
        "fremdverengung-zaehlt-jede-klausel",
        "fremdverengung.rs",
        "    schritte.retain(|s| s.wirksam);",
        "    schritte.retain(|s| { let _ = s; true });",
        "K100/E14 -- das Zeugnis zaehlt jede vorhandene `ensures`-Klausel statt nur die, "
        "die eine Grenze BEWEGT hat; eine Zeile, die niemanden bindet, sieht dann aus wie "
        "eine Vertrauensflaeche mit Wirkung",
    ),
    Mutation(
        "fremdverengung-ueberspringt-die-ruempfe-ohne-rumpf",
        "m1.rs",
        "        if !sig.rumpf_da {\n            for s in &v.schritte {",
        "        if false {\n            for s in &v.schritte {",
        "K100/E14 -- die Bereichsverengung aus einem fremden `ensures` wirkt weiter und "
        "steht in keinem Zeugnis; genau der Zustand vom 2026-08-20, als `sig.rumpf_da` "
        "an dieser Rufstelle gar nicht gefragt wurde",
    ),
    Mutation(
        "fremdverengung-vergisst-die-beziehung",
        "m1.rs",
        "            if !sig.rumpf_da {\n                self.fremd.push(Stelle {",
        "            if false {\n                self.fremd.push(Stelle {",
        "K100/E14 -- die RELATIONALE Haelfte (`ensures result <= s.len`) faellt aus der "
        "Buchung; die Flaeche sieht kleiner aus, als sie ist",
    ),
    Mutation(
        "zeugnis-druckt-abschnitt-f-nicht",
        "zeugnis.rs",
        "    aus.push_str(&crate::fremdverengung::zeige(&stellen, quelle));",
        "    let _ = quelle;",
        "K100/E14 -- die Zahl steht in der Befundzeile, die STELLEN stehen nirgends; eine "
        "Zahl ohne Fundstelle ist ein Rueckstand, kein Ergebnis",
    ),
    # --- Stufe 6, Teil C ---
    #
    # **Fuenf blinde Zweige im Namenssammler, und alle fuenf sahen aus wie Unbedenklichkeit.**
    # `sammle_namen_pred_geb` traegt seit dem 2026-08-21 keinen Auffangzweig mehr: die
    # `match`-Ketten sind vollstaendig, damit die naechste `PredArt`-Variante nicht wieder
    # still hineinfaellt. Jede Mutation hier nimmt genau EINEN dieser Zweige zurueck.
    Mutation(
        "self-im-ensures-geht-durch",
        "m1.rs",
        'if n == "Self" {',
        "if false {",
        "K100 -- `M120` faellt aus: `ensures Self.slots[0].rest <= 4096` an einer freien "
        "`fn` geht wieder durch, obwohl `Self` dort auf nichts zeigt (Gift 223)",
    ),
    Mutation(
        "self-als-typ-bleibt-unsichtbar",
        "m1.rs",
        'if p.teile.len() == 1 && p.teile[0].text == "Self" {',
        "if false {",
        "K100 -- die ZWEITE Schreibweise faellt aus: `lenof(Self)` ist ein Typ, nicht ein "
        "Ort, und ohne diese Zeile sieht `M120` nur die eine Haelfte (Gift 224)",
    ),
    Mutation(
        "sizeof-und-lenof-bleiben-blind",
        "m1.rs",
        "TypOderOrt::Ort(o) => aus_ort(o, gebunden, out),",
        "TypOderOrt::Ort(_) => {}",
        "K100 -- ein Tippfehler in `sizeof(...)`/`lenof(...)` einer Nachbedingung faellt "
        "wieder still durch; `M109` prueft nur, wohin der Sammler kommt (Gift 225)",
    ),
    Mutation(
        "aligned-bleibt-blind",
        "m1.rs",
        "Eingebaut::Aligned(a, b) => {\n                    aus_expr(a, gebunden, out);\n"
        "                    aus_expr(b, gebunden, out);\n                }",
        "Eingebaut::Aligned(_, _) => {}",
        "K100 -- `aligned` traegt ZWEI ganze Ausdrucksbaeume; ohne diesen Zweig ist keiner "
        "von beiden geprueft (Gift 227)",
    ),
    Mutation(
        "und-oder-folgt-bleiben-blind",
        "m1.rs",
        "PredArt::Und(a, b) | PredArt::Oder(a, b) | PredArt::Folgt(a, b) => {\n"
        "            sammle_namen_pred_geb(a, gebunden, out);\n"
        "            sammle_namen_pred_geb(b, gebunden, out);\n        }",
        "PredArt::Und(_, _) | PredArt::Oder(_, _) | PredArt::Folgt(_, _) => {}",
        "K100 -- jede ZUSAMMENGESETZTE Nachbedingung wird wieder ungeprueft; die linke "
        "Haelfte stimmt und die rechte ist ein Tippfehler (Gift 228)",
    ),
    Mutation(
        "negation-und-klammer-bleiben-blind",
        "m1.rs",
        "PredArt::Klammer(i) | PredArt::Nicht(i) => sammle_namen_pred_geb(i, gebunden, out),",
        "PredArt::Klammer(_) | PredArt::Nicht(_) => {}",
        "K100 -- die Negation ist im Korpus die HAEUFIGERE Verknuepfung (fuenf "
        "`ensures`-Zeilen fangen mit `!` an) und war bis 2026-08-21 unbesehen (Gift 229)",
    ),
    # --- Stufe 6, Teil D ---
    Mutation(
        # **`H015` faellt aus, und die Rueckgewinnung sieht weiter geprueft aus.** `H011` und
        # `H012` bleiben stehen -- sie halten die zwei PRUEFBAREN Haelften -- und genau das
        # ist die Gefahr: der Lauf ist gruen, die dritte Haelfte hat nie jemand
        # aufgeschrieben. *Der Zustand vom 2026-08-21, an `beispiele/43-gegenprobe.gab`
        # gemessen: `rcu … reclaims` ohne Gnadenfrist, 0 Fehler.*
        "gnadenfrist-wird-nicht-mehr-verlangt",
        "geteilt.rs",
        "                if !gnadenfrist.contains(d) {",
        "                if false && !gnadenfrist.contains(d) {",
        "H015 -- die GNADENFRIST wird nicht mehr verlangt; ein `rcu … reclaims` geht wieder "
        "durch, ohne dass eine Annahme sagt, wer garantiert, dass kein Leser mehr drin ist",
    ),
    Mutation(
        # Die andere Richtung derselben Regel: die Annahme muss die Domaene BEIM NAMEN
        # nennen. Nimmt der Abgleich jede Annahme, deckt eine beliebige Zeile ueber den
        # Rundungsmodus die Gnadenfrist einer RCU-Domaene mit ab.
        "gnadenfrist-nimmt-jede-annahme",
        "geteilt.rs",
        "            if rcu_domaenen.contains_key(wort) {\n                gnadenfrist.insert(wort.to_string());",
        "            if true {\n                gnadenfrist.extend(rcu_domaenen.keys().cloned());",
        "H015 -- jede beliebige Annahme deckt jede RCU-Domaene; der Satz muss die Domaene "
        "nicht mehr nennen",
    ),
    # --- Stufe 6, Teil E ---
    #
    # **«B38» -- der benannte Traeger und der Zustand am Eintritt.** Beide Haelften einzeln,
    # denn sie koennen einzeln ausfallen: `H101` kann verstummen (erste), und die Abhilfe,
    # die `H101` verlangt, kann UNSCHREIBBAR werden (zweite). *Die zweite ist die
    # unangenehmere: eine Regel, deren Abhilfe eine andere Regel ausloest, ist keine.*
    Mutation(
        "traeger-ohne-nested-masked-geht-durch",
        "kontexte.rs",
        "        if k.maskiert_verschachtelt {\n            lage.gedeckt += 1;",
        "        if !k.maskiert_verschachtelt {\n            lage.gedeckt += 1;",
        "B38 -- `H101` verstummt: ein Eintritt darf `masks IRQ` als Traeger nennen, ohne "
        "`nested masked` zu tragen. Genau die Zusicherung aus R15",
    ),
    Mutation(
        "nested-masked-deckt-nicht-mehr",
        "kontexte.rs",
        "maskiert && (k.nie_verschachtelt || k.maskiert_verschachtelt || !k.unterbricht)",
        "maskiert && (k.nie_verschachtelt || !k.unterbricht)",
        "B38 -- `nested masked` verliert die H013-Ausnahme, die `nested never` behaelt. "
        "Damit loest die von `H101` verlangte Abhilfe eine ZWEITE Absage aus",
    ),
    # --- Stufe 7 ---
    # **Der Grunderzeuger, sechs Regeln, sechs Beschaedigungen.** Jede trifft GENAU EINE:
    # wer eine davon ueberleben sieht, weiss sofort, welche Haelfte des Fehlerkanals heute
    # unbewacht ist.
    Mutation(
        "grund-ohne-deklaration-geht-durch",
        "m1.rs",
        "                let Some((voll, faelle)) = self.u.grund(&self.modul, &grund.text) else {",
        "                let Some((voll, faelle)) = self.u.grund(&self.modul, &grund.text)\n"
        "                    .or_else(|| self.u.gruende.iter().next().map(|(k, v)| (k.clone(), v))) else {",
        "M120 -- ein `R::F` mit unbekanntem `R` nimmt irgendeinen anderen `reason`; "
        "ein Name, den niemand erklaert, faellt an einer Bibliotheksgrenze nirgends auf",
    ),
    Mutation(
        "grundfall-wird-nicht-geprueft",
        "m1.rs",
        "                if !faelle.contains(&fall.text) {",
        "                if false && !faelle.contains(&fall.text) {",
        "M121 -- ein erfundener Fallname geht durch; im C entstuende `R_GibtsNicht`, "
        "und erst `cc` saehe es",
    ),
    Mutation(
        "grund-ohne-kanal-geht-durch",
        "m1.rs",
        "                if let Typ::Grund(g) = &t {\n                    let g = g.clone();",
        "                if let (Typ::Grund(g), Some(_)) = (&t, &self.fehlerkanal) {\n"
        "                    let g = g.clone();",
        "M122 -- ein `return R::F` in einer Funktion OHNE `or R` faellt nicht mehr; "
        "die C-Signatur haette keinen `*_grund`, in den der Wert ginge",
    ),
    Mutation(
        "match-ueber-grund-darf-luecken-haben",
        "m1.rs",
        "                        let fehlt: Vec<&String> = faelle\n"
        "                            .iter()\n"
        "                            .filter(|f| !genannt.contains(&f.as_str()))\n"
        "                            .collect();",
        "                        let fehlt: Vec<&String> = Vec::new();",
        "M123 -- ein `match` ueber einem Grund darf einen Fall auslassen; der erzeugte "
        "`switch` faellt dort durch und tut NICHTS",
    ),
    # **`M124` hat ZWEI Haelften, und darum zwei Mutationen.** Die STELLUNG entscheidet, wo
    # ein Grund stehen darf; die TYPEN entscheiden, wogegen er dort gehalten wird. *Eine
    # einzelne Mutation haette die andere Haelfte gedeckt aussehen lassen* -- gemessen: die
    # erste Fassung dieser Mutation zielte auf die Typhaelfte, und Gift 236 fiel trotzdem,
    # weil die Stellungshaelfte es fing.
    Mutation(
        "grund-darf-ueberall-stehen",
        "m1.rs",
        "                if !erlaubt {\n                    aus.push(e.span);\n                }",
        "                if false && !erlaubt {\n                    aus.push(e.span);\n                }",
        "M124 (Stellung) -- `let g = R::F;`, `nimm(R::F)`, `t.slots[e]`, `z = R::F` und "
        "`e + 1` gehen wieder still durch; sieben Stellungen, gemessen am 2026-08-21",
    ),
    Mutation(
        "grund-gegen-alles-vergleichbar",
        "m1.rs",
        "            if matches!((&ta, &tb), (Typ::Grund(x), Typ::Grund(y)) if x == y) {",
        "            if true {",
        "M124 (Typen) -- `e == 1` faellt nicht mehr; zwei `reason`-Deklarationen vergeben "
        "dieselbe Zahl fuer verschiedene Dinge",
    ),
    Mutation(
        "gebundener-grund-wird-nicht-erkannt",
        "m1.rs",
        "            ExprArt::Ort(o) => {\n"
        "                o.suffixe.is_empty()\n"
        "                    && matches!(lage.lokal.get(&o.basis.text), Some(Typ::Grund(_)))\n"
        "            }",
        "            ExprArt::Ort(_) => false,",
        "M124 (Stellung) -- das `e` eines `let … else` gilt nicht mehr als Grund; nur noch "
        "das geschriebene `R::F` faellt auf, und `e + 1` ist wieder still",
    ),
    Mutation(
        "kanal-ohne-einloeser-geht-durch",
        "namen.rs",
        "        if !scheitert(b) {",
        "        if false && !scheitert(b) {",
        "N034 -- eine eigene Funktion erklaert `or R` und kann nie scheitern; der "
        "Erzeuger gibt ihr einen `*_grund`, den kein Pfad je schreibt",
    ),
    Mutation(
        "offener-grund-darf-gematcht-werden",
        "m1.rs",
        "                    if !self.u.erschoepfende_gruende.contains(g) {",
        "                    if false && !self.u.erschoepfende_gruende.contains(g) {",
        "M125 -- `exhaustive` verliert seinen einzigen Leser im Pruefer wieder; ein "
        "offener Grund wird gematcht, und der erzeugte `switch` faellt bei einem neuen "
        "Wert durch",
    ),
    Mutation(
        "grundwert-wird-wieder-ein-ort",
        "gabbro-syntax/src/parse.rs",
        "                    if pfad.teile.len() == 2 {",
        "                    if false && pfad.teile.len() == 2 {",
        "Die Produktion `reasonval` selbst -- `R::F` wird wieder ein Ort mit Feldsuffix, "
        "und der Fehlerkanal hat wieder keine Schreibform",
    ),
    # --- fnptr ---
    #
    # **«B8», 2026-08-21.** Four mutations, one per half -- and the first is the one that
    # matters: it restores exactly the state this item removed. *If
    # `huelle-verliert-indirekten-ruf` survives, the effect hull is silently lost at every
    # indirect call site, and that is the worst possible outcome.*
    Mutation(
        "huelle-verliert-indirekten-ruf",
        "gabbro-check/src/aufrufgraph.rs",
        # **The anchor names the third line too**, because the block stands twice -- in
        # `gehe` and in `huelle_der_gerufenen`. `gehe` is the one hit: `E008` hangs there.
        "        for i in &k.indirect {\n            if !i.has_contract {\n                aufnehmen(",
        "        for i in &k.indirect[..0] {\n            if !i.has_contract {\n                aufnehmen(",
        "Die Wirkungen eines Gerufenen an einem ORT fallen aus der Huelle -- `E008` endet "
        "wieder an der ersten indirekten Aufrufgrenze, so wie vor dem 2026-08-15",
    ),
    Mutation(
        "fnzeiger-ohne-vertrag-geht-durch",
        "gabbro-check/src/namen.rs",
        "            let fehlt = match (f.effects.is_none(), f.costs.is_none()) {",
        "            let fehlt: Option<&str> = None;\n            let _ = match (f.effects.is_none(), f.costs.is_none()) {",
        "N035 -- ein `fn(…)`-Typ darf wieder ohne `effects` und ohne `costs` dastehen; "
        "jeder Ruf hindurch traegt dann nichts zur Huelle bei und kostet null",
    ),
    Mutation(
        "erzeuger-darf-mehr-versprechen",
        "gabbro-check/src/m1.rs",
        "            .find(|w| *w != \"pure\" && !z.effects.iter().any(|x| x == *w))",
        "            .find(|w| *w != \"pure\" && z.effects.iter().any(|x| x == *w))",
        "M128 -- die Teilmengenrichtung kippt: eine Funktion, die MEHR tut als ihr Slot "
        "erlaubt, kommt durch, und jeder Rufer rechnet mit der Zusage statt mit der Tatsache",
    ),
    Mutation(
        "indirekter-ruf-kostet-null",
        "gabbro-check/src/kosten.rs",
        "                crate::typen::Typ::FnPtr(v) => match v.costs {\n                    Some(n) => args.plus(Kosten::Zahl(n)),",
        "                crate::typen::Typ::FnPtr(v) => match v.costs {\n                    Some(_) => args.plus(Kosten::Zahl(0)),",
        "K001 -- die Kostenschranke am Zeigertyp wird nicht mehr addiert; ein Rumpf voller "
        "indirekter Rufe kommt unter jeder Zusage durch",
    ),
    # --- PL.1, finding 1 of 9: the K condition is enforced ---
    #
    # **If this mutation survives, the pass is back where it was on 2026-08-21**: the
    # `breaking` site is collected, counted and printed, and never refused -- while
    # `k_haelt()` demands its absence. *A guarantee that a measurement rests on.*
    Mutation(
        "k-bedingung-verlangt-breaking-nicht",
        "kbedingung.rs",
        "        for (was, span) in &t.breaking {",
        "        for (was, span) in t.breaking.iter().take(0) {",
        "D009 -- the K condition no longer refuses a `breaking` block on an `ops` carrier; "
        "a program passes pass 2 without satisfying the condition the K/A/W count rests on",
    ),
    # **And the ground underneath it** (2026-08-28). `D009` attributed the break to EVERY
    # carrier with `ops`, because the invariant's name was never looked up -- and without
    # that lookup a `breaking` clause may also name into the void. *A clause whose subject
    # stands nowhere* -- the same class as `S007`, `N033`, `M133`, `N020`.
    Mutation(
        "breaking-darf-ins-leere-nennen",
        "kbedingung.rs",
        "            if bekannt.contains_key(&i.text) {",
        "            if true {",
        "D013 -- `breaking` may name an invariant that does not exist; the three promises of "
        "SPRACHE.md 8.3 then hang on a name with no subject",
    ),
    # --- emit ---
    #
    # **Die aufgeloesten Auffangzweige der Emission** (2026-08-21). Jede dieser Mutationen
    # beschaedigt GENAU EINE Entscheidung, die vorher in einem `_`-Zweig fiel -- und ohne
    # sie waere die Aufloesung eine Umschreibung ohne Messung. *Ein Zweig, den man
    # ausschreibt und nicht beschaedigen kann, ist genauso unbeschaedigbar wie der
    # Sammelzweig davor.*
    Mutation(
        "sammler-erreicht-den-zweig-nicht-mehr",
        "emit.rs",
        "        for k in crate::unterbloecke(s) {\n            sammle_retry(baum, modul, k, aus);",
        "        for k in crate::unterbloecke(s)\n            .into_iter()\n"
        "            .filter(|_| !matches!(&s.art, StmtArt::Wenn(_)))\n"
        "        {\n            sammle_retry(baum, modul, k, aus);",
        "C001 -- ein `retry` in einem `if` bekommt wieder keine Schranke, und die Absenkung "
        "sagt dazu *die Kosten stehen nicht fest* -- eine Absage mit dem falschen Grund",
        flaeche="code",
    ),
    Mutation(
        # **Turned around on 2026-08-31, when the refusal fell.** It used to check that the
        # ONE unlowered statement kind was named -- `breaking` lowers now, so there is no
        # such refusal to blunt. **The damage the mutation stands for survives the change
        # and is worse than it was**: the region is lowered SILENTLY. What comes out is an
        # ordinary C block, and nobody reading it can see which invariant was suspended or
        # where the restoration is counted. *A dropped proof region looks exactly like a
        # program that never had one* -- which was the whole ground of the old refusal.
        "breaking-senkt-die-region-still-ab",
        "emit.rs",
        '                "{e}/* breaking {} -- PROOF region: inside it the invariant is not a\\n\\\n'
        '                 {e} * premise. At run time this is its statements and nothing else; the\\n\\\n'
        '                 {e} * restoration is booked as a preservation obligation (`gabbro pflichten`).\\n\\\n'
        '                 {e} */\\n",',
        '                "{e}/* {} */\\n",',
        "C001 -- die Beweisregion verschwindet aus dem Erzeugnis; das C sieht aus wie ein "
        "gewoehnlicher Block, und die ausgesetzte Invariante steht nirgends",
        flaeche="code",
    ),
    # **Berichtigung 2026-08-28 -- it said THREE forms, and there are two.** The anchor read
    #
    #     ~~`                "`sizeof` / `lenof` / `aligned` outside a `format` predicate ...`~~
    #
    # On 2026-08-26 `lenof` was given its own sentence AND its own lowering (a descent
    # measure over a fixed-length array), so the collective refusal covers two forms today,
    # not three. **The mutation keeps its whole point**: the refusal stops naming the form,
    # and a reader of the certificate cannot tell WHAT is missing. Only the count in the
    # rule text was wrong -- corrected here, not painted over.
    Mutation(
        "ausdrucksform-heisst-wieder-ausdrucksform",
        "emit.rs",
        '                    "`sizeof` / `aligned` outside a `format` predicate -- inside one they \\',
        '                    "expression form -- inside one they \\',
        "C001 -- die zwei Ausdrucksformen ohne Absenkung fallen wieder unter EINEN Satz "
        "zusammen, und keine von ihnen wird beim Namen genannt (bis zum 2026-08-26 waren es "
        "drei; `lenof` hat seither einen eigenen Satz und eine eigene Absenkung)",
        flaeche="code",
    ),
    Mutation(
        "gleitkomma-im-slot-wird-nicht-angesagt",
        "emit.rs",
        "                    if let SlotTyp::Typ(x) = &f.typ {\n                        ja |= im_typ(x);",
        "                    if let SlotTyp::Typ(x) = &f.typ {\n                        let _ = im_typ(x);",
        "F -- ein `f64` im Slot einer Tabelle laesst die Einheit ihre Gleitkommarechnung "
        "wieder verschweigen; `-ffast-math ist verboten` und die SSE2-Annahme stehen dann nicht im Erzeugnis",
        flaeche="code",
    ),
    Mutation(
        "indexuebergang-ohne-grund",
        "emit.rs",
        "                 and which register an index picks is a run time question",
        "                 and that is how it is",
        "C001 -- die Absage am `transition` ueber einem Index nennt wieder nur die FORM und "
        "nicht den Grund; die zweite Suffixform blieb darin ohnehin ungenannt",
        flaeche="code",
    ),
    # --- p6 ---
    #
    # **The annotation emission, and every mutation here is a WEAKENING.**
    #
    # Their brief stands in the surface description above: not a generator that stays
    # silent, but one that SPEAKS and says less than the contract demands. Each mutation
    # leaves the duty standing and makes it weaker -- the emitter's balance line stays
    # unchanged in five of seven, and that is exactly why the probes must look at the TEXT
    # and not at the number.
    Mutation(
        "p6-and-becomes-or",
        "refinement.rs",
        '        PredArt::Und(a, b) => Ok(format!(\n            "({}) \\\\<and> ({})",',
        '        PredArt::Und(a, b) => Ok(format!(\n            "({}) \\\\<or> ({})",',
        "P6 -- `requires k < 64 && n < 4096` wird als ODER erzeugt. Beide Konjunkten stehen "
        "weiter da, die Pflicht ist um die Haelfte schwaecher, und das Ziel geht durch",
        flaeche="annotation",
    ),
    Mutation(
        "p6-argument-without-stability",
        "refinement.rs",
        "            match caller.iter().find(|p| p.name == o.basis.text) {\n"
        "                Some(p) if p.untouched => Ok(var(&p.name)),",
        "            match caller.iter().find(|p| p.name == o.basis.text) {\n"
        "                Some(p) => Ok(var(&p.name)),",
        "P6 -- ein Parameter, den der Rumpf laengst ueberschrieben hat, wird wieder als "
        "Argument eingesetzt; das Ziel redet dann ueber einen Wert, den das Programm an "
        "dieser Stelle nicht mehr hat",
        flaeche="annotation",
    ),
    Mutation(
        "p6-own-precondition-without-stability",
        "refinement.rs",
        "            Binding::Own(caller) => match caller.iter().find(|p| p.name == name) {\n"
        "                Some(p) if p.untouched => Ok(var(&p.name)),",
        "            Binding::Own(caller) => match caller.iter().find(|p| p.name == name) {\n"
        "                Some(p) if true => Ok(var(&p.name)),",
        "P6 -- das eigene `requires` des Rufers wird wieder zur Annahme, auch wenn der Rumpf "
        "den Parameter geschrieben hat; bewiesen wird unter einer Voraussetzung, die am "
        "Rufort niemand gewaehrt",
        flaeche="annotation",
    ),
    Mutation(
        "p6-lock-witness-becomes-true",
        "refinement.rs",
        "        PredArt::Held { .. } => Err(Reason::LockWitness),",
        '        PredArt::Held { .. } => Ok("True".to_string()),',
        "P6 -- `requires Held(L)` wird ein triviales Ziel statt einer benannten Absage; eine "
        "von den Sperrpaessen GETRAGENE Pflicht sieht danach aus wie eine bewiesene",
        flaeche="annotation",
    ),
    Mutation(
        "p6-foreign-ensures-called-body-effect",
        "refinement.rs",
        "        Material::Foreign => Verdict::Refused(Reason::ForeignBody),",
        "        Material::Foreign => Verdict::Refused(Reason::BodyEffect),",
        "P6 -- eine ANNAHME ueber fremden Code wird als offene Pflicht gefuehrt; die Zahl "
        "sieht gleich aus, und die Vertrauensflaeche verschwindet aus dem Bericht",
        flaeche="annotation",
    ),
    Mutation(
        "p6-type-bound-pins-the-value",
        "pflichten.rs",
        "        crate::typen::Typ::Ganzzahl(b) => Some((b.min, b.max)),",
        "        crate::typen::Typ::Ganzzahl(b) => Some((b.max, b.max)),",
        "P6 -- die Typschranke wird ein Punkt statt eines Bereichs. Es steht MEHR da als "
        "vorher, jedes Ziel geht durch, und keine Zahl faellt",
        flaeche="annotation",
    ),
    # ---------------------------------------------------------------------------------
    # THE BODY CHANNEL (`lean.rs`) -- six weakenings, and FOUR of them leave the balance
    # line untouched. That is why the probes read the emitted TEXT and not only the count:
    # a duty that vanishes is noticed, one that gets weaker is not.
    # ---------------------------------------------------------------------------------
    Mutation(
        "lean-goal-becomes-weak",
        "lean.rs",
        '            "    : \\\\<exists> s\', finalState (exec \\\\<rho> body_{} s) = some s\'\\n",',
        '            "    : \\\\<forall> s\', finalState (exec \\\\<rho> body_{} s) = some s\'\\n",',
        "The body channel -- the goal becomes the WEAK form. `for all s\', if it ends in "
        "s\', then P` is vacuously true for a body that gets stuck, and a vacuous theorem "
        "reads exactly like a proved one",
        flaeche="annotation",
    ),
    Mutation(
        "lean-autoimplicit-back-on",
        "lean.rs",
        # **The anchor carries the NEXT line too.** Since the program export was built, the
        # same `push_str` stands in two places -- and `--anker` reported it AMBIGUOUS, which
        # is the tool doing its job: an anchor that matches twice mutates whichever comes
        # first, and the report then names the wrong artefact.
        's.push_str("set_option autoImplicit false\\n\\nopen Gabbro.Body\\n\\n");\n'
        '    s.push_str(&format!("namespace GabbroDuty.{name}\\n\\n"));',
        's.push_str("open Gabbro.Body\\n\\n");\n'
        '    s.push_str(&format!("namespace GabbroDuty.{name}\\n\\n"));',
        "The body channel -- `autoImplicit` stays on. A hypothesis whose predicate Lean does "
        "not know then becomes a bound variable instead of an error; the theorem stands over "
        "nothing and looks proved",
        flaeche="annotation",
    ),
    Mutation(
        "lean-call-loses-its-callee",
        "lean.rs",
        # Was `lean-call-silently-dropped` until the call gate was built: the old anchor sat
        # on the arm that refused every call, and that arm is gone. **The weakening it
        # measured is still real, one line further on** -- two callees that collapse into
        # one name make a contract hypothesis about the first cover the second.
        'Ok((quoted(&name), names.join(", "), args.join(", ")))',
        'Ok((quoted("f"), names.join(", "), args.join(", ")))',
        "The program export -- every call names the same callee. A caller's proof would then "
        "take a contract that belongs to a different routine",
        flaeche="annotation",
    ),
    Mutation(
        "lean-and-becomes-or",
        "lean.rs",
        '        PredArt::Und(a, b) => Ok(format!(\n            "(.bin .and {} {})",',
        '        PredArt::Und(a, b) => Ok(format!(\n            "(.bin .or {} {})",',
        "The body channel -- the postcondition `a && b` becomes an OR. Both conjuncts are "
        "still there, and the duty is half as strong",
        flaeche="annotation",
    ),
    Mutation(
        "lean-field-shape-guessed",
        "lean.rs",
        "        Typ::Wahrheit => Some(Shape::Bool),",
        "        Typ::Wahrheit => Some(Shape::Int),",
        "The body channel -- a `bool` field gets the number shape. The hypothesis then "
        "stands over something other than the declaration, and that gate exists for exactly "
        "this",
        flaeche="annotation",
    ),
    Mutation(
        "lean-balance-lies",
        "lean.rs",
        "        entries.len()\n    ));\n    s.push_str(\"\\n    The meaning of a body",
        "        proved\n    ));\n    s.push_str(\"\\n    The meaning of a body",
        "The body channel -- the header reports the number of goals as the total. The "
        "balance seems to add up, and the module looks complete",
        flaeche="annotation",
    ),
    # ---------------------------------------------------------------------------------
    # THE PROGRAM EXPORT (`gabbro lean`) -- four weakenings. This artefact carries no
    # specification, so what it can lose is the PROGRAM: a routine, a place, a dropped
    # precondition, or the balance that would have shown the loss.
    # ---------------------------------------------------------------------------------
    Mutation(
        "lean-program-loses-a-routine",
        "lean.rs",
        '                "-- REFUSED  {}  ({}): {}\\n\\n",',
        '                "-- {}  {}  {}\\n\\n",',
        "The program export -- a routine outside the fragment no longer says REFUSED. It is "
        "still listed, but nothing marks it as absent, and a specification then stands over "
        "a program that is not there",
        flaeche="annotation",
    ),
    Mutation(
        "lean-program-balance-lies",
        "lean.rs",
        '        "        @program 1  units {}  routines {}  bodies {carried}  refused {refused}  places {}\\n",',
        '        "        @program 1  units {}  routines {}  bodies {carried}  refused 0  places {}\\n",',
        "The program export -- the header reports no refusals. The balance seems to add up, "
        "and the export looks complete",
        flaeche="annotation",
    ),
    Mutation(
        "lean-program-drops-in-silence",
        "lean.rs",
        '                "\\n\\n    DROPPED from the precondition (a hypothesis fewer makes the goal harder,\\n    never the proof wrong): {}",',
        '                "{}",',
        "The program export -- a precondition this channel cannot say is dropped WITHOUT a "
        "word. Dropping is the safe direction; dropping in silence takes the trust surface "
        "out of the file",
        flaeche="annotation",
    ),
    Mutation(
        "lean-program-autoimplicit-back-on",
        "lean.rs",
        # **The anchor carries the NEXT line too**, because the same `push_str` stands in the
        # obligation channel: an anchor that matched both would mutate whichever came first
        # and the report would name the wrong artefact.
        's.push_str("set_option autoImplicit false\\n\\nopen Gabbro.Body\\n\\n");\n'
        '    s.push_str("namespace GabbroProgram\\n\\n");',
        's.push_str("open Gabbro.Body\\n\\n");\n'
        '    s.push_str("namespace GabbroProgram\\n\\n");',
        "The program export -- `autoImplicit` stays on. A place name a specification "
        "misspells then becomes a bound variable instead of an error",
        flaeche="annotation",
    ),
    Mutation(
        "lean-call-becomes-an-inlining",
        "lean.rs",
        # **One gate for all three call forms since `call_parts` was factored out** -- and
        # that is the point of the factoring: three lookups would be three chances to drift.
        '    if !c.allow_calls {\n        return Err(LeanReason::CallStatement);\n    }',
        '    if false {\n        return Err(LeanReason::CallStatement);\n    }',
        "The body channel -- the OBLIGATION channel translates a call too. It writes a goal, "
        "and a goal over a body that calls needs the callee's contract as a hypothesis; "
        "without it the emitter states something no proof can close",
        flaeche="annotation",
    ),
    Mutation(
        "lean-call-loses-its-arguments",
        "lean.rs",
        'Ok((quoted(&name), names.join(", "), args.join(", ")))',
        'Ok((quoted(&name), names.join(", "), String::new()))',
        "The program export -- a call carries no arguments. The callee then runs on an empty "
        "binding, and a caller's proof would hold over a call nobody made",
        flaeche="annotation",
    ),
    Mutation(
        "lean-compound-ignores-the-shape",
        "lean.rs",
        "                    (ZuwOp::Und, Shape::Bool) => Some(\"and\"),",
        "                    (ZuwOp::Und, _) => Some(\"and\"),",
        "The body channel -- `&=` on an INTEGER field becomes a logical and. The model has "
        "the bit MASK for it (`.band`); taken as a truth value it computes something Gabbro "
        "does not, and on a number `binop .and` is not even defined -- the body would get "
        "stuck where it runs",
        flaeche="annotation",
    ),
    Mutation(
        "lean-remainder-becomes-a-division",
        "lean.rs",
        # **The sharpest confusion the seven new operators allow.** Both are carried now, so
        # a swap changes no balance and no refusal -- only the number the body computes.
        'BinOp::Rest => "rem",',
        'BinOp::Rest => "div",',
        "The body channel -- `a % b` is written as a division. Nothing is refused and the "
        "balance still adds up; the datum simply says the body computes a quotient where it "
        "computes a remainder",
        flaeche="annotation",
    ),
    Mutation(
        "lean-record-field-becomes-a-slot",
        "lean.rs",
        'return Ok(format!("(.fieldOf {} {})", quoted(&base), quoted(&f.text)));',
        'return Ok(format!("(.slot {} 0 {})", quoted(&base), quoted(&f.text)));',
        "The body channel -- a RECORD field is read as a slot at index zero. A record is one "
        "object and a table a row of them; as one `Place` a slot could alias a record field",
        flaeche="annotation",
    ),
    Mutation(
        "lean-reserved-field-gets-a-shape",
        "lean.rs",
        "if f.reserviert { None } else { shape_of(&f.typ.typ, u, module) },",
        "shape_of(&f.typ.typ, u, module),",
        "The program export -- a `reserved` field of a `format` gets a shape. It is not "
        "readable, and a hypothesis about its value is one about something the wire never "
        "promised",
        flaeche="annotation",
    ),
    Mutation(
        "lean-let-call-becomes-a-binding",
        "lean.rs",
        # **The mutation has to COMPILE.** The first version cut the `if let` and left `r`
        # unbound, so `cargo` refused it -- caught, but by the compiler and not by a probe.
        # *A weakening that only the build notices is caught by luck: change one line
        # elsewhere and it slips through in silence.*
        '"(.bindCall {} {n} [{ps}] [{args}])",',
        '"(.bindName {} {n} [{ps}] [{args}])",',
        "The body channel -- `let n = f(a);` is taken as an ordinary expression again. The "
        "callee vanishes from the datum, and the binding is left standing over nothing",
        flaeche="annotation",
    ),
    Mutation(
        "lean-return-call-becomes-a-value",
        "lean.rs",
        'return Ok(format!("(.retCall {n} [{ps}] [{args}])"));',
        'return Ok(format!("(.ret {n} [{ps}] [{args}])"));',
        "The body channel -- `return f(a);` is taken as a value expression. The call is lost "
        "and the return stands over a term nobody produced",
        flaeche="annotation",
    ),
    Mutation(
        "lean-loop-without-invariant-passes",
        "lean.rs",
        '            let Some(inv) = inv else {\n                return Err(LeanReason::Loop);\n            };',
        '            let Some(inv) = inv else {\n                return Ok("(.ret none)".into());\n            };',
        "The body channel -- a loop with NO `invariant` becomes a datum anyway. A proof over "
        "it would then conclude from a loop exactly nothing while looking like it concluded "
        "something -- and the word exists to stop that",
        flaeche="annotation",
    ),
    Mutation(
        "lean-loops-share-one-id",
        "lean.rs",
        'let id = format!("{}#{}", c.routine, c.loops);',
        'let id = format!("{}#1", c.routine);',
        "The body channel -- two loops of one routine share an environment entry. A "
        "hypothesis about the first would then silently cover the second",
        flaeche="annotation",
    ),
    Mutation(
        "lean-loop-variable-becomes-global",
        "lean.rs",
        '            if let Schleife::Traverse(x) = sch.as_ref() {\n                c.locals.push(x.variable.text.clone());\n            }',
        '            if false {\n                c.locals.push(String::new());\n            }',
        "The body channel -- the bound variable of a `traverse` is read as a world name. The "
        "datum then says the body touches a global nobody declared",
        flaeche="annotation",
    ),
    Mutation(
        "m133-invariante-darf-nichts-nennen",
        "m1.rs",
        "                    if namen.is_empty() {",
        "                    if false {",
        "`M133` -- eine Schleifeninvariante darf wieder nichts nennen. `invariant true` "
        "traegt danach eine GEZAEHLTE Pflicht, an der kein Beweiser scheitern kann",
    ),
    Mutation(
        "lean-lock-loses-its-name",
        "lean.rs",
        '        StmtArt::Sperrt(l) => Ok(format!(\n            "(.locked {} {})",',
        '        StmtArt::Sperrt(l) => Ok(format!(\n            "(.locked \\"\\" {}{})",',
        "The body channel -- a critical section loses its lock name. Its meaning is the "
        "body's, but the record then no longer says WHERE a lock was held, and two different "
        "sections become one",
        flaeche="annotation",
    ),
    Mutation(
        "lean-publish-loses-its-payload",
        "lean.rs",
        '                nutzlast(&pb.nutzlast)',
        '                String::new()',
        "The body channel -- a release store no longer names its payload. The datum then "
        "hides exactly which places rest on `release_stellt_sichtbarkeit_her` and not on the "
        "transition, and `publishes nothing` becomes indistinguishable from a real payload",
        flaeche="annotation",
    ),
    Mutation(
        "p6-balance-lies",
        "refinement.rs",
        "    let refused = entries.len() - proved;",
        "    let refused = 0;",
        "P6 -- der Erzeuger meldet null Absagen. Die Theorie sieht vollstaendig aus, und "
        "`goals + refused = total` ist genau die Zeile, die das verhindern soll",
        flaeche="annotation",
    ),
    # --- race ---
    #
    # **`H017` -- der Domaenenname ohne Deklaration.** Dieselbe Gestalt wie `H016` an der
    # Sperre, und die Gefahr ist hier groesser: der RCU-Waechter laeuft ueberhaupt nur in
    # einer Einheit, die eine Domaene deklariert. *Faellt `H017` aus, ist ein
    # `observes NIEDADOM { … }` wieder unsichtbar -- der Leser sieht einen Lesebereich, der
    # Pruefer sieht einen Block.*
    Mutation(
        "domaene-ohne-deklaration-geht-durch",
        "geteilt.rs",
        "            if domaenen.contains_key(&name) || !reported.insert(name.clone()) {",
        "            if true || !reported.insert(name.clone()) {",
        "H017 -- ein `observes` auf eine Domaene, die keine `rcu`-Deklaration erklaert, geht "
        "wieder mit null Fehlern durch",
    ),
    Mutation(
        # Die andere Richtung: die Regel laeuft, aber nur noch ueber den obersten
        # Anweisungsrand. Ein `observes` in einem `if`-Zweig oder in einer Schleife wird
        # unsichtbar -- **genau die Stelle, an der ein Leser im echten Kern steht.**
        "domaenenprobe-steigt-nicht-ab",
        "geteilt.rs",
        "        for k in crate::unterbloecke(s) {\n            observes_blocks(k, f);",
        "        for k in crate::unterbloecke(s).into_iter().take(0) {\n            observes_blocks(k, f);",
        "H017 -- die Domaenenprobe sieht nur den obersten Anweisungsrand; ein `observes` in "
        "einem Zweig oder einer Schleife nennt wieder, was es will",
    ),
    # --- build gate («TB», 2026-08-28) ---
    #
    # The gate is the one surface where a silent failure ships the check harness instead of
    # dropping it. All three mutations are shapes the rule could plausibly have had on the
    # first try -- the wrong direction, a name test that is not one, and a reserved name
    # guarded at one item kind out of twenty-three.
    Mutation(
        "gatter-haelt-die-falsche-richtung",
        "gatter.rs",
        "        if ist_gegattert(item) {\n            return;\n        }\n        let ItemArt::Funktion(f) = &item.art else { return };",
        "        if !ist_gegattert(item) {\n            return;\n        }\n        let ItemArt::Funktion(f) = &item.art else { return };",
        "G001 -- die Rufregel prueft die GEGENrichtung: ein gegatterter Rufer waere verboten "
        "und ein ungegatterter erlaubt. Der Auslieferungsbau bindet wieder nicht, und die "
        "Regel steht laut daneben",
    ),
    Mutation(
        "jeder-name-ist-ein-bau",
        "gatter.rs",
        "            if !ist_testbuild(w) {",
        "            if !matches!(&w.art, ExprArt::Ort(_)) {",
        "G002 -- jeder blosse Name gilt wieder als Bau. `when DEBUG` geht durch, und der "
        "Erzeuger laesst das Item stehen -- also gattert eine Klausel, die aussieht, als "
        "gattere sie",
    ),
    Mutation(
        "reservierter-name-nur-an-funktionen",
        "gatter.rs",
        "        if let Some(n) = item.art.name() {",
        "        if let Some(n) = item.art.name().filter(|_| matches!(item.art, ItemArt::Funktion(_))) {",
        "G003 -- der reservierte Name wird nur noch an Funktionen gehalten; ein "
        "`const TESTBUILD` steht wieder daneben und schaltet nichts",
    ),
    # --- opsruf (2026-08-28) ---
    #
    # **`D012` -- the premises of `beweise/Table_Ops_Erhaltung.thy` at the call site.** The
    # generator shipped that morning with them in a C COMMENT; if this rule goes silent, that
    # is exactly the state it returns to -- and a comment claiming a pass checks something is
    # the class `H007`/`H008` stand against.
    Mutation(
        "ops-ruf-braucht-keine-voraussetzung",
        "opsruf.rs",
        "        if steht.contains(&verlangt) {",
        "        if true || steht.contains(&verlangt) {",
        "D012 -- eine erzeugte Operation darf wieder gerufen werden, ohne dass ihre "
        "Voraussetzung irgendwo ueber dem Ruf steht",
    ),
    Mutation(
        # The other direction, and the sharper one: the rule RUNS and holds only the first
        # premise. `einfuegen_erhaelt` has two, and the second (`erreicht sigma p`) is the one
        # that keeps a fresh slot from being hung under an unreachable parent -- **a call site
        # that satisfies half a theorem looks careful.**
        "ops-ruf-haelt-nur-die-erste-voraussetzung",
        "opsruf.rs",
        "    for f in &kopf.forderungen {",
        "    for f in kopf.forderungen.iter().take(1) {",
        "D012 -- nur noch die ERSTE Voraussetzung wird gehalten; `erreicht sigma p` faellt "
        "unter den Tisch, und beispiele/gift/323 geht durch",
    ),
    # --- m3, «B18»: the register class per phase (2026-08-28) ---
    #
    # **Both surfaces can fail SILENTLY**, and the first is the load-bearing one: without the
    # intersection over all stages `heimlich` passes again, and the line from F4 (*"after
    # `queue_arm` no path can write `USED_IDX`"*) is back in the state of 2026-08-26 --
    # 0 errors, while the register still booked it as carried.
    Mutation(
        "phasenklasse-ohne-marke-schweigt",
        "m3.rs",
        "    if !bestimmt {",
        "    if false {",
        "R006 -- wo KEINE Marke der Ordnung im Sichtbereich ist, wird gar nichts geprueft; "
        "beispiele/gift/401 geht wieder durch, und mit ihm die tragende «B18»-Fundstelle",
    ),
    Mutation(
        "phasenklasse-darf-eine-stufe-verschweigen",
        "m3.rs",
        "                if !fehlend.is_empty() {",
        "                if false {",
        "R009 -- eine Phasenliste darf eine Stufe der Ordnung auslassen; das stille Loch, "
        "gegen das die Vollstaendigkeitspflicht steht, ist wieder da",
    ),
    # --- m3 and emit, «B26»: the device promise that LOWERS (2026-08-28) ---
    #
    # **The first is the falsifier itself.** Without `R011` the clause is a counted duty
    # again, and that is the state «B26» stood in from 2026-08-24 until today -- a booking
    # that reads as a discharge.
    #
    # **The third damages the LOWERING and not the refusal**, and it is the sharper one:
    # substituting the binding into the condition is what keeps the volatile read at ONE.
    # Drop it and the condition reads the device a SECOND time -- *two reads of a volatile
    # register are two values*, and the check is then about neither of them. **That is «B33»
    # word for word, in the generator instead of the checker**, and no probe on the checker
    # side sees it. `emittiert_fehlbare_lesung_einmal` is what catches it.
    Mutation(
        "geraeteversprechen-darf-blank-gelesen-werden",
        "m3.rs",
        "        for o in orte {",
        "        for o in orte.into_iter().take(0) {",
        "R011 -- eine fehlbare Registerlesung darf wieder blank stehen; beispiele/gift/405 "
        "geht durch, und `requires … else` ist zurueck bei der blossen Zaehlung",
    ),
    Mutation(
        "falsifikator-darf-ins-leere-nennen",
        "m3.rs",
        "        if !faelle.iter().any(|c| c == &f.text) {",
        "        if false {",
        "R010 -- das `else` am Register darf einen Fall nennen, den der `reason` nicht hat; "
        "der Erzeuger schriebe einen C-Bezeichner, den keine Zeile erklaert",
    ),
    Mutation(
        "fehlbare-lesung-liest-zweimal",
        "gabbro-check/src/emit.rs",
        "        .insert(r.text.clone(), l.name.text.clone());",
        "        .insert(String::new(), l.name.text.clone());",
        "«B26»-Absenkung -- die Bedingung liest das fluechtige Register ein ZWEITES Mal statt "
        "die Bindung; zwei Lesungen sind zwei Werte, und genau das ist «B33»",
        "code",
    ),
    # --- lean.rs, the collecting bucket (2026-08-28, `B1`) ---
    #
    # **Seventeen refusals stood under one word, and not one was a call over a contract**
    # (`messung/RUF-TOR.md`). The three mutations below hit the three surfaces that can fall
    # back silently -- and two of them leave the balance line untouched, which is why the
    # probes read the emitted TEXT and not only the count.
    Mutation(
        "lean-optionswert-ist-wieder-ein-ruf",
        "lean.rs",
        "            if let ExprArt::Ruf(r) = &l.wert.art {\n"
        "                if !is_option_value(r) {",
        "            if let ExprArt::Ruf(r) = &l.wert.art {\n"
        "                if true {",
        "Der Rumpfkanal -- `let n = Some(i);` laeuft wieder in `call_parts` statt in "
        "`expr_term`. Das Modell traegt `.someOf` seit dem ersten Tag, und der Rumpf wird "
        "trotzdem ganz abgesagt: eine Fehluebersetzung, die wie eine Luecke aussieht",
        flaeche="annotation",
    ),
    Mutation(
        "lean-sammeltopf-schliesst-sich-wieder",
        "lean.rs",
        "    let kind = foreign_kind(r, c);",
        "    let kind: Option<LeanReason> = None;",
        "Der Rumpfkanal -- erzeugte Operation, `transition` und Konstruktor fallen wieder "
        "unter `call-not-compositional`. Die Zahl bleibt dieselbe, der Bericht sagt "
        "wieder, der Kanal warte auf ein Tor, das keine dieser Stellen naehme",
        flaeche="annotation",
    ),
    Mutation(
        "lean-konstruktor-heisst-wieder-ruf",
        "lean.rs",
        "    if r.ist_verbundwert() {\n"
        "        return Some(LeanReason::ConstructedValue);",
        "    if false {\n"
        "        return Some(LeanReason::ConstructedValue);",
        "Der Rumpfkanal -- ein Verbundkonstruktor gilt wieder als Ruf. `Value` hat keine "
        "Verbundform, und das ist ein Modellpreis; ein fehlendes Tor ist ein anderer",
        flaeche="annotation",
    ),
    # --- lean.rs, the suspension (2026-08-28, `B2`) ---
    #
    # **A suspension is not an exit** (`messung/AUSSETZUNG.md`). Four obligations
    # went through Lean the moment `breaking` stopped being filed as one. The two mutations
    # below hold both halves: the reading itself, and the NAME that makes it sound.
    Mutation(
        "lean-aussetzung-heisst-wieder-ausgang",
        "lean.rs",
        "        StmtArt::Bricht(b) => {",
        "        StmtArt::Bricht(_) if true => Err(LeanReason::NonLocalExit),\n"
        "        StmtArt::Bricht(b) => {",
        "Der Rumpfkanal -- `breaking` faellt wieder unter `non-local-exit`. Vier Pflichten "
        "verlieren ihr Ziel, und der Bericht sagt wieder, der Kanal warte auf ein "
        "Schleifentor, obwohl keine der vier in einer Schleife steht",
        flaeche="annotation",
    ),
    Mutation(
        "lean-aussetzung-verliert-ihren-namen",
        "lean.rs",
        '            let namen: Vec<String> = b.invarianten.iter().map(|i| quoted(&i.text)).collect();',
        '            let namen: Vec<String> = Vec::new();',
        "Der Rumpfkanal -- die ausgesetzte Invariante reist nicht mehr im Datum. Das Ziel "
        "geht weiter durch, und genau das ist die Gefahr: die Stelle, an der die Aussetzung "
        "lag, ist aus dem Zeugnis verschwunden und kein Leser findet sie wieder",
        flaeche="annotation",
    ),
    # --- lean.rs, the result (2026-08-28, `B3` / «B6») ---
    #
    # **`result` is a name, and the goal that uses it must demand that a value AROSE.**
    # A body that runs off the end has none; a goal without the `finalValue` conjunct would
    # prove the promise of a routine that never makes one (`messung/VIER-LUECKEN.md`).
    Mutation(
        "lean-ergebnis-ohne-wert",
        "lean.rs",
        '                "        \\\\<and> finalValue (exec \\\\<rho> body_{} s) = some v\\n",',
        # **Twice wrong, and the second time was the instructive one** (2026-08-30, the first
        # full run over the merged state).
        #
        # It first injected `True \<and>` -- with ONE backslash, which is not a Rust escape,
        # so the mutated tree did not compile and the run booked `ungueltig`. *An invalid
        # mutation shrinks the denominator without saying so*: 337 of 339 read better than
        # 337 of 340, and the difference was a typo.
        #
        # With the escape repaired it compiled and SURVIVED -- correctly, because
        # `True \<and> X` is `X`. **A mutation that injects a tautology damages nothing**, and
        # a survivor over it is a statement about the mutation, not about the checker.
        #
        # What damages: restating the FIRST conjunct in place of the second. `v` is then
        # unbound under the existential, and the goal says *"there is SOME value for which the
        # promise holds"* instead of *"the body produced one, and it holds for that one"* --
        # exactly the weakening the entry describes. `lean_ergebnis_verlangt_dass_ein_wert_entstand`
        # catches it.
        '                "        \\\\<and> finalState (exec \\\\<rho> body_{} s) = some s\'\\n",',
        "Der Rumpfkanal -- das Glied, das einen ERZEUGTEN Wert verlangt, wird verwaessert. "
        "Ein Rumpf, der hinten hinauslaeuft, hat kein Ergebnis, und die Zusage ueber "
        "`result` ginge trotzdem durch",
        flaeche="annotation",
    ),
    # **Both mutations sit on the same `match` arm and damage different things.**
    #
    # Since 2026-08-30 that arm decides two things at once: WHETHER `result` is translated
    # inside a body, and UNDER WHICH NAME it is refused when it is not. The first mutation
    # takes the refusal away; the second leaves it standing and takes away its own name.
    # *The second did not exist before, because the second name did not exist.*
    Mutation(
        "lean-ergebnis-auch-im-rumpf",
        "lean.rs",
        "            ResultSite::Body => Err(LeanReason::ResultInBody),",
        "            ResultSite::Body => {\n"
        "                c.uses_result = true;\n"
        "                Ok(\"(.name \\\"result\\\")\".into())\n"
        "            }",
        "Der Rumpfkanal -- `result` wird auch im RUMPF uebersetzt, wo es keinen Wert nennt. "
        "Das Datum sagt danach, der Rumpf lese einen lokalen Namen, den niemand bindet",
        flaeche="annotation",
    ),
    Mutation(
        "lean-ergebnis-rumpf-unter-klauselnamen",
        "lean.rs",
        "            ResultSite::Body => Err(LeanReason::ResultInBody),",
        "            ResultSite::Body => Err(LeanReason::Result),",
        "Der Rumpfkanal -- die zwei Faelle fallen wieder unter EINEN Namen. Die Absage bleibt "
        "stehen und heisst `result-in-ensures`; der Erklaertext daneben spricht von einer "
        "Klausel und von einem Tor, das gebaut wurde. Wer das Zeugnis liest, sucht die "
        "fehlende Wertform und findet einen Programmfehler unter ihrem Etikett",
        flaeche="annotation",
    ),
    # --- lean.rs, the local (2026-08-28, `B5`) ---
    #
    # **A local written as a world place is a WRONG PROGRAM, not a refusal** -- and nothing
    # was red while it stood. The mutation below restores exactly that state, and its point is
    # that the balance line does not move: the body is still carried, the datum is still valid
    # Lean, and it describes a routine nobody wrote.
    Mutation(
        "lean-lokale-wird-wieder-global",
        "lean.rs",
        "                let ist_lokal = c.locals.iter().any(|l| *l == z.ziel.basis.text);",
        "                let ist_lokal = false;",
        "Der Rumpfkanal -- eine Zuweisung an ein `let mut` wird wieder als Weltspeicher "
        "uebersetzt. Der Rumpf bindet den Namen, schreibt an einen Ort, den niemand "
        "deklariert, und liest den Namen zurueck: das Datum sagt, die Routine gebe ihren "
        "Anfangswert zurueck",
        flaeche="annotation",
    ),
    Mutation(
        "let-gebundener-geist-wird-nicht-erkannt",
        "emit.rs",
        "            u.parametertyp\n"
        "                .get(&o.basis.text)\n"
        "                .is_some_and(|t| ist_geist(t, u))\n"
        "                || u.geistlokal.contains(&o.basis.text)",
        "            u.parametertyp\n"
        "                .get(&o.basis.text)\n"
        "                .is_some_and(|t| ist_geist(t, u))",
        "Ein blanker Name gilt wieder nur als Geist, wenn ein PARAMETER ihn traegt. Ein "
        "`let p1 = mmu_an(p); return p1;` verliert seine Bindung an der einen Stelle und "
        "behaelt den Namen an der anderen: das Erzeugnis schreibt `return p1;` in eine "
        "`void`-Funktion, auf einen Bezeichner, den es selbst geloescht hat -- zwei Fehler "
        "am `cc`, und keiner davon im Pruefer sichtbar",
        "code",
    ),
    Mutation(
        "let-else-ueber-place-verliert-den-typ",
        "m1.rs",
        "                    LetQuelle::Ort(o) => {\n"
        "                        let roh = self.u.typ_von_ort(&self.modul, o, &lage.lokal);\n"
        "                        match option_nutzlast(&roh) {\n"
        "                            Some(nutz) => nutz,\n"
        "                            None => roh,\n"
        "                        }\n"
        "                    }",
        "                    LetQuelle::Ort(_) => crate::typen::Typ::Unbekannt,",
        "M104 (Deckung) -- ein `let … else` ueber einem `place` bindet seinen Namen wieder "
        "ohne Typ. Derselbe Rumpf ueber einem RUF sagt `u32 + u8` ab, ueber einem Register "
        "geht er durch: die Quelle des `let` entscheidet, ob der Ueberlauf auffaellt, "
        "«B14b» band den Platz und niemand band seinen Typ",
    ),
    # -- emit.rs: the WIDTH of a floating point computation (2026-08-31) -----------------
    Mutation(
        "f32-literal-verliert-sein-f",
        "gabbro-check/src/emit.rs",
        '    if schmal { format!("{t}f") } else { t }',
        "    let _ = schmal;\n    t",
        "«F» -- ein Gleitkommaliteral neben einem `f32` faellt wieder auf `double` zurueck, "
        "und C hebt die ganze Rechnung mit. Gemessen ueber 200 000 Werten: das Erzeugnis "
        "rechnet dann in 39 990 Faellen etwas anderes als `v * 0.1f`, also etwas anderes als "
        "der Pruefer ueber `f32` gesagt hat. `-Wall -Wextra` sieht es NICHT -- es braucht "
        "`-Wdouble-promotion` oder `-Wfloat-conversion`, und keiner von beiden steht im Tor",
        "code",
    ),
    Mutation(
        "zweiter-prototyp-kommt-zurueck",
        "gabbro-check/src/emit.rs",
        "    if !definiert {\n        if let Some(kern) = eigene.get(&f.name.text) {",
        "    if false {\n        if let Some(kern) = eigene.get(&f.name.text) {",
        "Ein Name bekommt wieder ZWEI Prototypen: der aus der Definition traegt "
        "`__attribute__((const))`, der aus dem `extern fn` nicht -- zwei Deklarationen "
        "derselben C-Funktion mit verschiedenen Zusagen an den Uebersetzer. "
        "`-Wredundant-decls` nennt es, `-Wall -Wextra` nicht. Und die widersprechende Form "
        "(`u64` gegen `u32`) wird wieder emittiert statt abgesagt -- genau EINE Probe faellt",
        "code",
    ),
    Mutation(
        "index-verengt-sich-wieder-stillschweigend",
        "gabbro-check/src/emit.rs",
        '        Some(h) if h <= zmax => format!("({ziel})({text})"),',
        '        Some(h) if h <= zmax && false => format!("({ziel})({text})"),',
        "Ein `index into T` (`uint32_t`) wird wieder ohne Umwandlung in ein `u16`-Feld und "
        "in ein `u16`-Atomar geschrieben -- dieselbe Familie wie `F06`: der Pruefer kennt "
        "die Schranke (`count 8`, drei Bit reichen), der Erzeuger senkt 32 ab. "
        "`cc -Wconversion` nennt es zweimal, `-Wall -Wextra` nicht, und genau EINE Probe "
        "faellt",
        "code",
    ),
]

# Die Sprechprobe des Geruests selbst -- in beide Richtungen.
NULLMUTATION = Mutation(
    "NULLMUTATION",
    "m1.rs",
    "//! **Pass 3 -- M1 und die drei Flussregeln V1–V3.**",
    "//! **Pass 3 -- M1 und die drei Flussregeln V1–V3.** (Nullmutation)",
    "nichts -- diese MUSS ueberleben, sonst misst das Geruest die Datei statt die Regel",
)


def hash_von(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def proben_laufen():
    """`cargo test` -- gibt (uebersetzt, alle_gruen)."""
    r = subprocess.run(
        ["cargo", "test", "--quiet"],
        cwd=WURZEL,
        capture_output=True,
        text=True, timeout=FRIST)
    text = r.stdout + r.stderr
    uebersetzt = "error[E" not in text and "could not compile" not in text
    return uebersetzt, r.returncode == 0


def fahre(m):
    """Eine Mutation anwenden, pruefen, byteweise zuruecknehmen."""
    urtext = m.pfad.read_text()
    urhash = hashlib.sha256(urtext.encode()).hexdigest()
    if m.alt not in urtext:
        return "ANKER FEHLT", None
    if urtext.count(m.alt) != 1:
        return "ANKER MEHRDEUTIG", None
    try:
        m.pfad.write_text(urtext.replace(m.alt, m.neu, 1))
        uebersetzt, gruen = proben_laufen()
    finally:
        m.pfad.write_text(urtext)
        if hash_von(m.pfad) != urhash:
            raise SystemExit(f"WIEDERHERSTELLUNG FEHLGESCHLAGEN: {m.pfad}")
    if not uebersetzt:
        return "ungueltig", None
    return ("UEBERLEBT" if gruen else "gefangen"), gruen


def anker_stand():
    """**Greift jeder Anker noch?** Reines Textzaehlen -- kein Bau, keine Sekunde.

    *Das ist die Stelle, an der der Katalog still verwittert.* Ein Anker, den der umgebaute
    Quelltext nicht mehr enthaelt, faellt in `fahre` unter `ungueltig` und damit unter
    "zaehlt nicht mit" -- und die Quote `131 von 132` liest sich weiter wie Deckung, obwohl
    sie ueber einer SCHRUMPFENDEN Bezugsgroesse gerechnet ist. Genau W14: *die eigene
    Deckung wird um eine Groessenordnung zu hoch geschaetzt.*

    Gemessen 2026-08-19: **25 von 155 Ankern waren tot** (19 fehlten, 6 mehrdeutig), sechs
    davon durch den Umbau desselben Tages. Der volle Lauf haette das gemeldet -- nach
    Minuten, in einer Fussnote, ohne den Rueckgabewert zu beruehren.
    """
    tot = []
    for m in MUTATIONEN:
        n = m.pfad.read_text().count(m.alt)
        if n != 1:
            tot.append((m, "FEHLT" if n == 0 else f"MEHRDEUTIG ({n}x)"))
    return tot


def emissionseinheiten():
    """**How many translation units does `pruefe-emission.sh` actually build and run?**

    Read, not remembered. The guard names most units in one `lauf "<name>" …` line -- but
    **not all of them**, and that difference cost this function a first version: it counted
    23 while the harness printed *"24 durchgestochen"*. The library chain (stage 10) is a
    unit without a `lauf` call, and it raises the same counter one more time.

    > *A guard that reproduces a number by a DIFFERENT arithmetic is the second register it
    > was built to remove* (W7). So this counts the way the shell counts: every `lauf` call,
    > plus every raise of `N_DURCHGESTOCHEN` that does not stand inside `lauf()`. The one
    > inside the function is indented; the ones outside are not.

    Returns `(units, fragment units, fragments nobody runs)`. A fragment unit is one whose
    name reads `fragmentN`; the file it is cut from may be `messung/fragmente/F0N.gab` or a
    slice of `dokumente/FRAGMENTE.md`, and for this count that difference does not matter --
    what matters is that a fragment reached `cc` at all.
    """
    import re
    text = (WURZEL / "instrumente" / "pruefe-emission.sh").read_text()
    namen = re.findall(r'^lauf "([^"]+)"', text, re.M)
    ausserhalb = len(re.findall(r"^N_DURCHGESTOCHEN=\$\(\(N_DURCHGESTOCHEN \+ 1\)\)", text, re.M))
    zahlen = {int(m.group(1)) for n in namen if (m := re.fullmatch(r"fragment(\d+)", n))}
    alle = sorted(p.stem for p in (WURZEL / "messung" / "fragmente").glob("F*.gab"))
    ohne = [s for s in alle if int(s[1:]) not in zahlen]
    return len(namen) + ausserhalb, len(zahlen), ohne


def emissionsflaeche_satz():
    """The `code` row -- with the two numbers read off the harness (see `FLAECHEN`)."""
    einheiten, fragmente, ohne = emissionseinheiten()
    return (f"Die C-Emission. {einheiten} Uebersetzungseinheiten gebaut und mutierbar, "
            f"{fragmente} davon Fragmente; {len(ohne)} Fragmente laeuft niemand "
            f"({', '.join(ohne) if ohne else 'keins'}), und `C001` weigert sich fuer jede "
            f"Form, die diese Einheiten nicht brauchen.")


def flaechen_stand():
    """**Traegt jede Mutation eine Flaeche, die es GIBT?**

    Die Aufstellung je Flaeche zaehlt `m.flaeche == name` ueber `FLAECHEN`. Ein Tippfehler
    darin nimmt die Mutation aus jeder Zeile heraus, ohne irgendwo aufzufallen: die
    Gesamtzahl stimmt weiter, die Summe der Flaechen nicht -- und die beiden stehen nicht
    nebeneinander. *Genau so hat `"pass"` ueber Wochen eine Parsermutation aus der
    Bezugsgroesse gehalten.*
    """
    return [m for m in MUTATIONEN if m.flaeche not in FLAECHEN]


def emissionsflaeche_sprechprobe():
    """**Does the `code` row FALL when the harness loses a unit?**

    R11: a row that reads a number is only worth more than a remembered one if it is seen
    moving. The probe counts over the real file, then over a copy with one `lauf` line
    struck out -- and the second count has to be smaller.
    """
    import re
    einheiten, fragmente, ohne = emissionseinheiten()
    text = (WURZEL / "instrumente" / "pruefe-emission.sh").read_text()
    ohne_eine = re.subn(r'^lauf "fragment2"', '# lauf "weg"', text, count=1, flags=re.M)
    if ohne_eine[1] != 1:
        return False, "die Sprechprobe findet `lauf \"fragment2\"` nicht mehr"
    gekuerzt = re.findall(r'^lauf "([^"]+)"', ohne_eine[0], re.M)
    if len(gekuerzt) + 1 != len(re.findall(r'^lauf "([^"]+)"', text, re.M)):
        return False, "eine entfernte Einheit senkt die Zahl NICHT"
    # **The other half of the arithmetic -- the half missing from the first version:**
    # exactly ONE raise is indented inside `lauf()`; every other one counts on its own.
    drin = len(re.findall(r"^\s+N_DURCHGESTOCHEN=\$\(\(N_DURCHGESTOCHEN \+ 1\)\)", text, re.M))
    if drin != 1:
        return False, f"{drin} Erhoehungen stehen IN `lauf()` -- die Arithmetik stimmt nicht"
    if fragmente + len(ohne) != 10:
        return False, f"{fragmente} gelaufen + {len(ohne)} ungelaufen ist nicht 10"
    return True, f"{einheiten} Einheiten, {fragmente}/10 Fragmenten, {len(ohne)} ohne Lauf"


def anker_sprechprobe():
    """In beide Richtungen: ein toter Anker MUSS auffallen, ein lebender NICHT."""
    echt = anker_stand()
    gift = Mutation("SPRECHPROBE", "typen.rs", "diese Zeile steht nirgends", "", "")
    n = gift.pfad.read_text().count(gift.alt)
    print("  toter Anker faellt auf:  ", "ok" if n != 1 else "GESCHEITERT")
    print(f"  lebender Katalog still:  {'ok' if not echt else 'GESCHEITERT'}")
    return n != 1



def baumstand(wurzel=None):
    """`sauber` · `schmutzig` · `unbekannt` -- **und die dritte ist nicht die erste.**

    Measured on `ki-pc-fisch-101`, 2026-08-31: a server working copy arrives by `rsync`,
    so its `.git` file points at a worktree directory that does not exist there. `git
    status --porcelain crates/` then exits **128 with an EMPTY stdout** -- and the old
    version of this function read that as *"clean"*.

    > **The check that protects this run against measuring a mixture was vacuous on the
    > very machine the heavy runs belong on.** `abnahme.py --voll` calls it there. A
    > mutation run killed halfway leaves a mutated tree behind, and the next run then
    > measures a mixture -- `W16`, word for word, and the guard against it said `ok`.

    *An empty output from a command that FAILED is not an answer.* The three states are
    kept apart so that the caller cannot collapse them by accident.
    """
    r = subprocess.run(
        ["git", "status", "--porcelain", "crates/"],
        cwd=wurzel or WURZEL,
        capture_output=True,
        text=True, timeout=FRIST)
    if r.returncode != 0:
        return "unbekannt"
    return "sauber" if r.stdout.strip() == "" else "schmutzig"


def sauberer_baum():
    return baumstand() == "sauber"


def main():
    # **TOOTH 0 -- THE SUBJECT HAS TO BE THERE** (2026-08-31). Over a tree without
    # `crates/` this tool died inside `anker_stand()` of a `FileNotFoundError`: return code
    # **1**, a traceback, and in a chain that reads exactly like a dead anchor. *A crash is
    # not a refusal -- a NAMED refusal is*, and a missing subject says the SETUP has to
    # change, not the tree.
    fehlend = sorted({str(m.pfad.relative_to(WURZEL)) for m in MUTATIONEN
                      if not m.pfad.is_file()})
    if fehlend:
        print("ABBRUCH: %d Quelldatei(en) des Katalogs fehlen -- es wurde NICHTS gemessen."
              % len(fehlend), file=sys.stderr)
        print("  " + ", ".join(fehlend[:6])
              + (" ..." if len(fehlend) > 6 else ""), file=sys.stderr)
        return 2

    # **Der Ankerstand zuerst, und er kostet nichts.** Er braucht weder Bau noch sauberen
    # Baum -- und weil er der Teil ist, der still verwittert, laeuft er VOR allem anderen.
    # **Und die Flaechen zuerst, aus demselben Grund** (2026-08-21): eine Mutation mit einer
    # Flaeche, die es nicht gibt, faellt aus der Bezugsgroesse und aus keiner anderen Zahl.
    falsch = flaechen_stand()
    if falsch:
        print(f"== {len(falsch)} Mutationen tragen eine Flaeche, die es nicht gibt ==")
        for m in falsch:
            print(f"  !! {m.name:<44} flaeche={m.flaeche!r}")
        print("  Bekannt sind: " + ", ".join(FLAECHEN))
        print("  Eine unbekannte Flaeche nimmt die Mutation aus JEDER Zeile der Aufstellung.")
        return 1

    if "--anker" in sys.argv:
        # **Every fallen probe below ends with 2, not 1** (2026-08-31). A probe that falls
        # says the anchor check does not measure -- and the count printed underneath is then
        # about the tool, not about the catalogue. The DEAD ANCHORS at the end keep their 1:
        # that one is a finding ABOUT THE CATALOGUE, not a failure of the measurement.
        print("== Sprechprobe des Ankerpruefers ==")
        if not anker_sprechprobe():
            return 2
        # **R14 fuer den Flaechenpruefer**: er muss eine erfundene Flaeche sehen.
        gift = Mutation("SPRECHPROBE", "typen.rs", "x", "y", "z", "keine-flaeche")
        if gift.flaeche in FLAECHEN:
            print("  SPRECHPROBE GESCHEITERT: `keine-flaeche` steht in FLAECHEN")
            return 2
        print("  erfundene Flaeche faellt:  ok")
        # **R14 for the tree check, and it took a server run to notice it was missing.**
        # A directory that is no git repository must come back as `unbekannt`, never as
        # `sauber` -- that difference is the whole protection against measuring a mixture.
        with tempfile.TemporaryDirectory() as d:
            fremd = baumstand(d)
        eigen = baumstand()
        if fremd != "unbekannt":
            print(f"  SPRECHPROBE GESCHEITERT: ein Nicht-Repository meldet `{fremd}`")
            return 2
        if eigen not in ("sauber", "schmutzig"):
            print(f"  SPRECHPROBE GESCHEITERT: der eigene Baum meldet `{eigen}`")
            return 2
        print(f"  Baumstand unterscheidet:   ok (fremd `unbekannt`, eigen `{eigen}`)")
        # **R14 for the area row that READS its number** (2026-08-30). It replaces a number
        # that had stood wrong since 2026-08-17 -- and without this probe it would only be
        # another place where the same thing can happen.
        ok, wort = emissionsflaeche_sprechprobe()
        print(f"  Emissionsflaeche liest:    {'ok -- ' + wort if ok else 'GESCHEITERT: ' + wort}")
        if not ok:
            return 2
        tot = anker_stand()
        print(f"\n== {len(MUTATIONEN) - len(tot)} von {len(MUTATIONEN)} Ankern greifen ==")
        for m, warum in tot:
            print(f"  !! {warum:<16} {m.name:<44} {m.pfad.name}")
        if tot:
            print(f"\n  {len(tot)} Mutationen messen NICHTS. Die Quote laeuft sonst ueber")
            print("  einer schrumpfenden Bezugsgroesse und liest sich wie Deckung.")
            return 1
        print("  ALL PASS")
        return 0

    # **The ANCHOR check runs first, and since 2026-08-31 that order carries an argument.**
    # It is the DIRECT measurement of the hazard the tree check is here for: a mutation still
    # applied has lost its `alt` text, so it shows up below as a dead anchor and stops the
    # run. The git view sees one thing more -- UNCOMMITTED work somebody could lose -- and
    # that is the half which does not exist on a copy.
    tot = anker_stand()
    if tot:
        print(f"== {len(tot)} von {len(MUTATIONEN)} Ankern greifen ins Leere ==")
        for m, warum in tot:
            print(f"  !! {warum:<16} {m.name:<44} {m.pfad.name}")
        print("\n  Ein toter Anker misst nichts, faellt aber unter `ungueltig` und damit")
        print("  aus der Quote heraus -- sie wuerde ueber einer schrumpfenden Bezugsgroesse")
        print("  gerechnet und laese sich wie Deckung. `--anker` sagt dasselbe ohne Bau.")
        return 1

    stand = baumstand()
    if stand == "schmutzig":
        print("crates/ ist nicht sauber -- erst committen. Diese Probe schreibt in Quellen.")
        return 2
    # **And "git could not look" is a state of its own since 2026-08-31.** On a server copy
    # that arrived by `rsync`, `git status` fails with 128 and an EMPTY stdout -- which read
    # as "clean" until today, so the protection against measuring a mixture was inert on
    # exactly the machine the heavy runs belong on (`abnahme.py --voll` calls it there).
    #
    # **The run continues, and the reason stands here rather than in nobody's head:** the
    # anchor check above is the direct measurement of the hazard, and it passed. What the git
    # view sees ON TOP of that is uncommitted work somebody could lose -- and a transferred
    # copy has none. *A gap with a name is not a green tick, and not a red one either.*
    if stand == "unbekannt":
        print("== LUECKE MIT NAMEN: git konnte `crates/` nicht ansehen ==")
        print("   Der Baum ist WEDER sauber noch schmutzig, sondern ungemessen -- so faellt")
        print("   `git status` auf einer per `rsync` uebertragenen Kopie (128, leere Ausgabe).")
        print("   Der Lauf geht weiter, weil der ANKERSTAND oben dieselbe Gefahr direkt misst:")
        print("   eine noch angewandte Mutation hat ihren `alt`-Text verloren und faellt dort.")
        print("   Was der git-Blick zusaetzlich sieht, ist NICHT COMMITTETE Arbeit.")
        print()

    print("== Sprechprobe des Geruests ==")
    zustand, _ = fahre(NULLMUTATION)
    print(f"  Nullmutation: {zustand}")
    if zustand != "UEBERLEBT":
        print("  GESCHEITERT: eine Aenderung ohne Wirkung darf keine Probe brechen.")
        return 1
    gift = Mutation(
        "SPRECHPROBE",
        "typen.rs",
        "        self.min >= ziel.min && self.max <= ziel.max",
        "        let _ = ziel; true",
        "",
    )
    zustand, _ = fahre(gift)
    print(f"  Giftmutation: {zustand}")
    if zustand != "gefangen":
        print("  GESCHEITERT: das Geruest faengt nicht einmal eine tote Bereichspruefung.")
        return 1
    if "--schnell" in sys.argv:
        return 0

    print(f"\n== {len(MUTATIONEN)} Mutationen ==\n")
    ueberlebt, gefangen, ungueltig = [], 0, []
    for m in MUTATIONEN:
        zustand, _ = fahre(m)
        marke = {"UEBERLEBT": "!!", "gefangen": "  ", "ungueltig": "??"}.get(zustand, "??")
        print(f"  {marke} {zustand:<10} {m.name:<28} {m.regel}")
        if zustand == "UEBERLEBT":
            ueberlebt.append(m)
        elif zustand == "gefangen":
            gefangen += 1
        else:
            ungueltig.append((m, zustand))

    gueltig = gefangen + len(ueberlebt)
    print(f"\n== {gefangen} von {gueltig} gueltigen Mutationen gefangen", end="")
    if gueltig:
        print(f" ({100 * gefangen // gueltig} %) ==")
    else:
        print(" ==")
    # **Die ehrliche Bezugsgroesse: Mutationen JE FLAECHE.** Eine Gesamtzahl ueber der
    # einzigen gebauten Flaeche liest sich sonst wie Deckung ueber allen.
    print("\n== Mutationen je Emissionsflaeche ==")
    for name, satz in FLAECHEN.items():
        n = sum(1 for m in MUTATIONEN if m.flaeche == name)
        marke = "  " if n else "!!"
        # A row may be a CALLABLE -- then it reads its numbers instead of stating them.
        print(f"  {marke} {name:<12} {n:>3} Mutationen  -- {satz() if callable(satz) else satz}")
    print("\n  Eine Flaeche mit 0 Mutationen ist nicht gedeckt, sondern unbeschaedigbar.")
    print(f"  `{gefangen} von {gueltig}` misst den PRUEFER; ueber Annotation und Code sagt es nichts.")
    if ungueltig:
        print(f"   {len(ungueltig)} zaehlen nicht mit:")
        for m, z in ungueltig:
            print(f"     {m.name}: {z}")
    if ueberlebt:
        print("\n== UEBERLEBT -- eine VERMUTUNG, dass diese Regel unbewacht ist ==")
        # **Ein Ueberlebender ist eine Hypothese, kein Befund** (W13). Gemessen 2026-08-19:
        # eine reparierte Mutation vertauschte zwei `match`-Zweige ueber verschiedene
        # Varianten -- also gar keine Beschaedigung. Sie "ueberlebte" zwangslaeufig und las
        # sich wie ein Loch im Pruefer. **Eine Mutation, die nichts beschaedigt, ist
        # schlimmer als ein toter Anker**: der tote Anker sagt nichts, der Scheinbefund sagt
        # etwas Falsches. Jeder Ueberlebende wird von Hand gelesen, bevor er gebucht wird.
        for m in ueberlebt:
            print(f"  {m.name:<28} {m.regel}")
        print("\n  Eine ueberlebende Mutation heisst: die Regel koennte ausfallen, ohne dass")
        print("  eine einzige Probe faellt. Das ist genau die Richtung, in der am 2026-08-14")
        print("  zwoelf Loecher offenstanden.")
    return 1 if ueberlebt else 0


if __name__ == "__main__":
    sys.exit(main())
