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

    ./mutiere-pruefer.py              alle Mutationen
    ./mutiere-pruefer.py --schnell    nur die Sprechprobe des Geruests
"""
import hashlib
import pathlib
import subprocess
import sys

WURZEL = pathlib.Path(__file__).resolve().parent
CHECK = WURZEL / "crates" / "gabbro-check" / "src"


# **Die Emissionsflaechen -- und die Bezugsgroesse, die 32/32 sonst verschweigt.**
# `32 von 32` ist ein Verhaeltnis ueber DER FLAECHE, die es beschaedigen kann. Wo nichts
# emittiert wird, kann nichts mutieren -- und eine Gesamtzahl liest sich dann wie Deckung.
FLAECHEN = {
    "pruefer": "Der Pruefer (Absagen). Gebaut, mutierbar.",
    "annotation": "Die ANNOTATIONSEMISSION -- der Wunschform-Kanal. NICHT GEBAUT, also "
                  "nicht mutierbar: ein Erzeuger, der stillschweigend abgeschwaechte "
                  "Vertraege ausgibt, liefert einen gruenen Beweis ueber eine schwaechere "
                  "Aussage, und keine Probe faengt ihn.",
    "code": "Die C-Emission. NICHT GEBAUT, also nicht mutierbar.",
    "schablone": "Die Erzeuger-Schablonen (16, keine bewiesen). Ueberwiegend ENTWORFEN -- "
                 "was kein Code ist, kann keine Mutation fangen.",
}


class Mutation:
    def __init__(self, name, datei, alt, neu, regel, flaeche="pruefer"):
        self.name = name
        self.pfad = CHECK / datei
        self.alt = alt
        self.neu = neu
        self.regel = regel
        self.flaeche = flaeche


# Jede Mutation beschaedigt GENAU EINE Regel. Der Text daneben sagt, welche -- wer eine
# Mutation ueberleben sieht, weiss damit sofort, was heute unbewacht ist.
MUTATIONEN = [
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
        "        self.min >= lo && self.max <= hi\n    }\n\n    pub fn enthaelt_null",
        "        let (lo, hi) = grenzen(self.breite, self.vorzeichen);\n"
        "        let _ = (lo, hi);\n        true\n    }\n\n    pub fn enthaelt_null",
        "M104 -- kein Ueberlauf verlaesst je die Breite",
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
        "    ergebnis(breite, vz, a.min - b.max, a.max - b.min)",
        "    ergebnis(breite, vz, a.min - b.min, a.max - b.min)",
        "die Untergrenze der Subtraktion (Unterlauf wird unsichtbar)",
    ),
    Mutation(
        "addition-zu-eng",
        "typen.rs",
        "    ergebnis(breite, vz, a.min + b.min, a.max + b.max)",
        "    ergebnis(breite, vz, a.min + b.min, a.max + b.min)",
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
        "    fn index_pruefen(&mut self, o: &Ort, lage: &Lage) {\n        let mut traeger",
        "    fn index_pruefen(&mut self, o: &Ort, lage: &Lage) {\n"
        "        if true {\n            let _ = (o, lage);\n            return;\n        }\n"
        "        let mut traeger",
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
        "                lage.fakten\n                    .retain(|f| !nennt_namen(f, &l.name.text));\n"
        "                lage.lokal\n                    .insert(l.name.text.clone(), ziel.unwrap_or(wert));",
        "                lage.lokal\n                    .insert(l.name.text.clone(), ziel.unwrap_or(wert));",
        "U2 -- eine neue Bindung erbt den Fakt ihres Vorgaengers",
    ),
    Mutation(
        "wrapping-ueberall",
        "m1.rs",
        "                if !ziel.laeuft_um() {\n"
        "                    self.passt(&ergebnis_typ, &ziel, z.wert.span, \"die Zuweisung\");\n"
        "                }",
        "                if ziel.laeuft_um() {\n"
        "                    self.passt(&ergebnis_typ, &ziel, z.wert.span, \"die Zuweisung\");\n"
        "                }",
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
        "            if !endet_immer(&l.sonst, div) {",
        "            if false && !endet_immer(&l.sonst, div) {",
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
    Mutation(
        "index-erbt-nicht",
        "umgebung.rs",
        "                    .find_map(|k| self.kapazitaeten.get(&k).copied())\n"
        "                    .map(|n| IntBereich::genau(32, false, 0, n as i128 - 1))",
        "                    .find_map(|k| self.kapazitaeten.get(&k).copied())\n"
        "                    .map(|_| IntBereich::voll(32, false))",
        "A3 -- `index into T` erbt die Schranke aus `count` nicht",
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
        "                if n > zusage {",
        "                if false && n > zusage {",
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
        "traversierung-kostenlos",
        "kosten.rs",
        "                (Kosten::Zahl(rumpf), Some(n)) => Kosten::Zahl(rumpf * n),",
        "                (Kosten::Zahl(rumpf), Some(_)) => Kosten::Zahl(rumpf),",
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
        "            .is_some_and(|n| div.iter().any(|d| d == &n.text)),",
        "            .is_some_and(|n| div.iter().any(|d| d == &n.text) && false),",
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
        "            if !alle_erwartet.contains(o) {",
        "            if !h.erwartet.iter().any(|(x, _)| x == o) {",
        "V001 -- die Paarung sieht nur die EIGENE Funktion, nicht die vereinigte Menge",
    ),
    Mutation(
        "verwaistes-awaits-egal",
        "paarung.rs",
        "            if !alle_publiziert.contains(o) {",
        "            if false && !alle_publiziert.contains(o) {",
        "V002 -- ein `awaits` ohne Gegenstueck darf stehen (liest gueltigen Muell)",
    ),
    Mutation(
        "relaxed-darf-tragen",
        "paarung.rs",
        "                        if ist_relaxed {",
        "                        if false && ist_relaxed {",
        "V004 -- `relaxed` darf eine Nutzlast tragen, die es nicht ordnet",
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
        text=True,
    )
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


def sauberer_baum():
    r = subprocess.run(
        ["git", "status", "--porcelain", "crates/"],
        cwd=WURZEL,
        capture_output=True,
        text=True,
    )
    return r.stdout.strip() == ""


def main():
    if not sauberer_baum():
        print("crates/ ist nicht sauber -- erst committen. Diese Probe schreibt in Quellen.")
        return 2

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
        print(f"  {marke} {name:<12} {n:>3} Mutationen  -- {satz}")
    print("\n  Eine Flaeche mit 0 Mutationen ist nicht gedeckt, sondern unbeschaedigbar.")
    print(f"  `{gefangen} von {gueltig}` misst den PRUEFER; ueber Annotation und Code sagt es nichts.")
    if ungueltig:
        print(f"   {len(ungueltig)} zaehlen nicht mit:")
        for m, z in ungueltig:
            print(f"     {m.name}: {z}")
    if ueberlebt:
        print("\n== UEBERLEBT -- jede dieser Regeln ist heute unbewacht ==")
        for m in ueberlebt:
            print(f"  {m.name:<28} {m.regel}")
        print("\n  Eine ueberlebende Mutation heisst: die Regel koennte ausfallen, ohne dass")
        print("  eine einzige Probe faellt. Das ist genau die Richtung, in der am 2026-08-14")
        print("  zwoelf Loecher offenstanden.")
    return 1 if ueberlebt else 0


if __name__ == "__main__":
    sys.exit(main())
