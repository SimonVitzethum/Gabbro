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
    ./mutiere-pruefer.py --anker      nur der Ankerstand -- ohne Bau, ohne sauberen Baum
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
    # **Seit 2026-08-17 nicht mehr null.** Ein Fragment ist durchgestochen -- .gab -> C ->
    # cc -Werror -> ausgefuehrt -> verglichen (`pruefe-emission.sh`). Die Flaeche ist damit
    # beschaedigbar geworden, und das ist der ganze Unterschied: was 0 Mutationen hat, ist
    # nicht gedeckt, sondern unbeschaedigbar.
    "code": "Die C-Emission. ZWEI Uebersetzungseinheiten gebaut und mutierbar (ein Beispiel "
            "und Fragment F7, die Geistloeschung); acht Fragmente ungeprueft, und `C001` "
            "weigert sich fuer jede Form, die diese beiden nicht brauchen.",
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
        "                    if !gehalten.iter().any(|h| h == sperre) && !fehlend.contains(sperre) {",
        "                    if gehalten.is_empty() && !fehlend.contains(sperre) {",
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
        '        // `Some`/`None` sind Konstruktoren, keine Aufrufe (s. «B35»).\n        if n.text != "Some" && n.text != "None" && !r.ist_verbundwert() {',
        '        // `Some`/`None` sind Konstruktoren, keine Aufrufe (s. «B35»).\n        if true {',
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
        "        _ => {\n            weigere(absagen, e.span, \"expression form\");\n            String::new()\n        }",
        "        _ => \"0\".into(),",
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
        "                        if c > 0 && n / c > 0 {\n                            aus.insert(r.span.von, n / c);",
        "                        if c > 0 && n > 0 {\n                            aus.insert(r.span.von, n);",
        "C-Absenkung -- `bounded N ops` wird als Durchgangszahl gelesen statt als Operationsbudget",
        "code",
    ),
    Mutation(
        "on-exceeded-darf-zurueckkehren",
        "emit.rs",
        "    if !u.funktionen.get(ausgang).is_some_and(|s| s.nie_rueck) {",
        "    if false && !u.funktionen.get(ausgang).is_some_and(|s| s.nie_rueck) {",
        "C-Absenkung -- `on_exceeded` darf auf etwas zeigen, das zurueckkehrt; die Schleife dreht weiter",
        "code",
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
        "            let bedingung = if untere_ist_null && vorzeichenlos.contains(&n.ort.basis.text) {",
        "            let bedingung = if untere_ist_null {",
        "C-Absenkung -- die untere `narrow`-Pruefung faellt auch fuer vorzeichenbehaftete Werte weg",
        "code",
    ),
    # -- emit.rs: `traverse` und `if` ------------------------------------------------------
    Mutation(
        "traversierung-laesst-den-letzten-aus",
        "emit.rs",
        "\"{e}for (uint32_t {v} = 0; {v} < (uint32_t)(sizeof({feld}) / sizeof({feld}[0])); {v}++) {{\\n\"",
        "\"{e}for (uint32_t {v} = 0; {v} + 1 < (uint32_t)(sizeof({feld}) / sizeof({feld}[0])); {v}++) {{\\n\"",
        "C-Absenkung -- die Traversierung laesst den letzten Slot aus; die Domaene ist nicht mehr vollstaendig",
        "code",
    ),
    Mutation(
        "traversierung-nimmt-den-punkt",
        "emit.rs",
        "            let feld = format!(\"{}->slots\", ort(o, u, absagen));",
        "            let feld = format!(\"{}.slots\", ort(o, u, absagen));",
        "C-Absenkung -- die Domaene greift durch den Zeiger mit `.` statt `->`",
        "code",
    ),
    Mutation(
        "zeugenordnung-egal",
        "emit.rs",
        "            if !matches!(x.abstieg, Abstieg::Unbesucht) {",
        "            if false && !matches!(x.abstieg, Abstieg::Unbesucht) {",
        "C-Absenkung -- `by consuming`/`by decreasing` laufen wie `by unvisited`",
        "code",
    ),
    Mutation(
        "forever-wird-abgesenkt",
        "emit.rs",
        "            Schleife::Forever(_) => weigere(",
        "            Schleife::Forever(_) => nichts_tun(",
        "C-Absenkung -- `forever` wird still uebergangen statt abgelehnt; `on_exceeded` faellt weg",
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
        "                \"(*(volatile {breite} *)({}->basis + {versatz}))\",",
        "                \"(*({breite} *)({}->basis + {versatz}))\",",
        "C-Absenkung -- ein Registerzugriff darf wegoptimiert werden",
        "code",
    ),
    Mutation(
        "dma-wird-abgesenkt",
        "emit.rs",
        "    if !matches!(d.raum, Raum::Mmio) {",
        "    if false && !matches!(d.raum, Raum::Mmio) {",
        "C-Absenkung -- `at dma` wird ohne Barriere abgesenkt, die M3 ausdruecklich nicht baut",
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
        "                nimm(&Ruf { pfad: Pfad { teile: vec![l.name.clone()], span: l.name.span }, argumente: vec![], marken: vec![], span: l.name.span }, aus);",
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
        '        // `Some`/`None` sind Konstruktoren, keine Aufrufe (s. «B35»).\n        if n.text != "Some" && n.text != "None" && !r.ist_verbundwert() {',
        '        // `Some`/`None` sind Konstruktoren, keine Aufrufe (s. «B35»).\n        if n.text != "Some" && n.text != "None" {',
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
        "atomic_store_explicit(&{ziel}, {}, {ordnung});",
        "{ziel} = {}; /* {ordnung} */",
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
        "zeugnis-schluckt-unbekannte-anweisungen",
        "zeugnis.rs",
        '            StmtArt::Bricht(_) => e.unzugeordnet.push("breaking".into()),',
        "            StmtArt::Bricht(_) => {}",
        "K100.4 -- dasselbe eine Ebene tiefer: eine Anweisung faellt still aus der Buchung",
    ),
    Mutation(
        "verbund-ohne-marken-geht-durch",
        "m1.rs",
        "        let gefunden = self.u.verbundfelder(&self.modul, &r.pfad).cloned();",
        "        let gefunden = if r.ist_verbundwert() { self.u.verbundfelder(&self.modul, &r.pfad).cloned() } else { None };",
        "B7 -- `P(1, 2)` ohne Feldnamen faellt nicht mehr; zwei gleichtypige Felder "
        "sind vertauschbar, ohne dass ein Typ dagegen spricht",
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


def anker_sprechprobe():
    """In beide Richtungen: ein toter Anker MUSS auffallen, ein lebender NICHT."""
    echt = anker_stand()
    gift = Mutation("SPRECHPROBE", "typen.rs", "diese Zeile steht nirgends", "", "")
    n = gift.pfad.read_text().count(gift.alt)
    print("  toter Anker faellt auf:  ", "ok" if n != 1 else "GESCHEITERT")
    print(f"  lebender Katalog still:  {'ok' if not echt else 'GESCHEITERT'}")
    return n != 1



def sauberer_baum():
    r = subprocess.run(
        ["git", "status", "--porcelain", "crates/"],
        cwd=WURZEL,
        capture_output=True,
        text=True,
    )
    return r.stdout.strip() == ""


def main():
    # **Der Ankerstand zuerst, und er kostet nichts.** Er braucht weder Bau noch sauberen
    # Baum -- und weil er der Teil ist, der still verwittert, laeuft er VOR allem anderen.
    if "--anker" in sys.argv:
        print("== Sprechprobe des Ankerpruefers ==")
        if not anker_sprechprobe():
            return 1
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

    if not sauberer_baum():
        print("crates/ ist nicht sauber -- erst committen. Diese Probe schreibt in Quellen.")
        return 2

    tot = anker_stand()
    if tot:
        print(f"== {len(tot)} von {len(MUTATIONEN)} Ankern greifen ins Leere ==")
        for m, warum in tot:
            print(f"  !! {warum:<16} {m.name:<44} {m.pfad.name}")
        print("\n  Ein toter Anker misst nichts, faellt aber unter `ungueltig` und damit")
        print("  aus der Quote heraus -- sie wuerde ueber einer schrumpfenden Bezugsgroesse")
        print("  gerechnet und laese sich wie Deckung. `--anker` sagt dasselbe ohne Bau.")
        return 1

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
