//! **Blindstellen: eine Form, die der Korpus nicht ausloest.**
//!
//! Am 2026-08-20 fand der erste Treiber, der nicht aus dem Entwurf kam, fuenf Fehler an einem
//! Nachmittag. Drei davon waren **ungebaute Haelften**: `SPRACHE.md`:355 sagte einen
//! `format`-Schreiber zu und es gab nur den Leser; die Geistloeschung liess `return m;`
//! stehen; die nominale Gleichheit wurde am Ruf nicht gehalten.
//!
//! **Keiner von ihnen war monatelang aufgefallen, und der Grund ist in allen drei Faellen
//! derselbe:**
//!
//! | Befund | die Form, die niemand schrieb |
//! |---|---|
//! | Geist-`return` | ein Geist in der RUECKGABE einer Funktion **mit Rumpf** |
//! | `format`-Schreiber | ein Formatfeld in SCHREIBSTELLUNG |
//! | nominale Gleichheit | zwei nominale Typen ueber demselben Traeger |
//!
//! Der Korpus ist **von der Sprache nach aussen** geschrieben -- eine Datei je Konstrukt --
//! und nie von einem Programm nach innen. Eine Datei je Konstrukt deckt jedes Konstrukt
//! einmal; die Fehler sitzen an den **Kombinationen**.
//!
//! ## Was dieses Werkzeug tut
//!
//! Es zaehlt **Form mal Stellung** ueber einer Menge Dateien und nennt die leeren Felder.
//! Eine Null heisst: *diese Form kommt in dieser Stellung nirgends vor* -- also kann keine
//! Probe, kein Waechter und keine Mutation sie ausloesen.
//!
//! > Es ist dieselbe Bauart wie `mutiere-pruefer.py`, eine Ebene hoeher. Dort gilt: *was 0
//! > Mutationen hat, ist nicht gedeckt, sondern unbeschaedigbar.* Hier: **was 0 Fundstellen
//! > hat, ist nicht geprueft, sondern unerreichbar.**
//!
//! ## Und was es NICHT sagt
//!
//! Eine besetzte Zelle heisst **nicht**, dass die Form richtig abgesenkt wird -- nur, dass
//! ein Pass sie sehen KANN. Zwei der fuenf Befunde faengt dieses Werkzeug darum gar nicht:
//! die Geraetegegenseite («V9») ist keine fehlende Form, sondern eine fehlende Kategorie,
//! und ein Rumpf, den ein Pass nicht LIEST, steht im Korpus sehr wohl da.
//!
//! *Auch das ist eine Zahl mit einer Grenze daneben, und die Grenze steht in der Ausgabe.*

use gabbro_syntax::ast::*;
use std::collections::BTreeMap;

/// Form x Stellung -> wie oft.
type Tafel = BTreeMap<(&'static str, &'static str), usize>;

fn zaehle(t: &mut Tafel, form: &'static str, stellung: &'static str) {
    *t.entry((form, stellung)).or_insert(0) += 1;
}

/// Die Typklasse eines Namens -- **und nur die vier nominalen plus die drei Traeger**.
fn typklassen(baum: &Programm) -> BTreeMap<String, &'static str> {
    let mut aus = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Typ(t) => {
            let k = if t.ghost {
                "ghost"
            } else if t.linear {
                "linear"
            } else if t.tagged {
                "tagged"
            } else if t.opaque {
                "opaque"
            } else if matches!(&t.rumpf, Some(TypExpr::Verbund(f, _)) if !f.is_empty()) {
                "verbund"
            } else {
                "bereich"
            };
            aus.insert(t.name.text.clone(), k);
        }
        ItemArt::Format(f) => {
            aus.insert(f.name.text.clone(), "format");
        }
        ItemArt::Tabelle(t) => {
            aus.insert(t.name.text.clone(), "table");
        }
        ItemArt::Device(d) => {
            aus.insert(d.name.text.clone(), "device");
        }
        _ => {}
    });
    aus
}

fn klasse_von<'a>(t: &TypExpr, k: &'a BTreeMap<String, &'static str>) -> Option<&'static str> {
    match t {
        TypExpr::Pfad(p) => p.teile.last().and_then(|i| k.get(&i.text)).copied(),
        TypExpr::Zeiger(z) => klasse_von(&z.ziel, k),
        _ => None,
    }
}

/// **Tafel A: eine Typklasse in einer Stellung.**
///
/// Hier faellt das Geist-`return` auf: `ghost` x `rueckgabe (rumpf)` ist null, weil
/// `beispiele/22` die ganze Bootstrecke als `extern fn` fuehrt -- also Prototypen, also
/// keine Ruempfe.
fn tafel_typen(baum: &Programm, t: &mut Tafel) {
    let k = typklassen(baum);
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Funktion(f) => {
            let hat_rumpf = matches!(f.rumpf, FnRumpf::Block(_));
            for p in &f.parameter {
                if let Some(c) = klasse_von(&p.typ, &k) {
                    zaehle(t, c, "parameter");
                }
            }
            if let Some(e) = &f.ergebnis {
                if let Some(c) = klasse_von(e, &k) {
                    zaehle(t, c, if hat_rumpf { "rueckgabe (rumpf)" } else { "rueckgabe (prototyp)" });
                }
            }
            if let FnRumpf::Block(b) = &f.rumpf {
                fn lets(b: &Block, k: &BTreeMap<String, &'static str>, t: &mut Tafel) {
                    for s in &b.anweisungen {
                        if let StmtArt::Let(l) = &s.art {
                            if let Some(c) = l.typ.as_ref().and_then(|x| klasse_von(x, k)) {
                                zaehle(t, c, "let-klausel");
                            }
                        }
                        for u in crate::unterbloecke(s) {
                            lets(u, k, t);
                        }
                    }
                }
                lets(b, &k, t);
            }
        }
        ItemArt::Statisch(s) => {
            if let Some(c) = klasse_von(&s.typ, &k) {
                zaehle(t, c, "static");
            }
        }
        ItemArt::Tabelle(tb) => {
            for f in tb.slot.iter().flat_map(|s| s.felder.iter()) {
                if let SlotTyp::Typ(x) = &f.typ {
                    if let Some(c) = klasse_von(x, &k) {
                        zaehle(t, c, "slotfeld");
                    }
                }
            }
        }
        _ => {}
    });
}

/// **Tafel B: eine Ortsart in einer Zugriffsart.**
///
/// Hier faellt der fehlende `format`-Schreiber auf: `formatfeld` x `geschrieben` ist null,
/// weil alle Korpusformate PARSER sind und keines je einen Rahmen stellt.
fn tafel_orte(baum: &Programm, t: &mut Tafel) {
    let k = typklassen(baum);
    // Name -> Ortsart, aus den Parametern und `static`-Deklarationen dieser Einheit.
    let mut art: BTreeMap<String, &'static str> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Statisch(s) => {
            art.insert(s.name.text.clone(), "static");
        }
        ItemArt::Atomic(a) => {
            art.insert(a.name.text.clone(), "atomic");
        }
        ItemArt::Accumulates(a) => {
            art.insert(a.name.text.clone(), "accumulates");
        }
        _ => {}
    });
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let mut lokal = art.clone();
        for p in &f.parameter {
            let a = match klasse_von(&p.typ, &k) {
                Some("format") => "formatfeld",
                Some("table") => "slotfeld",
                Some("device") => "register",
                Some("verbund") => "verbundfeld",
                _ => continue,
            };
            lokal.insert(p.name.text.clone(), a);
        }
        fn im_block(b: &Block, lokal: &BTreeMap<String, &'static str>, t: &mut Tafel) {
            for s in &b.anweisungen {
                if let StmtArt::Zuweisung(z) = &s.art {
                    if let Some(a) = lokal.get(&z.ziel.basis.text) {
                        zaehle(
                            t,
                            a,
                            if matches!(z.op, ZuwOp::Setzt) { "geschrieben" } else { "+= u.ae." },
                        );
                    }
                }
                for e in crate::eigene_ausdruecke(s) {
                    for o in crate::alle_orte(e) {
                        if let Some(a) = lokal.get(&o.basis.text) {
                            zaehle(t, a, "gelesen");
                        }
                    }
                }
                for u in crate::unterbloecke(s) {
                    im_block(u, lokal, t);
                }
            }
        }
        im_block(b, &lokal, t);
    });
}

/// **Tafel C: eine Anweisungsart in einem Rumpf.**
///
/// Hier faellt auf, welche Formen ausschliesslich auf der obersten Ebene stehen -- und damit,
/// welche Regel ueber Verschachtelung noch nie eine Fundstelle hatte. *`O006` und `H012` sind
/// beide daran gefallen: eine Regel, die an der Einrueckung endet, ist keine Regel ueber den
/// Fluss.*
fn tafel_anweisungen(baum: &Programm, t: &mut Tafel) {
    fn name(s: &Stmt) -> &'static str {
        match &s.art {
            StmtArt::Let(_) => "let",
            StmtArt::LetSonst(_) => "let … else",
            StmtArt::Zuweisung(_) => "zuweisung",
            StmtArt::Wenn(_) => "if",
            StmtArt::Match(_) => "match",
            StmtArt::Sperrt(_) => "locks",
            StmtArt::Observiert(_) => "observes",
            StmtArt::Narrow(_) => "narrow",
            StmtArt::Publish(_) => "publishes",
            StmtArt::AwaitLoad(_) => "awaits",
            StmtArt::Exchange(_) => "exchange",
            StmtArt::Bricht(_) => "breaking",
            StmtArt::Return(_) => "return",
            StmtArt::Leave(_) => "leave",
            StmtArt::Next(_) => "next",
            StmtArt::Ruf(_) => "ruf",
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(_) => "traverse",
                Schleife::Retry(_) => "retry",
                Schleife::Forever(_) => "forever",
            },
        }
    }
    fn im_block(b: &Block, wo: &'static str, t: &mut Tafel) {
        for s in &b.anweisungen {
            zaehle(t, name(s), wo);
            let innen: &'static str = match &s.art {
                StmtArt::Sperrt(_) => "in locks",
                StmtArt::Wenn(_) => "in if",
                StmtArt::Match(_) => "in match",
                StmtArt::Schleife(sch) => match sch.as_ref() {
                    Schleife::Traverse(_) => "in traverse",
                    Schleife::Retry(_) => "in retry",
                    Schleife::Forever(_) => "in forever",
                },
                _ => wo,
            };
            for u in crate::unterbloecke(s) {
                im_block(u, innen, t);
            }
        }
    }
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Funktion(f) => {
            if let FnRumpf::Block(b) = &f.rumpf {
                im_block(b, "fn-rumpf", t);
            }
        }
        ItemArt::Check(c) => im_block(&c.can_fail, "can_fail", t),
        _ => {}
    });
}

/// Eine Tafel als Text -- **und die leeren Felder ZUERST**, denn sie sind der Gegenstand.
fn zeige_tafel(
    titel: &str,
    was: &str,
    formen: &[&'static str],
    stellungen: &[&'static str],
    t: &Tafel,
    aus: &mut String,
    blind: &mut usize,
) {
    aus.push_str(&format!("\n== {titel} ==\n   {was}\n\n"));
    let breite = formen.iter().map(|f| f.len()).max().unwrap_or(8).max(8);
    aus.push_str(&format!("   {:breite$} ", ""));
    for s in stellungen {
        aus.push_str(&format!("{:>20} ", s));
    }
    aus.push('\n');
    for f in formen {
        aus.push_str(&format!("   {f:breite$} "));
        for s in stellungen {
            match t.get(&(*f, *s)) {
                Some(n) => aus.push_str(&format!("{n:>20} ")),
                None => aus.push_str(&format!("{:>20} ", "--")),
            }
        }
        aus.push('\n');
    }
    aus.push('\n');
    for f in formen {
        for s in stellungen {
            if !t.contains_key(&(*f, *s)) {
                *blind += 1;
                aus.push_str(&format!("   BLIND  {f} in Stellung `{s}`\n"));
            }
        }
    }
}

/// **Die Blindstellen einer Dateimenge.**
pub fn zeige(baeume: &[Programm]) -> String {
    let (mut a, mut b, mut c) = (Tafel::new(), Tafel::new(), Tafel::new());
    for baum in baeume {
        tafel_typen(baum, &mut a);
        tafel_orte(baum, &mut b);
        tafel_anweisungen(baum, &mut c);
    }
    let mut aus = String::new();
    aus.push_str("== Blindstellen: eine Form, die der Korpus nicht ausloest ==\n");
    aus.push_str(
        "-- Was 0 Fundstellen hat, ist nicht geprueft, sondern UNERREICHBAR: keine Probe,\n\
         -- kein Waechter und keine Mutation koennen es ausloesen.\n",
    );
    let mut blind = 0;
    zeige_tafel(
        "A -- Typklasse x Stellung",
        "Hier fiel am 2026-08-20 der Geist in der Rueckgabe einer Funktion MIT Rumpf.",
        &["opaque", "linear", "ghost", "tagged", "verbund", "bereich", "format", "table", "device"],
        &["parameter", "rueckgabe (rumpf)", "rueckgabe (prototyp)", "let-klausel", "slotfeld", "static"],
        &a,
        &mut aus,
        &mut blind,
    );
    zeige_tafel(
        "B -- Ortsart x Zugriffsart",
        "Hier fiel der fehlende `format`-Schreiber: alle Korpusformate sind PARSER.",
        &["slotfeld", "formatfeld", "register", "verbundfeld", "static", "atomic", "accumulates"],
        &["gelesen", "geschrieben", "+= u.ae."],
        &b,
        &mut aus,
        &mut blind,
    );
    zeige_tafel(
        "C -- Anweisungsart x Rumpf",
        "Hier faellt, welche Form nur auf der obersten Ebene steht -- `O006` und `H012` sind\n   beide daran gefallen: eine Regel, die an der Einrueckung endet, ist keine ueber den Fluss.",
        &["let", "let … else", "zuweisung", "if", "match", "locks", "observes", "narrow",
          "publishes", "awaits", "exchange", "breaking", "return", "leave", "next", "ruf",
          "traverse", "retry", "forever"],
        &["fn-rumpf", "can_fail", "in if", "in locks", "in match", "in traverse", "in retry", "in forever"],
        &c,
        &mut aus,
        &mut blind,
    );
    aus.push_str(&format!("\n== {blind} Blindstellen ==\n"));
    aus.push_str(
        "  Und was das NICHT heisst: eine BESETZTE Zelle sagt nur, dass ein Pass die Form\n\
         \x20 sehen KANN -- nicht, dass er sie richtig behandelt. Zwei der fuenf Befunde vom\n\
         \x20 2026-08-20 faengt dieses Werkzeug gar nicht: die Geraetegegenseite («V9») war\n\
         \x20 keine fehlende Form, sondern eine fehlende KATEGORIE, und ein Rumpf, den ein\n\
         \x20 Pass nicht LIEST, steht im Korpus sehr wohl da.\n",
    );
    aus
}
