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
                "record"
            } else {
                "range"
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

/// Die Typklasse und **ob sie hinter einem ZEIGER steht** (2026-08-20, am Abend).
///
/// Die erste Fassung packte den Zeiger aus und lieferte die Klasse des Ziels. Damit zaehlte
/// `static tz : ptr<normal, rw> Platz` als *Tabelle in Stellung `static`* -- und genau das
/// hatte ich als KEINE ZELLE ausgeschlossen, mit der Begruendung *„eine Tabelle ist kein
/// Wert"*.
///
/// **Die Begruendung stimmt und das Instrument war falsch.** Eine Tabelle als Wert gibt es
/// nicht; eine Tabelle hinter einem Zeiger ist der Normalfall. *Zwei Stellungen, die nichts
/// miteinander zu tun haben, standen in derselben Zelle.*
///
/// > Gefunden hat es die Gegenprobe des Instruments gegen sich selbst -- eine Minute,
/// > nachdem sie eingebaut war. **Ein Urteil, das eine Zelle aus dem Nenner nimmt, muss
/// > falsifizierbar sein, und der Korpus ist der Falsifikator.**
fn klasse_von<'a>(t: &TypExpr, k: &'a BTreeMap<String, &'static str>) -> Option<(&'static str, bool)> {
    match t {
        TypExpr::Pfad(p) => p.teile.last().and_then(|i| k.get(&i.text)).map(|c| (*c, false)),
        TypExpr::Zeiger(z) => klasse_von(&z.ziel, k).map(|(c, _)| (c, true)),
        _ => None,
    }
}

/// Die Stellung, und hinter einem Zeiger heisst sie anders.
fn hinter(stellung: &'static str, zeiger: bool) -> &'static str {
    if !zeiger {
        return stellung;
    }
    match stellung {
        "parameter" => "parameter (ptr)",
        "return (body)" => "return (ptr, body)",
        "return (prototype)" => "return (ptr, proto)",
        "let clause" => "let clause (ptr)",
        "slot field" => "slot field (ptr)",
        "static" => "static (ptr)",
        andere => andere,
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
                if let Some((c, z)) = klasse_von(&p.typ, &k) {
                    zaehle(t, c, hinter("parameter", z));
                }
            }
            if let Some(e) = &f.ergebnis {
                if let Some((c, z)) = klasse_von(e, &k) {
                    let st = if hat_rumpf { "return (body)" } else { "return (prototype)" };
                    zaehle(t, c, hinter(st, z));
                }
            }
            if let FnRumpf::Block(b) = &f.rumpf {
                fn lets(b: &Block, k: &BTreeMap<String, &'static str>, t: &mut Tafel) {
                    for s in &b.anweisungen {
                        if let StmtArt::Let(l) = &s.art {
                            if let Some((c, z)) = l.typ.as_ref().and_then(|x| klasse_von(x, k)) {
                                zaehle(t, c, hinter("let clause", z));
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
            if let Some((c, z)) = klasse_von(&s.typ, &k) {
                zaehle(t, c, hinter("static", z));
            }
        }
        ItemArt::Tabelle(tb) => {
            for f in tb.slot.iter().flat_map(|s| s.felder.iter()) {
                if let SlotTyp::Typ(x) = &f.typ {
                    if let Some((c, z)) = klasse_von(x, &k) {
                        zaehle(t, c, hinter("slot field", z));
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
            let a = match klasse_von(&p.typ, &k).map(|(c, _)| c) {
                Some("format") => "format field",
                Some("table") => "slot field",
                Some("device") => "register",
                Some("record") => "record field",
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
                            if matches!(z.op, ZuwOp::Setzt) { "written" } else { "+= etc." },
                        );
                    }
                }
                // **Ein `atomic` wird NICHT gelesen und nicht geschrieben** -- es wird
                // erwartet, veroeffentlicht oder getauscht. Die erste Fassung dieser Tafel
                // fuehrte es unter `read`/`written` und meldete drei leere Zellen als
                // Blindstellen. *Ein Instrument, das seine eigene Fehleichung als Luecke
                // meldet, ist schlimmer als keines* -- und es hat genau die Arbeit
                // vorgeschlagen, die es nicht gibt.
                match &s.art {
                    StmtArt::Publish(x) => {
                        if let Some(a) = lokal.get(&x.ziel.basis.text) {
                            zaehle(t, a, "publishes");
                        }
                    }
                    StmtArt::AwaitLoad(x) => {
                        if let Some(a) = lokal.get(&x.quelle.basis.text) {
                            zaehle(t, a, "awaits");
                        }
                    }
                    StmtArt::Exchange(x) => {
                        if let Some(a) = lokal.get(&x.ort.basis.text) {
                            zaehle(t, a, "exchange");
                        }
                    }
                    _ => {}
                }
                for e in crate::eigene_ausdruecke(s) {
                    for o in crate::alle_orte(e) {
                        if let Some(a) = lokal.get(&o.basis.text) {
                            zaehle(t, a, "read");
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
            StmtArt::Zuweisung(_) => "assignment",
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
            StmtArt::Ruf(_) => "call",
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
                im_block(b, "fn body", t);
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
    gift: &Tafel,
    aus: &mut String,
    blind: &mut usize,
    bewacht: &mut usize,
    besetzt: &mut usize,
    keine: &mut usize,
    widerspruch: &mut usize,
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
            // **Die Gegenprobe des Instruments gegen sich selbst** (2026-08-20).
            //
            // `keine_zelle` ist eine Liste von URTEILEN -- *dieses Paar ist keine Frage* --
            // und ein Urteil, das eine Zelle aus dem Nenner nimmt, verbessert die Kennzahl
            // zweifach. **Also muss es falsifizierbar sein**, und der Korpus ist der
            // Falsifikator: steht die Kombination irgendwo, war das Urteil falsch.
            //
            // > *Dieselbe Bauart wie ueberall hier:* eine Absage, der keine Probe je
            // > widersprechen kann, ist keine Absage, sondern eine Bequemlichkeit.
            if let Some(grund) = keine_zelle(f, s) {
                if t.contains_key(&(*f, *s)) || gift.contains_key(&(*f, *s)) {
                    *widerspruch += 1;
                    aus.push_str(&format!(
                        "   !! CONTRADICTION  {f} x `{s}` is declared no cell -- and the                          corpus HAS it. The judgement is wrong, not the corpus.\n                         \x20                   (it said: {grund})\n"
                    ));
                    continue;
                }
                *keine += 1;
                aus.push_str(&format!("   (no cell)  {f} x `{s}` -- {grund}\n"));
                continue;
            }
            if t.contains_key(&(*f, *s)) {
                *besetzt += 1;
                continue;
            }
            // **Leer im sauberen Korpus, besetzt im GIFT -- und das ist ein HINWEIS, keine
            // Zusage** (2026-08-20, am selben Abend korrigiert).
            //
            // Die erste Fassung nannte diesen Zustand `GUARDED` und schrieb daneben: *„der
            // staerkste Zustand, den eine Zelle haben kann."* **Das war zu viel behauptet**,
            // und die Abnahme der ersten Agentendateien hat es gezeigt: fuenf Zellen
            // wanderten von `guarded` nach `covered`, darunter *Zuweisung im `traverse`*.
            //
            // Die vier Giftdateien, die diese Zelle besetzen, erwarten `P001`, `M109`,
            // `E011` und `M101` -- **keine davon verbietet eine Zuweisung in einem
            // `traverse`.** Die Zuweisung steht dort als GERUEST, nicht als Gegenstand.
            //
            // > *Eine Giftdatei prueft EINE Regel; alles andere in ihr ist Beiwerk.* Aus
            // > „die Gestalt kommt nur im Gift vor" folgt darum nicht „eine Regel verbietet
            // > sie" -- es folgt nur, dass kein sauberes Programm sie bisher braucht.
            //
            // **Was ein echtes `guarded` verlangte, ist genau der gebuchte Posten**: eine
            // Probe JE KOMBINATION statt je Konstrukt. Solange die nicht da ist, heisst der
            // Zustand, was er ist.
            if gift.contains_key(&(*f, *s)) {
                *bewacht += 1;
                aus.push_str(&format!(
                    "   poison-only  {f} in position `{s}` -- occurs ONLY in the poison \
                     corpus; that is a hint, not a proof that a rule forbids it\n"
                ));
                continue;
            }
            *blind += 1;
            aus.push_str(&format!("   BLIND  {f} in position `{s}`\n"));
        }
    }
}

/// **Die Blindstellen einer Dateimenge.**
pub fn zeige(baeume: &[Programm], gifte: &[Programm]) -> String {
    let (mut a, mut b, mut c) = (Tafel::new(), Tafel::new(), Tafel::new());
    for baum in baeume {
        tafel_typen(baum, &mut a);
        tafel_orte(baum, &mut b);
        tafel_anweisungen(baum, &mut c);
    }
    let (mut ga, mut gb, mut gc) = (Tafel::new(), Tafel::new(), Tafel::new());
    for baum in gifte {
        tafel_typen(baum, &mut ga);
        tafel_orte(baum, &mut gb);
        tafel_anweisungen(baum, &mut gc);
    }
    let mut aus = String::new();
    aus.push_str("== Blind spots: a form the corpus cannot trigger ==\n");
    aus.push_str(
        "-- What has 0 sites is not checked but UNREACHABLE: no probe, no guardian and no\n\
         -- mutation can trigger it.\n",
    );
    let (mut blind, mut bewacht, mut besetzt, mut keine, mut widerspruch) = (0, 0, 0, 0, 0);
    zeige_tafel(
        "A -- type class x position",
        "Here the ghost in the RETURN of a function WITH a body fell on 2026-08-20.",
        &["opaque", "linear", "ghost", "tagged", "record", "range", "format", "table", "device"],
        &["parameter", "return (body)", "return (prototype)", "let clause", "slot field", "static",
          "parameter (ptr)", "return (ptr, body)", "return (ptr, proto)", "let clause (ptr)",
          "slot field (ptr)", "static (ptr)"],
        &a,
        &ga,
        &mut aus,
        &mut blind,
        &mut bewacht,
        &mut besetzt,
        &mut keine,
        &mut widerspruch,
    );
    // **Zwei Tafeln, weil es ZWEI Fragen sind** (2026-08-20, eine Stunde nach der ersten).
    //
    // Die erste Fassung fuehrte `atomic` unter `read`/`written` und meldete drei leere Zellen
    // als Blindstellen -- ein Atomic wird weder gelesen noch geschrieben, es wird erwartet,
    // veroeffentlicht oder getauscht. **Ich habe die Instanz behoben und die Klasse stehen
    // lassen:** danach standen `slot field in position publishes` und acht weitere da, und
    // die sind genauso keine Zellen.
    //
    // > *Ein Instrument, das das Kreuzprodukt seiner Achsen fuer die Frage haelt, meldet
    // > Arbeit, die es nicht gibt* -- und eine Zahl, die falsche Arbeit vorschlaegt, ist
    // > teurer als keine Zahl. **Die Spalten gehoeren zu ihren Zeilen, nicht zur Tafel.**
    zeige_tafel(
        "B1 -- ordinary place x access kind",
        "Here the missing `format` writer fell: every corpus format is a PARSER.",
        &["slot field", "format field", "register", "record field", "static"],
        &["read", "written", "+= etc."],
        &b,
        &gb,
        &mut aus,
        &mut blind,
        &mut bewacht,
        &mut besetzt,
        &mut keine,
        &mut widerspruch,
    );
    zeige_tafel(
        "B2 -- the PAIRED places, and only they",
        "`atomic` and `accumulates` are neither read nor written -- that is the whole point\n   of the two words, and it is why they need a table of their own.",
        &["atomic", "accumulates"],
        &["publishes", "awaits", "exchange", "read", "written"],
        &b,
        &gb,
        &mut aus,
        &mut blind,
        &mut bewacht,
        &mut besetzt,
        &mut keine,
        &mut widerspruch,
    );
    zeige_tafel(
        "C -- statement kind x body",
        "Here it shows which form stands only at the top level -- `O006` and `H012` both fell\n   on it: a rule that ends at the indentation is no rule about the flow.",
        &["let", "let … else", "assignment", "if", "match", "locks", "observes", "narrow",
          "publishes", "awaits", "exchange", "breaking", "return", "leave", "next", "call",
          "traverse", "retry", "forever"],
        &["fn body", "can_fail", "in if", "in locks", "in match", "in traverse", "in retry", "in forever"],
        &c,
        &gc,
        &mut aus,
        &mut blind,
        &mut bewacht,
        &mut besetzt,
        &mut keine,
        &mut widerspruch,
    );
    // **Vier Zahlen, nicht eine** (2026-08-20, am Abend desselben Tages).
    //
    // `151 -> 112` liest sich wie neununddreissig Fortschritt. Es waren einundzwanzig
    // geschriebene und achtzehn ENTFERNTE Zellen -- und eine Entfernung verbessert die
    // Kennzahl auf zwei Arten gleichzeitig: sie nimmt aus dem Zaehler UND aus dem Nenner.
    //
    // > *Solange die Begruendungen einzeln danebenstehen, ist das sauber.* Solange die ZAHL
    // > einteilig berichtet wird, ist es das in zwei Wochen nicht mehr -- dann steht da
    // > „39 geschlossen", und niemand kann es nachrechnen.
    //
    // **Also rechnet niemand es nach, sondern das Werkzeug sagt es selbst.**
    let gesamt = besetzt + bewacht + keine + blind + widerspruch;
    aus.push_str(&format!(
        "\n== {blind} blind · {besetzt} covered · {bewacht} poison-only · {keine} no cell \
         (of {gesamt} pairs) ==\n"
    ));
    if widerspruch > 0 {
        aus.push_str(&format!(
            "== {widerspruch} CONTRADICTIONS -- an exclusion the corpus refutes ==\n"
        ));
    }
    aus.push_str(
        "  The four numbers are reported apart ON PURPOSE. Closing a cell by WRITING and\n\
         \x20 removing one as `no cell` both make the blind count fall, and the second does it\n\
         \x20 twice -- it leaves the numerator and the denominator. A one-part number reads as\n\
         \x20 progress two weeks later, and nobody can recompute it.\n\
         \x20\n\
         \x20 POISON-ONLY means: empty in the clean corpus, occupied in the poison one. That\n\
         \x20 is a HINT and not a proof -- a poison file tests ONE rule, and everything else\n\
         \x20 in it is scaffolding. `assignment in traverse` sits in four poison files whose\n\
         \x20 expected codes are P001, M109, E011 and M101, and none of them forbids it.\n\
         \x20 A real `guarded` would need a probe PER COMBINATION, not per construct.\n\
         \x20\n\
         \x20 And what this does NOT say: an OCCUPIED cell says only that a pass CAN see the\n\
         \x20 form -- not that it handles it. Two of the five findings of 2026-08-20 this\n\
         \x20 tool does not catch at all: the device counterpart («V9») was a missing\n\
         \x20 CATEGORY, not a missing form, and a body a pass does not READ is present in\n\
         \x20 the corpus all the same. The counterpart for that is `pruefe-reichweite.py`.\n",
    );
    aus
}

/// **Welche Paare sind ueberhaupt keine Frage?**
///
/// Das Kreuzprodukt zweier Achsen ist nicht die Fragemenge -- **die Spalten gehoeren zu ihren
/// Zeilen.** Die erste Fassung dieses Werkzeugs meldete `atomic x read` als Blindstelle; ein
/// Atomic wird weder gelesen noch geschrieben. Ich habe die Instanz behoben und die Klasse
/// stehen lassen, und danach standen neun weitere da.
///
/// *Jeder Eintrag hier ist eine Aussage ueber die SPRACHE, einmal geschrieben* -- und nicht
/// eine Bequemlichkeit, die eine Zahl senkt. Wo ein Paar erlaubt und bloss ungeschrieben ist,
/// steht es nicht hier, sondern bleibt BLIND.
fn keine_zelle(form: &str, stellung: &str) -> Option<&'static str> {
    // **Eine `table`, ein `format`, ein `device` sind keine WERTE.** Man adressiert sie
    // durch einen Zeiger: `ptr<normal, rw> T`, `ptr<mmio, rw> Vtd`. Eine Tabelle
    // zurueckzugeben hiesse, NSLOTS Plaetze zu kopieren, und ein `format` IST eine Sicht auf
    // fremde Bytes -- sein Wert ist der Zeiger, nicht der Inhalt.
    if matches!(form, "table") && matches!(stellung, "return (body)" | "return (prototype)" | "let clause" | "slot field" | "static") {
        return Some("a table is not a value: it is addressed through `ptr<…> T`, and returning one would copy `count` slots");
    }
    if matches!(form, "format") && matches!(stellung, "slot field" | "static") {
        return Some("a `format` is a VIEW on foreign bytes -- what would lie in the slot is the buffer, and its type is the buffer's");
    }
    // Ein `device` ist ein Griff auf `basis`; er lebt in einem `let` oder einem Parameter.
    // In einem Slot oder einem `static` laege eine Kopie der Basisadresse -- **und dann ist
    // die Frage die Adresse und nicht das Geraet.**
    if matches!(form, "device") && matches!(stellung, "slot field" | "static") {
        return Some("a device handle is `basis` and nothing else -- in storage the question is the ADDRESS, and that is a `Pa`");
    }
    // **`publishes`/`awaits`/`exchange` gibt es nur an einem `atomic`.** Das ist der ganze
    // Zweck des Wortes: eine Paarung ohne Ordnung ist keine.
    if !matches!(form, "atomic") && matches!(stellung, "publishes" | "awaits" | "exchange") {
        return Some("the three paired forms exist only at an `atomic` -- a pairing without an ordering is none");
    }
    // Und umgekehrt: ein `atomic` wird nicht gelesen und nicht geschrieben.
    if matches!(form, "atomic") && matches!(stellung, "read" | "written" | "+= etc.") {
        return Some("an atomic is neither read nor written -- it is awaited, published or exchanged, and that is the point of the word");
    }
    // Ein `accumulates` meldet und liest gefaltet; es ist kein Paarungsplatz.
    if matches!(form, "accumulates") && matches!(stellung, "publishes" | "awaits" | "exchange") {
        return Some("`accumulates` folds on reading and reports on writing -- it needs no pairing, and that is why it exists");
    }
    // **Ein `format`-Feld traegt kein `+=`.** Der Erzeuger lehnt es benannt ab: ein
    // zusammengesetztes Schreiben waere ein Lesen und ein Schreiben durch zwei getrennte
    // Rufe, und ueber einem Puffer, an dem ein Geraet mitschreibt, ist die Frage genau das.
    if form == "format field" && stellung == "+= etc." {
        return Some("refused by name in the emitter: it would be a read and a write through two separate calls, over a buffer a device also writes");
    }
    None
}
