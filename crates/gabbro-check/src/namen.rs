//! **Pass 1 -- Namen.**
//!
//! E5: *jede Deklaration ist an genau einer Stelle vollstaendig.* Zwei Deklarationen desselben
//! Namens im selben Geltungsbereich sind damit kein Streit ueber Vorrang, sondern ein Fehler --
//! und zwar **hier**, nicht spaeter, wenn ein anderer Pass eine der beiden gewaehlt hat.
//!
//! Der Pass prueft **Doppelungen**, nicht Aufloesung: welcher Name wohin zeigt, entscheidet sich
//! erst mit der Modulaufloesung, und die gibt es noch nicht (s. `Zustand::Offen` in der
//! Passliste). Was er prueft, prueft er vollstaendig; was er nicht prueft, behauptet er nicht.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::{HashMap, HashSet};

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    geltungsbereich(&baum.items, absagen);
    entrust_annahme(baum, absagen);
    verweigerte_zahltypen(baum, absagen);
}

/// **`F006`: `long double`, `f16` und `float128` werden BENANNT abgelehnt.**
///
/// Ohne diese Zeilen bekaeme der Schreiber „unbekannter Typ" -- und daraus liest niemand,
/// dass es eine ENTSCHEIDUNG war. *Die Weigerung ist die Antwort, und sie muss ihren Grund
/// mitbringen.*
///
/// Und der Grund kommt aus dem Korpus, nicht aus einer Vorliebe (`FRAGMENTE.md`, «F0»/FF2):
/// in der Domaene, die Extragenauigkeit wirklich braucht, ist `long double` **eine Sprosse
/// von sieben** -- darueber `floatexp`, `doubleexp`, `softfloat`, `float128`, alles
/// Softwaretypen des Programms. **Wer mehr als `f64` braucht, will keinen
/// plattformabhaengigen 80-Bit-Typ, sondern eine BENANNTE Genauigkeit.**
fn verweigerte_zahltypen(baum: &Programm, absagen: &mut Absagen) {
    fn grund(n: &str) -> Option<&'static str> {
        match n {
            "f16" | "float16" | "half" => Some(
                "auf den meisten Zielen ist `f16` Speicherform plus Umwandlung und keine \
                 native Rechnung. „Vollstaendig\" hiesse Emulation oder Rechnen in `f32` -- \
                 und dann ist die DOPPELRUNDUNG f16 -> f32 -> f16 eine neue Falle, nicht eine \
                 kleinere Ausgabe derselben. Als reine Speicherform gehoert es zu `format`",
            ),
            "f80" | "f128" | "float128" | "longdouble" | "long_double" => Some(
                "das ist kein Typ, sondern eine Plattformlotterie: 80 Bit x87 auf x86-Linux, \
                 128 Bit anderswo, gleich `double` auf wieder anderen -- und der x87 rundet \
                 DOPPELT. Wer mehr als `f64` braucht, nennt eine Genauigkeit; der Korpus \
                 baut dafuer eine Leiter aus Softwaretypen (FRAGMENTE.md, «F0»/FF2)",
            ),
            _ => None,
        }
    }
    fn im_typ(t: &TypExpr, absagen: &mut Absagen) {
        match t {
            TypExpr::Pfad(p) => {
                if let Some(letzt) = p.teile.last() {
                    if let Some(g) = grund(&letzt.text) {
                        absagen.schiebe(
                            Absage::fehler(
                                "F006",
                                letzt.span,
                                format!("`{}` gibt es in Gabbro nicht, und zwar entschieden", letzt.text),
                            )
                            .mit_notiz(g),
                        );
                    }
                }
            }
            TypExpr::Feld(a) => im_typ(&a.element, absagen),
            TypExpr::Zeiger(z) => im_typ(&z.ziel, absagen),
            TypExpr::Verbund(fs, _) => {
                for f in fs {
                    im_typ(&f.typ.typ, absagen);
                }
            }
            _ => {}
        }
    }
    crate::fuer_jedes_item(baum, &mut |i| match &i.art {
        ItemArt::Konst(k) => im_typ(&k.typ, absagen),
        ItemArt::Statisch(st) => im_typ(&st.typ, absagen),
        ItemArt::Typ(t) => {
            if let Some(r) = &t.rumpf {
                im_typ(r, absagen);
            }
        }
        ItemArt::Funktion(f) => {
            for prm in &f.parameter {
                im_typ(&prm.typ, absagen);
            }
            if let Some(e) = &f.ergebnis {
                im_typ(e, absagen);
            }
        }
        _ => {}
    });
}

/// **`entrust` nennt eine Annahme, und sie muss es GEBEN.**
///
/// Dieselbe Frage wie bei `progress` (`S003`/`S004`), an einem anderen Konstrukt -- und
/// darum steht sie hier und nicht dort: *ob ein Name auf etwas Erklaertes zeigt, ist die
/// Frage des Namenspasses.* Der Sammler ist derselbe (`crate::annahmen`), damit die Antwort
/// es auch ist.
///
/// **Und sie ist der einzige Leser, den `entrust` bekommt.** Ueber den Rumpf des Gastes sagt
/// Gabbro nichts -- keine Kosten, keine Wirkungen, keine Terminierung. *Was bliebe, wenn auch
/// die Annahme ungeprueft waere, ist eine Deklaration, die nichts behauptet.*
fn entrust_annahme(baum: &Programm, absagen: &mut Absagen) {
    let annahmen = crate::annahmen(baum);
    let mut erklaert: HashSet<String> = HashSet::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let Some(n) = item.art.name() {
            erklaert.insert(n.text.clone());
        }
    });
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Entrust(t) = &item.art else { return };
        if !erklaert.contains(&t.raum.text) {
            absagen.schiebe(
                Absage::fehler(
                    "N006",
                    t.raum.span,
                    format!("`entrust {} at {}` -- the space is not declared here", t.name.text, t.raum.text),
                )
                .mit_notiz(
                    "`at` nimmt einen NAMEN und keinen Ausdruck: der Raum ist ein deklariertes \
                     Ding. Ein `entrust` auf einen gerechneten Wert waere ein Sprung an eine \
                     ausgerechnete Adresse",
                ),
            );
        }
        match annahmen.get(&t.annahme.text) {
            None => absagen.schiebe(
                Absage::fehler(
                    "N004",
                    t.annahme.span,
                    format!("`entrust {}` names no declared assumption", t.name.text),
                )
                .mit_notiz(
                    "der Gast bekommt Register, einen Stapel und einen `code`-Raum; DASS er \
                     seinen Vertrag haelt, ist eine Aussage ueber die Umgebung und gehoert \
                     in die Annahmenschicht -- sonst steht sie in keinem Manifest",
                ),
            ),
            Some(false) => absagen.schiebe(
                Absage::fehler(
                    "N005",
                    t.annahme.span,
                    format!("`entrust {}` rests on an unfalsifiable assumption", t.name.text),
                )
                .mit_notiz(
                    "eine Annahme ueber fremden Code, der keine Sonde je widersprechen kann, \
                     ist keine Isolation, sondern ein Wunsch",
                ),
            ),
            Some(true) => {}
        }
    });
}

fn geltungsbereich(items: &[Item], absagen: &mut Absagen) {
    let mut gesehen: HashMap<String, Span> = HashMap::new();
    for item in items {
        if let Some(name) = item.art.name() {
            // `arch` und `when` waehlen aus: zwei Deklarationen desselben Namens fuer
            // **verschiedene** Architekturen sind eine Deklaration je Ziel, keine Doppelung.
            // `FRAGMENTE.md` F5 schreibt `prim fn invoke … arch x86_64;` und dieselbe Zeile
            // mit `arch aarch64;` -- wer das als Fehler meldet, verbietet die bedingte
            // Uebersetzung, die `when` (SYNTAX.md §1) ausdruecklich traegt.
            match auswahl(item) {
                Auswahl::Immer => doppelt(
                    &mut gesehen,
                    &name.text,
                    name.span,
                    item.art.benennung(),
                    absagen,
                ),
                Auswahl::Arch(a) => doppelt(
                    &mut gesehen,
                    &format!("{}\u{1}arch:{a}", name.text),
                    name.span,
                    item.art.benennung(),
                    absagen,
                ),
                // Eine `when`-Bedingung kann dieser Pass nicht auswerten -- die
                // Konstantenauswertung ist Teil von M1 und noch nicht gebaut. Also wird
                // hier **nichts behauptet**.
                Auswahl::Bedingt => {}
            }
        }
        match &item.art {
            ItemArt::Modul(m) => geltungsbereich(&m.items, absagen),
            ItemArt::Tabelle(t) => tabelle(t, absagen),
            ItemArt::Reason(r) => reason(r, absagen),
            ItemArt::Device(d) => device(d, absagen),
            ItemArt::Typ(t) => typdecl(t, absagen),
            ItemArt::Format(f) => {
                felder(&f.felder, "Format", absagen);
                // **«B24» im Pruefer, seit 2026-08-19.** Die Regel gab es seit dem 18. --
                // im ERZEUGER, und `gabbro pruefe` senkt nicht ab. Sechs Giftformen, sechsmal
                // Schweigen. *Eine Regel auf einer Flaeche, die die meisten Programme nie
                // beruehren, hat keinen Biss.*
                formatbitlagen(f, absagen);
            }
            _ => {}
        }
    }
}

/// Wodurch ein Item ausgewaehlt wird -- der Schluessel, unter dem Doppelungen zaehlen.
enum Auswahl {
    Immer,
    Arch(String),
    Bedingt,
}

fn auswahl(item: &Item) -> Auswahl {
    if item.when.is_some() {
        return Auswahl::Bedingt;
    }
    if let ItemArt::Funktion(f) = &item.art {
        if f.when.is_some() {
            return Auswahl::Bedingt;
        }
        if let Some(a) = &f.arch {
            return Auswahl::Arch(a.text.clone());
        }
    }
    Auswahl::Immer
}

fn doppelt(
    gesehen: &mut HashMap<String, Span>,
    name: &str,
    span: Span,
    was: &str,
    absagen: &mut Absagen,
) {
    if let Some(erste) = gesehen.get(name) {
        absagen.schiebe(
            Absage::fehler(
                "N001",
                span,
                format!("`{name}` is declared twice in this scope ({was})"),
            )
            .mit_notiz(format!(
                "the first declaration is at offset {}",
                erste.von
            ))
            .mit_notiz("E5: every declaration is complete in exactly one place"),
        );
    } else {
        gesehen.insert(name.to_string(), span);
    }
}

fn typdecl(t: &TypDecl, absagen: &mut Absagen) {
    if let Some(TypExpr::Varianten(varianten, _)) = &t.rumpf {
        let mut gesehen = HashMap::new();
        for v in varianten {
            doppelt(
                &mut gesehen,
                &v.name.text,
                v.name.span,
                "Variante",
                absagen,
            );
        }
    }
    if let Some(TypExpr::Verbund(f, _)) = &t.rumpf {
        felder(f, "Verbund", absagen);
    }
}

fn felder(felder: &[FeldDecl], was: &str, absagen: &mut Absagen) {
    let mut gesehen = HashMap::new();
    for f in felder {
        doppelt(&mut gesehen, &f.name.text, f.name.span, was, absagen);
    }
}

fn tabelle(t: &Tabelle, absagen: &mut Absagen) {
    if let Some(slot) = &t.slot {
        let mut gesehen = HashMap::new();
        for f in &slot.felder {
            doppelt(&mut gesehen, &f.name.text, f.name.span, "Slotfeld", absagen);
        }
    }
    let mut gesehen = HashMap::new();
    for i in &t.invarianten {
        doppelt(
            &mut gesehen,
            &i.name.text,
            i.name.span,
            "Invariante",
            absagen,
        );
    }
}

fn reason(r: &Reason, absagen: &mut Absagen) {
    let mut gesehen = HashMap::new();
    let mut werte: HashMap<u128, Span> = HashMap::new();
    for f in &r.faelle {
        doppelt(&mut gesehen, &f.name.text, f.name.span, "Grund", absagen);
        if let Some(erste) = werte.get(&f.wert) {
            absagen.schiebe(
                Absage::fehler(
                    "N002",
                    f.span,
                    format!(
                        "the numeric value {} is assigned twice in `{}`",
                        f.wert, r.name.text
                    ),
                )
                .mit_notiz(format!("zuerst bei Versatz {}", erste.von))
                .mit_notiz(
                    "Regel 3 (abweisen, nie deuten): ein Grund ist ueber seine Zahl \
                     unterscheidbar, sonst ist der Bericht mehrdeutig",
                ),
            );
        } else {
            werte.insert(f.wert, f.span);
        }
    }
}

fn device(d: &Device, absagen: &mut Absagen) {
    let mut gesehen = HashMap::new();
    for r in &d.register {
        doppelt(&mut gesehen, &r.name.text, r.name.span, "Register", absagen);
        regfelder(r, absagen);
    }
    registerlagen(&d.register, &d.name.text, absagen);
    for b in &d.baenke {
        doppelt(&mut gesehen, &b.name.text, b.name.span, "Bank", absagen);
        let mut innen = HashMap::new();
        for r in &b.register {
            doppelt(&mut innen, &r.name.text, r.name.span, "Register", absagen);
            regfelder(r, absagen);
        }
        registerlagen(&b.register, &b.name.text, absagen);
        schritt_pruefen(b, absagen);
    }
    let mut uebergaenge = HashMap::new();
    for u in &d.uebergaenge {
        doppelt(
            &mut uebergaenge,
            &u.name.text,
            u.name.span,
            "Uebergang",
            absagen,
        );
    }
}

/// D2 -- vollstaendige Layouts: **zwei Feldnamen an einem Register sind ein Fehler, und zwei
/// Felder auf demselben Bit auch.** Ein ueberlappendes Layout ist genau die Falle, gegen die
/// „jedes Bit eines Wortes ist benannt" geschrieben wurde.
fn regfelder(r: &RegDecl, absagen: &mut Absagen) {
    let mut gesehen = HashMap::new();
    for (name, _) in &r.felder {
        doppelt(&mut gesehen, &name.text, name.span, "Registerfeld", absagen);
    }
    // **Und die andere Haelfte von «B24», seit 2026-08-19: liegt das Bit im Register?**
    //
    // `N003` prueft die Ueberlappung seit dem 2026-08-14 -- dass ein Bit ueberhaupt IN sein
    // Wort passt, prueft bis heute niemand. Gemessen: `reg R : u32 fields { A @40, }` ging
    // mit 0 Fehlern durch. *Dieselbe Zeile, die am `format` `N007` heisst.*
    let (breite, wort) = crate::bitlage::aus_intty(&r.typ);
    let wortname = format!("{wort:?}").to_lowercase();
    for (i, (name, bp)) in r.felder.iter().enumerate() {
        if let Some(b) = crate::bitlage::lage_pruefen(bp, breite * 8, i, &name.text, &wortname) {
            absagen.schiebe(Absage::fehler(b.kennung, name.span, b.text).mit_notiz(b.notiz));
        }
    }

    // Ueberlappung der Bitlagen.
    let mut belegt: Vec<(u128, u128, &Ident)> = Vec::new();
    for (name, bp) in &r.felder {
        let (hoch, tief) = match bp {
            BitPos::Bit(b) => (*b, *b),
            BitPos::Bereich(h, t) => (*h.max(t), *h.min(t)),
        };
        for (h2, t2, andere) in &belegt {
            if tief <= *h2 && *t2 <= hoch {
                absagen.schiebe(
                    Absage::fehler(
                        "N003",
                        name.span,
                        format!(
                            "the bits of `{}` overlap with `{}` in register `{}`",
                            name.text, andere.text, r.name.text
                        ),
                    )
                    .mit_notiz("D2: every bit of a word is named -- exactly once"),
                );
                break;
            }
        }
        belegt.push((hoch, tief, name));
    }
}

/// **«B24» am `format`: `N007` und `N008`.**
///
/// Der dritte Teil der Entscheidung -- *eine Luecke im Wort* -- bleibt beim Erzeuger. Der
/// Schnitt ist die Antwort auf „warum nicht alles hier": **eine Luecke macht das Wort fuer
/// den Erzeuger UNENTSCHEIDBAR; eine Lage jenseits der Breite und eine Ueberlappung sind
/// fuer jeden FALSCH.** *Und der Korpus haengt an genau diesem Schnitt:* `format Elf64Ph`
/// laesst mit `p_flags : u32 @[2:0]` neunundzwanzig Bits unbenannt und geht durch, weil
/// niemand es absenkt.
fn formatbitlagen(f: &Format, absagen: &mut Absagen) {
    let (_, befunde) = crate::bitlage::lies(&f.felder);
    for b in befunde {
        let span = f.felder[b.feld].name.span;
        let text = match b.anderes {
            Some(a) => format!("{} (with `{}`)", b.text, f.felder[a].name.text),
            None => b.text.clone(),
        };
        absagen.schiebe(Absage::fehler(b.kennung, span, text).mit_notiz(b.notiz));
    }
}

/// **`N009` -- der HAUPTSATZ von `Device_Konstruktor.thy` bekommt seine Pruefzeile.**
///
/// Der Satz heisst `getrennte_register_treffen_getrennte_zellen`, und er setzt
/// `getrennt r s` VORAUS: dass zwei `reg` einander nicht ueberlappen. **Bis zum 2026-08-19
/// rechnete das kein Pass nach** -- `pruefe-klauseln.py` fuehrte `versatz` als ZUSAGE mit
/// genau diesem Satz, und der Schablonenregister-Eintrag als Praemisse ohne Erzeuger.
///
/// *Ein bewiesener Satz, dessen Praemisse nichts herstellt, hat die Vertrauensbasis
/// verschoben und nicht verkleinert.* Das ist die sechste Klasse in Reinform, und hier faellt
/// die erste ihrer zehn Instanzen.
///
/// **Die Grenze steht im Code, nicht in einer Fussnote:** verglichen wird nur, was als
/// ZAHLLITERAL dasteht. Ein berechneter Versatz (`CAP.FRO * 16`) bleibt stumm -- W10, eine
/// untere Schranke weist weder zurueck noch bestaetigt sie. Und verglichen wird **innerhalb**
/// einer Ebene: die Register eines `device` unter sich, die einer `bank` unter sich. *Eine
/// Bank liegt an einer berechneten Basis; sie gegen die Hauptebene zu halten hiesse, die
/// Basis zu raten.*
fn registerlagen(regs: &[RegDecl], wo: &str, absagen: &mut Absagen) {
    let mut belegt: Vec<(i128, i128, &Ident)> = Vec::new();
    for r in regs {
        let ExprArt::Zahl(v) = &r.versatz.art else { continue };
        let von = *v as i128;
        let breite = crate::bitlage::aus_intty(&r.typ).0 as i128;
        let bis = von + breite;
        for (v2, b2, andere) in &belegt {
            if von < *b2 && *v2 < bis {
                absagen.schiebe(
                    Absage::fehler(
                        "N009",
                        r.name.span,
                        format!(
                            "`{}` at {von:#x}..{bis:#x} overlaps `{}` at {v2:#x}..{b2:#x} in `{wo}`",
                            r.name.text, andere.text
                        ),
                    )
                    .mit_notiz(
                        "`Device_Konstruktor.thy` proves that separate registers hit separate \
                         cells -- UNDER the premise `getrennt r s`. Overlapping ones make the \
                         theorem vacuous, not false",
                    ),
                );
                break;
            }
        }
        belegt.push((von, bis, &r.name));
    }
}

/// **`N010` -- `stride 0` macht jede Bankzelle LEER, und der Satz gilt dann trivial.**
///
/// Ausgespuelt beim Beweis von `device.konstruktor` am 2026-08-17:
/// `bankeintraege_ueberlappen_nicht` braucht `stride > 0` nicht als Praemisse -- bei null ist
/// jede Bankzelle leer, und leere Mengen schneiden sich nicht.
///
/// > *Richtig und nutzlos ist keine bestandene Pruefung.* **Ein Beweis, der einen Fall trivial
/// > macht statt ihn zu decken, hat ihn gefunden** -- und seit heute faellt der Fall am Pass
/// > statt im Kommentar.
fn schritt_pruefen(b: &Bank, absagen: &mut Absagen) {
    if let ExprArt::Zahl(0) = &b.schritt.art {
        absagen.schiebe(
            Absage::fehler(
                "N010",
                b.name.span,
                format!("bank `{}` has `stride 0` -- every cell is empty", b.name.text),
            )
            .mit_notiz(
                "`Device_Konstruktor.thy` then proves non-overlap VACUOUSLY: empty sets do \
                 not intersect. Right and useless is not a passed check",
            ),
        );
    }
}
