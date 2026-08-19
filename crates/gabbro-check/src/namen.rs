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
    geister_haben_keinen_speicher(baum, absagen);
    pro_kern_und_gegenprobe(baum, absagen);
    dispatch_loest_auf(baum, absagen);
    maschineneigenschaft(baum, absagen);
}

/// **`N016` -- `requires Has(X)` wird am RUFORT verlangt («NL.2», 2026-08-19).**
///
/// Gefunden, weil `pruefe-konstrukte.py` `axiom` als Konstrukt **ohne jede Giftprobe** meldete
/// -- und die Axiomschicht ist die Flaeche, auf der die ganze relative Zusage ruht
/// (*„bewiesen unter A1…An"*).
///
/// ```gabbro
/// axiom rdtscp() -> u64 requires Has(RDTSCP) effects { pure } falsifier sonde_rdtscp;
/// impl fn f() -> u64 … { return rdtscp(); }     -- 0 Fehler
/// ```
///
/// **Die Vorbedingung war Dekoration.** Ein Axiom mit Merkmalsvoraussetzung liesz sich rufen,
/// ohne dass irgendwo stand, dass die Maschine das Merkmal hat -- und im Zeugnis erscheint
/// `Has(RDTSCP)` nirgends, weil es an keiner Zusage haengt.
///
/// ## Die Regel ist die von `Held(…)`, an einem anderen Praedikat
///
/// **Wer ruft, traegt die Forderung weiter**, bis jemand sie erklaert. Genau so laeuft
/// `requires Held(L)` durch den Aufrufgraphen (`H005`) -- *es fehlte nicht die Form, sondern
/// die Anwendung auf das zweite Praedikat derselben Bauart.*
///
/// > **Und wo sie endet, ist eine Entscheidung, die noch nicht getroffen ist:** heute muss der
/// > Rufer sie DEKLARIEREN. Dass ein `check` oder eine `assume` sie HERSTELLT, ist eine Form,
/// > die es nicht gibt -- gebucht in `TODO.md`.
fn maschineneigenschaft(baum: &Programm, absagen: &mut Absagen) {
    let mut fordert: HashMap<String, Vec<String>> = HashMap::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        let (name, req) = match &i.art {
            ItemArt::Axiom(a) => (&a.name, &a.requires),
            ItemArt::Funktion(f) => (&f.name, &f.requires),
            _ => return,
        };
        let mut m = Vec::new();
        for p in req {
            has_aus_pred(p, &mut m);
        }
        if !m.is_empty() {
            fordert.insert(name.text.clone(), m);
        }
    });
    if fordert.is_empty() {
        return;
    }
    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Funktion(f) = &i.art else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let eigene = fordert.get(&f.name.text).cloned().unwrap_or_default();
        let mut rufe = Vec::new();
        sammle_rufe(b, &mut rufe);
        for (ziel, span) in rufe {
            let Some(verlangt) = fordert.get(&ziel) else { continue };
            for m in verlangt {
                if eigene.iter().any(|e| e == m) {
                    continue;
                }
                absagen.schiebe(
                    Absage::fehler(
                        "N016",
                        span,
                        format!("`{ziel}` requires `Has({m})`, and `{}` does not carry it", f.name.text),
                    )
                    .mit_notiz(
                        "a machine feature is not established by calling -- whoever calls                          carries the demand on, until somebody declares it",
                    )
                    .mit_notiz(
                        "the same rule `requires Held(L)` runs through the call graph with                          (`H005`); it is the second predicate of the same shape",
                    ),
                );
            }
        }
    });
}

fn has_aus_pred(p: &Pred, aus: &mut Vec<String>) {
    fn e(x: &Expr, aus: &mut Vec<String>) {
        match &x.art {
            ExprArt::Ruf(r) if r.pfad.teile.last().is_some_and(|i| i.text == "Has") => {
                if let Some(ExprArt::Ort(o)) = r.argumente.first().map(|a| &a.art) {
                    aus.push(o.text());
                }
            }
            ExprArt::Klammer(i) | ExprArt::Unaer(_, i) => e(i, aus),
            ExprArt::Binaer(_, a, b) => {
                e(a, aus);
                e(b, aus);
            }
            _ => {}
        }
    }
    match &p.art {
        PredArt::Vergleich(x) | PredArt::Element(x, _) => e(x, aus),
        PredArt::Quantor(q) => has_aus_pred(&q.rumpf, aus),
        _ => {}
    }
}

fn sammle_rufe(b: &Block, aus: &mut Vec<(String, Span)>) {
    fn ex(x: &Expr, aus: &mut Vec<(String, Span)>) {
        match &x.art {
            ExprArt::Ruf(r) => {
                if let Some(n) = r.pfad.teile.last() {
                    aus.push((n.text.clone(), x.span));
                }
                for a in &r.argumente {
                    ex(a, aus);
                }
            }
            ExprArt::Klammer(i) | ExprArt::Unaer(_, i) => ex(i, aus),
            ExprArt::Binaer(_, a, b) => {
                ex(a, aus);
                ex(b, aus);
            }
            _ => {}
        }
    }
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Let(l) => ex(&l.wert, aus),
            StmtArt::Zuweisung(z) => ex(&z.wert, aus),
            StmtArt::Return(Some(x)) => ex(x, aus),
            StmtArt::Ruf(r) => {
                if let Some(n) = r.pfad.teile.last() {
                    aus.push((n.text.clone(), r.span));
                }
            }
            StmtArt::Wenn(w) => {
                for (c, x) in &w.zweige {
                    ex(c, aus);
                    sammle_rufe(x, aus);
                }
                if let Some(x) = &w.sonst {
                    sammle_rufe(x, aus);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    sammle_rufe(&z.rumpf, aus);
                }
            }
            StmtArt::Bricht(x) => sammle_rufe(&x.rumpf, aus),
            StmtArt::Sperrt(x) => sammle_rufe(&x.rumpf, aus),
            StmtArt::Observiert(x) => sammle_rufe(&x.rumpf, aus),
            StmtArt::Narrow(x) => sammle_rufe(&x.sonst, aus),
            StmtArt::LetSonst(x) => sammle_rufe(&x.sonst, aus),
            StmtArt::Schleife(sch) => match sch.as_ref() {
                Schleife::Traverse(t) => sammle_rufe(&t.rumpf, aus),
                Schleife::Retry(r) => sammle_rufe(&r.rumpf, aus),
                Schleife::Forever(f) => sammle_rufe(&f.rumpf, aus),
            },
            _ => {}
        }
    }
}

/// **`N014`/`N015` -- `per cpu N` und `counterprobe` («NL.2.8», 2026-08-19).**
///
/// Zwei Zusagen, ein Pass, weil beide dieselbe Bauart haben: **ein Name oder eine Zahl, die
/// niemand nachschlaegt.**
///
/// * **`N014` -- `per cpu N`.** `pruefe-klauseln.py`: *„dass N zu NCORES passt, prueft kein
///   Pass."* Ob es zu `NCORES` passt, kann kein Pass wissen -- **welche Konstante die
///   Kernzahl ist, ist eine Konvention und keine Tatsache.** Was er wissen kann und heute
///   nicht prueft: *dass N ueberhaupt eine bekannte positive Zahl ist.* Ein `per cpu` ueber
///   einer unbekannten Groesse hat keine Zellenzahl, und die Absenkung koennte sie nur raten.
/// * **`N015` -- `counterprobe … expects <sonde>`.** *„Die Gegenprobe soll FALLEN. Kein Pass
///   fuehrt sie aus."* **Ausfuehren kann sie kein Pass** -- sie ist ein Laufzeitversuch. Was
///   er kann: den genannten Namen gegen die erklaerten Sonden halten, **dieselbe Regel wie
///   `S003` bei `progress`.** *Eine Gegenprobe, deren Sonde niemand erklaert hat, ist eine
///   Zeile ueber ein Programm, das es nicht gibt.*
fn pro_kern_und_gegenprobe(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let mut sonden = Vec::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        if let ItemArt::Assume(a) = &i.art {
            if let AnnahmeKlasse::Falsifizierbar(f) = &a.klasse {
                sonden.push(f.text.clone());
            }
        }
    });
    lauf_pro_kern(&baum.items, "", &u, &sonden, absagen);
}

/// **Der Modulpfad muss mitlaufen, und das war ein Fehler beim ersten Anlauf.**
///
/// `konst_wert("", e)` fand `NKERNE` nicht, weil die Konstante als
/// `beispiel::akkumulatoren::NKERNE` gebucht ist -- und meldete `N014` an einer richtigen
/// Zeile. *Dieselbe Klasse wie der `typ_von_ort`-Fund vom 2026-08-17: ein Blick in die Karte,
/// der den Modulweg wegliesz.*
fn lauf_pro_kern(
    items: &[Item],
    pfad: &str,
    u: &crate::umgebung::Umgebung,
    sonden: &[String],
    absagen: &mut Absagen,
) {
    for i in items {
        match &i.art {
            ItemArt::Modul(m) => {
                let unter = if pfad.is_empty() {
                    m.pfad.text()
                } else {
                    format!("{pfad}::{}", m.pfad.text())
                };
                lauf_pro_kern(&m.items, &unter, u, sonden, absagen);
            }
            ItemArt::Accumulates(a) => {
                let Some(e) = &a.pro_kern else { continue };
                match u.konst_wert(pfad, e) {
                    Some(n) if n > 0 => {}
                    _ => absagen.schiebe(
                        Absage::fehler(
                            "N014",
                            a.name.span,
                            format!("`per cpu` of `{}` is not a known positive number", a.name.text),
                        )
                        .mit_notiz(
                            "the lowering folds one cell per core -- without a cell count it \
                             would have to guess one, and that is what `C001` stands against",
                        ),
                    ),
                }
            }
            // **`counterprobe … expects <ident>` bleibt UNGEPRUEFT, und das ist ein Befund
            // ueber die Spezifikation.**
            //
            // Der erste Anlauf am 2026-08-19 baute `N015`: der Name muesse eine erklaerte
            // Sonde nennen, wie `S003` es fuer `progress` verlangt. **`SYNTAX.md`:975 sagt
            // nichts dergleichen** -- die Produktion lautet `"counterprobe" string "expects"
            // ident`, und **wo dieser `ident` deklariert wird, steht nirgends.**
            //
            // > *Zweiter Fall an einem Tag, in dem die Beschreibung einer Klausel als Quelle
            // > gelesen wurde und keine war* -- der erste war `leaves`. **Eine Regel zu bauen,
            // > waehrend die Bedeutung offen ist, hiesse die Frage still zu beantworten.**
            //
            // Der Posten steht in `TODO.md`: erst die Entscheidung, dann der Pass.
            _ => {}
        }
    }
}

/// **`N011` -- ein Geisttyp darf nicht in Speicher liegen («NL.2.4», 2026-08-19).**
///
/// `pruefe-klauseln.py` fuehrte `ghost` als ZUSAGE mit dem Satz: *„Ein Geisttyp darf im
/// erzeugten C nicht vorkommen. Ein Verbot, das kein Pass durchsetzt -- dieselbe Bauart wie
/// `opaque`."* Gemessen am selben Tag:
///
/// ```gabbro
/// linear ghost type Marke;
/// table W count 4 { slot { m : Marke, a : u32 in 0 .. 10, } }
/// type P = { m : Marke, a : u32, };
/// --> 5 Items, 0 Fehler, 0 Hinweise
/// ```
///
/// **Der Erzeuger merkte sich die Geisternamen und loeschte sie** -- und nichts verbot, sie
/// dorthin zu legen, wo Speicher ist. *Ein geloeschtes Feld in einem Verbund verschiebt jedes
/// folgende; ein geloeschter Slot aendert die Schrittweite der Tabelle.* Was der Erzeuger
/// still tut, tut er an einer Stelle, an der der Nutzer eine Zahl erwartet.
///
/// ## Wo Speicher ist, und wo nicht
///
/// **Speicher:** ein `slot`-Feld, ein Verbundfeld, ein `static`, ein `format`-Feld.
/// **Kein Speicher:** ein Parameter, ein Rueckgabetyp, ein `let` -- dort faedelt der Pruefer
/// den Wert, und M2 haelt ihn linear. *Genau das ist der Zweck eines Geisttyps, und die Regel
/// darf ihn nicht treffen.*
fn geister_haben_keinen_speicher(baum: &Programm, absagen: &mut Absagen) {
    let mut geister = Vec::new();
    sammle_geister(&baum.items, &mut geister);
    if geister.is_empty() {
        return;
    }
    pruefe_speicher(&baum.items, &geister, absagen);
}

fn sammle_geister(items: &[Item], aus: &mut Vec<String>) {
    for i in items {
        match &i.art {
            ItemArt::Typ(t) if t.ghost => aus.push(t.name.text.clone()),
            ItemArt::Modul(m) => sammle_geister(&m.items, aus),
            _ => {}
        }
    }
}

/// Nennt dieser Typausdruck einen Geist? *Auch durch ein Feld hindurch -- `[Marke; 8]` ist
/// acht Mal nichts, und das ist kein Feld, sondern ein Fehler.*
fn nennt_geist(t: &TypExpr, geister: &[String]) -> Option<String> {
    match t {
        TypExpr::Pfad(p) => {
            let n = p.text();
            let kurz = n.rsplit("::").next().unwrap_or(&n).to_string();
            geister.iter().find(|g| **g == kurz).cloned()
        }
        TypExpr::Feld(a) => nennt_geist(&a.element, geister),
        _ => None,
    }
}

fn pruefe_speicher(items: &[Item], geister: &[String], absagen: &mut Absagen) {
    fn melde(absagen: &mut Absagen, g: &str, span: Span, wo: &str) {
        absagen.schiebe(
            Absage::fehler("N011", span, format!("`{g}` is a ghost type and cannot lie in {wo}"))
                .mit_notiz(
                    "a ghost value does not exist at run time -- the generator erases it, and \
                     an erased field shifts every field after it",
                )
                .mit_notiz(
                    "a ghost belongs where the checker threads it: a parameter, a result, a \
                     `let`. There M2 holds it linear, and that is its purpose",
                ),
        );
    }
    for i in items {
        match &i.art {
            ItemArt::Modul(m) => pruefe_speicher(&m.items, geister, absagen),
            ItemArt::Tabelle(t) => {
                if let Some(s) = &t.slot {
                    for f in &s.felder {
                        if let SlotTyp::Typ(x) = &f.typ {
                            if let Some(g) = nennt_geist(x, geister) {
                                melde(absagen, &g, f.name.span, "a `slot` field");
                            }
                        }
                    }
                }
            }
            ItemArt::Typ(t) => {
                if let Some(TypExpr::Verbund(felder, _)) = &t.rumpf {
                    for f in felder {
                        if let Some(g) = nennt_geist(&f.typ.typ, geister) {
                            melde(absagen, &g, f.name.span, "a struct field");
                        }
                    }
                }
            }
            ItemArt::Statisch(s) => {
                if let Some(g) = nennt_geist(&s.typ, geister) {
                    melde(absagen, &g, s.name.span, "a `static`");
                }
            }
            ItemArt::Format(f) => {
                for x in &f.felder {
                    if let Some(g) = nennt_geist(&x.typ.typ, geister) {
                        melde(absagen, &g, x.name.span, "a `format` field");
                    }
                }
            }
            _ => {}
        }
    }
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
                                format!("`{}` does not exist in Gabbro, and that is decided", letzt.text),
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
                    "`at` takes a NAME and not an expression: the space is a declaration, \
                        not a computation",
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
                    "the guest gets registers, a stack and a `code` space -- and Gabbro \
                        owes it no proof, only isolation",
                ),
            ),
            Some(false) => absagen.schiebe(
                Absage::fehler(
                    "N005",
                    t.annahme.span,
                    format!("`entrust {}` rests on an unfalsifiable assumption", t.name.text),
                )
                .mit_notiz(
                    "an assumption about foreign code that no probe can ever refute \
                        belongs in the certificate, not in a pass",
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
            // **`walk` hatte die Pruefung nicht, die `table` hat.** Gefunden 2026-08-19, weil
            // `pruefe-konstrukte.py` `walk` als Konstrukt ohne jede Giftprobe meldete: zwei
            // gleichnamige Invarianten gingen mit 0 Fehlern durch, waehrend dieselbe Form an
            // einer `table` an `N001` faellt. *Dieselbe Regel, ein Konstrukt weiter -- und
            // niemandem aufgefallen, weil nie jemand daran geruettelt hat.*
            // **`entry` und `boot` -- zwoelf Felder, und niemand las sie.**
            //
            // Gefunden 2026-08-19 an `pruefe-konstrukte.py`: `entry` hatte keine Giftprobe,
            // und `regs in { a : rax, a : rdi, }` ging mit 0 Fehlern durch. **Zwei Namen fuer
            // dasselbe Register im Rumpf des Eintritts**, und der Erzeuger haette einen davon
            // still gewaehlt.
            //
            // *Dieselbe `doppelt`-Maschinerie wie an `table` und `device`; sie war nur nie an
            // dieses Konstrukt gehalten worden.* Und die zweite Haelfte -- dass ein Register
            // nicht zugleich `preserves` und `clobbers` sein darf -- ist derselbe Satz, eine
            // Zeile weiter: *was erhalten bleibt, wird nicht zerstoert.*
            ItemArt::Entry(e) => {
                // **Die NAMEN teilen einen Geltungsbereich, die REGISTER nicht.**
                //
                // *Erster Anlauf am 2026-08-19 pruefte beide zusammen und meldete `rax` an
                // `beispiele/07` -- der Syscall nimmt die Nummer in `rax` und gibt das
                // Ergebnis dort zurueck.* **Dasselbe Register, verschiedene Richtungen, und
                // beides richtig.** Der Korpus hat die Regel berichtigt, nicht umgekehrt.
                let mut namen = HashMap::new();
                for (n, _) in e.regs_in.iter().chain(e.regs_out.iter()) {
                    doppelt(&mut namen, &n.text, n.span, "Registerbindung", absagen);
                }
                for liste in [&e.regs_in, &e.regs_out] {
                    let mut register = HashMap::new();
                    for (_, r) in liste.iter() {
                        doppelt(&mut register, &r.text, r.span, "Register", absagen);
                    }
                }
                for c in &e.clobbers {
                    if let Some(p) = e.preserves.iter().find(|p| p.text == c.text) {
                        absagen.schiebe(
                            Absage::fehler(
                                "N017",
                                c.span,
                                format!("`{}` stands in both `preserves` and `clobbers`", c.text),
                            )
                            .mit_notiz(
                                "what is preserved is not destroyed -- the entry contract                                  would promise both at once",
                            )
                            .mit_notiz(format!("first at `preserves` {}", p.text)),
                        );
                    }
                }
            }
            // **`state` hatte die Pruefung nicht, die `device` hat** -- zwei gleichnamige
            // `transition` gingen mit 0 Fehlern durch. *`state` und `device`s `transition`
            // sind dasselbe Konstrukt auf zwei Ebenen (`SYNTAX.md`:775); nur eine der beiden
            // hatte die Regel.*
            ItemArt::State(s) => {
                let mut gesehen = HashMap::new();
                for u in &s.uebergaenge {
                    doppelt(&mut gesehen, &u.name.text, u.name.span, "Uebergang", absagen);
                }
            }
            ItemArt::Walk(w) => {
                let mut gesehen = HashMap::new();
                for i in &w.invarianten {
                    doppelt(&mut gesehen, &i.name.text, i.name.span, "Invariante", absagen);
                }
            }
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
                versatz_ist_beschraenkt(f, absagen);
                embeds_passt_ins_wort(f, absagen);
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
                .mit_notiz(format!("first at offset {}", erste.von))
                .mit_notiz(
                    "rule 3 (reject, never interpret): a reason is distinguishable by its \
                        number, otherwise the report is ambiguous",
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

/// **`N012` -- ein `offset_into` ohne Schranke ist eine Zusage ohne Halter («NL.2.5»).**
///
/// `pruefe-klauseln.py` fuehrte `offset_into` als ZUSAGE: *„Ein Feld als Versatz in ein
/// anderes; die Schranke wird nicht geprueft."*
///
/// `offset_into Self` sagt: **dieser Wert ist ein Versatz in DIESEN Puffer.** Der Wert kommt
/// aus dem Draht -- ein feindlicher ELF-Kopf setzt ihn, wohin er will. *Ohne eine Schranke ist
/// die Klausel Dokumentation, und der erste Zugriff darauf ist ein Fehlzugriff.*
///
/// Gemessen 2026-08-19: **fuenf Fundstellen, zwei ohne `where`** -- `e_shoff` und `p_offset`
/// in `beispiele/03`. *Die zwei sind unterbestimmt und nicht die Regel falsch; dieselbe Lage
/// wie bei `E010`, wo zwei eigene Beispiele fielen und es eine Eigenschaft meiner Sorgfalt
/// war, nicht der Lesart.*
///
/// **Verlangt wird, dass die `where`-Klausel das Feld SELBST und `lenof` nennt** -- genau die
/// Form, die die drei guten Stellen schreiben. *Ein `where` ueber irgendetwas waere ein Haken
/// zum Abhaken.*
fn versatz_ist_beschraenkt(f: &Format, absagen: &mut Absagen) {
    for x in &f.felder {
        let Some(ziel) = &x.offset_into else { continue };
        let genannt = x.bedingung.as_ref().map(|p| {
            let mut n = Vec::new();
            namen_im_praedikat(p, &mut n);
            (n.iter().any(|y| *y == x.name.text), n.iter().any(|y| y == "lenof"))
        });
        match genannt {
            Some((true, true)) => {}
            _ => absagen.schiebe(
                Absage::fehler(
                    "N012",
                    x.name.span,
                    format!(
                        "`{}` is an `offset_into {}` and carries no bound",
                        x.name.text, ziel.text
                    ),
                )
                .mit_notiz(
                    "the value comes off the wire -- a hostile header sets it wherever it \
                     likes, and without a bound the first access through it is out of buffer",
                )
                .mit_notiz(
                    "the form is `where <field> + … <= lenof(Self)`: the clause has to name \
                     the field ITSELF and `lenof`, otherwise it is a box to tick",
                ),
            ),
        }
    }
}

/// Die Namen eines Praedikats, `lenof` eingeschlossen -- es ist die Schranke, um die es geht.
fn namen_im_praedikat(p: &Pred, aus: &mut Vec<String>) {
    fn e(x: &Expr, aus: &mut Vec<String>) {
        match &x.art {
            ExprArt::Ort(o) => aus.push(o.basis.text.clone()),
            ExprArt::Klammer(i) | ExprArt::Unaer(_, i) => e(i, aus),
            ExprArt::Binaer(_, a, b) => {
                e(a, aus);
                e(b, aus);
            }
            ExprArt::Ruf(r) => {
                for a in &r.argumente {
                    e(a, aus);
                }
            }
            ExprArt::Eingebaut(b) => match b.as_ref() {
                Eingebaut::Lenof(t) => {
                    aus.push("lenof".into());
                    if let TypOderOrt::Ort(o) = t {
                        aus.push(o.basis.text.clone());
                    }
                }
                Eingebaut::Sizeof(_) => aus.push("sizeof".into()),
                Eingebaut::Aligned(a, c) => {
                    e(a, aus);
                    e(c, aus);
                }
            },
            _ => {}
        }
    }
    match &p.art {
        PredArt::Vergleich(x) | PredArt::Element(x, _) => e(x, aus),
        PredArt::Quantor(q) => namen_im_praedikat(&q.rumpf, aus),
        _ => {}
    }
}

/// **`N013` -- ein `embeds` muss ins Wort seines Traegers passen («NL.2.7», 2026-08-19).**
///
/// `pruefe-klauseln.py` fuehrte `embeds` als ZUSAGE: *„Ein Zeiger, der zugleich Bitfeld ist.
/// Ob das Bitfeld ins Wort passt, ist «B24»s Frage -- und sie wird hier nicht gestellt."*
///
/// **«B24» ist seit dem 2026-08-18 entschieden**, und die Antwort gilt hier genauso: eine
/// Bitlage liegt im EIGENEN Wort des Feldes; jenseits davon gibt es nichts zu bedeuten.
/// `rahmen : u64 embeds [51:12] scale 4096` ist gut, `u32 embeds [51:12]` nicht.
///
/// *Es ist dieselbe Zeile wie `N007` am `@[hi:lo]` -- und sie stand an zwei Konstrukten, von
/// denen nur eines sie hatte.*
fn embeds_passt_ins_wort(f: &Format, absagen: &mut Absagen) {
    for x in &f.felder {
        let Some((hi, lo)) = x.typ.embeds else { continue };
        let Some((breite, wort)) = crate::bitlage::wortbreite(&x.typ.typ) else { continue };
        let bits = breite * 8;
        if hi < lo {
            absagen.schiebe(
                Absage::fehler(
                    "N013",
                    x.name.span,
                    format!("`{}` writes `embeds [{hi}:{lo}]` -- the high bit is below the low one", x.name.text),
                )
                .mit_notiz("a bit range runs from high to low, and `[3:7]` names none"),
            );
        } else if hi >= bits as u128 {
            absagen.schiebe(
                Absage::fehler(
                    "N013",
                    x.name.span,
                    format!(
                        "bit {hi} of `embeds` in `{}` lies outside its own word ({} has bits 0..{})",
                        x.name.text,
                        format!("{wort:?}").to_lowercase(),
                        bits - 1
                    ),
                )
                .mit_notiz(
                    "«B24», decided 2026-08-18: a position lies inside the field's OWN word -- \
                     and an embedded pointer is a bit field like any other",
                ),
            );
        }
    }
}

/// **`N018` -- `dispatch` muss auf etwas Erklaertes zeigen («NL.2», 2026-08-19).**
///
/// Gefunden an `pruefe-konstrukte.py`: `entry` und `boot` hatten keine Giftprobe, und
/// `dispatch t::gibt_es_nicht;` ging mit **0 Fehlern** durch.
///
/// **`dispatch` ist der Weiterweg** -- die eine Zeile, an der ein Eintritt oder der
/// Systemstart in gewoehnlichen Code uebergeht. *Zeigt sie ins Leere, ist der Eintritt eine
/// Deklaration ohne Fortsetzung, und der Erzeuger schriebe einen Sprung auf ein Symbol, das
/// der Binder sucht und nicht findet.*
fn dispatch_loest_auf(baum: &Programm, absagen: &mut Absagen) {
    let mut funktionen = Vec::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        if let ItemArt::Funktion(f) = &i.art {
            funktionen.push(f.name.text.clone());
        }
    });
    crate::fuer_jedes_item(baum, &mut |i| {
        let (pfad, wo) = match &i.art {
            ItemArt::Entry(e) => (&e.dispatch, &e.name),
            ItemArt::Boot(b) => (&b.dispatch, &b.name),
            _ => return,
        };
        let Some(letzt) = pfad.teile.last() else { return };
        if funktionen.iter().any(|f| *f == letzt.text) {
            return;
        }
        absagen.schiebe(
            Absage::fehler(
                "N018",
                letzt.span,
                format!("`dispatch {}` of `{}` names no declared function", pfad.text(), wo.text),
            )
            .mit_notiz(
                "`dispatch` is the way onward -- the one line at which an entry or the boot                  path hands over to ordinary code",
            )
            .mit_notiz(
                "pointing nowhere makes the entry a declaration without a continuation, and                  the generator would emit a jump to a symbol the linker looks for in vain",
            ),
        );
    });
}
