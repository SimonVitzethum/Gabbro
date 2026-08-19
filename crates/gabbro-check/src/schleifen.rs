//! **Pass 6 -- M4/Schleifen, der Teil, der ohne Typen faellt.**
//!
//! `SPRACHE.md` §8.2: *„Beide zielen auf eine **benannte** Schleifenform. `break`/`continue`
//! ohne Namen gibt es nicht -- bei geschachtelten Schleifen ist das Ziel sonst Konvention statt
//! Syntax."* Der Parser nimmt `leave x;` an, weil `x` ein Bezeichner ist; **ob es eine Marke
//! gibt, kann nur dieser Pass sagen.**
//!
//! Was hier NICHT faellt und in M2 gehoert: `leaves identlist` nennt die linearen Werte, die den
//! Ausgang verlassen -- ob die Liste stimmt, entscheidet der Linearitaetspass.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};

/// Was der Pass beim Absteigen mitfuehrt.
///
/// **Bis 2026-08-18 war das nur `div`.** `progress` kam dazu, weil `pruefe-klauseln.py` das
/// Feld als ungelesen ausgewiesen hat -- *gefunden von einem Werkzeug, nicht von Hand.*
struct Lage<'a> {
    /// Die Namen, die `-> never` oder `diverges` erklaeren.
    div: &'a [String],
    /// **Alle erklaerten Funktionsnamen.** Ohne sie kann `S006` nicht zwischen *„kehrt
    /// zurueck"* und *„gibt es hier nicht"* unterscheiden -- und der zweite Fall gehoert dem
    /// Namenspass.
    bekannt: &'a [String],
    /// Annahme -> ist sie falsifizierbar?
    annahmen: std::collections::BTreeMap<String, bool>,
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    let div = divergierende(baum);
    let mut bekannt = Vec::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        if let ItemArt::Funktion(f) = &i.art {
            bekannt.push(f.name.text.clone());
        }
    });
    let lg = Lage {
        div: &div,
        bekannt: &bekannt,
        annahmen: crate::annahmen(baum),
    };
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        ItemArt::Funktion(f) => {
            if let FnRumpf::Block(b) = &f.rumpf {
                block(b, &mut Vec::new(), &lg, absagen);
            }
        }
        ItemArt::Check(c) => block(&c.can_fail, &mut Vec::new(), &lg, absagen),
        _ => {}
    });
}

fn block(b: &Block, marken: &mut Vec<String>, lg: &Lage, absagen: &mut Absagen) {
    for s in &b.anweisungen {
        anweisung(s, marken, lg, absagen);
    }
}

fn anweisung(s: &Stmt, marken: &mut Vec<String>, lg: &Lage, absagen: &mut Absagen) {
    match &s.art {
        StmtArt::Leave(ziel) => ziel_pruefen(ziel, marken, "leave", absagen),
        StmtArt::Next(ziel) => ziel_pruefen(ziel, marken, "next", absagen),
        StmtArt::Wenn(w) => {
            for (_, b) in &w.zweige {
                block(b, marken, lg, absagen);
            }
            if let Some(b) = &w.sonst {
                block(b, marken, lg, absagen);
            }
        }
        StmtArt::Match(m) => {
            for z in &m.zweige {
                block(&z.rumpf, marken, lg, absagen);
            }
        }
        StmtArt::Bricht(b) => block(&b.rumpf, marken, lg, absagen),
        StmtArt::Narrow(n) => block(&n.sonst, marken, lg, absagen),
        StmtArt::Sperrt(l) => block(&l.rumpf, marken, lg, absagen),
        StmtArt::Observiert(o) => block(&o.rumpf, marken, lg, absagen),
        StmtArt::LetSonst(l) => {
            // **U7.** `SYNTAX.md` §7: *„der `else`-Zweig muss divergieren oder
            // zurueckkehren"*. Faellt er durch, ist `let … else` genau der verborgene
            // Kontrollfluss, gegen den es geschrieben wurde -- der Name waere danach
            // gebunden, ohne dass je ein Wert entstand.
            if !crate::endet_immer(&l.sonst, lg.div) {
                absagen.schiebe(
                    Absage::fehler(
                        "S002",
                        l.sonst.span,
                        format!(
                            "the `else` branch of `let {} = …` falls through",
                            l.name.text
                        ),
                    )
                    .mit_notiz(
                        "SYNTAX.md §7: the only error propagation is `let … else (e) { …\
                            }`, and its branch must diverge or return",
                    ),
                );
            }
            block(&l.sonst, marken, lg, absagen);
        }
        StmtArt::Exchange(e) => {
            if let XForm::Update { rumpf, .. } = &e.form {
                block(rumpf, marken, lg, absagen);
            }
        }
        StmtArt::Schleife(sch) => match sch.as_ref() {
            // `traverse` traegt keine Marke -- die Grammatik gibt ihr keine Stelle dafuer.
            Schleife::Traverse(t) => {
                abstieg_pruefen(t, absagen);
                block(&t.rumpf, marken, lg, absagen)
            }
            Schleife::Retry(r) => {
                ausgang_pruefen(&r.bei_ueberschreitung, lg, absagen);
                fortschritt_pruefen(r.fortschritt.as_ref(), lg, absagen);
                mit_marke(r.marke.as_ref(), &r.rumpf, marken, lg, absagen);
            }
            Schleife::Forever(f) => {
                ausgang_pruefen(&f.bei_ueberschreitung, lg, absagen);
                fortschritt_pruefen(f.fortschritt.as_ref(), lg, absagen);
                mit_marke(f.marke.as_ref(), &f.rumpf, marken, lg, absagen);
            }
        },
        _ => {}
    }
}

fn mit_marke(
    marke: Option<&Ident>,
    rumpf: &Block,
    marken: &mut Vec<String>,
    lg: &Lage,
    absagen: &mut Absagen,
) {
    if let Some(m) = marke {
        marken.push(m.text.clone());
        block(rumpf, marken, lg, absagen);
        marken.pop();
    } else {
        block(rumpf, marken, lg, absagen);
    }
}

/// Verlaesst dieser Block seinen Weg immer? Syntaktisch, ohne Fixpunkt -- dieselbe Frage,
/// die M1 fuer die V1-Verneinung stellt.
///
/// **Wer divergiert, endet auch.** Ein Block, der auf `exit();` endet, faellt nicht durch --
/// wenn `exit` als `-> never` oder mit `diverges` erklaert ist.
///
/// Bis 2026-08-15 sah `endet_immer` nur `return`/`leave`/`next` und hielt jeden Aufruf fuer
/// eine gewoehnliche Anweisung. **Sieben `S002` im Fragmentkorpus kamen allein daher** --
/// jeder Fehlerzweig eines `let … else`, der mit einem Abbruch endet, galt als
/// durchfallend. Der Pass war zu streng, und zwar an der Stelle, an der ein Kernel seine
/// Fehlerbehandlung schreibt.
///
/// *Gefunden am Fragmentlauf, wie schon der `E005`-Fehler. Die Fragmente sind das einzige
/// Werkzeug im Ordner, das den Pruefer gegen ECHTEN Code haelt statt gegen Beispiele, die
/// ich selbst geschrieben habe.*
fn divergierende(baum: &Programm) -> Vec<String> {
    let mut aus = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            let nie = matches!(&f.ergebnis, Some(TypExpr::Never(_)));
            let div = f.klasse == Some(FnKlasse::Divergent)
                || f.effects.as_ref().is_some_and(|w| {
                    w.liste.iter().any(|e| matches!(e.art, WirkungArt::Divergiert))
                });
            if nie || div {
                aus.push(f.name.text.clone());
            }
        }
    });
    aus
}


fn ziel_pruefen(ziel: &Ident, marken: &[String], wort: &str, absagen: &mut Absagen) {
    if marken.iter().any(|m| m == &ziel.text) {
        return;
    }
    let mut a = Absage::fehler(
        "S001",
        ziel.span,
        format!(
            "`{wort} {}` targets no enclosing loop label",
            ziel.text
        ),
    )
    .mit_notiz(
        "SPRACHE.md §8.2: there is no unnamed `break`/`continue` -- with nested loops the \
            target would be convention",
    );
    if marken.is_empty() {
        a = a.mit_notiz("no label is in scope here; `retry`/`forever` take one");
    } else {
        a = a.mit_notiz(format!("im Geltungsbereich: {}", marken.join(", ")));
    }
    absagen.schiebe(a);
}

/// **`progress` hatte bis 2026-08-18 keinen Leser** -- ausgewiesen von `pruefe-klauseln.py`.
///
/// **Was hier NICHT geprueft wird, ist Lebendigkeit.** D8 sagt es und behaelt recht:
/// *„`progress` nennt Annahmen, beweist keine Lebendigkeit. Kein Konstrukt behauptet eine."*
/// Ein Pass, der hier mehr verspraeche, waere genau die Sorte Zusage, gegen die dieser Ordner
/// gebaut ist.
///
/// **Geprueft wird, was die Sprache verspricht**, nicht mehr: `progress` nennt WER die
/// Schleife beendet, und zwar als **Annahme mit Falsifikator** (`SYNTAX.md` §8.3: *„The
/// watchdog IS the falsifier"*). Zwei Weisen, wie dieses Versprechen leer sein kann:
///
/// ```text
/// S003   der Name gehoert keiner Annahme -- die Schleife ruht auf einem Wort,
///        das niemand aufgeschrieben hat, und im Zeugnis steht es nirgends
/// S004   die Annahme ist `unfalsifiable` -- dann endet die Schleife, weil es
///        dasteht, und keine Sonde kann je widersprechen
/// ```
///
/// *Eine unfalsifizierbare Fortschrittsannahme nimmt dem Wachhund seinen Gegenstand.*
fn fortschritt_pruefen(zeuge: Option<&Ident>, lg: &Lage, absagen: &mut Absagen) {
    let Some(z) = zeuge else { return };
    match lg.annahmen.get(&z.text) {
        None => absagen.schiebe(
            Absage::fehler(
                "S003",
                z.span,
                format!("`progress {}` names no declared assumption", z.text),
            )
            .mit_notiz(
                "SYNTAX.md §8.3: `progress` names WHO ends the loop, and that must be a \
                    declared assumption -- otherwise it is a hope with a keyword in front",
            ),
        ),
        Some(false) => absagen.schiebe(
            Absage::fehler(
                "S004",
                z.span,
                format!("`progress {}` rests on an unfalsifiable assumption", z.text),
            )
            .mit_notiz(
                "the watchdog IS the falsifier (`on_exceeded`); an assumption without one \
                    is a claim",
            ),
        ),
        Some(true) => {}
    }
}

/// **`S005` -- das Abstiegsmass muss sich bewegen koennen («NL.2.3», 2026-08-19).**
///
/// `pruefe-klauseln.py` fuehrte `abstieg` als schaerfste der elf verbliebenen Zusagen:
/// *„Wie der `traverse` absteigt. `schleifen.rs` geht in den Rumpf, liest den Abstieg aber
/// nicht -- **und an ihm haengt die Terminierung.**"*
///
/// ## Was geprueft wird, und was ausdruecklich nicht
///
/// **Nicht:** dass das Mass faellt. Das ist eine Aussage ueber Werte und gehoert dem
/// Beweiser -- `consuming.ordnung` (S1) fuehrt sie als Schablone.
///
/// **Sondern:** dass es sich ueberhaupt bewegen KANN. Ein `by decreasing E`, in dem weder die
/// Traversierungsvariable noch ein Name vorkommt, den der Rumpf schreibt, ist ueber alle
/// Durchgaenge KONSTANT -- und ein konstantes Mass faellt nie.
///
/// ```gabbro
/// traverse v of g over ancestors of g by decreasing v         -- die Variable, ok
/// traverse w of s over elems of s.worte by decreasing (lenof(s.worte) - i)
///                                                              -- `i` schreibt der Rumpf, ok
/// traverse i over slots of w by unvisited by decreasing GRENZE -- KONSTANT
/// ```
///
/// > **Es ist die notwendige Bedingung, nicht die hinreichende** -- und genau darum steht sie
/// > hier statt beim Beweiser. *Eine notwendige Bedingung, die ein Pass halten kann, ist mehr
/// > wert als eine hinreichende, die niemand haelt.*
fn abstieg_pruefen(t: &Traverse, absagen: &mut Absagen) {
    let Abstieg::Fallend(e) = &t.abstieg else { return };
    let mut namen = Vec::new();
    namen_im_ausdruck(e, &mut namen);
    if namen.is_empty() {
        // Ein Mass ohne jeden Namen ist eine Zahl -- dasselbe Urteil, anderer Weg dorthin.
        melde(t, e.span, absagen);
        return;
    }
    if namen.iter().any(|n| *n == t.variable.text) {
        return; // die Traversierung bewegt sie selbst
    }
    let mut geschrieben = Vec::new();
    geschriebene_namen(&t.rumpf, &mut geschrieben);
    if namen.iter().any(|n| geschrieben.contains(n)) {
        return;
    }
    melde(t, e.span, absagen);
}

fn melde(t: &Traverse, span: gabbro_syntax::span::Span, absagen: &mut Absagen) {
    absagen.schiebe(
        Absage::fehler(
            "S005",
            span,
            "the descent measure names neither the traversal variable nor a name the body \
                writes"
                .to_string(),
        )
        .mit_notiz(format!(
            "`{}` therefore does not move across the passes -- and a constant measure \
                never falls",
            t.variable.text
        ))
        .mit_notiz(
            "checked is the NECESSARY condition, not the sufficient one: THAT it falls is \
                the prover's business (`consuming.ordnung`)",
        ),
    );
}

fn namen_im_ausdruck(e: &Expr, aus: &mut Vec<String>) {
    match &e.art {
        ExprArt::Ort(o) => {
            aus.push(o.basis.text.clone());
            for s in &o.suffixe {
                if let OrtSuffix::Index(i) = s {
                    namen_im_ausdruck(i, aus);
                }
            }
        }
        ExprArt::Klammer(i) | ExprArt::Unaer(_, i) => namen_im_ausdruck(i, aus),
        ExprArt::Binaer(_, a, b) => {
            namen_im_ausdruck(a, aus);
            namen_im_ausdruck(b, aus);
        }
        ExprArt::Ruf(r) => {
            for a in &r.argumente {
                namen_im_ausdruck(a, aus);
            }
        }
        ExprArt::Eingebaut(b) => match b.as_ref() {
            // **`lenof(s.worte)` nennt einen Ort, und der zaehlt.** Ohne diesen Zweig
            // saehe das Mass aus `FRAGMENTE.md`:1110 wie eine Konstante aus.
            Eingebaut::Sizeof(TypOderOrt::Ort(o)) | Eingebaut::Lenof(TypOderOrt::Ort(o)) => {
                aus.push(o.basis.text.clone())
            }
            Eingebaut::Aligned(a, c) => {
                namen_im_ausdruck(a, aus);
                namen_im_ausdruck(c, aus);
            }
            _ => {}
        },
        _ => {}
    }
}

fn geschriebene_namen(b: &Block, aus: &mut Vec<String>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => aus.push(z.ziel.basis.text.clone()),
            StmtArt::Publish(p) => aus.push(p.ziel.basis.text.clone()),
            StmtArt::Exchange(e) => aus.push(e.ort.basis.text.clone()),
            _ => {}
        }
        for k in crate::unterbloecke(s) {
            geschriebene_namen(k, aus);
        }
    }
}

/// **`S006` -- `on_exceeded` muss divergieren, und der Pruefer sagte es nicht.**
///
/// Gefunden 2026-08-19 bei der Handpruefung der 37 Klauseleintraege. Die Tabelle fuehrte
/// `bei_ueberschreitung` als ABSENKUNG mit dem Satz *„Der Zweig bei ueberschrittener Schranke
/// ist Code, keine Zusage."* **Das ist falsch:** es IST eine Zusage, und `emit.rs`:2310 haelt
/// sie -- *„`on_exceeded` must name a function returning `never`"*.
///
/// ```gabbro
/// retry bounded 8 ops on_exceeded kehrt_zurueck { … }   -- gabbro pruefe: 0 Fehler
///                                                       -- gabbro emit:   C001
/// ```
///
/// > **Dieselbe Klasse wie «B24» vor dem 2026-08-19:** eine Regel, die nur auf der
/// > Erzeugerflaeche steht, und die beruehren die meisten Programme nie.
///
/// *Warum die Zusage noetig ist:* der Wachhund ist der Ausgang, an dem die Schranke ihre
/// Wirklichkeit beruehrt. Kehrte er zurueck, liefe die Schleife weiter -- und die Schranke
/// waere eine Zahl ohne Folge.
fn ausgang_pruefen(a: &Ident, lg: &Lage, absagen: &mut Absagen) {
    if lg.div.iter().any(|d| *d == a.text) {
        return;
    }
    // **Ein UNBEKANNTER Name gehoert dem Namenspass, nicht dieser Regel** -- W10.
    //
    // *Gefunden an der eigenen Testliste:* `on_exceeded w` in einem Ausschnitt, in dem `w`
    // nirgends deklariert ist. Die erste Fassung meldete *„names a function that returns"*,
    // und das war zweimal falsch: der Name nennt keine Funktion, und ob sie zurueckkehrt,
    // weisz hier niemand. **Was nicht genau gemeldet werden kann, setzt kein Pass durch** --
    // dieselbe Begruendung, an der Lesart B gestorben ist.
    if !lg.bekannt.iter().any(|f| *f == a.text) {
        return;
    }
    absagen.schiebe(
        Absage::fehler(
            "S006",
            a.span,
            format!("`on_exceeded {}` names a function that returns", a.text),
        )
        .mit_notiz(
            "the watchdog is the exit at which the bound touches reality -- if it returned, \
             the loop would carry on and the bound would be a number without a consequence",
        )
        .mit_notiz(
            "declare it `-> never` or `effects { diverges }`; a `reason` value would need an \
             error-return convention, and that is not decided",
        ),
    );
}
