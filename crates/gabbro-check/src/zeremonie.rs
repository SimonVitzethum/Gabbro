//! **Das Zeremonieregister -- Stufe 2, und das erste Instrument fuer Ziel 3.**
//!
//! Von den vier Zielen hatte **eines als einziges keine Zahl**: *„moeglichst gut nutzbar"*.
//! Ohne eine ist das eine Meinung -- und *„keine Klempnerei beim Endnutzer"* ist eine
//! Nutzbarkeitsaussage. Dieses Modul zaehlt, was ein Programmierer hinschreiben MUSS und was
//! keinen Rechenschritt beschreibt.
//!
//! ## Und die Kalibrierung steht IM Werkzeug, nicht im Auge des Lesers
//!
//! Ein Nutzbarkeitsmass wird sofort zum Optimierungsziel. Faellt es unkalibriert, dann faellt
//! als erstes das, was am billigsten wegzulassen ist -- und das ist `effects`, `costs`, die
//! Paarungsklauseln. **Genau der Gegenstand der Sprache.**
//!
//! Deshalb zwei Achsen statt einer, und sie sind ausdruecklich verschieden:
//!
//! ```text
//! ACHSE 1, gemessen    steht diese Tatsache ein ZWEITES Mal in dieser Einheit?
//!                      -> ableitbar / redundant / tragend
//! ACHSE 2, erklaert    darf die Zahl sinken?
//!                      -> je Regel ein Ja oder Nein MIT GRUND, und beides steht im Bericht
//! ```
//!
//! > **Achse 1 ist mechanisch, Achse 2 ist eine Entscheidung -- und sie steht als
//! > Entscheidung da.** Das ist die Lehre aus `N_ritus` (W19): ein Urteil, das sich als
//! > Messung liest, bekommt die Autoritaet einer Messung. *Die zaehlbare Haelfte wird
//! > gezaehlt, die geurteilte wird benannt.*
//!
//! ## Was `ableitbar` heisst und was es NICHT heisst
//!
//! Ableitbar heisst: **dieselbe Tatsache steht mechanisch lesbar an einer zweiten Stelle
//! dieser Einheit**, und der Bericht nennt welche. Es heisst nicht *„weg damit"*. Eine
//! ableitbare Zeile kann am richtigen Ort stehen -- die Spalte sagt, was der Uebersetzer
//! selbst wuesste; ob er es trotzdem verlangen soll, ist Achse 2.
//!
//! ## Die Grundgesamtheit, und was ausdruecklich NICHT darin ist
//!
//! Gezaehlt wird **jede Klausel und jede Annotation** -- jedes Stueck Text, das keinen
//! Rechenschritt beschreibt. Was draussen bleibt, steht im Bericht unter `NOT counted`, aus
//! demselben Grund wie bei `gabbro paesse`: *was ein Werkzeug nicht misst, muss es sagen,
//! sonst sieht ungemessenes Schweigen wie eine Null aus* (W11).

use crate::typen::Typ;
use crate::umgebung::Umgebung;
use gabbro_syntax::ast::*;
use std::collections::HashMap;

// ---------------------------------------------------------------------------------------
// Die Regeltafel -- Achse 1 und Achse 2 nebeneinander, und beide sichtbar
// ---------------------------------------------------------------------------------------

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Klasse {
    /// Dieselbe Tatsache steht mechanisch lesbar an einer zweiten Stelle.
    Ableitbar,
    /// Dieselbe Tatsache steht zweimal.
    Redundant,
    /// Sie steht nirgends sonst.
    Tragend,
}

impl Klasse {
    pub fn name(self) -> &'static str {
        match self {
            Klasse::Ableitbar => "derivable",
            Klasse::Redundant => "redundant",
            Klasse::Tragend => "load-bearing",
        }
    }
}

pub struct Regel {
    pub kennung: &'static str,
    pub klasse: Klasse,
    /// Was die Regel trifft -- englisch, das ist Nutzerflaeche.
    pub was: &'static str,
    /// **Achse 2.** Darf die Zahl dieser Regel fallen?
    pub darf_sinken: bool,
    /// Und warum. **Keine Regel ohne Grund** -- ein Nein ohne Satz waere ein Machtwort.
    pub grund: &'static str,
}

/// **Die Tafel. Wer eine Regel hinzufuegt, muss Achse 2 mitbeantworten** -- das Feld ist nicht
/// optional, und der Waechter liest die Gruende nach.
pub const REGELN: &[Regel] = &[
    Regel {
        kennung: "A1",
        klasse: Klasse::Ableitbar,
        was: "`let` annotation equal to the callee's declared result type",
        darf_sinken: true,
        grund: "the signature stands in this unit: reading it off is a lookup, not a guess",
    },
    Regel {
        kennung: "A2",
        klasse: Klasse::Ableitbar,
        was: "`let` annotation equal to the declared type of the place on the right",
        darf_sinken: true,
        grund: "the table, format or device declaration already says it",
    },
    Regel {
        kennung: "A3",
        klasse: Klasse::Ableitbar,
        was: "`let` annotation equal to the declared type of a name in scope",
        darf_sinken: true,
        grund: "parameter, constant or earlier binding carries the same type",
    },
    Regel {
        kennung: "A4",
        klasse: Klasse::Ableitbar,
        was: "an effect entry that a callee of this body already declares",
        darf_sinken: true,
        grund: "yes, but in exactly ONE way: the caller's list is COMPUTED from the callees \
                and printed (`gabbro abi`). Dropping the entries without computing them \
                somewhere undoes `E008` -- the posting that made `effects` compositional on \
                2026-08-15, when a `pure` promise still ended at the first call boundary",
    },
    Regel {
        kennung: "R1",
        klasse: Klasse::Redundant,
        was: "an effect entry that stands twice in the same `effects` list",
        darf_sinken: true,
        grund: "the second copy adds no permission and no obligation",
    },
    Regel {
        kennung: "R2",
        klasse: Klasse::Redundant,
        was: "a `requires` textually equal to another `requires` of the same function",
        darf_sinken: true,
        grund: "the same precondition, twice",
    },
    Regel {
        kennung: "R3",
        klasse: Klasse::Redundant,
        was: "an `ensures` textually equal to another `ensures` of the same function",
        darf_sinken: true,
        grund: "the same postcondition, twice",
    },
    Regel {
        kennung: "R4",
        klasse: Klasse::Redundant,
        was: "a `requires` that repeats the declared range of a parameter",
        darf_sinken: true,
        grund: "`p : u32 in 0 ..< N` already binds `p`; the clause restates the type",
    },
    Regel {
        kennung: "T1",
        klasse: Klasse::Tragend,
        was: "an effect entry",
        darf_sinken: false,
        grund: "the effect list IS the subject, not the form around it; and since `E008` it \
                includes the callees', which is what makes it readable at the declaration",
    },
    Regel {
        kennung: "T2",
        klasse: Klasse::Tragend,
        was: "`costs`",
        darf_sinken: false,
        grund: "a bound that stands nowhere else; without it the cost pass has nothing to hold \
                the body against",
    },
    Regel {
        kennung: "T3",
        klasse: Klasse::Tragend,
        was: "`requires` / `ensures` that no other clause repeats",
        darf_sinken: false,
        grund: "the contract; a call site narrows on it and a body owes it",
    },
    Regel {
        kennung: "T4",
        klasse: Klasse::Tragend,
        was: "`maintains`",
        darf_sinken: false,
        grund: "which invariant survives this function stands in no other place",
    },
    Regel {
        kennung: "T5",
        klasse: Klasse::Tragend,
        was: "a table `invariant`",
        darf_sinken: false,
        grund: "the connecting truth of the carrier; the slot types cannot say it",
    },
    Regel {
        kennung: "T6",
        klasse: Klasse::Tragend,
        was: "a loop bound, `on_exceeded`, `progress` or `decreases`",
        darf_sinken: false,
        grund: "termination is not readable from the body; that is the whole point of D0",
    },
    Regel {
        kennung: "T7",
        klasse: Klasse::Tragend,
        was: "`touches` on a traversal",
        darf_sinken: false,
        grund: "what a pass may touch inside the walk is a claim about the walk, not about \
                the statements in it",
    },
    Regel {
        kennung: "T8",
        klasse: Klasse::Tragend,
        was: "a `let` annotation this compiler cannot read off",
        darf_sinken: false,
        grund: "it says something the right-hand side does not say -- a widening, a narrowing, \
                or the only type there is",
    },
    Regel {
        kennung: "T9",
        klasse: Klasse::Tragend,
        was: "a `reserved` field",
        darf_sinken: false,
        grund: "silence about a bit is not the same statement as `reserved`: one is an \
                omission, the other a promise not to write",
    },
    Regel {
        kennung: "T10",
        klasse: Klasse::Tragend,
        was: "a register access class (`class rw`, `class w1c`, per register or per field)",
        darf_sinken: false,
        grund: "no reading of the C could recover it; the hardware manual is the only other \
                place it stands",
    },
    Regel {
        kennung: "T11",
        klasse: Klasse::Tragend,
        was: "`assume` with its falsifier",
        darf_sinken: false,
        grund: "an assumption no probe can contradict is not a statement (`N031`)",
    },
    Regel {
        kennung: "T12",
        klasse: Klasse::Tragend,
        was: "a range on a declared type (`u32 in 0 ..< N`)",
        darf_sinken: false,
        grund: "the range is the value-carried bound; dropping it moves the check to every \
                use site instead",
    },
];

/// **Was dieses Register ausdruecklich NICHT zaehlt** -- und warum. Steht im Bericht.
///
/// *Was ein Werkzeug nicht misst, muss es sagen* -- sonst sieht ungemessenes Schweigen wie
/// eine Null aus.
pub const NICHT_GEZAEHLT: &[(&str, &str)] = &[
    ("`module` / `use` / `pub`", "structure, not a clause about behaviour"),
    ("`section` / `arch` / `when`", "placement and configuration, no proof surface"),
    ("`reason` cases and their texts", "they ARE the payload, not a clause about it"),
    ("`entrust` / `boot` / `entry`", "one clause each in the corpus -- too few to weigh"),
    ("`by` induction hints", "a proof hint; counted by `gabbro pflichten`, not here"),
    ("type declarations themselves", "a name for a shape is not ceremony"),
];

// ---------------------------------------------------------------------------------------
// Der Befund
// ---------------------------------------------------------------------------------------

pub struct Stelle {
    pub regel: &'static str,
    /// Wo sie steht -- `fn name`, `table T`, `device D`.
    pub ort: String,
    /// Der Wortlaut, aus der Quelle geschnitten.
    pub was: String,
    /// **Bei `ableitbar` und `redundant`: wo die zweite Stelle steht.** Ohne den Nachweis
    /// waere die Einordnung eine Behauptung.
    pub nachweis: Option<String>,
}

impl Stelle {
    pub fn klasse(&self) -> Klasse {
        REGELN
            .iter()
            .find(|r| r.kennung == self.regel)
            .map(|r| r.klasse)
            .expect("every site carries a rule from the table")
    }
    pub fn darf_sinken(&self) -> bool {
        REGELN
            .iter()
            .find(|r| r.kennung == self.regel)
            .map(|r| r.darf_sinken)
            .expect("every site carries a rule from the table")
    }
}

/// Der Wortlaut einer Stelle, aus der Quelle geschnitten und auf eine Zeile gebracht.
///
/// **One site, one cut.** `manifest.rs` needs the same wording for the precondition of an
/// `axiom`, and a second cut with a different truncation limit would be the same sentence
/// in two versions.
pub(crate) fn schnitt(quelle: &str, span: gabbro_syntax::span::Span) -> String {
    let (a, b) = (span.von as usize, span.bis as usize);
    if a > b || b > quelle.len() {
        return String::new();
    }
    let roh = &quelle[a..b];
    let mut s = String::new();
    let mut luecke = false;
    for c in roh.chars() {
        if c.is_whitespace() {
            luecke = true;
            continue;
        }
        if luecke && !s.is_empty() {
            s.push(' ');
        }
        luecke = false;
        s.push(c);
    }
    if s.chars().count() > 72 {
        s = s.chars().take(69).collect::<String>() + "...";
    }
    s
}

pub fn sammle(baum: &Programm, quelle: &str) -> Vec<Stelle> {
    let u = Umgebung::sammle(baum);
    // **Der Aufrufgraph, fuer A4.** `huelle_der_gerufenen` traegt die Wirkung des Gerufenen
    // ueber den Aufrufrand -- mit der Abbildung auf die Argumente, die `E008` selbst nicht
    // macht. *Hier ist die feinere Fassung zulaessig, weil ein Irrtum eine tragende Zeile
    // als ableitbar buchen wuerde und nicht umgekehrt* -- darum die Absicherung unten.
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    let mut aus = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| match &item.art {
        ItemArt::Funktion(f) => funktion(f, modul, &u, &g, quelle, &mut aus),
        ItemArt::Tabelle(t) => tabelle(t, quelle, &mut aus),
        ItemArt::Format(fo) => format_(fo, quelle, &mut aus),
        ItemArt::Device(d) => geraet(d, quelle, &mut aus),
        ItemArt::Assume(a) => aus.push(Stelle {
            regel: "T11",
            ort: format!("assume {}", a.name.text),
            was: schnitt(quelle, a.span),
            nachweis: None,
        }),
        ItemArt::Statisch(s) => bereich_von_typ(&s.typ, &format!("static {}", s.name.text), quelle, &mut aus),
        _ => {}
    });
    aus
}

// ---------------------------------------------------------------------------------------
// Funktionen -- hier liegt das meiste
// ---------------------------------------------------------------------------------------

fn funktion(
    f: &FnDecl,
    modul: &str,
    u: &Umgebung,
    g: &crate::aufrufgraph::Graph,
    quelle: &str,
    aus: &mut Vec<Stelle>,
) {
    let ort = format!("fn {}", f.name.text);

    // **Die Bereiche an den Parametertypen** -- der wertgetragene Teil des Vertrags.
    for p in &f.parameter {
        bereich_von_typ(&p.typ, &ort, quelle, aus);
    }
    if let Some(e) = &f.ergebnis {
        bereich_von_typ(e, &ort, quelle, aus);
    }

    // `requires` -- doppelt (R2), Wiederholung eines Parameterbereichs (R4), sonst tragend.
    let mut gesehen: Vec<String> = Vec::new();
    for r in &f.requires {
        let text = schnitt(quelle, r.span);
        if let Some(v) = gesehen.iter().find(|x| **x == text) {
            aus.push(Stelle {
                regel: "R2",
                ort: ort.clone(),
                was: text.clone(),
                nachweis: Some(format!("stands already as `{v}`")),
            });
            continue;
        }
        gesehen.push(text.clone());
        match wiederholt_parameterbereich(r, f, quelle) {
            Some(p) => aus.push(Stelle {
                regel: "R4",
                ort: ort.clone(),
                was: text,
                nachweis: Some(format!("the type of `{p}` already binds it")),
            }),
            None => aus.push(Stelle {
                regel: "T3",
                ort: ort.clone(),
                was: text,
                nachweis: None,
            }),
        }
    }

    let mut gesehen_e: Vec<String> = Vec::new();
    for e in &f.ensures {
        let text = schnitt(quelle, e.span);
        if let Some(v) = gesehen_e.iter().find(|x| **x == text) {
            aus.push(Stelle {
                regel: "R3",
                ort: ort.clone(),
                was: text,
                nachweis: Some(format!("stands already as `{v}`")),
            });
            continue;
        }
        gesehen_e.push(text.clone());
        aus.push(Stelle {
            regel: "T3",
            ort: ort.clone(),
            was: text,
            nachweis: None,
        });
    }

    for m in &f.maintains {
        aus.push(Stelle {
            regel: "T4",
            ort: ort.clone(),
            was: format!("maintains {}", m.text),
            nachweis: None,
        });
    }

    if let Some(w) = &f.effects {
        // **Was die Gerufenen ohnehin nennen.** Ist die Huelle unvollstaendig (Zyklus,
        // Gerufener ohne `effects`, unbekannter Name), gilt sie als LEER: eine untere
        // Schranke darf keine Zeile als ableitbar buchen. *Die Vergroeberung geht in die
        // Richtung `tragend`, und nur deshalb ist sie zulaessig* (W10).
        let h = g.huelle_der_gerufenen(&g.schluessel_von(modul, &f.name.text));
        let von_gerufenen = if h.unvollstaendig.is_some() {
            std::collections::BTreeSet::new()
        } else {
            h.wirkungen
        };
        wirkungen(w, &ort, quelle, &von_gerufenen, aus);
    }
    if let Some(c) = &f.costs {
        aus.push(Stelle {
            regel: "T2",
            ort: ort.clone(),
            was: format!("costs {}", schnitt(quelle, c.span)),
            nachweis: None,
        });
    }
    if let Some(d) = &f.decreases {
        aus.push(Stelle {
            regel: "T6",
            ort: ort.clone(),
            was: format!("decreases {}", schnitt(quelle, d.span)),
            nachweis: None,
        });
    }

    // **Der Rumpf.** Nur hier braucht es die Umgebung -- eine `let`-Annotation ist genau dann
    // ableitbar, wenn die rechte Seite denselben Typ ERKLAERT nennt.
    let FnRumpf::Block(b) = &f.rumpf else { return };
    let mut lokal: HashMap<String, Typ> = HashMap::new();
    for p in &f.parameter {
        lokal.insert(p.name.text.clone(), u.typ_von_ausdruck_decl(modul, &p.typ));
    }
    block(b, modul, u, quelle, &ort, &mut lokal, aus);
}

fn wirkungen(
    w: &Wirkungen,
    ort: &str,
    quelle: &str,
    von_gerufenen: &std::collections::BTreeSet<String>,
    aus: &mut Vec<Stelle>,
) {
    let mut gesehen: Vec<String> = Vec::new();
    for e in &w.liste {
        let text = e.art.text();
        if gesehen.contains(&text) {
            aus.push(Stelle {
                regel: "R1",
                ort: ort.to_string(),
                was: text,
                nachweis: Some("the same entry stands earlier in this list".into()),
            });
            continue;
        }
        gesehen.push(text.clone());
        if von_gerufenen.contains(&text) {
            aus.push(Stelle {
                regel: "A4",
                ort: ort.to_string(),
                was: text,
                nachweis: Some("a callee of this body declares it".into()),
            });
            continue;
        }
        aus.push(Stelle {
            regel: "T1",
            ort: ort.to_string(),
            was: text,
            nachweis: None,
        });
    }
    let _ = quelle;
}

/// **Wiederholt diese Vorbedingung den Bereich eines Parameters?**
///
/// Die Form, auf die es ankommt, ist `requires p < N` neben `p : u32 in 0 ..< N` -- und
/// genauso `p <= N` neben `0 .. N`. *Mehr wird nicht erkannt, und was nicht erkannt wird,
/// faellt nach `tragend`* -- die Vergroeberung geht in die sichere Richtung (W10): eine
/// unerkannte Redundanz kostet eine zu hohe `tragend`-Zahl, eine erfundene wuerde eine
/// Vertragszeile zum Rueckstand erklaeren.
fn wiederholt_parameterbereich(r: &Pred, f: &FnDecl, quelle: &str) -> Option<String> {
    let PredArt::Vergleich(e) = &r.art else { return None };
    let ExprArt::Binaer(op, links, rechts) = &e.art else { return None };
    let ExprArt::Ort(o) = &links.art else { return None };
    if !o.suffixe.is_empty() {
        return None;
    }
    let p = f.parameter.iter().find(|p| p.name.text == o.basis.text)?;
    let TypExpr::Int(i) = &p.typ else { return None };
    let b = i.bereich.as_ref()?;
    let obergrenze = schnitt(quelle, b.bis.span);
    let rechte = schnitt(quelle, rechts.span);
    let passt = match op {
        BinOp::Kleiner => b.exklusiv,
        BinOp::KleinerGleich => !b.exklusiv,
        _ => false,
    };
    if passt && obergrenze == rechte && !obergrenze.is_empty() {
        Some(p.name.text.clone())
    } else {
        None
    }
}

/// Ein Bereich an einem geschriebenen Typ -- `u32 in 0 ..< N`, auch unter Zeiger und Feld.
fn bereich_von_typ(t: &TypExpr, ort: &str, quelle: &str, aus: &mut Vec<Stelle>) {
    match t {
        TypExpr::Int(i) => {
            if let Some(b) = &i.bereich {
                aus.push(Stelle {
                    regel: "T12",
                    ort: ort.to_string(),
                    was: format!("in {}", schnitt(quelle, b.span)),
                    nachweis: None,
                });
            }
        }
        TypExpr::Float(fl) => {
            if let Some(b) = &fl.bereich {
                aus.push(Stelle {
                    regel: "T12",
                    ort: ort.to_string(),
                    was: format!("in {}", schnitt(quelle, b.span)),
                    nachweis: None,
                });
            }
        }
        TypExpr::Feld(a) => bereich_von_typ(&a.element, ort, quelle, aus),
        TypExpr::Zeiger(z) => bereich_von_typ(&z.ziel, ort, quelle, aus),
        TypExpr::Verbund(felder, _) => {
            for f in felder {
                bereich_von_typ(&f.typ.typ, ort, quelle, aus);
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------------------
// Traeger
// ---------------------------------------------------------------------------------------

fn tabelle(t: &Tabelle, quelle: &str, aus: &mut Vec<Stelle>) {
    let ort = format!("table {}", t.name.text);
    for i in &t.invarianten {
        aus.push(Stelle {
            regel: "T5",
            ort: ort.clone(),
            was: format!("invariant {}", i.name.text),
            nachweis: None,
        });
    }
    if let Some(s) = &t.slot {
        for f in &s.felder {
            if let SlotTyp::Typ(ty) = &f.typ {
                bereich_von_typ(ty, &ort, quelle, aus);
            }
        }
    }
}

fn format_(f: &Format, quelle: &str, aus: &mut Vec<Stelle>) {
    let ort = format!("format {}", f.name.text);
    for d in &f.felder {
        if d.reserviert {
            aus.push(Stelle {
                regel: "T9",
                ort: ort.clone(),
                was: schnitt(quelle, d.span),
                nachweis: None,
            });
        }
        bereich_von_typ(&d.typ.typ, &ort, quelle, aus);
    }
}

fn geraet(d: &Device, quelle: &str, aus: &mut Vec<Stelle>) {
    let ort = format!("device {}", d.name.text);
    for r in &d.register {
        aus.push(Stelle {
            regel: "T10",
            ort: ort.clone(),
            was: format!("reg {} class {}", r.name.text, klassenwort(r.klasse)),
            nachweis: None,
        });
        for (n, _, k) in &r.felder {
            if let Some(k) = k {
                aus.push(Stelle {
                    regel: "T10",
                    ort: ort.clone(),
                    was: format!("{}.{} class {}", r.name.text, n.text, klassenwort(*k)),
                    nachweis: None,
                });
            }
        }
        if let Some(p) = &r.requires {
            aus.push(Stelle {
                regel: "T3",
                ort: ort.clone(),
                was: format!("{} requires {}", r.name.text, schnitt(quelle, p.span)),
                nachweis: None,
            });
        }
    }
}

fn klassenwort(k: RegKlasse) -> &'static str {
    match k {
        RegKlasse::Lesen => "r",
        RegKlasse::Schreiben => "w",
        RegKlasse::LesenSchreiben => "rw",
        RegKlasse::W1c => "w1c",
        RegKlasse::Rc => "rc",
    }
}

// ---------------------------------------------------------------------------------------
// Der Rumpf -- `let`-Annotationen und die Schleifenklauseln
// ---------------------------------------------------------------------------------------

fn block(
    b: &Block,
    modul: &str,
    u: &Umgebung,
    quelle: &str,
    ort: &str,
    lokal: &mut HashMap<String, Typ>,
    aus: &mut Vec<Stelle>,
) {
    for s in &b.anweisungen {
        anweisung(s, modul, u, quelle, ort, lokal, aus);
    }
}

fn anweisung(
    s: &Stmt,
    modul: &str,
    u: &Umgebung,
    quelle: &str,
    ort: &str,
    lokal: &mut HashMap<String, Typ>,
    aus: &mut Vec<Stelle>,
) {
    match &s.art {
        StmtArt::Let(l) => {
            let rechts = typ_der_rechten(&l.wert, modul, u, lokal);
            match &l.typ {
                Some(t) => {
                    bereich_von_typ(t, ort, quelle, aus);
                    let erklaert = u.typ_von_ausdruck_decl(modul, t);
                    let text = format!("let {} : {}", l.name.text, schnitt(quelle, t.span()));
                    match rechts {
                        Some((r, woher, regel)) if r == erklaert && !r.ist_unbekannt() => {
                            aus.push(Stelle {
                                regel,
                                ort: ort.to_string(),
                                was: text,
                                nachweis: Some(woher),
                            });
                        }
                        _ => aus.push(Stelle {
                            regel: "T8",
                            ort: ort.to_string(),
                            was: text,
                            nachweis: None,
                        }),
                    }
                    lokal.insert(l.name.text.clone(), erklaert);
                }
                None => {
                    if let Some((r, _, _)) = rechts {
                        lokal.insert(l.name.text.clone(), r);
                    }
                }
            }
        }
        StmtArt::LetSonst(x) => {
            block(&x.sonst, modul, u, quelle, ort, lokal, aus);
        }
        StmtArt::Wenn(w) => {
            for (_, r) in &w.zweige {
                block(r, modul, u, quelle, ort, lokal, aus);
            }
            if let Some(r) = &w.sonst {
                block(r, modul, u, quelle, ort, lokal, aus);
            }
        }
        StmtArt::Match(m) => {
            for z in &m.zweige {
                block(&z.rumpf, modul, u, quelle, ort, lokal, aus);
            }
        }
        StmtArt::Bricht(x) => block(&x.rumpf, modul, u, quelle, ort, lokal, aus),
        StmtArt::Sperrt(x) => block(&x.rumpf, modul, u, quelle, ort, lokal, aus),
        StmtArt::Observiert(x) => block(&x.rumpf, modul, u, quelle, ort, lokal, aus),
        StmtArt::Narrow(x) => block(&x.sonst, modul, u, quelle, ort, lokal, aus),
        StmtArt::Schleife(sch) => schleife(sch, modul, u, quelle, ort, lokal, aus),
        _ => {}
    }
}

fn schleife(
    sch: &Schleife,
    modul: &str,
    u: &Umgebung,
    quelle: &str,
    ort: &str,
    lokal: &mut HashMap<String, Typ>,
    aus: &mut Vec<Stelle>,
) {
    match sch {
        Schleife::Traverse(t) => {
            // `t.mass` since 2026-09-01: the witness is a clause, not a run form. The
            // ceremony line names it the way the source spells it.
            if let Some(e) = &t.mass {
                aus.push(Stelle {
                    regel: "T6",
                    ort: ort.to_string(),
                    was: format!("decreases {}", schnitt(quelle, e.span)),
                    nachweis: None,
                });
            }
            if let Some(w) = &t.touches {
                let mut gesehen: Vec<String> = Vec::new();
                for e in &w.liste {
                    let text = format!("touches {}", e.art.text());
                    if gesehen.contains(&text) {
                        aus.push(Stelle {
                            regel: "R1",
                            ort: ort.to_string(),
                            was: text,
                            nachweis: Some("the same entry stands earlier in this list".into()),
                        });
                        continue;
                    }
                    gesehen.push(text.clone());
                    aus.push(Stelle {
                        regel: "T7",
                        ort: ort.to_string(),
                        was: text,
                        nachweis: None,
                    });
                }
            }
            block(&t.rumpf, modul, u, quelle, ort, lokal, aus);
        }
        Schleife::Retry(r) => {
            aus.push(Stelle {
                regel: "T6",
                ort: ort.to_string(),
                was: format!("up to {}", schnitt(quelle, r.schranke.span)),
                nachweis: None,
            });
            aus.push(Stelle {
                regel: "T6",
                ort: ort.to_string(),
                was: format!("on_exceeded {}", r.bei_ueberschreitung.text),
                nachweis: None,
            });
            if let Some(p) = &r.fortschritt {
                aus.push(Stelle {
                    regel: "T6",
                    ort: ort.to_string(),
                    was: format!("progress {}", p.text),
                    nachweis: None,
                });
            }
            if let Some(w) = &r.effects {
                // Eine Schleifenwirkungsliste hat keinen eigenen Graphknoten -- A4 kann hier
                // nicht greifen, und eine leere Menge sagt das, statt es zu raten.
                wirkungen(w, ort, quelle, &std::collections::BTreeSet::new(), aus);
            }
            block(&r.rumpf, modul, u, quelle, ort, lokal, aus);
        }
        Schleife::Forever(f) => {
            aus.push(Stelle {
                regel: "T6",
                ort: ort.to_string(),
                was: format!("per_pass bounded {}", schnitt(quelle, f.je_durchgang.span)),
                nachweis: None,
            });
            aus.push(Stelle {
                regel: "T6",
                ort: ort.to_string(),
                was: format!("on_exceeded {}", f.bei_ueberschreitung.text),
                nachweis: None,
            });
            if let Some(p) = &f.fortschritt {
                aus.push(Stelle {
                    regel: "T6",
                    ort: ort.to_string(),
                    was: format!("progress {}", p.text),
                    nachweis: None,
                });
            }
            wirkungen(&f.effects, ort, quelle, &std::collections::BTreeSet::new(), aus);
            block(&f.rumpf, modul, u, quelle, ort, lokal, aus);
        }
    }
}

/// **Der Typ der rechten Seite -- nachgeschlagen, nicht geraten. Und mit ihm die REGEL.**
///
/// Genau drei Formen, und jede hat eine Deklaration, auf die der Nachweis zeigt. Alles andere
/// gibt `None`, und die Annotation faellt dann nach `T8`: *was der Uebersetzer nicht ablesen
/// kann, sagt etwas, das er nicht weiss.*
///
/// **Until 2026-08-31 the rule stood in a SECOND function** (`regel_fuer_herkunft`) that made
/// the same case distinction over again and ended in `_ => "A3"`. Two registers over one
/// thing is `W7`, and these two had already drifted apart: for `let x : T = (f());`
/// `typ_der_rechten` unwrapped the parenthesis and found `A1`, while the rule function saw
/// the parenthesis and reported **`A3`** -- *evidence pointing at a declaration it never
/// read.* Measured over 499 corpus files the arm never fired; the parenthesised form is
/// writable today all the same.
///
/// Now **one** place decides both, and a parenthesis inherits the rule of its content.
fn typ_der_rechten(
    e: &Expr,
    modul: &str,
    u: &Umgebung,
    lokal: &HashMap<String, Typ>,
) -> Option<(Typ, String, &'static str)> {
    match &e.art {
        ExprArt::Klammer(x) => typ_der_rechten(x, modul, u, lokal),
        ExprArt::Ruf(r) => {
            let s = u.funktion(modul, r.path()?)?;
            let t = s.ergebnis.clone()?;
            Some((t, format!("declared result of `{}`", r.target_text()), "A1"))
        }
        ExprArt::Ort(o) => {
            let t = u.typ_von_ort(modul, o, lokal);
            if t.ist_unbekannt() {
                return None;
            }
            // `A3` is a bare name in scope, `A2` a place that reaches through a declaration
            // (`t->slots[i].f`) -- the suffixes are the difference, and the rule table says
            // so in both entries.
            let regel = if o.suffixe.is_empty() { "A3" } else { "A2" };
            Some((t, format!("declared type of `{}`", o.text()), regel))
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------------------
// Der Bericht
// ---------------------------------------------------------------------------------------

pub fn zeige(baum: &Programm, quelle: &str, datei: &str, ausfuehrlich: bool) -> String {
    let stellen = sammle(baum, quelle);
    let mut s = String::new();
    s.push_str(&format!("-- Ceremony register: {datei}\n"));
    s.push_str(
        "-- Every clause and annotation: text that describes no computation step.\n\
         -- Axis 1 is MEASURED (does this fact stand a second time?), axis 2 is DECLARED\n\
         -- (may the number fall?) -- and they are kept apart on purpose.\n\n",
    );

    if stellen.is_empty() {
        s.push_str("   no clause and no annotation in this unit\n");
        s.push_str("   And what that does NOT mean: a file with 0 ceremony is not usable,\n");
        s.push_str("   it is unmeasured -- there is nothing here that Gabbro could hold.\n");
        return s;
    }

    for k in [Klasse::Ableitbar, Klasse::Redundant, Klasse::Tragend] {
        let eigene: Vec<&Stelle> = stellen.iter().filter(|x| x.klasse() == k).collect();
        s.push_str(&format!("{:<14} {}\n", k.name(), eigene.len()));
        // **Je Regel eine Zeile.** Eine Spaltensumme ohne die Regeln darunter sagt nicht,
        // WORAUS sie besteht -- und genau daran entscheidet sich, ob sie fallen darf.
        for r in REGELN.iter().filter(|r| r.klasse == k) {
            let n = eigene.iter().filter(|x| x.regel == r.kennung).count();
            if n > 0 {
                s.push_str(&format!(
                    "   {:<4} {n:>4}   may fall: {}\n",
                    r.kennung,
                    if r.darf_sinken { "yes" } else { "NO" }
                ));
            }
        }
        if ausfuehrlich {
            for x in &eigene {
                s.push_str(&format!("     [{}] {} :: {}\n", x.regel, x.ort, x.was));
                if let Some(n) = &x.nachweis {
                    s.push_str(&format!("          proof: {n}\n"));
                }
            }
        }
    }
    s.push('\n');

    let faellt: usize = stellen.iter().filter(|x| x.darf_sinken()).count();
    s.push_str(&format!(
        "== {} sites: {faellt} may fall, {} may NOT ==\n",
        stellen.len(),
        stellen.len() - faellt
    ));
    s.push_str(
        "   `derivable` means: the same fact stands mechanically readable a second time in\n\
         \x20  this unit, and the register names where. It does NOT mean \"drop it\".\n",
    );
    s
}

/// Die Kalibriertafel -- **sie gehoert in die Ausgabe, nicht in eine Fussnote.**
pub fn tafel() -> String {
    let mut s = String::new();
    s.push_str("-- The calibration: it lives IN the tool, not in the reader's eye.\n");
    s.push_str("-- Axis 1 is measured; axis 2 is a DECISION and stands here as one.\n\n");
    for k in [Klasse::Ableitbar, Klasse::Redundant, Klasse::Tragend] {
        s.push_str(&format!("{}\n", k.name().to_uppercase()));
        for r in REGELN.iter().filter(|r| r.klasse == k) {
            s.push_str(&format!(
                "  {:<4} {}\n       may fall: {}\n       because:  {}\n",
                r.kennung,
                r.was,
                if r.darf_sinken { "yes" } else { "NO" },
                r.grund
            ));
        }
        s.push('\n');
    }
    s.push_str("NOT counted here -- and that is said, not left silent:\n");
    for (was, warum) in NICHT_GEZAEHLT {
        s.push_str(&format!("  {was}\n       because:  {warum}\n"));
    }
    s.push_str(
        "\nAnd the doctrine line, the same as for the other three counters:\n\
         what has 0 findings is not usable but UNMEASURED.\n",
    );
    s
}
