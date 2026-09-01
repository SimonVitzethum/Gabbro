//! **Pass 4 — M3: Adressräume und Zugriffsrechte am Zeiger. Der letzte ganz fehlende.**
//!
//! `SYNTAX.md` §3: `ptr<raum, rechte> Ziel`. Der Raum steht **am Typ**, nicht in einer
//! Konvention — und daraus fallen drei Pflichten, die sonst ein Mensch tragen müsste:
//!
//! 1. **Rechte.** Ein Lesen braucht `r`, ein Schreiben `w`. Ein Zeiger ohne das Recht ist
//!    kein Laufzeitfehler, sondern ein Übersetzungsfehler.
//! 2. **Die DMA-Grenze.** Ein `dma`-Zeiger erreicht Speicher, in den ein **Gerät** schreibt.
//!    Ihn wie `normal` zu lesen heisst, eine Momentaufnahme für eine Tatsache zu halten.
//! 3. **Die Platzierungsregel.** Ein Träger mit erzeugten Operationen (`ops`) darf **nicht**
//!    in einem `dma`-erreichbaren Raum liegen — sonst umgeht das Gerät jede Grammatik
//!    (`TODO.md`, Durchstich 2 von `by ops`).
//!
//! ## Was dieser Pass NICHT ist
//!
//! **Er ist kein Alias-Analysator.** Zwei `ptr<normal, rw>` auf dasselbe Objekt bleiben
//! ununterscheidbar — dafür steht `own` und die Auflösung aus A1 (*Kernzustand braucht
//! keinen Zeiger*). *Das steht hier, damit niemand die Deckung grösser liest, als sie ist.*
//!
//! ## Die Grobheit hat eine Richtung (W9)
//!
//! Wo der Zeigertyp eines Ortes **nicht auflösbar** ist (fremdes Modul, unbekannter Typ),
//! sagt der Pass **nichts** — statt anzunehmen, es sei `normal`. Eine Annahme wäre hier in
//! die **unsichere** Richtung grob: sie liesse einen `mmio`-Zugriff als gewöhnlichen durch.

use gabbro_syntax::ast::*;
use gabbro_syntax::diag::{Absage, Absagen};
use gabbro_syntax::span::Span;
use std::collections::BTreeMap;

/// Was über einen Zeigerparameter bekannt ist.
#[derive(Clone)]
struct Zeiger {
    raum: Raum,
    rechte: Vec<Recht>,
}

impl Zeiger {
    fn darf_lesen(&self) -> bool {
        self.rechte.iter().any(|r| {
            matches!(
                r,
                Recht::Lesen | Recht::LesenSchreiben | Recht::Eigen(_)
            )
        })
    }
    fn darf_schreiben(&self) -> bool {
        self.rechte
            .iter()
            .any(|r| matches!(r, Recht::Schreiben | Recht::LesenSchreiben | Recht::Eigen(_)))
    }
}

fn raumname(r: &Raum) -> String {
    match r {
        Raum::Normal => "normal".into(),
        Raum::Mmio => "mmio".into(),
        Raum::Dma => "dma".into(),
        Raum::Code => "code".into(),
        Raum::Boot => "boot".into(),
        Raum::Port => "port".into(),
        Raum::Benannt(i) => i.text.clone(),
    }
}

/// **`R004` — zweimal `own` auf denselben Gegenstand.**
///
/// `own` war bis 2026-08-19 ein Synonym für `rw`: drei Lesestellen, alle drei behandeln
/// `Recht::Eigen` genau wie `Recht::LesenSchreiben`. Ein Ruf `zwei(q, q)` auf zwei
/// `own`-Parameter ging mit **0 Fehlern** durch — *zwei Besitzer derselben Region*, und
/// `m2.rs`s Modulkopf führt genau diesen Satz als das, wogegen die Linearität steht.
///
/// **Was diese Regel NICHT tut: eine Aliasanalyse.** Zwei verschiedene Namen, die auf
/// dasselbe zeigen, bleiben ununterscheidbar — das ist M3s offener Rest und eine
/// Sprachentscheidung (`own` als Freigabeoperation oder als Signaturvermerk). Hier steht
/// die Hälfte, die **keine Entscheidung braucht**: derselbe Ort, syntaktisch, an zwei
/// `own`-Stellen desselben Rufs. *Unter jeder Lesart von `own` ist das ein Widerspruch.*
///
/// > **Die erste Beissstelle von `own`** — bis hierher war es eine Klausel ohne Leser,
/// > dieselbe Klasse wie `obermenge`, `gates`, `mirrors` und `counterprobe` vor «K5».
fn eigen_doppelt(baum: &Programm, absagen: &mut Absagen) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    // Welche Parameter einer Funktion tragen `own`? Der Schlüssel ist qualifiziert.
    let mut eigen: BTreeMap<String, Vec<bool>> = BTreeMap::new();
    // **`R007`, 2026-08-24 -- die zweite Markierung: SCHREIBBAR und nicht `own`.**
    //
    // `messung/RACE.md` lists four race forms nothing carries at all. `A1` is the one that
    // needs no alias analysis: *two pointer arguments that are SYNTACTICALLY the same place*.
    // `gabbro alias` has counted it since 2026-08-21 (`S3`, one site, writable) -- and no
    // pass refused it. *A measurement without a rule is the state a rule grows out of.*
    let mut schreibend: BTreeMap<String, Vec<bool>> = BTreeMap::new();
    let mut raeume: BTreeMap<String, Vec<Option<Raum>>> = BTreeMap::new();
    let mut parameternamen: BTreeMap<String, Vec<String>> = BTreeMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        if let ItemArt::Funktion(f) = &item.art {
            let voll = crate::umgebung::qualifiziere(modul, &f.name.text);
            eigen.insert(
                voll.clone(),
                f.parameter
                    .iter()
                    .map(|p| match &p.typ {
                        TypExpr::Zeiger(z) => {
                            z.rechte.iter().any(|r| matches!(r, Recht::Eigen(_)))
                        }
                        _ => false,
                    })
                    .collect(),
            );
            // **`R008`, 2026-08-24 -- der ADRESSRAUM je Zeigerparameter.**
            //
            // `Typ::Zeiger(Box<Typ>)` carries no space at all: the semantic type drops
            // `Raum` at construction, and that is why nothing could ever check it. The
            // DECLARATION still has it (`TypExpr::Zeiger(z).raum`), so the comparison
            // happens here, where R004 and R007 already read declarations.
            raeume.insert(
                voll.clone(),
                f.parameter
                    .iter()
                    .map(|p| match &p.typ {
                        TypExpr::Zeiger(z) => Some(z.raum.clone()),
                        _ => None,
                    })
                    .collect(),
            );
            parameternamen.insert(
                voll.clone(),
                f.parameter.iter().map(|p| p.name.text.clone()).collect(),
            );
            schreibend.insert(
                voll,
                f.parameter
                    .iter()
                    .map(|p| match &p.typ {
                        // `own` stays out: `R004` covers it, and two rules over one site
                        // would be two reports over one finding.
                        TypExpr::Zeiger(z) => {
                            !z.rechte.iter().any(|r| matches!(r, Recht::Eigen(_)))
                                && z.rechte.iter().any(|r| matches!(r, Recht::Schreiben | Recht::LesenSchreiben))
                        }
                        _ => false,
                    })
                    .collect(),
            );
        }
    });
    let g = crate::aufrufgraph::erhebe_mit(baum, &u);
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let Some(k) = g.knoten.get(&crate::umgebung::qualifiziere(modul, &f.name.text)) else {
            return;
        };
        let eigene = crate::umgebung::qualifiziere(modul, &f.name.text);
        for (ziel, args) in &k.rufe {
            // **`R008` -- the address space must MATCH.**
            //
            // `ptr<mmio, rw> T` and `ptr<normal, rw> T` are different memories: one is
            // volatile and device-mapped, the other is not. Until today they were
            // interchangeable at a call, with zero errors -- and «B33» rests on knowing that
            // a place IS volatile, so laundering the space through a call undermines that
            // reasoning too.
            //
            // **Only a bare parameter name counts as an argument here**, and that is an
            // UNDER-approximation stated as one: a field, a local, a return value carries no
            // declared space that this pass could read. *`Typ` drops `Raum`; the declaration
            // is the only place it survives.*
            if let (Some(zraeume), Some(eigene_raeume), Some(eigene_namen)) = (
                raeume.get(ziel),
                raeume.get(&eigene),
                parameternamen.get(&eigene),
            ) {
                for (i, a) in args.iter().enumerate() {
                    let (Some(ort), Some(Some(soll))) = (a, zraeume.get(i)) else {
                        continue;
                    };
                    let Some(j) = eigene_namen.iter().position(|n| n == ort) else {
                        continue;
                    };
                    let Some(Some(ist)) = eigene_raeume.get(j) else {
                        continue;
                    };
                    if ist != soll {
                        absagen.schiebe(
                            Absage::fehler(
                                "R008",
                                f.name.span,
                                format!(
                                    "`{}` passes `{ort}` in space `{}` to a parameter of \
                                     `{}` declared `{}`",
                                    f.name.text,
                                    raumname(ist),
                                    crate::umgebung::kurzname(ziel),
                                    raumname(soll)
                                ),
                            )
                            .mit_notiz(
                                "the address space is part of what a pointer IS -- `mmio` is \
                                 volatile and device-mapped, `normal` is not, and the \
                                 emitter lowers them differently",
                            )
                            .mit_notiz(
                                "only a bare parameter name is compared: a field, a local or \
                                 a return value carries no declared space this pass can read",
                            ),
                        );
                    }
                }
            }
            // **`R007` -- two WRITABLE pointer arguments at the same place.**
            //
            // Compared is the PLACE, not the root: `f(p->a, p->b)` are two distinct fields
            // and no aliasing hazard. *The stricter reading would be the root, and it would
            // be too strong* -- it would fall at every call passing two fields of one
            // record.
            if let Some(smarken) = schreibend.get(ziel) {
                // **A name of its own, and that is not taste:** were it named like `R004`'s,
                // the anchor `zweimal-own-egal` would be AMBIGUOUS -- a mutation hitting two
                // sites measures neither. *`--anker` said so at once.*
                let mut geschriebene: Vec<&String> = Vec::new();
                for (i, a) in args.iter().enumerate() {
                    if !smarken.get(i).copied().unwrap_or(false) {
                        continue;
                    }
                    let Some(ort) = a else { continue };
                    if geschriebene.iter().any(|g| *g == ort) {
                        absagen.schiebe(
                            Absage::fehler(
                                "R007",
                                f.name.span,
                                format!(
                                    "`{}` passes `{ort}` to two writable pointer parameters \
                                     of `{}`",
                                    f.name.text,
                                    crate::umgebung::kurzname(ziel)
                                ),
                            )
                            .mit_notiz(
                                "the callee computes with two names it may assume are \
                                 distinct -- a write through one silently undoes the other",
                            )
                            .mit_notiz(
                                "this is the SYNTACTIC half of the alias question, and the \
                                 only half decidable without an alias analysis: two \
                                 DIFFERENT names for one object stay indistinguishable \
                                 (`messung/RACE.md`, A2/A3)",
                            ),
                        );
                        break;
                    }
                    geschriebene.push(ort);
                }
            }
            let Some(marken) = eigen.get(ziel) else {
                continue;
            };
            // Nur die Argumente, die auf einem `own`-Parameter landen und ein ORT sind.
            let mut gesehen: Vec<&String> = Vec::new();
            for (i, a) in args.iter().enumerate() {
                if !marken.get(i).copied().unwrap_or(false) {
                    continue;
                }
                let Some(ort) = a else { continue };
                if gesehen.iter().any(|g| *g == ort) {
                    absagen.schiebe(
                        Absage::fehler(
                            "R004",
                            f.name.span,
                            format!(
                                "`{}` passes `{ort}` to two `own` parameters of `{}`",
                                f.name.text,
                                crate::umgebung::kurzname(ziel)
                            ),
                        )
                        .mit_notiz(
                            "`own` says: this is the one owner -- two of them on the same \
                             object is two owners of the same region",
                        )
                        .mit_notiz(
                            "this is the syntactic half; two DIFFERENT names pointing at the \
                             same object stay indistinguishable (M3's open alias question)",
                        ),
                    );
                    break;
                }
                gesehen.push(ort);
            }
        }
    });
}

/// **Was eine Registerklasse ERLAUBT** -- und die Lesart steht hier, weil sie sonst nirgends
/// stand.
///
/// `w1c` und `rc` sind die zwei Klassen, bei denen das LESEN oder das SCHREIBEN eine
/// Nebenwirkung hat, nicht ein Verbot: ein RW1C-Register liest man gewoehnlich und loescht
/// ein Bit, indem man eine Eins hineinschreibt; ein RC-Register loescht sich beim Lesen und
/// nimmt kein Schreiben an. *Beide sind damit lesbar; nur `w` ist es nicht.*
pub(crate) fn darf_lesen_reg(k: RegKlasse) -> bool {
    !matches!(k, RegKlasse::Schreiben)
}

pub(crate) fn darf_schreiben_reg(k: RegKlasse) -> bool {
    matches!(
        k,
        RegKlasse::Schreiben | RegKlasse::LesenSchreiben | RegKlasse::W1c
    )
}

pub(crate) fn klassenwort(k: RegKlasse) -> &'static str {
    match k {
        RegKlasse::Lesen => "r",
        RegKlasse::Schreiben => "w",
        RegKlasse::LesenSchreiben => "rw",
        RegKlasse::W1c => "w1c",
        RegKlasse::Rc => "rc",
    }
}

#[derive(Clone)]
pub(crate) struct RegInfo {
    pub(crate) klasse: RegKlasse,
    /// **«B23»: die Klasse JE FELD.** `FSTS` ist gemischt -- 7:0 sind RW1C, 15:8 (FRI) sind
    /// nur lesbar, und FRI ist die Stelle, an der der Treiber den Eintrag ueberhaupt findet.
    /// Ein Feld ohne eigenes Wort erbt die Klasse seines Registers.
    pub(crate) felder: BTreeMap<String, RegKlasse>,
    /// **«B18»: die Klasse JE PHASE**, `class rw in setup, r in live`. Empty means the
    /// register carries one class for all time -- then `registerklassen` below decides it.
    /// **Non-empty means this pass says NOTHING about the register**: the stage is what
    /// decides, and the stage lives in `phasen.rs`. *Two registers over one site would be
    /// W7; the reading happens where the stage is known.*
    pub(crate) phasen: Vec<(RegKlasse, Ident)>,
    /// **«B26»: the FALSIFIER of the `requires`** -- `(reason, case)`, present exactly where
    /// the declaration carries `requires … else R::C`. Then the READ is fallible (`R011`).
    pub(crate) fehlbar: Option<(String, String)>,
}

/// **The register table per device** -- register name to class, fields and phase list.
///
/// It stands here and not in `phasen.rs` because `m3.rs` is the ONE register over register
/// classes. `phasen.rs` calls it for «B18»; **a second table would be W7.**
pub(crate) fn geraetetabelle(baum: &Programm) -> BTreeMap<String, BTreeMap<String, RegInfo>> {
    let mut geraete: BTreeMap<String, BTreeMap<String, RegInfo>> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Device(d) = &item.art else {
            return;
        };
        let mut regs: BTreeMap<String, RegInfo> = BTreeMap::new();
        let nimm = |r: &RegDecl, regs: &mut BTreeMap<String, RegInfo>| {
            let felder = r
                .felder
                .iter()
                .map(|(n, _, k)| (n.text.clone(), k.unwrap_or(r.klasse)))
                .collect();
            regs.insert(
                r.name.text.clone(),
                RegInfo {
                    klasse: r.klasse,
                    felder,
                    phasen: r.phasen.clone(),
                    fehlbar: r
                        .requires_grund
                        .as_ref()
                        .map(|(g, f)| (g.text.clone(), f.text.clone())),
                },
            );
        };
        for r in &d.register {
            nimm(r, &mut regs);
        }
        // Ein `bank`-Register wird ueber `d.BANK[i].REG` erreicht und traegt dieselbe Klasse.
        for b in &d.baenke {
            for r in &b.register {
                nimm(r, &mut regs);
            }
        }
        geraete.insert(d.name.text.clone(), regs);
    });
    geraete
}

/// **Welcher lokale Name traegt welches Geraet?** Parameter -- als Zeiger wie als Wert --
/// und die `let`-gebundenen Griffe (`let v = Vtd(basis);`, `beispiele/09`).
pub(crate) fn griffe_von(
    f: &FnDecl,
    geraete: &BTreeMap<String, BTreeMap<String, RegInfo>>,
) -> BTreeMap<String, String> {
    let mut griffe: BTreeMap<String, String> = BTreeMap::new();
    for p in &f.parameter {
        let ziel = match &p.typ {
            TypExpr::Pfad(pf) => pf.teile.last(),
            TypExpr::Zeiger(z) => match &z.ziel {
                TypExpr::Pfad(pf) => pf.teile.last(),
                _ => None,
            },
            _ => None,
        };
        if let Some(n) = ziel {
            if geraete.contains_key(&n.text) {
                griffe.insert(p.name.text.clone(), n.text.clone());
            }
        }
    }
    if let FnRumpf::Block(b) = &f.rumpf {
        sammle_griffe(b, geraete, &mut griffe);
    }
    griffe
}

/// **`class` an einem Register war eine Zusage, die kein Pass eingeloest hat** (2026-08-20).
///
/// `PFLICHTEN.md` buchte *„a `class r` register is never written, a `class w` never read"* als
/// erledigt **durch `R002`/`R003`** -- und die beiden pruefen ZEIGERRECHTE, nicht
/// Registerklassen. Die Notiz an `R003` sagte den Satz sogar (*„`class w` on a register means
/// the same"*), und der Code tat ihn nicht:
///
/// ```gabbro
/// reg NUR_W : u32 @0x00 class w fields { A @0 }
/// return d.NUR_W.A;                       -- 0 Fehler, bis heute
/// ```
///
/// *Dieselbe Klasse wie «B33» eine Stunde vorher: der Ordner beschrieb die Regel, der Pruefer
/// tat sie nicht.* **Eine Buchung, die auf eine Regel zeigt, die anderswohin sieht, ist
/// schlimmer als eine offene Zeile -- sie sieht geschlossen aus.**
fn registerklassen(baum: &Programm, absagen: &mut Absagen) {
    let geraete = geraetetabelle(baum);
    if geraete.is_empty() {
        return;
    }

    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let griffe = griffe_von(f, &geraete);
        if griffe.is_empty() {
            return;
        }
        klassenblock(b, &geraete, &griffe, absagen);
    });
}

fn sammle_griffe(
    b: &Block,
    geraete: &BTreeMap<String, BTreeMap<String, RegInfo>>,
    griffe: &mut BTreeMap<String, String>,
) {
    for s in &b.anweisungen {
        if let StmtArt::Let(l) = &s.art {
            if let ExprArt::Ruf(r) = &l.wert.art {
                if let Some(n) = r.path().and_then(|p| p.teile.last()) {
                    if geraete.contains_key(&n.text) {
                        griffe.insert(l.name.text.clone(), n.text.clone());
                    }
                }
            }
        }
        for k in crate::unterbloecke(s) {
            sammle_griffe(k, geraete, griffe);
        }
    }
}

fn klassenblock(
    b: &Block,
    geraete: &BTreeMap<String, BTreeMap<String, RegInfo>>,
    griffe: &BTreeMap<String, String>,
    absagen: &mut Absagen,
) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => {
                klassenpruefung(&z.ziel, s.span, false, geraete, griffe, absagen);
                // `X |= 1` ist ein Lesen UND ein Schreiben; ein `class w` traegt es nicht.
                if !matches!(z.op, ZuwOp::Setzt) {
                    klassenpruefung(&z.ziel, s.span, true, geraete, griffe, absagen);
                }
                rmw_pruefung(&z.ziel, s.span, geraete, griffe, absagen);
            }
            StmtArt::Publish(p) => {
                klassenpruefung(&p.ziel, s.span, false, geraete, griffe, absagen)
            }
            _ => {}
        }
        for e in crate::eigene_ausdruecke(s) {
            for o in crate::alle_orte(e) {
                klassenpruefung(o, s.span, true, geraete, griffe, absagen);
            }
        }
        for k in crate::unterbloecke(s) {
            klassenblock(k, geraete, griffe, absagen);
        }
    }
}

/// **Which register does this place address?** `d.REG`, `d.REG.FELD` or
/// `d.BANK[i].REG[.FELD]`.
///
/// It stands here because `m3.rs` is the ONE register over register accesses; `phasen.rs`
/// calls it for «B18». *A second resolution would be W7 -- and the two could drift apart
/// without anybody noticing.*
pub(crate) struct Treffer<'a> {
    pub(crate) reg: &'a Ident,
    pub(crate) feld: Option<&'a Ident>,
    pub(crate) info: &'a RegInfo,
}

pub(crate) fn ort_register<'a>(
    o: &'a Ort,
    geraete: &'a BTreeMap<String, BTreeMap<String, RegInfo>>,
    griffe: &BTreeMap<String, String>,
) -> Option<Treffer<'a>> {
    let dev = griffe.get(&o.basis.text)?; // kein Geraetegriff -- der Pass sagt nichts (W9)
    let regs = geraete.get(dev)?;
    // Die Namensfolge ohne Indizes: `[BANK, REG, FELD]` oder `[REG, FELD]` oder `[REG]`.
    let namen: Vec<&Ident> = o
        .suffixe
        .iter()
        .filter_map(|x| match x {
            OrtSuffix::Feld(i) | OrtSuffix::Ueber(i) => Some(i),
            OrtSuffix::Index(_) => None,
        })
        .collect();
    // Der erste Name, den dieses Geraet als Register kennt -- so faellt ein Bankname weg,
    // ohne dass der Pass die Bankliste ein zweites Mal fuehren muss (W7).
    let k = namen.iter().position(|n| regs.contains_key(&n.text))?;
    let reg = namen[k];
    let info = &regs[&reg.text];
    let feld = namen.get(k + 1).copied();
    Some(Treffer { reg, feld, info })
}

/// Ein Zugriff auf `d.REG`, `d.REG.FELD` oder `d.BANK[i].REG[.FELD]` -- gegen die Klasse.
fn klassenpruefung(
    o: &Ort,
    span: Span,
    lesend: bool,
    geraete: &BTreeMap<String, BTreeMap<String, RegInfo>>,
    griffe: &BTreeMap<String, String>,
    absagen: &mut Absagen,
) {
    let Some(t) = ort_register(o, geraete, griffe) else {
        return;
    };
    let (reg, info, feld) = (t.reg, t.info, t.feld);
    // **«B18»: a phase-classed register is NOT decided by this walk.** Which class holds
    // depends on the stage of the mark, and the stage is walked in `phasen.rs`, which calls
    // `phasenzugriff` below. *To guess here would be to take the first stage for all time.*
    if !info.phasen.is_empty() {
        return;
    }
    let (klasse, wo) = match feld.and_then(|f| info.felder.get(&f.text).map(|k| (*k, Some(f)))) {
        Some((k, f)) => (k, f),
        None => (info.klasse, None),
    };
    let erlaubt = if lesend {
        darf_lesen_reg(klasse)
    } else {
        darf_schreiben_reg(klasse)
    };
    if erlaubt {
        return;
    }
    let stelle = match wo {
        Some(f) => format!("{}.{}", reg.text, f.text),
        None => reg.text.clone(),
    };
    let (code, wort, tat) = if lesend {
        ("R005", "read", "readable")
    } else {
        ("R006", "written", "writable")
    };
    let mut a = Absage::fehler(
        code,
        span,
        format!(
            "`{}` is {wort}, but `{stelle}` is `class {}`",
            o.text(),
            klassenwort(klasse)
        ),
    )
    .mit_notiz(format!(
        "a `class {}` register is not {tat} -- that is a statement about the HARDWARE, and \
         the compiler is the only place it can be held",
        klassenwort(klasse)
    ));
    if wo.is_some() && klasse != info.klasse {
        a = a.mit_notiz(format!(
            "the field carries its own class; the register `{}` is `class {}` (\u{ab}B23\u{bb})",
            reg.text,
            klassenwort(info.klasse)
        ));
    }
    absagen.schiebe(a);
}

/// **`R012` -- a read-modify-write on a word whose READ or WRITE has a side effect.**
///
/// Writing one bit field means writing the whole word, so the emitter reads it first and puts
/// the untouched bits back. **That is only harmless where putting a bit back is a no-op**, and
/// `w1c` and `rc` are exactly the two classes where it is not:
///
/// * `w1c` -- writing a one CLEARS. The read picks up every error bit currently set, the
///   write-back sets those ones again, and each of them clears. *Acknowledging one bit
///   silently acknowledges every bit that was standing.*
/// * `rc` -- reading CLEARS. The read of the read-modify-write is itself the loss.
///
/// **And this is not a rule about the FIELD, it is a rule about the WORD.** `beispiele/45`
/// declares `FSTS` as `class rw` with two `w1c` fields inside it; the register class was the
/// only thing the emitter looked at, so the word passed as ordinary and the generated
/// acknowledgement of `PFO` cleared `PPF` along with it -- measured, shipped, and green in
/// every pass:
///
/// ```c
/// uint32_t _v = (*(volatile uint32_t *)(v->basis + 52));
/// (*(volatile uint32_t *)(v->basis + 52)) =
///     (uint32_t)((_v & (uint32_t)~(uint32_t)1u) | ((uint32_t)(1) << 0u & (uint32_t)1u));
/// ```
///
/// > That is why `w1c` moving out of the *type* words and in beside `class` is not
/// > housekeeping. **A write-1-to-clear register is not a number of another type, it is an
/// > access BEHAVIOUR** -- and as long as it was filed as a type, a read-modify-write over it
/// > was type-correct and wrong.
///
/// **The exits both exist and neither is `extern`:** the whole-word write `v.FSTS = 1;`
/// lowers to a single volatile store with no read, and `transition` writes the whole word
/// too -- with `mirrors` it reads the MIRROR, a different register, never the target.
///
/// *Not `R006`:* that one says the place is not writable. A `w1c` field IS writable
/// (`darf_schreiben_reg` says so, correctly). What is refused here is one particular WAY of
/// writing it.
fn rmw_pruefung(
    o: &Ort,
    span: Span,
    geraete: &BTreeMap<String, BTreeMap<String, RegInfo>>,
    griffe: &BTreeMap<String, String>,
    absagen: &mut Absagen,
) {
    let Some(t) = ort_register(o, geraete, griffe) else {
        return;
    };
    // A whole-word write is not a read-modify-write, and it is the answer to this refusal.
    if t.feld.is_none() {
        return;
    }
    // **A phase-classed register is not decided here**, exactly as in `klassenpruefung`:
    // which class holds depends on the stage, and the stage is walked in `phasen.rs`.
    if !t.info.phasen.is_empty() {
        return;
    }
    // The whole word, not the addressed field: the read picks up every bit of it.
    let heikel = |k: &RegKlasse| matches!(k, RegKlasse::W1c | RegKlasse::Rc);
    let schuldig = if heikel(&t.info.klasse) {
        Some((t.reg.text.clone(), t.info.klasse))
    } else {
        t.info
            .felder
            .iter()
            .find(|(_, k)| heikel(k))
            .map(|(n, k)| (format!("{}.{n}", t.reg.text), *k))
    };
    let Some((stelle, klasse)) = schuldig else { return };
    let wort = klassenwort(klasse);
    let wirkung = if klasse == RegKlasse::W1c {
        "writing a one CLEARS, so the read-modify-write puts back every bit that was \
         standing and clears it"
    } else {
        "reading CLEARS, so the read of the read-modify-write is itself the loss"
    };
    absagen.schiebe(
        Absage::fehler(
            "R012",
            span,
            format!(
                "`{}` writes ONE BIT of a word that carries `class {wort}` at `{stelle}`",
                o.text()
            ),
        )
        .mit_notiz(format!("`{wort}`: {wirkung}"))
        .mit_notiz(format!(
            "writing a bit field is a read-modify-write on the WHOLE word `{}`, and the \
             class of the word decides, not the class of the field",
            t.reg.text
        ))
        .mit_notiz(
            "the whole-word write `d.REG = <bits>;` emits a single store without a read, and \
             `transition` writes the whole word as well",
        ),
    );
}

pub fn pass(baum: &Programm, absagen: &mut Absagen) {
    registerklassen(baum, absagen);
    // «B26»: the declaration first, then the read -- an `else` that names nothing makes
    // every statement about an access to it worthless.
    geraeteversprechen(baum, absagen);
    fehlbare_lesungen(baum, absagen);
    eigen_doppelt(baum, absagen);

    // **Die Platzierungsregel zuerst** -- sie betrifft Deklarationen, nicht Rümpfe.
    let mut mit_ops: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Tabelle(t) = &item.art {
            if !t.ops.is_empty() {
                mit_ops.push(t.name.text.clone());
            }
        }
    });

    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let mut zeiger: BTreeMap<String, Zeiger> = BTreeMap::new();
        for p in &f.parameter {
            if let TypExpr::Zeiger(z) = &p.typ {
                // **Platzierungsregel:** ein `ops`-Traeger in einem `dma`-Raum umgeht die
                // Grammatik -- das Geraet schreibt an den erzeugten Operationen vorbei.
                if z.raum == Raum::Dma {
                    if let TypExpr::Pfad(pf) = &z.ziel {
                        if let Some(n) = pf.teile.last() {
                            if mit_ops.contains(&n.text) {
                                absagen.schiebe(
                                    Absage::fehler(
                                        "R001",
                                        p.name.span,
                                        format!(
                                            "`{}` points into the `dma` space at `{}`, and that \
                                             table declares `ops`",
                                            p.name.text, n.text
                                        ),
                                    )
                                    .mit_notiz(
                                        "the K condition requires that ALL write sites of the \
                                         carrier are generated -- a device writes past any \
                                         grammar there is",
                                    )
                                    .mit_notiz(
                                        "the honest form is a placement rule, like the one for \
                                         the GDT: a `by ops` carrier lies in no \
                                         `dma`-reachable region",
                                    ),
                                );
                            }
                        }
                    }
                }
                zeiger.insert(
                    p.name.text.clone(),
                    Zeiger {
                        raum: z.raum.clone(),
                        rechte: z.rechte.clone(),
                    },
                );
            }
        }
        if zeiger.is_empty() {
            return;
        }
        if let FnRumpf::Block(b) = &f.rumpf {
            block(b, &zeiger, absagen);
        }
    });
}

/// **Der Abstieg geht über `crate::unterbloecke`** — erschöpfend über `StmtArt`, ohne
/// `_`-Zweig. Vorher fehlten `observes` und `exchange`: ein Lesen über einen `ptr<…, r>` in
/// einem RCU-Leseblock oder in einem `update`-Rumpf war für die Rechteprüfung unsichtbar.
fn block(b: &Block, zeiger: &BTreeMap<String, Zeiger>, absagen: &mut Absagen) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Zuweisung(z) => schreibt(&z.ziel, s.span, zeiger, absagen),
            StmtArt::Publish(p) => schreibt(&p.ziel, s.span, zeiger, absagen),
            _ => {}
        }
        for e in crate::eigene_ausdruecke(s) {
            liest_expr(e, s.span, zeiger, absagen);
        }
        for k in crate::unterbloecke(s) {
            block(k, zeiger, absagen);
        }
    }
}

fn schreibt(o: &Ort, span: Span, zeiger: &BTreeMap<String, Zeiger>, absagen: &mut Absagen) {
    let Some(z) = zeiger.get(&o.basis.text) else {
        return; // nicht aufloesbar -- der Pass sagt nichts (W9)
    };
    if !z.darf_schreiben() {
        absagen.schiebe(
            Absage::fehler(
                "R002",
                span,
                format!(
                    "`{}` is written, but the pointer carries no `w`",
                    o.text()
                ),
            )
            .mit_notiz(format!(
                "`{}` is declared `ptr<{}, …>` without write permission -- that is a \
                 compile error, not a runtime check",
                o.basis.text,
                raumname(&z.raum)
            )),
        );
    }
}

fn liest(o: &Ort, span: Span, zeiger: &BTreeMap<String, Zeiger>, absagen: &mut Absagen) {
    let Some(z) = zeiger.get(&o.basis.text) else {
        return;
    };
    if !z.darf_lesen() {
        absagen.schiebe(
            Absage::fehler(
                "R003",
                span,
                format!("`{}` is read, but the pointer carries no `r`", o.text()),
            )
            .mit_notiz("a `w` pointer is not readable -- `class w` on a register means the same"),
        );
    }
}

/// Ueber `crate::alle_orte` -- ein Lesen in Indexposition ist ein Lesen (2026-08-20).
fn liest_expr(e: &Expr, span: Span, zeiger: &BTreeMap<String, Zeiger>, absagen: &mut Absagen) {
    for o in crate::alle_orte(e) {
        liest(o, span, zeiger, absagen);
    }
}

// =======================================================================================
// «B18» -- the register class PER PHASE. 2026-08-28.
//
// `dokumente/PFLICHTEN.md` carried two corpus sites, and the second one is load-bearing:
//
//     impl fn heimlich(q : ptr<dma, rw> Virtq) effects { writes q } costs <= 4 ops
//         { q.USED_IDX = 7; }        ->  0 errors, measured 2026-08-26
//
// **A linear mark is a permission nobody is obliged to hold.** `L101` (issued in `m2.rs`,
// which is where linearity lives) holds that whoever
// HAS the mark passes it on; it does not hold that whoever WRITES must have it. The
// fragment writes the closing form itself, as a comment, because it could not be written:
//
//     reg USED_IDX : u16 wrapping @0x202 class rw in setup, r in live
//
// And the line under it says why a fixed class would be wrong: **`class r` alone would
// forbid the very zeroing that disarms the paid-for trap of a reused ring.**
//
// The decision and both rejected forms stand in `messung/PHASENKLASSE.md`. The half that
// closes the measured site is this one:
//
// > **Where the stage is not determined, what holds is what EVERY stage permits.**
//
// That forces nobody to carry the mark -- it only says what follows without it. For
// `class rw in setup, r in live` the intersection is `r`, and `heimlich` falls at `R006` --
// issued in `phasenzugriff` at the foot of this same `m3.rs`.
// =======================================================================================

/// Which order do these stage names belong to? **Exactly one, or the declaration is wrong.**
pub(crate) fn ordnung_der_phasen<'a>(
    phasen: &[(RegKlasse, Ident)],
    ordnungen: &'a BTreeMap<String, Vec<String>>,
) -> Vec<&'a String> {
    ordnungen
        .iter()
        .filter(|(_, stufen)| phasen.iter().all(|(_, s)| stufen.contains(&s.text)))
        .map(|(n, _)| n)
        .collect()
}

/// The class that holds in one stage -- `None` if the list does not name that stage.
fn klasse_in_stufe(phasen: &[(RegKlasse, Ident)], stufe: &str) -> Option<RegKlasse> {
    phasen.iter().find(|(_, s)| s.text == stufe).map(|(k, _)| *k)
}

/// **`R009` -- the phase list at a register declaration.**
///
/// Four ways to get it wrong, one identifier: the stages belong to no declared `order`, or
/// to more than one, or one is named twice, or one of the order's stages is missing.
/// **Completeness is a duty and not pedantry:** an unnamed stage would be a silent hole in
/// a rule whose whole purpose is to close one. *From strict one can loosen, never the other
/// way* (K11.1).
///
/// The fifth is a shape and not an omission: a phase-classed register whose FIELDS carry
/// their own `class` would mean two class systems over one word. «B23» stands per field,
/// «B18» stands per phase, and the two do not compose today.
pub(crate) fn phasendeklarationen(
    baum: &Programm,
    ordnungen: &BTreeMap<String, Vec<String>>,
    absagen: &mut Absagen,
) {
    let pruefe = |r: &RegDecl, absagen: &mut Absagen| {
        if r.phasen.is_empty() {
            return;
        }
        for (n, _, k) in &r.felder {
            if k.is_some() {
                absagen.schiebe(
                    Absage::fehler(
                        "R009",
                        n.span,
                        format!(
                            "`{}` carries a class per phase, and the field `{}` carries one \
                             of its own",
                            r.name.text, n.text
                        ),
                    )
                    .mit_notiz(
                        "«B23» stands per field, «B18» stands per phase -- one word cannot \
                         carry both class systems at once",
                    ),
                );
            }
        }
        let kandidaten = ordnung_der_phasen(&r.phasen, ordnungen);
        match kandidaten.len() {
            0 => {
                let bekannt = if ordnungen.is_empty() {
                    "no `linear ghost type … order { … }` is declared in this unit".to_string()
                } else {
                    format!(
                        "the declared orders are: {}",
                        ordnungen
                            .iter()
                            .map(|(n, s)| format!("{n} ({})", s.join(", ")))
                            .collect::<Vec<_>>()
                            .join("; ")
                    )
                };
                absagen.schiebe(
                    Absage::fehler(
                        "R009",
                        r.span,
                        format!(
                            "`{}` names the stages {} -- no declared `order` has them all",
                            r.name.text,
                            r.phasen
                                .iter()
                                .map(|(_, s)| s.text.clone())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    )
                    .mit_notiz(bekannt)
                    .mit_notiz(
                        "a phase at a register is a stage OF SOMETHING -- the carrier is the \
                         same linear ghost mark that `advances` steps",
                    ),
                );
            }
            1 => {
                let ordnung = kandidaten[0];
                let stufen = &ordnungen[ordnung];
                for (i, (_, s)) in r.phasen.iter().enumerate() {
                    if r.phasen[..i].iter().any(|(_, t)| t.text == s.text) {
                        absagen.schiebe(
                            Absage::fehler(
                                "R009",
                                s.span,
                                format!("`{}` names the stage `{}` twice", r.name.text, s.text),
                            )
                            .mit_notiz("one stage, one class -- otherwise the order decides"),
                        );
                    }
                }
                let fehlend: Vec<&String> = stufen
                    .iter()
                    .filter(|s| !r.phasen.iter().any(|(_, t)| t.text == **s))
                    .collect();
                if !fehlend.is_empty() {
                    absagen.schiebe(
                        Absage::fehler(
                            "R009",
                            r.span,
                            format!(
                                "`{}` says nothing about the stage(s) {} of `{}`",
                                r.name.text,
                                fehlend
                                    .iter()
                                    .map(|s| format!("`{s}`"))
                                    .collect::<Vec<_>>()
                                    .join(", "),
                                ordnung
                            ),
                        )
                        .mit_notiz(format!("the order is: {}", stufen.join(", ")))
                        .mit_notiz(
                            "every stage must be named -- an unnamed one would be a silent \
                             hole in the rule that exists to close it",
                        ),
                    );
                }
            }
            _ => {
                absagen.schiebe(
                    Absage::fehler(
                        "R009",
                        r.span,
                        format!(
                            "the stages of `{}` fit more than one `order`: {}",
                            r.name.text,
                            kandidaten
                                .iter()
                                .map(|o| format!("`{o}`"))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    )
                    .mit_notiz(
                        "which mark decides the class would then depend on which order the \
                         reader looked at first",
                    ),
                );
            }
        }
    };
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Device(d) = &item.art else {
            return;
        };
        for r in &d.register {
            pruefe(r, absagen);
        }
        for b in &d.baenke {
            for r in &b.register {
                pruefe(r, absagen);
            }
        }
    });
}

/// **The access to a phase-classed register, against the stage that holds here.**
///
/// Called from `phasen.rs`, which walks the stage of every mark through a body (`O003`,
/// `O004`, `O006`). The identifiers stay HERE, where `R005`/`R006` already live -- one
/// identifier belongs to one file (`pruefe-kennungen.py`), and the rule is the same rule
/// with a class looked up differently. *That is «B23»'s precedent, word for word.*
///
/// `stand` is what `phasen.rs` knows: local mark name -> stage. `markenordnung` says which
/// order each local mark belongs to. **Where the register's order has no mark in `stand`,
/// every stage is possible, and only what all of them permit is allowed.**
#[allow(clippy::too_many_arguments)]
pub(crate) fn phasenzugriff(
    o: &Ort,
    span: Span,
    lesend: bool,
    geraete: &BTreeMap<String, BTreeMap<String, RegInfo>>,
    griffe: &BTreeMap<String, String>,
    ordnungen: &BTreeMap<String, Vec<String>>,
    markenordnung: &BTreeMap<String, String>,
    stand: &BTreeMap<String, String>,
    absagen: &mut Absagen,
) {
    let Some(t) = ort_register(o, geraete, griffe) else {
        return;
    };
    let info = t.info;
    if info.phasen.is_empty() {
        return;
    }
    let kandidaten = ordnung_der_phasen(&info.phasen, ordnungen);
    if kandidaten.len() != 1 {
        return; // `R009` has already spoken -- a second message would be noise
    }
    let ordnung = kandidaten[0];
    // Which stages are possible here? The stages of every mark of this order whose stage
    // `phasen.rs` knows -- and if there is none, all of them.
    let mut moeglich: Vec<String> = markenordnung
        .iter()
        .filter(|(_, ord)| *ord == ordnung)
        .filter_map(|(name, _)| stand.get(name).cloned())
        .collect();
    moeglich.sort();
    moeglich.dedup();
    let bestimmt = !moeglich.is_empty();
    if !bestimmt {
        moeglich = ordnungen[ordnung].clone();
    }
    let schuldig = moeglich.iter().find(|s| match klasse_in_stufe(&info.phasen, s) {
        Some(k) if lesend => !darf_lesen_reg(k),
        Some(k) => !darf_schreiben_reg(k),
        None => false, // `R009` names the missing stage
    });
    let Some(stufe) = schuldig else { return };
    let klasse = klasse_in_stufe(&info.phasen, stufe).unwrap();
    let stelle = match t.feld {
        Some(f) => format!("{}.{}", t.reg.text, f.text),
        None => t.reg.text.clone(),
    };
    let (code, wort, tat) = if lesend {
        ("R005", "read", "readable")
    } else {
        ("R006", "written", "writable")
    };
    let mut a = Absage::fehler(
        code,
        span,
        format!(
            "`{}` is {wort}, but `{stelle}` is `class {}` in stage `{stufe}`",
            o.text(),
            klassenwort(klasse)
        ),
    )
    .mit_notiz(format!(
        "a `class {}` register is not {tat} -- that is a statement about the HARDWARE, and \
         the compiler is the only place it can be held",
        klassenwort(klasse)
    ));
    a = if bestimmt {
        a.mit_notiz(format!(
            "the mark of `{ordnung}` stands on `{stufe}` here (\u{ab}B18\u{bb})"
        ))
    } else {
        a.mit_notiz(format!(
            "no mark of `{ordnung}` is in scope, so the stage is NOT determined here -- what \
             holds is what EVERY stage permits, and `{stufe}` does not (\u{ab}B18\u{bb})"
        ))
        .mit_notiz(
            "a linear mark is a permission nobody is obliged to hold; this is what follows \
             without it, not a duty to carry it",
        )
    };
    absagen.schiebe(a);
}

// =======================================================================================
// «B26» -- the device promise that LOWERS. 2026-08-28.
//
// Half closed on 2026-08-24: `requires` at a register became a COUNTED obligation
// (`gabbro pflichten` prints `D  Device promise at a register`). *A clause nobody read
// became a duty with a name and a number* -- and there it stopped. The row said which half
// was still open, in its own words: the promise carries **no falsifier** and does not LOWER.
//
// **Why a FACT out of it would be wrong:** the register is volatile, and a hostile or broken
// device may report anything. Turning `requires` into something the checker may ASSUME would
// be the «B33» error again -- and «B33» is the entry directly above it in the register.
//
// So the closing form makes the READ fallible instead:
//
//     reg QUEUE_SIZE : u16 @0x0c class r requires QUEUE_SIZE <= QMAX else Geraetelug::ZuGross
//     let q = d.QUEUE_SIZE else (e) { return Geraetelug::ZuGross; }
//
// `R010` holds the declaration, `R011` holds the read, and `emit.rs::fehlbare_lesung` does
// the lowering -- ONE volatile read, and the condition checked on the binding.
//
// **W24 measured this before the build, and it turned the plan's own sentence around**
// (`messung/GERAETEVERSPRECHEN.md`): the plan said the emitter ALREADY carried that form.
// It did not. `gabbro emit` refused `let … else` over a PLACE, by name.
// =======================================================================================

/// **`R010` -- the falsifier at the declaration names a reason this unit declares.**
///
/// One identifier, two ways to be wrong: the `reason` type is not declared here, or it is
/// and has no such case. *An `else` that names nothing would hand `e` a value out of
/// nowhere, and the emitter would build a C identifier for it that no line declares.*
pub(crate) fn geraeteversprechen(baum: &Programm, absagen: &mut Absagen) {
    let mut gruende: BTreeMap<String, Vec<String>> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Reason(r) = &item.art {
            gruende.insert(
                r.name.text.clone(),
                r.faelle.iter().map(|f| f.name.text.clone()).collect(),
            );
        }
    });
    let pruefe = |r: &RegDecl, absagen: &mut Absagen| {
        let Some((g, f)) = &r.requires_grund else {
            return;
        };
        let Some(faelle) = gruende.get(&g.text) else {
            absagen.schiebe(
                Absage::fehler(
                    "R010",
                    g.span,
                    format!(
                        "`{}` falls back on `{}::{}`, and `{}` is no `reason` of this unit",
                        r.name.text, g.text, f.text, g.text
                    ),
                )
                .mit_notiz(
                    "the `else` of a device promise names the reason `e` holds -- it is the \
                     one place the failure of a volatile read gets a name",
                ),
            );
            return;
        };
        if !faelle.iter().any(|c| c == &f.text) {
            absagen.schiebe(
                Absage::fehler(
                    "R010",
                    f.span,
                    format!("`{}` has no case `{}`", g.text, f.text),
                )
                .mit_notiz(format!("the cases are: {}", faelle.join(", "))),
            );
        }
    };
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Device(d) = &item.art else {
            return;
        };
        for r in &d.register {
            pruefe(r, absagen);
        }
        for b in &d.baenke {
            for r in &b.register {
                pruefe(r, absagen);
            }
        }
    });
}

/// **`R011` -- a fallible register read outside a `let … else`. THIS is the falsifier.**
///
/// Without this line `requires … else` would be one more counted clause: the read would go
/// through unchecked and the promise would be a fact after all. *A booking is not a
/// discharge, and buying a decrement with bookkeeping is exactly what K100's second gate
/// exists to prevent.*
///
/// The place of a `let … else` is NOT in `eigene_ausdruecke` (it lives in `LetQuelle`), so
/// the allowed site steps aside on its own -- no exception list, and nothing to keep in sync.
fn fehlbare_lesungen(baum: &Programm, absagen: &mut Absagen) {
    let geraete = geraetetabelle(baum);
    if geraete.is_empty() {
        return;
    }
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Block(b) = &f.rumpf else {
            return;
        };
        let griffe = griffe_von(f, &geraete);
        if griffe.is_empty() {
            return;
        }
        fehlbarer_block(b, &geraete, &griffe, absagen);
    });
}

fn fehlbarer_block(
    b: &Block,
    geraete: &BTreeMap<String, BTreeMap<String, RegInfo>>,
    griffe: &BTreeMap<String, String>,
    absagen: &mut Absagen,
) {
    for s in &b.anweisungen {
        // **This statement's own expressions AND a bare call's arguments.** `eigene_ausdruecke` gives nothing
        // for a bare call, so `benutze(d.REG)` would slip past -- and a rule with a hole in
        // the commonest shape is not a rule.
        let mut orte: Vec<&Ort> = Vec::new();
        for e in crate::eigene_ausdruecke(s) {
            orte.extend(crate::alle_orte(e));
        }
        if let StmtArt::Ruf(r) = &s.art {
            for a in &r.argumente {
                orte.extend(crate::alle_orte(a));
            }
        }
        for o in orte {
            let Some(t) = ort_register(o, geraete, griffe) else {
                continue;
            };
            let Some((g, fall)) = &t.info.fehlbar else {
                continue;
            };
            absagen.schiebe(
                Absage::fehler(
                    "R011",
                    s.span,
                    format!(
                        "`{}` is read plainly, and `{}` promises `requires … else {}::{}`",
                        o.text(),
                        t.reg.text,
                        g,
                        fall
                    ),
                )
                .mit_notiz(format!(
                    "write `let <name> = {} else (e) {{ … }}` -- the read is FALLIBLE, and \
                     the `else` branch is where the device's lie becomes visible",
                    o.text()
                ))
                .mit_notiz(
                    "the register is volatile and a hostile device may report anything -- a \
                     promise the checker simply ASSUMED would be a fact it does not have \
                     («B33»)",
                ),
            );
        }
        for k in crate::unterbloecke(s) {
            fehlbarer_block(k, geraete, griffe, absagen);
        }
    }
}
