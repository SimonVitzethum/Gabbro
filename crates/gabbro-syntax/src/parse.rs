//! Der Parser. **Handgeschrieben, kein Generator** (`SPRACHE.md` Teil III, §6) und
//! regelweise gegen `SYNTAX.md` gelegt: zu jeder EBNF-Regel gehoert eine Funktion, die ihren
//! Namen traegt.
//!
//! **Der Parser deutet nicht.** Wo die Grammatik eine Klausel verlangt, verlangt er sie; wo sie
//! sie freistellt, laesst er das Feld leer und ueberlaesst die Pflicht dem Pass, der sie kennt.
//! Er erfindet keine Voreinstellung -- E3: nichts ist implizit.
//!
//! **Zwei Stellen, an denen ein Wort des Wortschatzes doch ein Name sein darf**, beide
//! eindeutig aus der Grammatik:
//!
//! 1. **nach `.` und `->`** (`placesuffix = "." ident`): dort kann kein Schluesselwort stehen,
//!    also kann keins verwechselt werden -- `c.slots[s]` steht so in `FRAGMENTE.md`;
//! 2. **als deklarierter Feldname** in `field`/`slotdecl`, wo dem Namen ein `:` folgt.
//!
//! Ueberall sonst gilt der geschlossene Wortschatz: `let slot = …` ist kein Bezeichner, und die
//! Absage sagt das mit Wort und Fundstelle.

use crate::ast::*;
use crate::diag::{Absage, Absagen};
use crate::kw::Kw;
use crate::lex::{Art, Token, Z};
use crate::span::Span;

/// Der Parser hat die Absage schon abgelegt; das hier ist nur der Ruecksprung.
#[derive(Debug, Clone, Copy)]
pub struct Abbruch;

type Erg<T> = Result<T, Abbruch>;

pub struct Parser<'a> {
    quelle: &'a str,
    tokens: Vec<Token>,
    pos: usize,
    absagen: &'a mut Absagen,
    /// Waehrend eines Rueckversuchs werden Absagen nicht abgelegt.
    stumm: usize,
    /// **Die eine mehrdeutige Stelle der Grammatik**, aufgeloest statt geraten.
    ///
    /// `placesuffix = "->" ident` und `placeshift = place ":" expr "->" expr` treffen sich in
    /// `transition ack { REG: A -> B }`: `A -> B` ist zugleich ein Ort mit Feldzugriff und ein
    /// Uebergang. Innerhalb der beiden Ausdruecke eines `placeshift` ist `->` deshalb **kein**
    /// Ortssuffix -- der Ort davor darf eins tragen. Ohne diese Regel ist `FRAGMENTE.md`s
    /// `transition drv { DEVICE_STATUS: ACK -> ACK | DRIVER }` nicht lesbar.
    pfeil_ist_suffix: bool,
}

/// Zerlegt und parst eine Quelle. Absagen sammeln sich in `absagen`.
pub fn parse(quelle: &str, absagen: &mut Absagen) -> Programm {
    let tokens = crate::lex::zerlege(quelle, absagen);
    let mut p = Parser {
        quelle,
        tokens,
        pos: 0,
        absagen,
        stumm: 0,
        pfeil_ist_suffix: true,
    };
    p.programm()
}

impl<'a> Parser<'a> {
    // -- Grundwerkzeug -------------------------------------------------------------------

    fn blick(&self) -> Token {
        self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    fn blick_n(&self, n: usize) -> Token {
        self.tokens[(self.pos + n).min(self.tokens.len() - 1)]
    }

    fn span(&self) -> Span {
        self.blick().span
    }

    fn ende(&self) -> bool {
        matches!(self.blick().art, Art::Ende)
    }

    fn vor(&mut self) -> Token {
        let t = self.blick();
        if !self.ende() {
            self.pos += 1;
        }
        t
    }

    fn absage(&mut self, a: Absage) {
        if self.stumm == 0 {
            self.absagen.schiebe(a);
        }
    }

    /// Ein Rueckversuch: Stellung merken, stumm probieren, bei Misserfolg zuruecksetzen.
    fn versuch<T>(&mut self, f: impl FnOnce(&mut Self) -> Erg<T>) -> Option<T> {
        let merk = self.pos;
        let vorher = self.absagen.absagen.len();
        self.stumm += 1;
        let r = f(self);
        self.stumm -= 1;
        match r {
            Ok(v) => Some(v),
            Err(_) => {
                self.pos = merk;
                self.absagen.absagen.truncate(vorher);
                None
            }
        }
    }

    fn ist_z(&self, z: Z) -> bool {
        self.blick().art == Art::Zeichen(z)
    }

    fn ist_kw(&self, k: Kw) -> bool {
        self.blick().art == Art::Wort(k)
    }

    fn friss_z(&mut self, z: Z) -> bool {
        if self.ist_z(z) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn friss_kw(&mut self, k: Kw) -> bool {
        if self.ist_kw(k) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn erwarte_z(&mut self, z: Z) -> Erg<Span> {
        if self.ist_z(z) {
            Ok(self.vor().span)
        } else {
            let t = self.blick();
            let gefunden = t.benennung(self.quelle);
            self.absage(Absage::fehler(
                "P001",
                t.span,
                format!("`{}` erwartet, {} gefunden", z.text(), gefunden),
            ));
            Err(Abbruch)
        }
    }

    fn erwarte_kw(&mut self, k: Kw) -> Erg<Span> {
        if self.ist_kw(k) {
            Ok(self.vor().span)
        } else {
            let t = self.blick();
            let gefunden = t.benennung(self.quelle);
            self.absage(Absage::fehler(
                "P001",
                t.span,
                format!("`{}` erwartet, {} gefunden", k.text(), gefunden),
            ));
            Err(Abbruch)
        }
    }

    /// Ein freier Bezeichner. Ein Wort des Wortschatzes ist hier **kein** Name.
    fn erwarte_ident(&mut self) -> Erg<Ident> {
        let t = self.blick();
        if t.art == Art::Ident && t.text(self.quelle) == "_" {
            self.absage(
                Absage::fehler("P034", t.span, "`_` allein ist kein Bezeichner")
                    .mit_notiz(
                        "es gibt keinen Auffangzweig (`match` ist erschoepfend) und keinen \
                         Platzhalterbinder -- eine neue Variante soll die Uebersetzung brechen",
                    )
                    .mit_notiz("Namen wie `_start` bleiben erlaubt"),
            );
            return Err(Abbruch);
        }
        match t.art {
            Art::Ident => {
                self.pos += 1;
                Ok(Ident {
                    text: t.text(self.quelle).to_string(),
                    span: t.span,
                })
            }
            // Einbuchstabige Woerter (`r`, `w`, `x`) sind kontextuell -- s. kw.rs.
            Art::Wort(k) if !k.reserviert() => {
                self.pos += 1;
                Ok(Ident {
                    text: k.text().to_string(),
                    span: t.span,
                })
            }
            Art::Wort(k) => {
                self.absage(
                    Absage::fehler(
                        "P002",
                        t.span,
                        format!("`{}` ist ein Wort des Wortschatzes und kein Bezeichner", k),
                    )
                    .mit_notiz(
                        "SYNTAX.md: der Wortschatz ist eine geschlossene Tabelle -- \
                         alles andere ist ein Bezeichner",
                    ),
                );
                Err(Abbruch)
            }
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(Absage::fehler(
                    "P003",
                    t.span,
                    format!("Bezeichner erwartet, {gefunden} gefunden"),
                ));
                Err(Abbruch)
            }
        }
    }

    /// Ein Name in Feldstellung: nach `.`/`->` oder vor `:` in einer Felddeklaration.
    /// Dort ist ein Wort des Wortschatzes eindeutig ein Name -- s. Kopf dieser Datei.
    fn erwarte_feldname(&mut self) -> Erg<Ident> {
        let t = self.blick();
        match t.art {
            Art::Ident => {
                self.pos += 1;
                Ok(Ident {
                    text: t.text(self.quelle).to_string(),
                    span: t.span,
                })
            }
            Art::Wort(k) => {
                self.pos += 1;
                Ok(Ident {
                    text: k.text().to_string(),
                    span: t.span,
                })
            }
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(Absage::fehler(
                    "P003",
                    t.span,
                    format!("Feldname erwartet, {gefunden} gefunden"),
                ));
                Err(Abbruch)
            }
        }
    }

    fn erwarte_zahl(&mut self) -> Erg<(u128, Span)> {
        let t = self.blick();
        if let Art::Zahl(v) = t.art {
            self.pos += 1;
            Ok((v, t.span))
        } else {
            let gefunden = t.benennung(self.quelle);
            self.absage(Absage::fehler(
                "P004",
                t.span,
                format!("Zahl erwartet, {gefunden} gefunden"),
            ));
            Err(Abbruch)
        }
    }

    fn erwarte_text(&mut self) -> Erg<Textliteral> {
        let t = self.blick();
        if t.art == Art::Text {
            self.pos += 1;
            Ok(Textliteral {
                text: t.text(self.quelle).to_string(),
                span: t.span,
            })
        } else {
            let gefunden = t.benennung(self.quelle);
            self.absage(Absage::fehler(
                "P005",
                t.span,
                format!("Zeichenkette erwartet, {gefunden} gefunden"),
            ));
            Err(Abbruch)
        }
    }

    // -- 1. Programm, Module ---------------------------------------------------------------

    fn programm(&mut self) -> Programm {
        let mut items = Vec::new();
        while !self.ende() {
            match self.item() {
                Ok(i) => items.push(i),
                Err(_) => {
                    if !self.synchronisiere() {
                        break;
                    }
                    // Eine schliessende Klammer auf oberster Ebene gehoert zu dem Rumpf, den
                    // die Absage gerade gekostet hat. Sie noch einmal zu melden, macht aus
                    // einem Befund zwei -- und der zweite hat keinen eigenen Inhalt.
                    while self.ist_z(Z::GeschweiftZu) {
                        self.pos += 1;
                    }
                }
            }
        }
        Programm { items }
    }

    /// Nach einer Absage bis zum naechsten Item-Anfang gehen. Gibt `false`, wenn nichts mehr
    /// kommt -- sonst laeuft der Parser auf der Stelle.
    fn synchronisiere(&mut self) -> bool {
        let start = self.pos;
        let mut tiefe = 0i32;
        while !self.ende() {
            match self.blick().art {
                Art::Zeichen(Z::GeschweiftAuf) => tiefe += 1,
                Art::Zeichen(Z::GeschweiftZu) => {
                    tiefe -= 1;
                    if tiefe < 0 {
                        // Ein `}`, das nicht zu uns gehoert -- gehoert es dem **umgebenden**
                        // Rumpf, ist hier Schluss. Folgt ihm aber noch etwas, das kein Item
                        // anfaengt (`protects { … } rank 0 …`), gehoerte es zur kaputten
                        // Deklaration: dann weiter, sonst verschluckt die Erholung die
                        // schliessende Klammer des Moduls und jedes weitere Item faellt.
                        let danach = self.blick_n(1);
                        let aeusserlich = match danach.art {
                            Art::Ende | Art::Zeichen(Z::GeschweiftZu) => true,
                            Art::Wort(k) => faengt_item_an(k),
                            _ => false,
                        };
                        if aeusserlich {
                            return self.pos > start;
                        }
                        tiefe = 0;
                    }
                }
                Art::Zeichen(Z::Semi) if tiefe == 0 => {
                    self.pos += 1;
                    return true;
                }
                Art::Wort(k) if tiefe == 0 && self.pos > start && faengt_item_an(k) => {
                    return true;
                }
                _ => {}
            }
            self.pos += 1;
        }
        self.pos > start
    }

    fn item(&mut self) -> Erg<Item> {
        let anfang = self.span();
        let when = if self.ist_kw(Kw::When) {
            self.pos += 1;
            Some(self.expr()?)
        } else {
            None
        };
        let oeffentlich = self.friss_kw(Kw::Pub);
        let t = self.blick();
        let art = match t.art {
            Art::Wort(Kw::Module) => ItemArt::Modul(self.moduledecl(oeffentlich)?),
            Art::Wort(Kw::Use) => ItemArt::Use(self.usedecl(oeffentlich)?),
            Art::Wort(Kw::Const) => ItemArt::Konst(self.constdecl(oeffentlich)?),
            Art::Wort(Kw::Static) => ItemArt::Statisch(self.staticdecl(oeffentlich)?),
            Art::Wort(Kw::Opaque | Kw::Linear | Kw::Tagged | Kw::Type) => {
                ItemArt::Typ(self.typedecl(oeffentlich)?)
            }
            Art::Wort(
                Kw::Fn | Kw::Spec | Kw::Impl | Kw::Raw | Kw::Divergent | Kw::Prim | Kw::Extern,
            ) => ItemArt::Funktion(self.fndecl(oeffentlich)?),
            Art::Wort(Kw::Atomic) => ItemArt::Atomic(self.atomicdecl(oeffentlich)?),
            Art::Wort(Kw::Format) => ItemArt::Format(self.format()?),
            Art::Wort(Kw::Table) => ItemArt::Tabelle(self.table()?),
            Art::Wort(Kw::Reason) => ItemArt::Reason(self.reason()?),
            Art::Wort(Kw::State) => ItemArt::State(self.statedecl()?),
            Art::Wort(Kw::Device) => ItemArt::Device(self.device()?),
            Art::Wort(Kw::Assume) => ItemArt::Assume(self.assume()?),
            Art::Wort(Kw::Axiom) => ItemArt::Axiom(self.axiom()?),
            Art::Wort(Kw::Check) => ItemArt::Check(self.check()?),
            Art::Wort(Kw::Lock) => ItemArt::Lock(self.lockdecl()?),
            Art::Wort(Kw::Accumulates) => ItemArt::Accumulates(self.accdecl()?),
            Art::Wort(Kw::Walk) => ItemArt::Walk(self.walkdecl()?),
            Art::Wort(Kw::Entry) => ItemArt::Entry(self.entrydecl()?),
            Art::Wort(Kw::Boot) => ItemArt::Boot(self.bootdecl()?),
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(
                    Absage::fehler(
                        "P006",
                        t.span,
                        format!("hier faengt kein Item an: {gefunden}"),
                    )
                    .mit_notiz(
                        "`item` kennt: module use type const static fn format table reason \
                         state device assume axiom check atomic lock accumulates walk entry boot",
                    ),
                );
                return Err(Abbruch);
            }
        };
        let span = anfang.bis_zu(self.vorheriger_span());
        Ok(Item { when, art, span })
    }

    fn vorheriger_span(&self) -> Span {
        if self.pos == 0 {
            self.tokens[0].span
        } else {
            self.tokens[self.pos - 1].span
        }
    }

    fn moduledecl(&mut self, oeffentlich: bool) -> Erg<Modul> {
        self.erwarte_kw(Kw::Module)?;
        let pfad = self.pfad()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut items = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            match self.item() {
                Ok(i) => items.push(i),
                Err(_) => {
                    if !self.synchronisiere() {
                        break;
                    }
                }
            }
        }
        self.erwarte_z(Z::GeschweiftZu)?;
        Ok(Modul {
            oeffentlich,
            pfad,
            items,
        })
    }

    fn usedecl(&mut self, oeffentlich: bool) -> Erg<UseDecl> {
        self.erwarte_kw(Kw::Use)?;
        let pfad = self.pfad()?;
        self.erwarte_z(Z::Semi)?;
        Ok(UseDecl { oeffentlich, pfad })
    }

    fn constdecl(&mut self, oeffentlich: bool) -> Erg<KonstDecl> {
        self.erwarte_kw(Kw::Const)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::Kolon)?;
        let typ = self.typeexpr()?;
        self.erwarte_z(Z::Gleich)?;
        let wert = self.expr()?;
        self.erwarte_z(Z::Semi)?;
        Ok(KonstDecl {
            oeffentlich,
            name,
            typ,
            wert,
        })
    }

    fn staticdecl(&mut self, oeffentlich: bool) -> Erg<StatischDecl> {
        self.erwarte_kw(Kw::Static)?;
        let veraenderlich = self.friss_kw(Kw::Mut);
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::Kolon)?;
        let typ = self.typeexpr()?;
        self.erwarte_z(Z::Gleich)?;
        let wert = self.expr()?;
        let section = if self.friss_kw(Kw::Section) {
            Some(self.erwarte_text()?)
        } else {
            None
        };
        self.erwarte_z(Z::Semi)?;
        Ok(StatischDecl {
            oeffentlich,
            veraenderlich,
            name,
            typ,
            wert,
            section,
        })
    }

    fn pfad(&mut self) -> Erg<Pfad> {
        let erste = self.erwarte_ident()?;
        let mut teile = vec![erste];
        while self.ist_z(Z::Kolon2) {
            self.pos += 1;
            teile.push(self.erwarte_feldname()?);
        }
        let span = teile[0].span.bis_zu(teile[teile.len() - 1].span);
        Ok(Pfad { teile, span })
    }

    // -- 2. Typen --------------------------------------------------------------------------

    fn typedecl(&mut self, oeffentlich: bool) -> Erg<TypDecl> {
        let anfang = self.span();
        let opaque = self.friss_kw(Kw::Opaque);
        let linear = self.friss_kw(Kw::Linear);
        let ghost = if linear { self.friss_kw(Kw::Ghost) } else { false };
        let tagged = self.friss_kw(Kw::Tagged);
        self.erwarte_kw(Kw::Type)?;
        let name = self.erwarte_ident()?;
        let parameter = if self.friss_z(Z::RundAuf) {
            let mut liste = Vec::new();
            if !self.ist_z(Z::RundZu) {
                loop {
                    liste.push(self.typeexpr()?);
                    if !self.friss_z(Z::Komma) {
                        break;
                    }
                }
            }
            self.erwarte_z(Z::RundZu)?;
            Some(liste)
        } else {
            None
        };
        let rumpf = if self.friss_z(Z::Gleich) {
            Some(self.typeexpr()?)
        } else {
            None
        };
        self.erwarte_z(Z::Semi)?;
        Ok(TypDecl {
            oeffentlich,
            opaque,
            linear,
            ghost,
            tagged,
            name,
            parameter,
            rumpf,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    fn typeexpr(&mut self) -> Erg<TypExpr> {
        let t = self.blick();
        match t.art {
            Art::Wort(k) if k.ist_intty() => Ok(TypExpr::Int(self.intty()?)),
            Art::Wort(Kw::Bool) => {
                self.pos += 1;
                Ok(TypExpr::Bool(t.span))
            }
            Art::Wort(Kw::Never) => {
                self.pos += 1;
                Ok(TypExpr::Never(t.span))
            }
            Art::Wort(Kw::Ptr) => Ok(TypExpr::Zeiger(Box::new(self.ptrty()?))),
            Art::Wort(Kw::Fn) => Ok(TypExpr::FnZeiger(Box::new(self.fnptr()?))),
            Art::Wort(Kw::SelfWort) => {
                self.pos += 1;
                Ok(TypExpr::Pfad(Pfad {
                    teile: vec![Ident {
                        text: "Self".to_string(),
                        span: t.span,
                    }],
                    span: t.span,
                }))
            }
            Art::Zeichen(Z::EckAuf) => {
                let anfang = self.vor().span;
                let element = self.typeexpr()?;
                self.erwarte_z(Z::Semi)?;
                let laenge = self.expr()?;
                let ende = self.erwarte_z(Z::EckZu)?;
                Ok(TypExpr::Feld(Box::new(ArrayTy {
                    element,
                    laenge,
                    span: anfang.bis_zu(ende),
                })))
            }
            Art::Zeichen(Z::GeschweiftAuf) => self.verbund_oder_varianten(),
            Art::Ident => Ok(TypExpr::Pfad(self.pfad()?)),
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(Absage::fehler(
                    "P007",
                    t.span,
                    format!("Typ erwartet, {gefunden} gefunden"),
                ));
                Err(Abbruch)
            }
        }
    }

    fn intty(&mut self) -> Erg<IntTy> {
        let t = self.blick();
        let Art::Wort(wort) = t.art else {
            let gefunden = t.benennung(self.quelle);
            self.absage(Absage::fehler(
                "P008",
                t.span,
                format!("Ganzzahltyp erwartet, {gefunden} gefunden"),
            ));
            return Err(Abbruch);
        };
        if !wort.ist_intty() {
            self.absage(Absage::fehler(
                "P008",
                t.span,
                format!("Ganzzahltyp erwartet, `{wort}` gefunden"),
            ));
            return Err(Abbruch);
        }
        self.pos += 1;
        let bereich = if self.ist_kw(Kw::In) {
            self.pos += 1;
            Some(self.range()?)
        } else {
            None
        };
        Ok(IntTy {
            wort,
            bereich,
            span: t.span.bis_zu(self.vorheriger_span()),
        })
    }

    fn range(&mut self) -> Erg<Bereich> {
        let von = self.expr()?;
        let exklusiv = if self.friss_z(Z::BereichEx) {
            true
        } else {
            self.erwarte_z(Z::Bereich)?;
            false
        };
        let bis = self.expr()?;
        Ok(Bereich {
            span: von.span.bis_zu(bis.span),
            von,
            bis,
            exklusiv,
        })
    }

    fn ptrty(&mut self) -> Erg<PtrTy> {
        let anfang = self.erwarte_kw(Kw::Ptr)?;
        self.erwarte_z(Z::Kleiner)?;
        let raum = self.space()?;
        self.erwarte_z(Z::Komma)?;
        let rechte = self.rights()?;
        self.erwarte_z(Z::Groesser)?;
        let ziel = self.typeexpr()?;
        Ok(PtrTy {
            raum,
            rechte,
            span: anfang.bis_zu(ziel.span()),
            ziel,
        })
    }

    fn space(&mut self) -> Erg<Raum> {
        let t = self.blick();
        let raum = match t.art {
            Art::Wort(Kw::Normal) => Raum::Normal,
            Art::Wort(Kw::Mmio) => Raum::Mmio,
            Art::Wort(Kw::Dma) => Raum::Dma,
            Art::Wort(Kw::Code) => Raum::Code,
            Art::Wort(Kw::Boot) => Raum::Boot,
            Art::Wort(Kw::Port) => Raum::Port,
            Art::Ident => return Ok(Raum::Benannt(self.erwarte_ident()?)),
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(
                    Absage::fehler(
                        "P009",
                        t.span,
                        format!("Adressraum erwartet, {gefunden} gefunden"),
                    )
                    .mit_notiz("`normal` `mmio` `dma` `code` `boot` `port` oder ein Name"),
                );
                return Err(Abbruch);
            }
        };
        self.pos += 1;
        Ok(raum)
    }

    fn rights(&mut self) -> Erg<Vec<Recht>> {
        let mut liste = vec![self.right()?];
        while self.friss_z(Z::Plus) {
            liste.push(self.right()?);
        }
        Ok(liste)
    }

    fn right(&mut self) -> Erg<Recht> {
        let t = self.blick();
        let recht = match t.art {
            Art::Wort(Kw::R) => Recht::Lesen,
            Art::Wort(Kw::W) => Recht::Schreiben,
            Art::Wort(Kw::Rw) => Recht::LesenSchreiben,
            Art::Wort(Kw::X) => Recht::Ausfuehren,
            Art::Wort(Kw::Own) => {
                self.pos += 1;
                let marke = if self.friss_z(Z::At) {
                    Some(self.erwarte_ident()?)
                } else {
                    None
                };
                return Ok(Recht::Eigen(marke));
            }
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(
                    Absage::fehler(
                        "P010",
                        t.span,
                        format!("Zugriffsrecht erwartet, {gefunden} gefunden"),
                    )
                    .mit_notiz("`r` `w` `rw` `x` `own[@marke]`"),
                );
                return Err(Abbruch);
            }
        };
        self.pos += 1;
        Ok(recht)
    }

    fn fnptr(&mut self) -> Erg<FnZeiger> {
        let anfang = self.erwarte_kw(Kw::Fn)?;
        self.erwarte_z(Z::RundAuf)?;
        let mut parameter = Vec::new();
        if !self.ist_z(Z::RundZu) {
            loop {
                parameter.push(self.typeexpr()?);
                if !self.friss_z(Z::Komma) {
                    break;
                }
            }
        }
        self.erwarte_z(Z::RundZu)?;
        let ergebnis = if self.friss_z(Z::Pfeil) {
            Some(self.typeexpr()?)
        } else {
            None
        };
        Ok(FnZeiger {
            parameter,
            ergebnis,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    /// `structty` und `variants` fangen beide mit `{` an. Unterschieden wird am zweiten
    /// Token: einem Feld folgt `:`, einer Variante `(`, `,` oder `}`.
    fn verbund_oder_varianten(&mut self) -> Erg<TypExpr> {
        let anfang = self.span();
        let ist_verbund = matches!(self.blick_n(2).art, Art::Zeichen(Z::Kolon));
        if ist_verbund {
            self.erwarte_z(Z::GeschweiftAuf)?;
            let mut felder = Vec::new();
            while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
                felder.push(self.field()?);
            }
            let ende = self.erwarte_z(Z::GeschweiftZu)?;
            Ok(TypExpr::Verbund(felder, anfang.bis_zu(ende)))
        } else {
            self.erwarte_z(Z::GeschweiftAuf)?;
            let mut varianten = Vec::new();
            if !self.ist_z(Z::GeschweiftZu) {
                loop {
                    let name = self.erwarte_ident()?;
                    let nutzlast = if self.friss_z(Z::RundAuf) {
                        let t = self.typeexpr()?;
                        self.erwarte_z(Z::RundZu)?;
                        Some(t)
                    } else {
                        None
                    };
                    varianten.push(Variante { name, nutzlast });
                    if !self.friss_z(Z::Komma) {
                        break;
                    }
                    if self.ist_z(Z::GeschweiftZu) {
                        break;
                    }
                }
            }
            let ende = self.erwarte_z(Z::GeschweiftZu)?;
            Ok(TypExpr::Varianten(varianten, anfang.bis_zu(ende)))
        }
    }

    /// `field = ident ":" fieldty [ "@" bitpos ] [ "offset_into" ident ] [ "where" pred ]
    ///          [ "reserved" ] ","`
    fn field(&mut self) -> Erg<FeldDecl> {
        let name = self.erwarte_feldname()?;
        self.erwarte_z(Z::Kolon)?;
        let typ = self.fieldty()?;
        let bitpos = if self.friss_z(Z::At) {
            Some(self.bitpos()?)
        } else {
            None
        };
        let offset_into = if self.friss_kw(Kw::OffsetInto) {
            Some(self.typname_als_ident()?)
        } else {
            None
        };
        let bedingung = if self.friss_kw(Kw::Where) {
            Some(self.pred()?)
        } else {
            None
        };
        let reserviert = self.friss_kw(Kw::Reserved);
        self.erwarte_z(Z::Komma)?;
        Ok(FeldDecl {
            span: name.span.bis_zu(self.vorheriger_span()),
            name,
            typ,
            bitpos,
            offset_into,
            bedingung,
            reserviert,
        })
    }

    /// `offset_into Self` -- `Self` ist ein Wort, steht hier aber in Namensstellung.
    fn typname_als_ident(&mut self) -> Erg<Ident> {
        if self.ist_kw(Kw::SelfWort) {
            let t = self.vor();
            return Ok(Ident {
                text: "Self".to_string(),
                span: t.span,
            });
        }
        self.erwarte_ident()
    }

    fn fieldty(&mut self) -> Erg<FeldTy> {
        let typ = self.typeexpr()?;
        if self.friss_kw(Kw::Embeds) {
            self.erwarte_z(Z::EckAuf)?;
            let (hoch, _) = self.erwarte_zahl()?;
            self.erwarte_z(Z::Kolon)?;
            let (tief, _) = self.erwarte_zahl()?;
            self.erwarte_z(Z::EckZu)?;
            let scale = if self.friss_kw(Kw::Scale) {
                Some(self.expr()?)
            } else {
                None
            };
            Ok(FeldTy {
                typ,
                embeds: Some((hoch, tief)),
                scale,
            })
        } else {
            Ok(FeldTy {
                typ,
                embeds: None,
                scale: None,
            })
        }
    }

    fn bitpos(&mut self) -> Erg<BitPos> {
        if self.friss_z(Z::EckAuf) {
            let (hoch, _) = self.erwarte_zahl()?;
            self.erwarte_z(Z::Kolon)?;
            let (tief, _) = self.erwarte_zahl()?;
            self.erwarte_z(Z::EckZu)?;
            Ok(BitPos::Bereich(hoch, tief))
        } else {
            let (b, _) = self.erwarte_zahl()?;
            Ok(BitPos::Bit(b))
        }
    }

    fn params(&mut self) -> Erg<Vec<Parameter>> {
        let mut liste = Vec::new();
        loop {
            let name = self.erwarte_ident()?;
            self.erwarte_z(Z::Kolon)?;
            let typ = self.typeexpr()?;
            liste.push(Parameter { name, typ });
            if !self.friss_z(Z::Komma) {
                break;
            }
        }
        Ok(liste)
    }

    // -- 4. Ausdruecke ---------------------------------------------------------------------

    fn expr(&mut self) -> Erg<Expr> {
        self.orexpr()
    }

    fn orexpr(&mut self) -> Erg<Expr> {
        let mut links = self.andexpr()?;
        while self.friss_z(Z::StrichStrich) {
            let rechts = self.andexpr()?;
            links = Expr {
                span: links.span.bis_zu(rechts.span),
                art: ExprArt::Binaer(BinOp::Oder, Box::new(links), Box::new(rechts)),
            };
        }
        Ok(links)
    }

    fn andexpr(&mut self) -> Erg<Expr> {
        let mut links = self.cmpexpr()?;
        while self.friss_z(Z::UndUnd) {
            let rechts = self.cmpexpr()?;
            links = Expr {
                span: links.span.bis_zu(rechts.span),
                art: ExprArt::Binaer(BinOp::Und, Box::new(links), Box::new(rechts)),
            };
        }
        Ok(links)
    }

    /// `cmpexpr = bitexpr [ cmp bitexpr ]` -- **hoechstens einer**, Vergleiche ketten nicht.
    fn cmpexpr(&mut self) -> Erg<Expr> {
        let links = self.bitexpr()?;
        let op = match self.blick().art {
            Art::Zeichen(Z::GleichGleich) => BinOp::Gleich,
            Art::Zeichen(Z::Ungleich) => BinOp::Ungleich,
            Art::Zeichen(Z::Kleiner) => BinOp::Kleiner,
            Art::Zeichen(Z::KleinerGleich) => BinOp::KleinerGleich,
            Art::Zeichen(Z::Groesser) => BinOp::Groesser,
            Art::Zeichen(Z::GroesserGleich) => BinOp::GroesserGleich,
            _ => return Ok(links),
        };
        self.pos += 1;
        let rechts = self.bitexpr()?;
        Ok(Expr {
            span: links.span.bis_zu(rechts.span),
            art: ExprArt::Binaer(op, Box::new(links), Box::new(rechts)),
        })
    }

    fn bitexpr(&mut self) -> Erg<Expr> {
        let mut links = self.addexpr()?;
        loop {
            let op = match self.blick().art {
                Art::Zeichen(Z::Und) => BinOp::BitUnd,
                Art::Zeichen(Z::Strich) => BinOp::BitOder,
                Art::Zeichen(Z::Dach) => BinOp::BitXor,
                Art::Zeichen(Z::SchiebLinks) => BinOp::SchiebLinks,
                Art::Zeichen(Z::SchiebRechts) => BinOp::SchiebRechts,
                _ => break,
            };
            self.pos += 1;
            let rechts = self.addexpr()?;
            links = Expr {
                span: links.span.bis_zu(rechts.span),
                art: ExprArt::Binaer(op, Box::new(links), Box::new(rechts)),
            };
        }
        Ok(links)
    }

    fn addexpr(&mut self) -> Erg<Expr> {
        let mut links = self.mulexpr()?;
        loop {
            let op = match self.blick().art {
                Art::Zeichen(Z::Plus) => BinOp::Plus,
                Art::Zeichen(Z::Minus) => BinOp::Minus,
                _ => break,
            };
            self.pos += 1;
            let rechts = self.mulexpr()?;
            links = Expr {
                span: links.span.bis_zu(rechts.span),
                art: ExprArt::Binaer(op, Box::new(links), Box::new(rechts)),
            };
        }
        Ok(links)
    }

    fn mulexpr(&mut self) -> Erg<Expr> {
        let mut links = self.unary()?;
        loop {
            let op = match self.blick().art {
                Art::Zeichen(Z::Stern) => BinOp::Mal,
                Art::Zeichen(Z::Schraeg) => BinOp::Geteilt,
                Art::Zeichen(Z::Prozent) => BinOp::Rest,
                _ => break,
            };
            self.pos += 1;
            let rechts = self.unary()?;
            links = Expr {
                span: links.span.bis_zu(rechts.span),
                art: ExprArt::Binaer(op, Box::new(links), Box::new(rechts)),
            };
        }
        Ok(links)
    }

    fn unary(&mut self) -> Erg<Expr> {
        let t = self.blick();
        let op = match t.art {
            Art::Zeichen(Z::Bang) => Some(UnOp::Nicht),
            Art::Zeichen(Z::Minus) => Some(UnOp::Negativ),
            _ => None,
        };
        if let Some(op) = op {
            self.pos += 1;
            let inner = self.primary()?;
            return Ok(Expr {
                span: t.span.bis_zu(inner.span),
                art: ExprArt::Unaer(op, Box::new(inner)),
            });
        }
        self.primary()
    }

    fn primary(&mut self) -> Erg<Expr> {
        let t = self.blick();
        match t.art {
            Art::Zahl(v) => {
                self.pos += 1;
                Ok(Expr {
                    art: ExprArt::Zahl(v),
                    span: t.span,
                })
            }
            Art::Wort(Kw::True) => {
                self.pos += 1;
                Ok(Expr {
                    art: ExprArt::Wahr,
                    span: t.span,
                })
            }
            Art::Wort(Kw::False) => {
                self.pos += 1;
                Ok(Expr {
                    art: ExprArt::Falsch,
                    span: t.span,
                })
            }
            Art::Wort(Kw::Result) => {
                self.pos += 1;
                Ok(Expr {
                    art: ExprArt::Ergebnis,
                    span: t.span,
                })
            }
            Art::Wort(Kw::Old) => {
                self.pos += 1;
                self.erwarte_z(Z::RundAuf)?;
                let ort = self.place()?;
                let ende = self.erwarte_z(Z::RundZu)?;
                Ok(Expr {
                    art: ExprArt::Alt(ort),
                    span: t.span.bis_zu(ende),
                })
            }
            Art::Wort(Kw::Sizeof) | Art::Wort(Kw::Lenof) => {
                let ist_size = matches!(t.art, Art::Wort(Kw::Sizeof));
                self.pos += 1;
                self.erwarte_z(Z::RundAuf)?;
                let arg = self.typ_oder_ort()?;
                let ende = self.erwarte_z(Z::RundZu)?;
                let e = if ist_size {
                    Eingebaut::Sizeof(arg)
                } else {
                    Eingebaut::Lenof(arg)
                };
                Ok(Expr {
                    art: ExprArt::Eingebaut(Box::new(e)),
                    span: t.span.bis_zu(ende),
                })
            }
            Art::Wort(Kw::Aligned) => {
                self.pos += 1;
                self.erwarte_z(Z::RundAuf)?;
                let a = self.expr()?;
                self.erwarte_z(Z::Komma)?;
                let b = self.expr()?;
                let ende = self.erwarte_z(Z::RundZu)?;
                Ok(Expr {
                    art: ExprArt::Eingebaut(Box::new(Eingebaut::Aligned(a, b))),
                    span: t.span.bis_zu(ende),
                })
            }
            Art::Zeichen(Z::RundAuf) => {
                self.pos += 1;
                let inner = self.expr()?;
                let ende = self.erwarte_z(Z::RundZu)?;
                Ok(Expr {
                    art: ExprArt::Klammer(Box::new(inner)),
                    span: t.span.bis_zu(ende),
                })
            }
            // `Self` und die Ganzzahlwoerter tragen Pfade: `Self.slots[s]`, `u64::max`.
            Art::Wort(Kw::SelfWort) => {
                self.pos += 1;
                let basis = Ident {
                    text: "Self".to_string(),
                    span: t.span,
                };
                let ort = self.place_ab(basis)?;
                Ok(Expr {
                    span: ort.span,
                    art: ExprArt::Ort(ort),
                })
            }
            Art::Wort(k) if k.ist_intty() && self.blick_n(1).art == Art::Zeichen(Z::Kolon2) => {
                self.pos += 1;
                let mut teile = vec![Ident {
                    text: k.text().to_string(),
                    span: t.span,
                }];
                while self.friss_z(Z::Kolon2) {
                    teile.push(self.erwarte_feldname()?);
                }
                let span = t.span.bis_zu(self.vorheriger_span());
                let pfad = Pfad { teile, span };
                if self.ist_z(Z::RundAuf) {
                    let ruf = self.ruf_ab(pfad)?;
                    Ok(Expr {
                        span: ruf.span,
                        art: ExprArt::Ruf(ruf),
                    })
                } else {
                    Ok(Expr {
                        span,
                        art: ExprArt::Ort(Ort {
                            basis: pfad.teile[0].clone(),
                            suffixe: pfad.teile[1..]
                                .iter()
                                .map(|i| OrtSuffix::Feld(i.clone()))
                                .collect(),
                            span,
                        }),
                    })
                }
            }
            Art::Ident | Art::Wort(_) => {
                // `place` oder `call`/`cast` -- der Unterschied ist die Klammer.
                let erste = self.erwarte_ident()?;
                if self.ist_z(Z::Kolon2) || self.ist_z(Z::RundAuf) {
                    let mut teile = vec![erste];
                    while self.friss_z(Z::Kolon2) {
                        teile.push(self.erwarte_feldname()?);
                    }
                    let span = teile[0].span.bis_zu(self.vorheriger_span());
                    let pfad = Pfad { teile, span };
                    if self.ist_z(Z::RundAuf) {
                        let ruf = self.ruf_ab(pfad)?;
                        return Ok(Expr {
                            span: ruf.span,
                            art: ExprArt::Ruf(ruf),
                        });
                    }
                    let ort = Ort {
                        basis: pfad.teile[0].clone(),
                        suffixe: pfad.teile[1..]
                            .iter()
                            .map(|i| OrtSuffix::Feld(i.clone()))
                            .collect(),
                        span,
                    };
                    return Ok(Expr {
                        span: ort.span,
                        art: ExprArt::Ort(ort),
                    });
                }
                let ort = self.place_ab(erste)?;
                Ok(Expr {
                    span: ort.span,
                    art: ExprArt::Ort(ort),
                })
            }
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(Absage::fehler(
                    "P011",
                    t.span,
                    format!("Ausdruck erwartet, {gefunden} gefunden"),
                ));
                Err(Abbruch)
            }
        }
    }

    fn typ_oder_ort(&mut self) -> Erg<TypOderOrt> {
        let t = self.blick();
        let ist_typ = match t.art {
            Art::Wort(k) => {
                k.ist_intty()
                    || matches!(k, Kw::Bool | Kw::Never | Kw::Ptr | Kw::Fn)
                    // `Self` ist als Ganzes ein Typ, `Self.feld` ein Ort.
                    || (k == Kw::SelfWort && !matches!(self.blick_n(1).art, Art::Zeichen(Z::Punkt)))
            }
            Art::Zeichen(Z::EckAuf) | Art::Zeichen(Z::GeschweiftAuf) => true,
            _ => false,
        };
        if ist_typ {
            Ok(TypOderOrt::Typ(self.typeexpr()?))
        } else {
            Ok(TypOderOrt::Ort(self.place()?))
        }
    }

    fn ruf_ab(&mut self, pfad: Pfad) -> Erg<Ruf> {
        self.erwarte_z(Z::RundAuf)?;
        let mut argumente = Vec::new();
        if !self.ist_z(Z::RundZu) {
            loop {
                argumente.push(self.expr()?);
                if !self.friss_z(Z::Komma) {
                    break;
                }
            }
        }
        let ende = self.erwarte_z(Z::RundZu)?;
        Ok(Ruf {
            span: pfad.span.bis_zu(ende),
            pfad,
            argumente,
        })
    }

    fn place(&mut self) -> Erg<Ort> {
        let basis = if self.ist_kw(Kw::SelfWort) {
            let t = self.vor();
            Ident {
                text: "Self".to_string(),
                span: t.span,
            }
        } else {
            self.erwarte_ident()?
        };
        self.place_ab(basis)
    }

    fn place_ab(&mut self, basis: Ident) -> Erg<Ort> {
        let mut suffixe = Vec::new();
        loop {
            if self.friss_z(Z::Punkt) {
                suffixe.push(OrtSuffix::Feld(self.erwarte_feldname()?));
            } else if self.pfeil_ist_suffix && self.ist_z(Z::Pfeil) {
                self.pos += 1;
                suffixe.push(OrtSuffix::Ueber(self.erwarte_feldname()?));
            } else if self.ist_z(Z::EckAuf) {
                self.pos += 1;
                let idx = self.expr()?;
                self.erwarte_z(Z::EckZu)?;
                suffixe.push(OrtSuffix::Index(idx));
            } else {
                break;
            }
        }
        Ok(Ort {
            span: basis.span.bis_zu(self.vorheriger_span()),
            basis,
            suffixe,
        })
    }

    fn placelist(&mut self) -> Erg<Vec<Ort>> {
        let mut liste = vec![self.place()?];
        while self.friss_z(Z::Komma) {
            liste.push(self.place()?);
        }
        Ok(liste)
    }

    fn identlist(&mut self) -> Erg<Vec<Ident>> {
        let mut liste = vec![self.erwarte_ident()?];
        while self.friss_z(Z::Komma) {
            liste.push(self.erwarte_ident()?);
        }
        Ok(liste)
    }

    // -- 5. Praedikate ---------------------------------------------------------------------

    fn pred(&mut self) -> Erg<Pred> {
        self.orpred()
    }

    fn orpred(&mut self) -> Erg<Pred> {
        let mut links = self.andpred()?;
        while self.friss_z(Z::StrichStrich) {
            let rechts = self.andpred()?;
            links = Pred {
                span: links.span.bis_zu(rechts.span),
                art: PredArt::Oder(Box::new(links), Box::new(rechts)),
            };
        }
        Ok(links)
    }

    fn andpred(&mut self) -> Erg<Pred> {
        let mut links = self.notpred()?;
        while self.friss_z(Z::UndUnd) {
            let rechts = self.notpred()?;
            links = Pred {
                span: links.span.bis_zu(rechts.span),
                art: PredArt::Und(Box::new(links), Box::new(rechts)),
            };
        }
        Ok(links)
    }

    fn notpred(&mut self) -> Erg<Pred> {
        let anfang = self.span();
        let negiert = self.friss_z(Z::Bang);
        let mut p = self.atompred()?;
        if negiert {
            p = Pred {
                span: anfang.bis_zu(p.span),
                art: PredArt::Nicht(Box::new(p)),
            };
        }
        if self.friss_z(Z::Doppelpfeil) {
            let rechts = self.pred()?;
            p = Pred {
                span: p.span.bis_zu(rechts.span),
                art: PredArt::Folgt(Box::new(p), Box::new(rechts)),
            };
        }
        Ok(p)
    }

    fn atompred(&mut self) -> Erg<Pred> {
        if self.ist_kw(Kw::Forall) || self.ist_kw(Kw::Exists) {
            return self.quant();
        }
        // `cmpexpr`, `member` und `reach` fangen alle mit einem Ausdruck an. Der
        // Rueckversuch trennt sie von `"(" pred ")"`, das ein Quantor enthalten kann.
        if let Some(p) = self.versuch(|s| {
            let e = s.cmpexpr()?;
            if s.ist_kw(Kw::In) {
                s.pos += 1;
                let d = s.domain()?;
                return Ok(Pred {
                    span: e.span.bis_zu(s.vorheriger_span()),
                    art: PredArt::Element(e, d),
                });
            }
            if s.ist_kw(Kw::Reaches) {
                let ExprArt::Ort(von) = e.art.clone() else {
                    return Err(Abbruch);
                };
                s.pos += 1;
                let nach = s.place()?;
                s.erwarte_kw(Kw::Via)?;
                let via = s.erwarte_feldname()?;
                return Ok(Pred {
                    span: e.span.bis_zu(via.span),
                    art: PredArt::Erreicht { von, nach, via },
                });
            }
            Ok(Pred {
                span: e.span,
                art: PredArt::Vergleich(e),
            })
        }) {
            return Ok(p);
        }
        if self.ist_z(Z::RundAuf) {
            let anfang = self.vor().span;
            let inner = self.pred()?;
            let ende = self.erwarte_z(Z::RundZu)?;
            return Ok(Pred {
                span: anfang.bis_zu(ende),
                art: PredArt::Klammer(Box::new(inner)),
            });
        }
        let t = self.blick();
        let gefunden = t.benennung(self.quelle);
        self.absage(Absage::fehler(
            "P012",
            t.span,
            format!("Praedikat erwartet, {gefunden} gefunden"),
        ));
        Err(Abbruch)
    }

    fn quant(&mut self) -> Erg<Pred> {
        let t = self.vor();
        let art = if t.art == Art::Wort(Kw::Forall) {
            QuantorArt::Alle
        } else {
            QuantorArt::Existiert
        };
        let variable = self.erwarte_ident()?;
        self.erwarte_kw(Kw::In)?;
        let domaene = self.domain()?;
        self.erwarte_z(Z::Kolon)?;
        let rumpf = self.pred()?;
        Ok(Pred {
            span: t.span.bis_zu(rumpf.span),
            art: PredArt::Quantor(Box::new(Quantor {
                art,
                variable,
                domaene,
                rumpf,
            })),
        })
    }

    fn domain(&mut self) -> Erg<Domaene> {
        let t = self.blick();
        match t.art {
            Art::Wort(Kw::Slots) => {
                self.pos += 1;
                self.erwarte_kw(Kw::Of)?;
                Ok(Domaene::SlotsVon(self.place()?))
            }
            Art::Wort(Kw::Chain) => {
                self.pos += 1;
                self.erwarte_z(Z::RundAuf)?;
                let a = self.erwarte_feldname()?;
                self.erwarte_z(Z::Komma)?;
                let b = self.erwarte_feldname()?;
                self.erwarte_z(Z::RundZu)?;
                self.erwarte_kw(Kw::In)?;
                Ok(Domaene::KetteIn {
                    a,
                    b,
                    ort: self.place()?,
                })
            }
            Art::Wort(Kw::Descendants) => {
                self.pos += 1;
                self.erwarte_kw(Kw::Of)?;
                Ok(Domaene::NachfahrenVon(self.place()?))
            }
            Art::Wort(Kw::Queue) => {
                self.pos += 1;
                Ok(Domaene::Schlange(self.place()?))
            }
            Art::Wort(Kw::Fields) => {
                self.pos += 1;
                self.erwarte_kw(Kw::Of)?;
                Ok(Domaene::FelderVon(self.pfad()?))
            }
            Art::Wort(Kw::Elems) => {
                self.pos += 1;
                self.erwarte_kw(Kw::Of)?;
                Ok(Domaene::ElementeVon(self.place()?))
            }
            Art::Wort(Kw::Threads) => {
                self.pos += 1;
                Ok(Domaene::Threads)
            }
            Art::Wort(Kw::Mappings) => {
                self.pos += 1;
                self.erwarte_kw(Kw::Of)?;
                Ok(Domaene::AbbildungenVon(self.place()?))
            }
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(
                    Absage::fehler(
                        "P013",
                        t.span,
                        format!("Quantorendomaene erwartet, {gefunden} gefunden"),
                    )
                    .mit_notiz(
                        "acht Domaenen, geschlossen: slots of · chain(a,b) in · descendants of \
                         · queue · fields of · elems of · threads · mappings of",
                    )
                    .mit_notiz(
                        "es gibt keine benutzerdefinierte Domaene -- was hier herausfaellt, \
                         ist NICHT formulierbar (SYNTAX.md §5)",
                    ),
                );
                Err(Abbruch)
            }
        }
    }

    fn predlist(&mut self) -> Erg<Vec<Pred>> {
        let mut liste = vec![self.pred()?];
        while self.friss_z(Z::Komma) {
            liste.push(self.pred()?);
        }
        Ok(liste)
    }

    // -- 6. Funktionen ---------------------------------------------------------------------

    fn fndecl(&mut self, oeffentlich: bool) -> Erg<FnDecl> {
        let anfang = self.span();
        let klasse = match self.blick().art {
            Art::Wort(Kw::Spec) => Some(FnKlasse::Spec),
            Art::Wort(Kw::Impl) => Some(FnKlasse::Impl),
            Art::Wort(Kw::Raw) => Some(FnKlasse::Raw),
            Art::Wort(Kw::Divergent) => Some(FnKlasse::Divergent),
            Art::Wort(Kw::Prim) => Some(FnKlasse::Prim),
            Art::Wort(Kw::Extern) => Some(FnKlasse::Extern),
            _ => None,
        };
        if klasse.is_some() {
            self.pos += 1;
        }
        self.erwarte_kw(Kw::Fn)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::RundAuf)?;
        let parameter = if self.ist_z(Z::RundZu) {
            Vec::new()
        } else {
            self.params()?
        };
        self.erwarte_z(Z::RundZu)?;
        let ergebnis = if self.friss_z(Z::Pfeil) {
            Some(self.typeexpr()?)
        } else {
            None
        };
        // E4: die Klauseln stehen in FESTER Reihenfolge -- ein Werkzeug, das sortieren muss,
        // kann nicht sagen „hier fehlt `effects`".
        let requires = if self.friss_kw(Kw::Requires) {
            self.predlist()?
        } else {
            Vec::new()
        };
        let ensures = if self.friss_kw(Kw::Ensures) {
            self.predlist()?
        } else {
            Vec::new()
        };
        let maintains = if self.friss_kw(Kw::Maintains) {
            self.identlist()?
        } else {
            Vec::new()
        };
        let effects = if self.ist_kw(Kw::Effects) {
            Some(self.effects_block()?)
        } else {
            None
        };
        let costs = if self.friss_kw(Kw::Costs) {
            self.erwarte_z(Z::KleinerGleich)?;
            let e = self.expr()?;
            self.erwarte_kw(Kw::Ops)?;
            Some(e)
        } else {
            None
        };
        let by = if self.friss_kw(Kw::By) {
            self.inductlist()?
        } else {
            Vec::new()
        };
        let section = if self.friss_kw(Kw::Section) {
            Some(self.erwarte_text()?)
        } else {
            None
        };
        let arch = if self.friss_kw(Kw::Arch) {
            Some(self.erwarte_ident()?)
        } else {
            None
        };
        let when = if self.friss_kw(Kw::When) {
            Some(self.expr()?)
        } else {
            None
        };
        let rumpf = if self.ist_z(Z::GeschweiftAuf) {
            FnRumpf::Block(self.block()?)
        } else if self.friss_z(Z::Gleich) {
            let p = self.pred()?;
            self.erwarte_z(Z::Semi)?;
            FnRumpf::Pred(p)
        } else {
            self.erwarte_z(Z::Semi)?;
            FnRumpf::Keiner
        };
        Ok(FnDecl {
            oeffentlich,
            klasse,
            name,
            parameter,
            ergebnis,
            requires,
            ensures,
            maintains,
            effects,
            costs,
            by,
            section,
            arch,
            when,
            rumpf,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    fn effects_block(&mut self) -> Erg<Wirkungen> {
        let anfang = self.erwarte_kw(Kw::Effects)?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let liste = self.efflist()?;
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(Wirkungen {
            liste,
            span: anfang.bis_zu(ende),
        })
    }

    fn efflist(&mut self) -> Erg<Vec<Wirkung>> {
        let mut liste = vec![self.eff()?];
        while self.friss_z(Z::Komma) {
            liste.push(self.eff()?);
        }
        Ok(liste)
    }

    fn eff(&mut self) -> Erg<Wirkung> {
        let t = self.blick();
        let art = match t.art {
            Art::Wort(Kw::Reads) => {
                self.pos += 1;
                WirkungArt::Liest(self.place()?)
            }
            Art::Wort(Kw::Writes) => {
                self.pos += 1;
                WirkungArt::Schreibt(self.place()?)
            }
            Art::Wort(Kw::Locks) => {
                self.pos += 1;
                WirkungArt::Sperrt(self.place()?)
            }
            Art::Wort(Kw::Masks) => {
                self.pos += 1;
                WirkungArt::Maskiert(self.erwarte_ident()?)
            }
            Art::Wort(Kw::Allocs) => {
                self.pos += 1;
                WirkungArt::Belegt(self.erwarte_ident()?)
            }
            Art::Wort(Kw::Consumes) => {
                self.pos += 1;
                WirkungArt::Verbraucht(self.place()?)
            }
            Art::Wort(Kw::Publishes) => {
                self.pos += 1;
                WirkungArt::Veroeffentlicht(self.place()?)
            }
            Art::Wort(Kw::Diverges) => {
                self.pos += 1;
                WirkungArt::Divergiert
            }
            Art::Wort(Kw::Pure) => {
                self.pos += 1;
                WirkungArt::Rein
            }
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(
                    Absage::fehler(
                        "P014",
                        t.span,
                        format!("Wirkung erwartet, {gefunden} gefunden"),
                    )
                    .mit_notiz(
                        "reads writes locks masks allocs consumes publishes diverges pure",
                    ),
                );
                return Err(Abbruch);
            }
        };
        Ok(Wirkung {
            art,
            span: t.span.bis_zu(self.vorheriger_span()),
        })
    }

    fn inductlist(&mut self) -> Erg<Vec<Induktion>> {
        let mut liste = vec![self.induct()?];
        while self.friss_z(Z::Komma) {
            liste.push(self.induct()?);
        }
        Ok(liste)
    }

    fn induct(&mut self) -> Erg<Induktion> {
        let anfang = self.erwarte_kw(Kw::Induction)?;
        self.erwarte_kw(Kw::Over)?;
        let domaene = self.domain()?;
        Ok(Induktion {
            domaene,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    // -- 7. Anweisungen --------------------------------------------------------------------

    fn block(&mut self) -> Erg<Block> {
        let anfang = self.erwarte_z(Z::GeschweiftAuf)?;
        let mut anweisungen = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            match self.stmt() {
                Ok(s) => anweisungen.push(s),
                Err(e) => {
                    // Eine kaputte Anweisung kostet die Anweisung, nicht die Funktion:
                    // sonst zeigt ein Lauf einen Befund und verschweigt die neun dahinter.
                    // Im Rueckversuch wird nicht erholt -- dort ist der Abbruch das Ergebnis.
                    if self.stumm > 0 || !self.synchronisiere_anweisung() {
                        return Err(e);
                    }
                }
            }
        }
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(Block {
            anweisungen,
            span: anfang.bis_zu(ende),
        })
    }

    /// Nach einer kaputten Anweisung bis hinter das naechste `;` derselben Ebene gehen --
    /// oder bis vor das `}`, das den Block schliesst.
    fn synchronisiere_anweisung(&mut self) -> bool {
        let start = self.pos;
        let mut tiefe = 0i32;
        while !self.ende() {
            match self.blick().art {
                Art::Zeichen(Z::GeschweiftAuf) => tiefe += 1,
                Art::Zeichen(Z::GeschweiftZu) => {
                    if tiefe == 0 {
                        return self.pos > start;
                    }
                    tiefe -= 1;
                    // Ein Block als Anweisung endet mit seiner Klammer.
                    if tiefe == 0 {
                        self.pos += 1;
                        return true;
                    }
                }
                Art::Zeichen(Z::Semi) if tiefe == 0 => {
                    self.pos += 1;
                    return true;
                }
                _ => {}
            }
            self.pos += 1;
        }
        self.pos > start
    }

    fn stmt(&mut self) -> Erg<Stmt> {
        let anfang = self.span();
        if self.ist_z(Z::Semi) {
            self.absage(
                Absage::fehler("P033", anfang, "ein Semikolon allein ist keine Anweisung")
                    .mit_notiz(
                        "die Formen mit Block -- `if`, `match`, `traverse`, `retry`, \
                         `forever`, `breaking`, `narrow … else`, `locks`, `let … else` -- \
                         tragen KEIN abschliessendes Semikolon",
                    ),
            );
            return Err(Abbruch);
        }
        // Abweisen, nie deuten: die Formen, die es absichtlich nicht gibt, bekommen ihre
        // eigene Absage statt eines Folgefehlers drei Token weiter.
        if self.blick().art == Art::Ident {
            let wort = self.blick().text(self.quelle);
            if let Some(grund) = abgeschaffte_form(wort) {
                self.absage(
                    Absage::fehler("P035", anfang, format!("`{wort}` gibt es in Gabbro nicht"))
                        .mit_notiz(grund)
                        .mit_notiz("SYNTAX.md, „Was es absichtlich nicht gibt\u{201c}"),
                );
                return Err(Abbruch);
            }
        }
        let art = match self.blick().art {
            Art::Wort(Kw::Let) => self.letform()?,
            Art::Wort(Kw::If) => StmtArt::Wenn(self.ifstmt()?),
            Art::Wort(Kw::Match) => StmtArt::Match(self.matchstmt()?),
            Art::Wort(Kw::Traverse) => {
                StmtArt::Schleife(Box::new(Schleife::Traverse(self.traverse()?)))
            }
            Art::Wort(Kw::Retry) => StmtArt::Schleife(Box::new(Schleife::Retry(self.retry()?))),
            Art::Wort(Kw::Forever) => {
                StmtArt::Schleife(Box::new(Schleife::Forever(self.forever()?)))
            }
            Art::Wort(Kw::Breaking) => {
                self.pos += 1;
                let invarianten = self.identlist()?;
                let rumpf = self.block()?;
                StmtArt::Bricht(BrichtStmt {
                    invarianten,
                    rumpf,
                })
            }
            Art::Wort(Kw::Narrow) => {
                self.pos += 1;
                let ort = self.place()?;
                self.erwarte_kw(Kw::To)?;
                let bereich = self.range()?;
                self.erwarte_kw(Kw::Else)?;
                let sonst = self.block()?;
                StmtArt::Narrow(NarrowStmt {
                    ort,
                    bereich,
                    sonst,
                })
            }
            Art::Wort(Kw::Locks) => {
                self.pos += 1;
                let sperre = self.place()?;
                let rumpf = self.block()?;
                StmtArt::Sperrt(SperrtStmt { sperre, rumpf })
            }
            Art::Wort(Kw::Leave) => {
                self.pos += 1;
                let n = self.erwarte_ident()?;
                self.erwarte_z(Z::Semi)?;
                StmtArt::Leave(n)
            }
            Art::Wort(Kw::Next) => {
                self.pos += 1;
                let n = self.erwarte_ident()?;
                self.erwarte_z(Z::Semi)?;
                StmtArt::Next(n)
            }
            Art::Wort(Kw::Return) => {
                self.pos += 1;
                let wert = if self.ist_z(Z::Semi) {
                    None
                } else {
                    Some(self.expr()?)
                };
                self.erwarte_z(Z::Semi)?;
                StmtArt::Return(wert)
            }
            _ => self.zuweisung_oder_ruf()?,
        };
        Ok(Stmt {
            art,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    /// Vier Formen fangen mit `let` an: `letstmt`, `letstmt … else`, `awaitload`, `exchstmt`.
    /// Unterschieden wird **nach** dem `=`, an dem Wort, das dem ersten Ausdruck folgt.
    fn letform(&mut self) -> Erg<StmtArt> {
        self.erwarte_kw(Kw::Let)?;
        let veraenderlich = self.friss_kw(Kw::Mut);
        let name = self.erwarte_ident()?;
        let typ = if self.friss_z(Z::Kolon) {
            Some(self.typeexpr()?)
        } else {
            None
        };
        self.erwarte_z(Z::Gleich)?;

        let wert = self.expr()?;

        if self.ist_kw(Kw::Awaits) {
            let ExprArt::Ort(quelle) = wert.art else {
                self.absage(Absage::fehler(
                    "P015",
                    wert.span,
                    "vor `awaits` steht ein Ort, kein zusammengesetzter Ausdruck",
                ));
                return Err(Abbruch);
            };
            self.pos += 1;
            self.erwarte_z(Z::GeschweiftAuf)?;
            let erwartet = self.placelist()?;
            self.erwarte_z(Z::GeschweiftZu)?;
            self.erwarte_z(Z::Semi)?;
            return Ok(StmtArt::AwaitLoad(AwaitLoad {
                name,
                quelle,
                erwartet,
            }));
        }

        if self.ist_kw(Kw::Exchange) {
            let ExprArt::Ort(ort) = wert.art else {
                self.absage(Absage::fehler(
                    "P015",
                    wert.span,
                    "vor `exchange` steht ein Ort, kein zusammengesetzter Ausdruck",
                ));
                return Err(Abbruch);
            };
            self.pos += 1;
            let form = self.xform()?;
            let nutzlast = if self.friss_kw(Kw::Publishes) {
                Some(self.nutzlast()?)
            } else {
                None
            };
            let erwartet = if self.friss_kw(Kw::Awaits) {
                self.erwarte_z(Z::GeschweiftAuf)?;
                let l = self.placelist()?;
                self.erwarte_z(Z::GeschweiftZu)?;
                Some(l)
            } else {
                None
            };
            self.erwarte_z(Z::Semi)?;
            return Ok(StmtArt::Exchange(Box::new(ExchangeStmt {
                name,
                ort,
                form,
                nutzlast,
                erwartet,
            })));
        }

        if self.ist_kw(Kw::Else) {
            let ExprArt::Ruf(ruf) = wert.art else {
                self.absage(
                    Absage::fehler(
                        "P016",
                        wert.span,
                        "`let … else` traegt einen Aufruf, keinen anderen Ausdruck",
                    )
                    .mit_notiz("`letstmt = \"let\" ident \"=\" call \"else\" \"(\" ident \")\" block`"),
                );
                return Err(Abbruch);
            };
            self.pos += 1;
            self.erwarte_z(Z::RundAuf)?;
            let fehlername = self.erwarte_ident()?;
            self.erwarte_z(Z::RundZu)?;
            let sonst = self.block()?;
            return Ok(StmtArt::LetSonst(LetSonst {
                name,
                ruf,
                fehlername,
                sonst,
            }));
        }

        self.erwarte_z(Z::Semi)?;
        Ok(StmtArt::Let(LetStmt {
            veraenderlich,
            name,
            typ,
            wert,
        }))
    }

    fn xform(&mut self) -> Erg<XForm> {
        if self.friss_kw(Kw::Update) {
            self.erwarte_z(Z::RundAuf)?;
            let binder = self.erwarte_ident()?;
            self.erwarte_z(Z::RundZu)?;
            let rumpf = self.block()?;
            Ok(XForm::Update { binder, rumpf })
        } else {
            let wert = self.expr()?;
            self.erwarte_kw(Kw::When)?;
            let bedingung = self.pred()?;
            self.erwarte_kw(Kw::Returns)?;
            let ergebnis = self.erwarte_ident()?;
            Ok(XForm::Vergleich {
                wert,
                bedingung,
                ergebnis,
            })
        }
    }

    /// `( placelist | "nothing" )` -- **ohne** geschweifte Klammern (SYNTAX.md §11).
    ///
    /// Die Beispiele derselben Datei schreiben sie **mit** (`publishes { color_report }`),
    /// und der Parser hat lange nur diese Form genommen: die EBNF-treue fiel, die
    /// EBNF-fremde kam durch. Jetzt gehen beide, und die Klammerform sagt es (`P032`).
    fn nutzlast(&mut self) -> Erg<Nutzlast> {
        if self.ist_kw(Kw::Nothing) {
            let t = self.vor();
            return Ok(Nutzlast::Nichts(t.span));
        }
        if self.ist_z(Z::GeschweiftAuf) {
            let auf = self.vor().span;
            let liste = self.placelist()?;
            let zu = self.erwarte_z(Z::GeschweiftZu)?;
            self.absage(
                Absage::hinweis(
                    "P032",
                    auf.bis_zu(zu),
                    "`publishes { … }` steht nicht in der EBNF",
                )
                .mit_notiz(
                    "SYNTAX.md §11: `publishes ( placelist | \"nothing\" )` -- ohne Klammern; \
                     die Beispiele derselben Datei schreiben sie mit",
                )
                .mit_notiz("angenommen; die Grammatik ist an dieser Stelle nachzuziehen"),
            );
            return Ok(Nutzlast::Orte(liste));
        }
        Ok(Nutzlast::Orte(self.placelist()?))
    }

    fn zuweisung_oder_ruf(&mut self) -> Erg<StmtArt> {
        // Ein Aufruf traegt einen Pfad, eine Zuweisung einen Ort. Beide fangen mit einem
        // Bezeichner an; die Klammer entscheidet.
        let erste = self.erwarte_ident()?;
        if self.ist_z(Z::Kolon2) || self.ist_z(Z::RundAuf) {
            let mut teile = vec![erste];
            while self.friss_z(Z::Kolon2) {
                teile.push(self.erwarte_feldname()?);
            }
            let span = teile[0].span.bis_zu(self.vorheriger_span());
            let pfad = Pfad { teile, span };
            let ruf = self.ruf_ab(pfad)?;
            self.erwarte_z(Z::Semi)?;
            return Ok(StmtArt::Ruf(ruf));
        }
        let ziel = self.place_ab(erste)?;
        let t = self.blick();
        let op = match t.art {
            Art::Zeichen(Z::Gleich) => ZuwOp::Setzt,
            Art::Zeichen(Z::PlusGleich) => ZuwOp::Plus,
            Art::Zeichen(Z::MinusGleich) => ZuwOp::Minus,
            Art::Zeichen(Z::UndGleich) => ZuwOp::Und,
            Art::Zeichen(Z::StrichGleich) => ZuwOp::Oder,
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(
                    Absage::fehler(
                        "P017",
                        t.span,
                        format!("Zuweisung oder Aufruf erwartet, {gefunden} gefunden"),
                    )
                    .mit_notiz("E2: eine Zuweisung ist kein Ausdruck"),
                );
                return Err(Abbruch);
            }
        };
        self.pos += 1;
        let wert = self.expr()?;
        if self.ist_kw(Kw::Publishes) {
            self.pos += 1;
            let nutzlast = self.nutzlast()?;
            self.erwarte_z(Z::Semi)?;
            if op != ZuwOp::Setzt {
                self.absage(Absage::fehler(
                    "P018",
                    t.span,
                    "eine Veroeffentlichung steht an `=`, nicht an einer Rechenzuweisung",
                ));
                return Err(Abbruch);
            }
            return Ok(StmtArt::Publish(PublishStmt {
                ziel,
                wert,
                nutzlast,
            }));
        }
        self.erwarte_z(Z::Semi)?;
        Ok(StmtArt::Zuweisung(Zuweisung { ziel, op, wert }))
    }

    fn ifstmt(&mut self) -> Erg<WennStmt> {
        self.erwarte_kw(Kw::If)?;
        let bed = self.expr()?;
        let rumpf = self.block()?;
        let mut zweige = vec![(bed, rumpf)];
        let mut sonst = None;
        while self.ist_kw(Kw::Else) {
            self.pos += 1;
            if self.friss_kw(Kw::If) {
                let b = self.expr()?;
                let r = self.block()?;
                zweige.push((b, r));
            } else {
                sonst = Some(self.block()?);
                break;
            }
        }
        Ok(WennStmt { zweige, sonst })
    }

    fn matchstmt(&mut self) -> Erg<MatchStmt> {
        self.erwarte_kw(Kw::Match)?;
        let gegenstand = self.expr()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut zweige = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            let anfang = self.span();
            let variante = self.erwarte_ident()?;
            let binder = if self.friss_z(Z::RundAuf) {
                let b = self.erwarte_ident()?;
                self.erwarte_z(Z::RundZu)?;
                Some(b)
            } else {
                None
            };
            self.erwarte_z(Z::Doppelpfeil)?;
            let rumpf = self.block()?;
            zweige.push(MatchZweig {
                variante,
                binder,
                rumpf,
                span: anfang.bis_zu(self.vorheriger_span()),
            });
        }
        self.erwarte_z(Z::GeschweiftZu)?;
        Ok(MatchStmt {
            gegenstand,
            zweige,
        })
    }

    // -- 8. Schleifen ----------------------------------------------------------------------

    fn traverse(&mut self) -> Erg<Traverse> {
        let anfang = self.erwarte_kw(Kw::Traverse)?;
        let variable = self.erwarte_ident()?;
        let gegenstand = if self.friss_kw(Kw::Of) {
            Some(self.expr()?)
        } else {
            None
        };
        self.erwarte_kw(Kw::Over)?;
        let domaene = self.domain()?;
        self.erwarte_kw(Kw::By)?;
        let abstieg = match self.blick().art {
            Art::Wort(Kw::Unvisited) => {
                self.pos += 1;
                Abstieg::Unbesucht
            }
            Art::Wort(Kw::Consuming) => {
                self.pos += 1;
                Abstieg::Verbrauchend
            }
            Art::Wort(Kw::Decreasing) => {
                self.pos += 1;
                Abstieg::Fallend(self.expr()?)
            }
            _ => {
                let t = self.blick();
                let gefunden = t.benennung(self.quelle);
                self.absage(
                    Absage::fehler(
                        "P019",
                        t.span,
                        format!("Abstiegsmass erwartet, {gefunden} gefunden"),
                    )
                    .mit_notiz("`by unvisited` · `by consuming` · `by decreasing expr`"),
                );
                return Err(Abbruch);
            }
        };
        let touches = if self.friss_kw(Kw::Touches) {
            let liste = self.efflist()?;
            Some(Wirkungen {
                span: liste[0].span.bis_zu(self.vorheriger_span()),
                liste,
            })
        } else {
            None
        };
        let rumpf = self.block()?;
        Ok(Traverse {
            variable,
            gegenstand,
            domaene,
            abstieg,
            touches,
            rumpf,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    fn retry(&mut self) -> Erg<Retry> {
        let anfang = self.erwarte_kw(Kw::Retry)?;
        let marke = if matches!(self.blick().art, Art::Ident) {
            Some(self.erwarte_ident()?)
        } else {
            None
        };
        let bis = if self.friss_kw(Kw::Until) {
            Some(self.pred()?)
        } else {
            None
        };
        self.erwarte_kw(Kw::Bounded)?;
        let schranke = self.expr()?;
        self.erwarte_kw(Kw::Ops)?;
        let fortschritt = if self.friss_kw(Kw::Progress) {
            Some(self.erwarte_ident()?)
        } else {
            None
        };
        self.erwarte_kw(Kw::OnExceeded)?;
        let bei_ueberschreitung = self.erwarte_ident()?;
        let effects = if self.ist_kw(Kw::Effects) {
            Some(self.effects_block()?)
        } else {
            None
        };
        let rumpf = self.block()?;
        Ok(Retry {
            marke,
            bis,
            schranke,
            fortschritt,
            bei_ueberschreitung,
            effects,
            rumpf,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    fn forever(&mut self) -> Erg<Forever> {
        let anfang = self.erwarte_kw(Kw::Forever)?;
        let marke = if matches!(self.blick().art, Art::Ident) {
            Some(self.erwarte_ident()?)
        } else {
            None
        };
        self.erwarte_kw(Kw::PerPass)?;
        self.erwarte_kw(Kw::Bounded)?;
        let je_durchgang = self.expr()?;
        self.erwarte_kw(Kw::Ops)?;
        self.erwarte_kw(Kw::OnExceeded)?;
        let bei_ueberschreitung = self.erwarte_ident()?;
        let effects = self.effects_block()?;
        let fortschritt = if self.friss_kw(Kw::Progress) {
            Some(self.erwarte_ident()?)
        } else {
            None
        };
        let verlaesst = if self.friss_kw(Kw::Leaves) {
            self.identlist()?
        } else {
            Vec::new()
        };
        let rumpf = self.block()?;
        Ok(Forever {
            marke,
            je_durchgang,
            bei_ueberschreitung,
            effects,
            fortschritt,
            verlaesst,
            rumpf,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    // -- 9. Tabellen, Formate --------------------------------------------------------------

    fn table(&mut self) -> Erg<Tabelle> {
        let anfang = self.erwarte_kw(Kw::Table)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut konstanten = Vec::new();
        let mut slot = None;
        let mut invarianten = Vec::new();
        let mut ops = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            match self.blick().art {
                Art::Wort(Kw::Const) => konstanten.push(self.constdecl(false)?),
                Art::Wort(Kw::Slot) => {
                    let s = self.slotdecl()?;
                    if slot.is_some() {
                        self.absage(Absage::fehler(
                            "P020",
                            s.span,
                            "`table` kennt genau ein `slot`-Wort",
                        ));
                        return Err(Abbruch);
                    }
                    slot = Some(s);
                }
                Art::Wort(Kw::Invariant) => invarianten.push(self.invariant()?),
                Art::Wort(Kw::Ops) => {
                    self.pos += 1;
                    ops.extend(self.identlist()?);
                    self.erwarte_z(Z::Semi)?;
                }
                _ => {
                    let t = self.blick();
                    let gefunden = t.benennung(self.quelle);
                    self.absage(
                        Absage::fehler(
                            "P021",
                            t.span,
                            format!("im `table`-Rumpf erwartet: const, slot, invariant, ops -- {gefunden} gefunden"),
                        ),
                    );
                    return Err(Abbruch);
                }
            }
        }
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(Tabelle {
            name,
            konstanten,
            slot,
            invarianten,
            ops,
            span: anfang.bis_zu(ende),
        })
    }

    fn slotdecl(&mut self) -> Erg<SlotDecl> {
        let anfang = self.erwarte_kw(Kw::Slot)?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut felder = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            let name = self.erwarte_feldname()?;
            self.erwarte_z(Z::Kolon)?;
            let typ = self.slottype()?;
            self.erwarte_z(Z::Komma)?;
            felder.push(SlotFeld {
                span: name.span.bis_zu(self.vorheriger_span()),
                name,
                typ,
            });
        }
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(SlotDecl {
            felder,
            span: anfang.bis_zu(ende),
        })
    }

    fn slottype(&mut self) -> Erg<SlotTyp> {
        if self.friss_kw(Kw::Index) {
            self.erwarte_kw(Kw::Into)?;
            return Ok(SlotTyp::Index(self.erwarte_ident()?));
        }
        if self.friss_kw(Kw::Option) {
            self.erwarte_kw(Kw::Index)?;
            self.erwarte_kw(Kw::Into)?;
            return Ok(SlotTyp::OptionIndex(self.erwarte_ident()?));
        }
        if let Art::Wort(k) = self.blick().art {
            if k.ist_intty() {
                let ity = self.intty()?;
                if self.friss_kw(Kw::Wrapping) {
                    return Ok(SlotTyp::Wrapping(ity));
                }
                return Ok(SlotTyp::Typ(TypExpr::Int(ity)));
            }
        }
        Ok(SlotTyp::Typ(self.typeexpr()?))
    }

    fn invariant(&mut self) -> Erg<Invariante> {
        let anfang = self.erwarte_kw(Kw::Invariant)?;
        let name = self.erwarte_ident()?;
        self.erwarte_kw(Kw::Cost)?;
        let kosten = self.costexpr()?;
        self.erwarte_kw(Kw::Runs)?;
        let laeuft = if self.friss_kw(Kw::Online) {
            Laeuft::Online
        } else {
            self.erwarte_kw(Kw::Offline)?;
            Laeuft::Offline
        };
        let by = if self.friss_kw(Kw::By) {
            self.inductlist()?
        } else {
            Vec::new()
        };
        self.erwarte_z(Z::Kolon)?;
        let pred = self.pred()?;
        self.erwarte_z(Z::Semi)?;
        Ok(Invariante {
            name,
            kosten,
            laeuft,
            by,
            pred,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    /// `costexpr = "O" "(" expr ")"` -- `O` ist ein Grossbuchstabe und damit kein Wort des
    /// Wortschatzes; hier steht er als Bezeichner in fester Stellung.
    fn costexpr(&mut self) -> Erg<Expr> {
        let t = self.blick();
        let name = self.erwarte_ident()?;
        if name.text != "O" {
            self.absage(
                Absage::fehler(
                    "P022",
                    t.span,
                    format!("Kostenangabe faengt mit `O` an, `{}` gefunden", name.text),
                )
                .mit_notiz("`costexpr = \"O\" \"(\" expr \")\"`"),
            );
            return Err(Abbruch);
        }
        self.erwarte_z(Z::RundAuf)?;
        let e = self.expr()?;
        self.erwarte_z(Z::RundZu)?;
        Ok(e)
    }

    fn walkdecl(&mut self) -> Erg<WalkDecl> {
        let anfang = self.erwarte_kw(Kw::Walk)?;
        let name = self.erwarte_ident()?;
        self.erwarte_kw(Kw::Levels)?;
        let ebenen = self.expr()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        self.erwarte_kw(Kw::Node)?;
        self.erwarte_z(Z::Kolon)?;
        let knoten = match self.typeexpr()? {
            TypExpr::Feld(a) => *a,
            anderes => {
                self.absage(Absage::fehler(
                    "P023",
                    anderes.span(),
                    "`node` einer `walk`-Deklaration ist ein Feld `[T; N]`",
                ));
                return Err(Abbruch);
            }
        };
        self.erwarte_z(Z::Komma)?;
        self.erwarte_kw(Kw::Down)?;
        self.erwarte_z(Z::Kolon)?;
        let ab = self.erwarte_feldname()?;
        self.erwarte_kw(Kw::When)?;
        let ab_wenn = self.pred()?;
        self.erwarte_z(Z::Komma)?;
        self.erwarte_kw(Kw::Leaf)?;
        self.erwarte_z(Z::Kolon)?;
        let blatt = self.pred()?;
        self.erwarte_z(Z::Komma)?;
        let mut invarianten = Vec::new();
        while self.ist_kw(Kw::Invariant) {
            invarianten.push(self.invariant()?);
        }
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(WalkDecl {
            name,
            ebenen,
            knoten,
            ab,
            ab_wenn,
            blatt,
            invarianten,
            span: anfang.bis_zu(ende),
        })
    }

    fn format(&mut self) -> Erg<Format> {
        let anfang = self.erwarte_kw(Kw::Format)?;
        let name = self.erwarte_ident()?;
        let mut version = None;
        if self.ist_z(Z::At) {
            let at = self.vor().span;
            let wort = self.erwarte_feldname()?;
            if wort.text != "version" {
                self.absage(Absage::fehler(
                    "P024",
                    at.bis_zu(wort.span),
                    format!("`@version` erwartet, `@{}` gefunden", wort.text),
                ));
                return Err(Abbruch);
            }
            version = Some(self.erwarte_zahl()?.0);
        }
        let endian = if self.friss_kw(Kw::Endian) {
            if self.friss_kw(Kw::Little) {
                Some(Endian::Klein)
            } else {
                self.erwarte_kw(Kw::Big)?;
                Some(Endian::Gross)
            }
        } else {
            None
        };
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut felder = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            felder.push(self.field()?);
        }
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(Format {
            name,
            version,
            endian,
            felder,
            span: anfang.bis_zu(ende),
        })
    }

    fn reason(&mut self) -> Erg<Reason> {
        let anfang = self.erwarte_kw(Kw::Reason)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut faelle = Vec::new();
        let mut erschoepfend = false;
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            if self.ist_kw(Kw::Exhaustive) {
                self.pos += 1;
                erschoepfend = true;
                continue;
            }
            let fname = self.erwarte_ident()?;
            self.erwarte_z(Z::Gleich)?;
            let (wert, _) = self.erwarte_zahl()?;
            let text = self.erwarte_text()?;
            faelle.push(ReasonFall {
                span: fname.span.bis_zu(text.span),
                name: fname,
                wert,
                text,
            });
        }
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(Reason {
            name,
            faelle,
            erschoepfend,
            span: anfang.bis_zu(ende),
        })
    }

    fn statedecl(&mut self) -> Erg<StateDecl> {
        let anfang = self.erwarte_kw(Kw::State)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut uebergaenge = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            uebergaenge.push(self.transition()?);
        }
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(StateDecl {
            name,
            uebergaenge,
            span: anfang.bis_zu(ende),
        })
    }

    // -- 10. Geraete -----------------------------------------------------------------------

    fn device(&mut self) -> Erg<Device> {
        let anfang = self.erwarte_kw(Kw::Device)?;
        let name = self.erwarte_ident()?;
        let parameter = if self.friss_z(Z::RundAuf) {
            let p = if self.ist_z(Z::RundZu) {
                Vec::new()
            } else {
                self.params()?
            };
            self.erwarte_z(Z::RundZu)?;
            p
        } else {
            Vec::new()
        };
        self.erwarte_kw(Kw::At)?;
        let raum = self.space()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut mirrors = None;
        let mut register = Vec::new();
        let mut baenke = Vec::new();
        let mut uebergaenge = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            match self.blick().art {
                Art::Wort(Kw::Mirrors) => {
                    let m_anfang = self.vor().span;
                    let ziel = self.place()?;
                    self.erwarte_kw(Kw::From)?;
                    let quelle = self.place()?;
                    let m_ende = self.erwarte_z(Z::Semi)?;
                    if mirrors.is_some() {
                        self.absage(
                            Absage::fehler(
                                "P025",
                                m_anfang.bis_zu(m_ende),
                                "`mirrors` steht EINMAL je Geraet",
                            )
                            .mit_notiz("SYNTAX.md §10: nicht je Uebergang"),
                        );
                        return Err(Abbruch);
                    }
                    mirrors = Some(Mirrors {
                        ziel,
                        quelle,
                        span: m_anfang.bis_zu(m_ende),
                    });
                }
                Art::Wort(Kw::Reg) => register.push(self.regdecl()?),
                Art::Wort(Kw::Bank) => baenke.push(self.bank()?),
                Art::Wort(Kw::Transition) => uebergaenge.push(self.transition()?),
                _ => {
                    let t = self.blick();
                    let gefunden = t.benennung(self.quelle);
                    self.absage(Absage::fehler(
                        "P026",
                        t.span,
                        format!(
                            "im `device`-Rumpf erwartet: mirrors, reg, bank, transition -- \
                             {gefunden} gefunden"
                        ),
                    ));
                    return Err(Abbruch);
                }
            }
        }
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(Device {
            name,
            parameter,
            raum,
            mirrors,
            register,
            baenke,
            uebergaenge,
            span: anfang.bis_zu(ende),
        })
    }

    fn regdecl(&mut self) -> Erg<RegDecl> {
        let anfang = self.erwarte_kw(Kw::Reg)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::Kolon)?;
        let typ = self.intty()?;
        self.erwarte_z(Z::At)?;
        let versatz = self.expr()?;
        self.erwarte_kw(Kw::Class)?;
        let t = self.blick();
        let klasse = match t.art {
            Art::Wort(Kw::R) => RegKlasse::Lesen,
            Art::Wort(Kw::W) => RegKlasse::Schreiben,
            Art::Wort(Kw::Rw) => RegKlasse::LesenSchreiben,
            Art::Wort(Kw::W1c) => RegKlasse::W1c,
            Art::Wort(Kw::Rc) => RegKlasse::Rc,
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(
                    Absage::fehler(
                        "P027",
                        t.span,
                        format!("Registerklasse erwartet, {gefunden} gefunden"),
                    )
                    .mit_notiz("`r` `w` `rw` `w1c` `rc`"),
                );
                return Err(Abbruch);
            }
        };
        self.pos += 1;
        let mut felder = Vec::new();
        if self.friss_kw(Kw::Fields) {
            self.erwarte_z(Z::GeschweiftAuf)?;
            while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
                let fname = self.erwarte_feldname()?;
                self.erwarte_z(Z::At)?;
                let bp = self.bitpos()?;
                felder.push((fname, bp));
                if !self.friss_z(Z::Komma) {
                    break;
                }
            }
            self.erwarte_z(Z::GeschweiftZu)?;
        }
        let requires = if self.friss_kw(Kw::Requires) {
            Some(self.pred()?)
        } else {
            None
        };
        Ok(RegDecl {
            name,
            typ,
            versatz,
            klasse,
            felder,
            requires,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    fn bank(&mut self) -> Erg<Bank> {
        let anfang = self.erwarte_kw(Kw::Bank)?;
        let name = self.erwarte_ident()?;
        self.erwarte_kw(Kw::At)?;
        let basis = self.expr()?;
        self.erwarte_kw(Kw::Stride)?;
        let schritt = self.expr()?;
        self.erwarte_kw(Kw::Count)?;
        let anzahl = self.expr()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut register = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            register.push(self.regdecl()?);
        }
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(Bank {
            name,
            basis,
            schritt,
            anzahl,
            register,
            span: anfang.bis_zu(ende),
        })
    }

    fn transition(&mut self) -> Erg<Uebergang> {
        let anfang = self.erwarte_kw(Kw::Transition)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut schritte = Vec::new();
        loop {
            let ort = self.place()?;
            self.erwarte_z(Z::Kolon)?;
            // Ab hier ist `->` der Uebergangspfeil und kein Ortssuffix -- s. `pfeil_ist_suffix`.
            // **Die Wiederherstellung darf kein `?` ueberspringen.** Tat sie es, blieb der
            // Schalter nach einem Fehler im ERSTEN Ausdruck stehen und machte `->` fuer den
            // Rest der Uebersetzungseinheit zum Nichtsuffix -- ein Tippfehler in einem
            // `transition` erzeugte Phantomabsagen in jeder spaeteren Zeile.
            self.pfeil_ist_suffix = false;
            let ergebnis = (|s: &mut Self| {
                let von = s.expr()?;
                s.erwarte_z(Z::Pfeil)?;
                let nach = s.expr()?;
                Ok((von, nach))
            })(self);
            self.pfeil_ist_suffix = true;
            let (von, nach) = ergebnis?;
            schritte.push(OrtSchritt {
                span: ort.span.bis_zu(nach.span),
                ort,
                von,
                nach,
            });
            if !self.friss_z(Z::Komma) {
                break;
            }
        }
        self.erwarte_z(Z::GeschweiftZu)?;
        let requires = if self.friss_kw(Kw::Requires) {
            Some(self.pred()?)
        } else {
            None
        };
        let effects = if self.ist_kw(Kw::Effects) {
            Some(self.effects_block()?)
        } else {
            None
        };
        Ok(Uebergang {
            name,
            schritte,
            requires,
            effects,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    // -- 11. Nebenlaeufigkeit --------------------------------------------------------------

    fn atomicdecl(&mut self, oeffentlich: bool) -> Erg<AtomicDecl> {
        let anfang = self.erwarte_kw(Kw::Atomic)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::Kolon)?;
        let typ = self.typeexpr()?;
        // `atomicdecl` in SYNTAX.md kennt diese Klausel NICHT -- das Beispiel zwei Zeilen
        // darunter benutzt sie, `SPRACHE.md` §11.3 verlangt sie („Die Deklaration darf
        // zusaetzlich eine Obermenge nennen"), und `FRAGMENTE.md` F6 schreibt sie achtmal.
        // Angenommen wird sie deshalb, aber nicht stumm: die EBNF ist nachzuziehen.
        let obermenge = if self.ist_kw(Kw::Publishes) {
            let stelle = self.vor().span;
            let n = self.nutzlast()?;
            self.absage(
                Absage::hinweis(
                    "P031",
                    stelle,
                    "`publishes` an einer `atomic`-Deklaration steht nicht in der EBNF",
                )
                .mit_notiz(
                    "SPRACHE.md §11.3 traegt die Klausel (die Deklaration darf zusaetzlich \
                     eine Obermenge nennen), SYNTAX.md §11 zeigt sie im Beispiel -- \
                     `atomicdecl` selbst fuehrt sie nicht",
                )
                .mit_notiz("angenommen; die Grammatik ist an dieser Stelle nachzuziehen"),
            );
            Some(n)
        } else {
            None
        };
        let ordnung = match self.blick().art {
            Art::Wort(Kw::Acquire) => Some(Ordnung::Acquire),
            Art::Wort(Kw::Release) => Some(Ordnung::Release),
            Art::Wort(Kw::Seq) => Some(Ordnung::Seq),
            Art::Wort(Kw::Relaxed) => Some(Ordnung::Relaxed),
            _ => None,
        };
        if ordnung.is_some() {
            self.pos += 1;
        }
        self.erwarte_z(Z::Semi)?;
        Ok(AtomicDecl {
            oeffentlich,
            name,
            typ,
            obermenge,
            ordnung,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    fn lockdecl(&mut self) -> Erg<LockDecl> {
        let anfang = self.erwarte_kw(Kw::Lock)?;
        let name = self.erwarte_ident()?;
        self.erwarte_kw(Kw::Protects)?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let schuetzt = self.placelist()?;
        self.erwarte_z(Z::GeschweiftZu)?;
        self.erwarte_kw(Kw::Rank)?;
        let rang = self.expr()?;
        let haltezeit = if self.friss_kw(Kw::Held) {
            self.erwarte_z(Z::KleinerGleich)?;
            let e = self.expr()?;
            self.erwarte_kw(Kw::Ops)?;
            Some(e)
        } else {
            None
        };
        let maskiert = if self.friss_kw(Kw::Masks) {
            Some(self.erwarte_ident()?)
        } else {
            None
        };
        self.erwarte_z(Z::Semi)?;
        Ok(LockDecl {
            name,
            schuetzt,
            rang,
            haltezeit,
            maskiert,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    fn accdecl(&mut self) -> Erg<AccDecl> {
        let anfang = self.erwarte_kw(Kw::Accumulates)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::Kolon)?;
        let typ = self.typeexpr()?;
        self.erwarte_kw(Kw::Merge)?;
        let t = self.blick();
        let merge = match t.art {
            Art::Wort(Kw::Max) => MergeOp::Max,
            Art::Wort(Kw::Min) => MergeOp::Min,
            Art::Wort(Kw::Add) => MergeOp::Add,
            Art::Wort(Kw::Or) => MergeOp::Or,
            Art::Wort(Kw::And) => MergeOp::And,
            _ => {
                let gefunden = t.benennung(self.quelle);
                self.absage(
                    Absage::fehler(
                        "P028",
                        t.span,
                        format!("Merge-Operation erwartet, {gefunden} gefunden"),
                    )
                    .mit_notiz("die Menge ist geschlossen: max min add or and"),
                );
                return Err(Abbruch);
            }
        };
        self.pos += 1;
        self.erwarte_z(Z::Semi)?;
        Ok(AccDecl {
            name,
            typ,
            merge,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    // -- 12. Annahmen und Axiome -----------------------------------------------------------

    fn annahmeklasse(&mut self) -> Erg<AnnahmeKlasse> {
        if self.friss_kw(Kw::Falsifier) {
            Ok(AnnahmeKlasse::Falsifizierbar(self.erwarte_ident()?))
        } else if self.friss_kw(Kw::Unfalsifiable) {
            Ok(AnnahmeKlasse::NichtFalsifizierbar(self.erwarte_text()?))
        } else {
            let t = self.blick();
            let gefunden = t.benennung(self.quelle);
            self.absage(
                Absage::fehler(
                    "P029",
                    t.span,
                    format!("`falsifier` oder `unfalsifiable` erwartet, {gefunden} gefunden"),
                )
                .mit_notiz(
                    "die dritte Klasse -- *nicht gefahren* -- ist die Abwesenheit beider \
                     Angaben und ein Uebersetzungsfehler: eine nicht gefahrene Annahme darf \
                     nie wie eine falsifizierte aussehen",
                ),
            );
            Err(Abbruch)
        }
    }

    fn assume(&mut self) -> Erg<Assume> {
        let anfang = self.erwarte_kw(Kw::Assume)?;
        let name = self.erwarte_ident()?;
        let text = self.erwarte_text()?;
        let klasse = self.annahmeklasse()?;
        self.erwarte_z(Z::Semi)?;
        Ok(Assume {
            name,
            text,
            klasse,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    fn axiom(&mut self) -> Erg<Axiom> {
        let anfang = self.erwarte_kw(Kw::Axiom)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::RundAuf)?;
        let parameter = if self.ist_z(Z::RundZu) {
            Vec::new()
        } else {
            self.params()?
        };
        self.erwarte_z(Z::RundZu)?;
        let effects = self.effects_block()?;
        let klasse = self.annahmeklasse()?;
        self.erwarte_z(Z::Semi)?;
        Ok(Axiom {
            name,
            parameter,
            effects,
            klasse,
            span: anfang.bis_zu(self.vorheriger_span()),
        })
    }

    // -- 13. `check` -----------------------------------------------------------------------

    fn check(&mut self) -> Erg<Check> {
        let anfang = self.erwarte_kw(Kw::Check)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        self.erwarte_kw(Kw::Claim)?;
        let claim = self.erwarte_text()?;
        self.erwarte_kw(Kw::Measures)?;
        let measures = self.placelist()?;
        self.erwarte_kw(Kw::Gates)?;
        let gates = self.identlist()?;
        self.erwarte_kw(Kw::CanFail)?;
        let can_fail = self.block()?;
        let floor = if self.friss_kw(Kw::Floor) {
            self.predlist()?
        } else {
            Vec::new()
        };
        let counterprobe = if self.friss_kw(Kw::Counterprobe) {
            let t = self.erwarte_text()?;
            self.erwarte_kw(Kw::Expects)?;
            let e = self.erwarte_ident()?;
            Some((t, e))
        } else {
            None
        };
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(Check {
            name,
            claim,
            measures,
            gates,
            can_fail,
            floor,
            counterprobe,
            span: anfang.bis_zu(ende),
        })
    }

    // -- 14. Eintritt und Boot -------------------------------------------------------------

    fn entrydecl(&mut self) -> Erg<EntryDecl> {
        let anfang = self.erwarte_kw(Kw::Entry)?;
        let name = self.erwarte_ident()?;
        let vektor = if self.friss_kw(Kw::Vector) {
            Some(self.expr()?)
        } else {
            None
        };
        let via = if self.friss_kw(Kw::Via) {
            Some(self.erwarte_ident()?)
        } else {
            None
        };
        self.erwarte_kw(Kw::Arch)?;
        let arch = self.erwarte_ident()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        self.erwarte_kw(Kw::Regs)?;
        self.erwarte_kw(Kw::In)?;
        let regs_in = self.regsliste()?;
        self.erwarte_kw(Kw::Regs)?;
        self.erwarte_kw(Kw::Out)?;
        let regs_out = self.regsliste()?;
        self.erwarte_kw(Kw::Preserves)?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let preserves = self.identlist()?;
        self.erwarte_z(Z::GeschweiftZu)?;
        self.erwarte_kw(Kw::Clobbers)?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let clobbers = self.identlist()?;
        self.erwarte_z(Z::GeschweiftZu)?;
        // entryextra
        self.erwarte_kw(Kw::Stack)?;
        let stack = self.erwarte_ident()?;
        let pro_kern = if self.friss_kw(Kw::Per) {
            self.erwarte_kw(Kw::Cpu)?;
            true
        } else {
            false
        };
        let ist = if self.friss_kw(Kw::Ist) {
            Some(self.expr()?)
        } else {
            None
        };
        let verschachtelt = if self.friss_kw(Kw::Nested) {
            Some(match self.blick().art {
                Art::Wort(Kw::Never) => {
                    self.pos += 1;
                    Verschachtelt::Nie
                }
                Art::Wort(Kw::Masked) => {
                    self.pos += 1;
                    Verschachtelt::Maskiert
                }
                Art::Wort(Kw::Bounded) => {
                    self.pos += 1;
                    Verschachtelt::Begrenzt(self.expr()?)
                }
                _ => {
                    let t = self.blick();
                    let gefunden = t.benennung(self.quelle);
                    self.absage(Absage::fehler(
                        "P030",
                        t.span,
                        format!("`never`, `masked` oder `bounded` erwartet, {gefunden} gefunden"),
                    ));
                    return Err(Abbruch);
                }
            })
        } else {
            None
        };
        self.erwarte_kw(Kw::Dispatch)?;
        let dispatch = self.pfad()?;
        self.erwarte_z(Z::Semi)?;
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(EntryDecl {
            name,
            vektor,
            via,
            arch,
            regs_in,
            regs_out,
            preserves,
            clobbers,
            stack,
            pro_kern,
            ist,
            verschachtelt,
            dispatch,
            span: anfang.bis_zu(ende),
        })
    }

    fn regsliste(&mut self) -> Erg<Vec<(Ident, Ident)>> {
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut liste = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            let reg = self.erwarte_ident()?;
            self.erwarte_z(Z::Kolon)?;
            let typ = self.typname_als_ident()?;
            self.erwarte_z(Z::Komma)?;
            liste.push((reg, typ));
        }
        self.erwarte_z(Z::GeschweiftZu)?;
        Ok(liste)
    }

    fn bootdecl(&mut self) -> Erg<BootDecl> {
        let anfang = self.erwarte_kw(Kw::Boot)?;
        let name = self.erwarte_ident()?;
        self.erwarte_kw(Kw::Arch)?;
        let arch = self.erwarte_ident()?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut schritte = Vec::new();
        while self.ist_kw(Kw::Step) {
            self.pos += 1;
            let erste = self.erwarte_ident()?;
            if self.ist_z(Z::RundAuf) || self.ist_z(Z::Kolon2) {
                let mut teile = vec![erste];
                while self.friss_z(Z::Kolon2) {
                    teile.push(self.erwarte_feldname()?);
                }
                let span = teile[0].span.bis_zu(self.vorheriger_span());
                let ruf = self.ruf_ab(Pfad { teile, span })?;
                schritte.push(BootSchritt::Ruf(ruf));
            } else {
                self.erwarte_z(Z::Gleich)?;
                let wert = self.expr()?;
                schritte.push(BootSchritt::Setzt { name: erste, wert });
            }
            self.erwarte_z(Z::Semi)?;
        }
        self.erwarte_kw(Kw::Dispatch)?;
        let dispatch = self.pfad()?;
        self.erwarte_z(Z::Semi)?;
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(BootDecl {
            name,
            arch,
            schritte,
            dispatch,
            span: anfang.bis_zu(ende),
        })
    }
}

/// Die Formen der Verbotsliste, jede mit ihrem Ersatz. Ohne diese Tabelle faellt `while (x) {}`
/// als „`;` erwartet" -- ein Folgefehler, der den Grund verschweigt.
fn abgeschaffte_form(wort: &str) -> Option<&'static str> {
    match wort {
        "while" | "for" | "do" | "loop" => Some(
            "es gibt drei Schleifenformen und nur diese: `traverse … over … by …`, \
             `retry … bounded … ops on_exceeded …`, `forever per_pass bounded … ops`",
        ),
        "break" => Some("die geordnete Abschaltung heisst `leave <marke>;`"),
        "continue" => Some("der naechste Durchgang heisst `next <marke>;`"),
        "goto" => Some("es gibt keinen Sprung -- der Kontrollfluss steht in der Form"),
        "switch" => Some("`match` ist erschoepfend und hat keinen Auffangzweig"),
        "unsafe" => Some(
            "unsichere Fenster gibt es nicht; was die Maschine anfasst, steht in `axiom`, \
             `raw fn` oder `prim fn` -- benannt und gezaehlt",
        ),
        _ => None,
    }
}

/// Faengt mit diesem Wort ein Item an? Auch die Erholung und der Korpuslauf fragen das.
pub fn faengt_item_an(k: Kw) -> bool {
    matches!(
        k,
        Kw::Module
            | Kw::Use
            | Kw::Type
            | Kw::Opaque
            | Kw::Linear
            | Kw::Tagged
            | Kw::Const
            | Kw::Static
            | Kw::Fn
            | Kw::Spec
            | Kw::Impl
            | Kw::Raw
            | Kw::Divergent
            | Kw::Prim
            | Kw::Extern
            | Kw::Format
            | Kw::Table
            | Kw::Reason
            | Kw::State
            | Kw::Device
            | Kw::Assume
            | Kw::Axiom
            | Kw::Check
            | Kw::Atomic
            | Kw::Lock
            | Kw::Accumulates
            | Kw::Walk
            | Kw::Entry
            | Kw::Boot
            | Kw::Pub
            | Kw::When
    )
}
