//! The parser. **Hand-written, no generator** (`SPRACHE.md` part III, §6) and laid rule by
//! rule against `SYNTAX.md`: every EBNF rule has a function carrying its name.
//!
//! **The parser does not interpret.** Where the grammar demands a clause, it demands it; where
//! the grammar leaves it optional, it leaves the field empty and hands the obligation to the
//! pass that knows it. It invents no default -- E3: nothing is implicit.
//!
//! **Two places where a word of the vocabulary may be a name after all**, both unambiguous
//! from the grammar:
//!
//! 1. **after `.` and `->`** (`placesuffix = "." ident`): no keyword can stand there, so none
//!    can be confused -- `c.slots[s]` is written that way in `FRAGMENTE.md`;
//! 2. **as a declared field name** in `field`/`slotdecl`, where the name is followed by `:`.
//!
//! Everywhere else the closed vocabulary holds: `let slot = …` is not an identifier, and the
//! refusal says so with the word and the site.

use crate::ast::*;
use crate::diag::{Absage, Absagen};
use crate::kw::Kw;
use crate::lex::{Art, Token, Z};
use crate::span::Span;

/// The parser has already filed the refusal; this is only the return jump.
#[derive(Debug, Clone, Copy)]
pub struct Abbruch;

type Erg<T> = Result<T, Abbruch>;

pub struct Parser<'a> {
    quelle: &'a str,
    tokens: Vec<Token>,
    pos: usize,
    absagen: &'a mut Absagen,
    /// During a backtracking attempt, refusals are not filed.
    stumm: usize,
    /// **The one ambiguous place in the grammar**, resolved rather than guessed.
    ///
    /// `placesuffix = "->" ident` and `placeshift = place ":" expr "->" expr` meet in
    /// `transition ack { REG: A -> B }`: `A -> B` is at once a place with field access and a
    /// transition. Inside the two expressions of a `placeshift`, `->` is therefore **not** a
    /// place suffix -- the place before it may carry one. Without this rule `FRAGMENTE.md`'s
    /// `transition drv { DEVICE_STATUS: ACK -> ACK | DRIVER }` is unreadable.
    pfeil_ist_suffix: bool,
}

/// Lexes and parses a source. Refusals accumulate in `absagen`.
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
    // -- Basic tooling ------------------------------------------------------------------

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

    /// A backtracking attempt: remember the position, try silently, reset on failure.
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

    /// A free identifier. A word of the vocabulary is **not** a name here.
    fn erwarte_ident(&mut self) -> Erg<Ident> {
        let t = self.blick();
        if t.art == Art::Ident && t.text(self.quelle) == "_" {
            self.absage(
                Absage::fehler("P034", t.span, "`_` on its own is not an identifier")
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
            // Single-letter words (`r`, `w`, `x`) are contextual -- see kw.rs.
            Art::Wort(k) if !k.reserviert() => {
                self.pos += 1;
                Ok(Ident {
                    text: k.text().to_string(),
                    span: t.span,
                })
            }
            Art::Wort(k) => {
                let mut a = Absage::fehler(
                    "P002",
                    t.span,
                    format!("`{}` is a word of the vocabulary, not an identifier", k),
                )
                .mit_notiz(
                    "SYNTAX.md: der Wortschatz ist eine geschlossene Tabelle -- \
                     alles andere ist ein Bezeichner",
                );
                // **M-woerter:** the decision was "rename rather than soften". So the burden
                // does not land on the writer, the compiler names the replacement.
                if let Some(v) = crate::kw::ersatzvorschlag(k) {
                    a = a.mit_notiz(format!("stattdessen: `{v}`"));
                }
                self.absage(a);
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

    /// A name in field position: after `.`/`->` or before `:` in a field declaration.
    /// There a word of the vocabulary is unambiguously a name -- see the head of this file.
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

    /// **«B22» geschlossen 2026-08-17: benachbarte Zeichenketten werden EINE.**
    ///
    /// Der Befund lautete: *„`claim` nimmt eine Zeichenkette, und `char` schliesst `newline`
    /// aus. Alle drei echten Behauptungen sind mehrzeilig; hier zusammengezogen. **Eine
    /// Behauptung, die in eine Zeile passen muss, wird kuerzer geschrieben, nicht genauer.**"*
    ///
    /// **Die naheliegende Reparatur waere gewesen, `newline` in der Zeichenkette zu
    /// erlauben** -- und sie haette die Pruefung mitgenommen, die dahintersteht: ein
    /// vergessenes Anfuehrungszeichen verschluckt sonst den Rest der Datei, und `L001` faende
    /// es nie. *Eine Laufzeitpruefung wegzunehmen ist ausschliesslich M1-begruendet (W6); hier
    /// waere es gar nicht begruendet gewesen.*
    ///
    /// Stattdessen: **zwei Zeichenketten nebeneinander sind eine**, mit einem Leerzeichen
    /// verbunden. Die Regel *„eine Zeichenkette endet auf ihrer Zeile"* bleibt unangetastet,
    /// und die Behauptung darf so lang werden, wie sie genau sein muss.
    ///
    /// ```gabbro
    /// claim "Am Fuss jedes EL0-Stacks bleibt ein Achtel unberuehrt,"
    ///       "und tiefste Kette plus IRQ-Handler passen zusammen in die Groesse."
    /// ```
    fn erwarte_text(&mut self) -> Erg<Textliteral> {
        let t = self.blick();
        if t.art == Art::Text {
            self.pos += 1;
            let mut text = t.text(self.quelle).to_string();
            let mut span = t.span;
            while self.blick().art == Art::Text {
                let w = self.blick();
                self.pos += 1;
                text.push(' ');
                text.push_str(w.text(self.quelle));
                span = crate::span::Span::neu(span.von, w.span.bis);
            }
            Ok(Textliteral { text, span })
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

    // -- 1. Program, modules --------------------------------------------------------------

    fn programm(&mut self) -> Programm {
        let mut items = Vec::new();
        while !self.ende() {
            match self.item() {
                Ok(i) => items.push(i),
                Err(_) => {
                    if !self.synchronisiere() {
                        break;
                    }
                    // A closing brace at top level belongs to the body the refusal has just
                    // cost. Reporting it again turns one finding into two -- and the second
                    // has no content of its own.
                    while self.ist_z(Z::GeschweiftZu) {
                        self.pos += 1;
                    }
                }
            }
        }
        Programm { items }
    }

    /// After a refusal, advance to the next item start. Returns `false` when nothing more
    /// follows -- otherwise the parser would spin in place.
    fn synchronisiere(&mut self) -> bool {
        let start = self.pos;
        let mut tiefe = 0i32;
        while !self.ende() {
            match self.blick().art {
                Art::Zeichen(Z::GeschweiftAuf) => tiefe += 1,
                Art::Zeichen(Z::GeschweiftZu) => {
                    tiefe -= 1;
                    if tiefe < 0 {
                        // A `}` that is not ours -- if it belongs to the **enclosing** body,
                        // we stop here. But if something follows that starts no item
                        // (`protects { … } rank 0 …`), it belonged to the broken declaration:
                        // then continue, otherwise recovery swallows the module's closing
                        // brace and every further item falls.
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
        // **Laxity closed (2026-08-15).** `pub` was eaten before EVERY item and silently
        // dropped for thirteen item kinds -- the EBNF carries it on exactly seven
        // (`moduledecl usedecl constdecl staticdecl typedecl fndecl atomicdecl`). A
        // visibility word the parser accepts and throws away is worse than one it rejects:
        // the reader sees a promise nobody keeps.
        let pub_span = self.blick().span;
        let oeffentlich = self.friss_kw(Kw::Pub);
        let t = self.blick();
        if oeffentlich
            && !matches!(
                t.art,
                Art::Wort(
                    Kw::Module
                        | Kw::Use
                        | Kw::Const
                        | Kw::Static
                        | Kw::Opaque
                        | Kw::Linear
                        | Kw::Tagged
                        | Kw::Type
                        | Kw::Fn
                        | Kw::Spec
                        | Kw::Impl
                        | Kw::Raw
                        | Kw::Divergent
                        | Kw::Prim
                        | Kw::Extern
                        | Kw::Atomic
                )
            )
        {
            self.absage(
                Absage::fehler(
                    "P034",
                    pub_span,
                    format!(
                        "`pub` is not in the grammar here: {} carries no `[ \"pub\" ]`",
                        t.benennung(self.quelle)
                    ),
                )
                .mit_notiz(
                    "`[ \"pub\" ]` steht an sieben Item-Arten: module use const static type \
                     fn atomic -- der Parser nahm es ueberall an und warf es weg",
                ),
            );
        }
        let art = match t.art {
            Art::Wort(Kw::Module) => ItemArt::Modul(self.moduledecl(oeffentlich)?),
            Art::Wort(Kw::Use) => ItemArt::Use(self.usedecl(oeffentlich)?),
            // **`const` faengt zweierlei an**, und ein Blick auf das naechste Wort trennt
            // sie: `const N : u32 = 4;` ist eine Konstante, `const fn f(...)` eine Funktion,
            // die eine liefert. *Kein Kontextschalter -- ein Wort weiter, und es steht fest.*
            Art::Wort(Kw::Const) if matches!(self.blick_n(1).art, Art::Wort(Kw::Fn)) => {
                ItemArt::Funktion(self.fndecl(oeffentlich)?)
            }
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
            Art::Wort(Kw::Group) => ItemArt::Gruppe(self.gruppedecl()?),
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
                        format!("no item starts here: {gefunden}"),
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
        // **G5.** `u64::max` -- both segments are vocabulary words. As the FIRST segment a
        // primitive type is admitted (`pathseg = ident | "u8" | … | "i64"`); that covers the
        // limit values without softening the vocabulary anywhere else.
        let erste = match self.blick().art {
            Art::Wort(k)
                if k.ist_intty() && matches!(self.blick_n(1).art, Art::Zeichen(Z::Kolon2)) =>
            {
                let span = self.blick().span;
                self.pos += 1;
                Ident {
                    text: k.text().to_string(),
                    span,
                }
            }
            _ => self.erwarte_ident()?,
        };
        let mut teile = vec![erste];
        while self.ist_z(Z::Kolon2) {
            self.pos += 1;
            teile.push(self.erwarte_feldname()?);
        }
        let span = teile[0].span.bis_zu(teile[teile.len() - 1].span);
        Ok(Pfad { teile, span })
    }

    // -- 2. Types -------------------------------------------------------------------------

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
        // **«B37»: `order { roh, mmu, caps }` -- die Stufen einer linearen Geistmarke.**
        //
        // Sie steht VOR dem `=`, weil sie kein Rumpf ist: eine Ordnung sagt nichts darueber,
        // woraus der Wert besteht, sondern nur, welche Schritte auf ihm zulaessig sind.
        // *Ein `linear ghost type` hat ohnehin keinen Rumpf -- er traegt nur seinen Namen.*
        let ordnung = if self.friss_kw(Kw::Order) {
            self.erwarte_z(Z::GeschweiftAuf)?;
            let l = self.identlist()?;
            self.erwarte_z(Z::GeschweiftZu)?;
            Some(l)
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
            ordnung,
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
            Art::Wort(Kw::Index) | Art::Wort(Kw::Option) => {
                let anfang = self.span();
                let optional = self.friss_kw(Kw::Option);
                self.erwarte_kw(Kw::Index)?;
                self.erwarte_kw(Kw::Into)?;
                let tabelle = self.erwarte_ident()?;
                Ok(TypExpr::Index {
                    span: anfang.bis_zu(tabelle.span),
                    tabelle,
                    optional,
                })
            }
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

    /// `structty` and `variants` both start with `{`. They are told apart at the second
    /// token: a field is followed by `:`, a variant by `(`, `,` or `}`.
    ///
    /// **`type T = { };` is NEITHER** (2026-08-16). Until then the empty-brace case fell into
    /// the `variants` branch and produced an **empty sum type** -- a type without a value over
    /// which a `match` is exhaustive by doing nothing. *That is not the same as an empty
    /// record, and both are implausible as intentions.* **E3 says: nothing is implicit** --
    /// including a choice between two meanings that nobody wrote down.
    fn verbund_oder_varianten(&mut self) -> Erg<TypExpr> {
        let anfang = self.span();
        if matches!(self.blick_n(1).art, Art::Zeichen(Z::GeschweiftZu)) {
            let sp = anfang.bis_zu(self.blick_n(1).span);
            self.absage(
                Absage::fehler("P035", sp, "`{ }` is neither a record nor a sum type")
                    .mit_notiz(
                        "der leere Klammerpaar-Fall ergab bisher stillschweigend einen LEEREN \
                         SUMMENTYP -- einen Typ ohne Wert, ueber den ein `match` erschoepfend \
                         ist, indem er nichts tut",
                    )
                    .mit_notiz(
                        "E3: nichts ist implizit -- auch keine Wahl zwischen zwei Bedeutungen, \
                         die niemand hingeschrieben hat",
                    ),
            );
            return Err(Abbruch);
        }
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

    /// `offset_into Self` -- `Self` is a word, but stands here in name position.
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

    // -- 4. Expressions --------------------------------------------------------------------

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

    /// `cmpexpr = bitexpr [ cmp bitexpr ]` -- **at most one**, comparisons do not chain.
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
        // «B35»: `optionexpr = "Some" "(" expr ")" | "None"`. In the tree it is a `Ruf` --
        // a constructor IS a call, and a variant of its own would have touched every `match`
        // over `ExprArt` without distinguishing anything the checker separates. The one place
        // that MUST separate it is the cost pass; it is written there.
        if let Art::Wort(k @ (Kw::Some | Kw::None)) = self.blick().art {
            let sp = self.blick().span;
            self.pos += 1;
            let mut argumente = Vec::new();
            if k == Kw::Some {
                self.erwarte_z(Z::RundAuf)?;
                argumente.push(self.expr()?);
                self.erwarte_z(Z::RundZu)?;
            }
            let span = sp.bis_zu(self.vorheriger_span());
            return Ok(Expr {
                art: ExprArt::Ruf(Ruf {
                    pfad: Pfad {
                        teile: vec![Ident {
                            text: k.text().to_string(),
                            span: sp,
                        }],
                        span: sp,
                    },
                    argumente,
                    // `Some(x)` traegt keine Marke -- der Variantenname IST die Marke.
                    marken: Vec::new(),
                    span,
                }),
                span,
            });
        }

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
            // `Self` and the integer words carry paths: `Self.slots[s]`, `u64::max`.
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
                // `place` or `call`/`cast` -- the parenthesis makes the difference.
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
                    // `Self` as a whole is a type, `Self.field` a place.
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

    /// `call = path "(" [ arglist ] ")"`, `arglist = arg { "," arg }`, `arg = [ ident ":" ] expr`
    ///
    /// **Die Marke ist eindeutig, ohne dass der Parser irgendetwas wissen muss.** Ein
    /// Ausdruck kann in Gabbro nie mit `ident ":"` anfangen: Pfade trennen mit `::`, Orte mit
    /// `.` und `[`. Deshalb reicht ein Blick auf zwei Zeichen -- **kein Kontextschalter, und
    /// damit auch kein stiller Verleser** («B7»).
    fn ruf_ab(&mut self, pfad: Pfad) -> Erg<Ruf> {
        self.erwarte_z(Z::RundAuf)?;
        let mut argumente = Vec::new();
        let mut marken: Vec<Ident> = Vec::new();
        if !self.ist_z(Z::RundZu) {
            loop {
                // Marke und Wert werden ZUSAMMEN angehaengt -- die Invariante von
                // `Ruf::marken` entsteht hier und nirgends sonst.
                // `erwarte_feldname`, nicht `erwarte_ident`: die Deklarationsseite laesst
                // Schluesselwoerter als Feldnamen zu (`count`, `len`), und eine Marke, die
                // ihr Feld nicht benennen kann, waere keine.
                let marke = if matches!(self.blick().art, Art::Ident | Art::Wort(_))
                    && self.blick_n(1).art == Art::Zeichen(Z::Kolon)
                {
                    let m = self.erwarte_feldname()?;
                    self.erwarte_z(Z::Kolon)?;
                    Some(m)
                } else {
                    None
                };
                let wert = self.expr()?;
                // **Halb markiert ist schlimmer als gar nicht markiert.** Bei `P(a: 1, 2)`
                // sieht die Ablesung des Lesers wie eine Zuordnung aus und ist eine Reihung.
                // Der Pruefer haelt spaeter `map fst zs = fs` dagegen (`M106`) -- aber nur,
                // wenn der Schluesselstrom ueberhaupt vollstaendig ist.
                //
                // Das erste Argument legt die Betriebsart fest, jedes weitere muss sie halten.
                let markiert = !argumente.is_empty() && !marken.is_empty();
                if !argumente.is_empty() && marke.is_some() != markiert {
                    self.absage(
                        Absage::fehler(
                            "P036",
                            wert.span,
                            "in einer Argumentliste sind entweder ALLE Argumente markiert \
                             oder keines",
                        )
                        .mit_notiz(
                            "`P(a: 1, b: 2)` stellt einen Verbund her, `f(1, 2)` ruft eine \
                             Funktion -- eine halb markierte Liste ist weder das eine noch \
                             das andere",
                        ),
                    );
                    return Err(Abbruch);
                }
                if let Some(m) = marke {
                    marken.push(m);
                }
                argumente.push(wert);
                if !self.friss_z(Z::Komma) {
                    break;
                }
                if self.ist_z(Z::RundZu) {
                    break;
                }
            }
        }
        let ende = self.erwarte_z(Z::RundZu)?;
        Ok(Ruf {
            span: pfad.span.bis_zu(ende),
            pfad,
            argumente,
            marken,
        })
    }

    /// **Die Absage, die «B7» als ENTSCHEIDUNG sichtbar macht statt als Folgefehler.**
    ///
    /// An den drei Stellen, an denen ein Mensch ein Verbundliteral hinschreiben wuerde --
    /// `return P { … };`, `let x = P { … };`, `x = P { … };` -- ist ein `{` nach dem Ausdruck
    /// heute schlicht falsch. Bis hierher fiel dort „`;` erwartet, `{` gefunden": richtig und
    /// nutzlos.
    ///
    /// > *Eine Form, die es absichtlich nicht gibt, verdient eine Absage mit ihrem Grund --
    /// > nicht das Schweigen einer Form, an die niemand gedacht hat.*
    ///
    /// Sie steht **nur** an diesen drei Stellen, nicht in `expr`. In `if x { … }`,
    /// `match a { … }`, `traverse i over d { … }` gehoert das `{` dazu; ein Wachhund dort
    /// waere genau der Kontextschalter, den diese Entscheidung vermeidet.
    fn kein_verbundliteral(&mut self, nach: Span) {
        if !self.ist_z(Z::GeschweiftAuf) {
            return;
        }
        self.absage(
            Absage::fehler(
                "P037",
                nach.bis_zu(self.span()),
                "Gabbro hat kein geschweiftes Verbundliteral",
            )
            .mit_notiz("statt `P { a: 1, b: 2 }` schreibt man `P(a: 1, b: 2)`")
            .mit_notiz(
                "die Felderliste einer Deklaration IST ihr Konstruktor -- genau wie die \
                 Parameterliste eines `device` (`Vtd(basis)`)",
            )
            .mit_notiz(
                "SYNTAX.md, \u{201e}Was es absichtlich nicht gibt\u{201c}: ein `{` nach einem \
                 Ausdruck gehoert in Gabbro immer einem Block",
            ),
        );
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

    /// **G7.** `identlist` demands at least one name -- an entry that destroys nothing could
    /// not say so until 2026-08-15. The empty list is a STATEMENT ("destroys nothing"), not an
    /// absence; forbidding it in the grammar meant making the strongest promise unwritable.
    fn identlist_leer_erlaubt(&mut self) -> Erg<Vec<Ident>> {
        if self.ist_z(Z::GeschweiftZu) {
            return Ok(Vec::new());
        }
        self.identlist()
    }

    // -- 5. Predicates --------------------------------------------------------------------

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
        // `heldpred = "Held" "(" ident [ "," "shared" ] ")"` -- a rule of its own instead of
        // softening the expression: `shared` is a word of the vocabulary and stays one.
        if matches!(self.blick().art, Art::Ident) && self.blick().text(self.quelle) == "Held" {
            if let Some(p) = self.versuch(|s| {
                let anfang = s.span();
                s.pos += 1;
                s.erwarte_z(Z::RundAuf)?;
                let sperre = s.erwarte_ident()?;
                let geteilt = if s.friss_z(Z::Komma) {
                    s.erwarte_kw(Kw::Shared)?;
                    true
                } else {
                    false
                };
                s.erwarte_z(Z::RundZu)?;
                Ok(Pred {
                    span: anfang.bis_zu(s.vorheriger_span()),
                    art: PredArt::Held {
                        sperre,
                        geteilt,
                        span: anfang,
                    },
                })
            }) {
                return Ok(p);
            }
        }
        // `cmpexpr`, `member` and `reach` all start with an expression. Backtracking
        // separates them from `"(" pred ")"`, which may contain a quantifier.
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
            Art::Wort(Kw::Ancestors) => {
                self.pos += 1;
                self.erwarte_kw(Kw::Of)?;
                Ok(Domaene::VorfahrenVon(self.place()?))
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
                         · queue · fields of · elems of · threads · mappings of · ancestors of",
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

    // -- 6. Functions --------------------------------------------------------------------

    fn fndecl(&mut self, oeffentlich: bool) -> Erg<FnDecl> {
        let anfang = self.span();
        let klasse = match self.blick().art {
            Art::Wort(Kw::Spec) => Some(FnKlasse::Spec),
            Art::Wort(Kw::Const) => Some(FnKlasse::Konst),
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
        // E4: the clauses stand in a FIXED order -- a tool that has to sort cannot say
        // "`effects` is missing here".
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
        // **«B37»: `advances roh -> mmu`.** Sie steht zwischen `maintains` und `effects`,
        // weil sie zu den ZUSAGEN gehoert und nicht zu den Wirkungen: was der Schritt
        // anfasst, sagt `effects`; WELCHER Schritt es ist, sagt diese Zeile.
        let advances = if self.friss_kw(Kw::Advances) {
            let von = self.erwarte_ident()?;
            self.erwarte_z(Z::Pfeil)?;
            let nach = self.erwarte_ident()?;
            Some((von, nach))
        } else {
            None
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
            advances,
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
                if self.friss_kw(Kw::Shared) {
                    WirkungArt::SperrtGeteilt(self.place()?)
                } else {
                    WirkungArt::Sperrt(self.place()?)
                }
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

    // -- 7. Statements -------------------------------------------------------------------

    fn block(&mut self) -> Erg<Block> {
        let anfang = self.erwarte_z(Z::GeschweiftAuf)?;
        let mut anweisungen = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            match self.stmt() {
                Ok(s) => anweisungen.push(s),
                Err(e) => {
                    // A broken statement costs the statement, not the function: otherwise a
                    // run shows one finding and hides the nine behind it. During backtracking
                    // there is no recovery -- there the abort IS the result.
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

    /// After a broken statement, advance past the next `;` of the same level -- or up to the
    /// `}` that closes the block.
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
                    // A block used as a statement ends with its brace.
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
                Absage::fehler("P033", anfang, "a semicolon on its own is not a statement")
                    .mit_notiz(
                        "die Formen mit Block -- `if`, `match`, `traverse`, `retry`, \
                         `forever`, `breaking`, `narrow … else`, `locks`, `let … else` -- \
                         tragen KEIN abschliessendes Semikolon",
                    ),
            );
            return Err(Abbruch);
        }
        // Refuse, never interpret: the forms that deliberately do not exist get a refusal of
        // their own instead of a knock-on error three tokens later.
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
                let geteilt = self.friss_kw(Kw::Shared);
                let sperre = self.place()?;
                let rumpf = self.block()?;
                StmtArt::Sperrt(SperrtStmt {
                    sperre,
                    geteilt,
                    rumpf,
                })
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
                if let Some(w) = &wert {
                    self.kein_verbundliteral(w.span);
                }
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

    /// Four forms start with `let`: `letstmt`, `letstmt … else`, `awaitload`, `exchstmt`.
    /// They are told apart **after** the `=`, by the word following the first expression.
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
                    "before `awaits` stands a place, not a compound expression",
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
                    "before `exchange` stands a place, not a compound expression",
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
            // **«B14b»: die Quelle darf ein Ruf ODER ein `place` sein.** Ein Atomic ist ein
            // `place`, und `option`-wertige Orte auszupacken war bis heute unmoeglich.
            let quelle = match wert.art {
                ExprArt::Ruf(ruf) => LetQuelle::Ruf(ruf),
                ExprArt::Ort(o) => LetQuelle::Ort(o),
                _ => {
                    self.absage(
                        Absage::fehler(
                            "P016",
                            wert.span,
                            "`let … else` carries a call or a place, no other expression",
                        )
                        .mit_notiz("`letstmt = \"let\" ident \"=\" ( call | place ) \"else\" \"(\" ident \")\" block`"),
                    );
                    return Err(Abbruch);
                }
            };
            self.pos += 1;
            self.erwarte_z(Z::RundAuf)?;
            let fehlername = self.erwarte_ident()?;
            self.erwarte_z(Z::RundZu)?;
            let sonst = self.block()?;
            return Ok(StmtArt::LetSonst(LetSonst {
                name,
                quelle,
                fehlername,
                sonst,
            }));
        }

        self.kein_verbundliteral(wert.span);
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

    /// `nutzlast = "{" placelist "}" | "nothing"` -- **the braced form IS the form.**
    ///
    /// Until 2026-08-15 the parser accepted both spellings and reported `P032` for the
    /// braces, because the EBNF did not carry them: the EBNF-faithful form fell, the
    /// EBNF-foreign one came through. Decided by the CORPUS: 22 times `nothing`, 11 times
    /// with braces, 2 times without. **The grammar follows the 33.**
    fn nutzlast(&mut self) -> Erg<Nutzlast> {
        if self.ist_kw(Kw::Nothing) {
            let t = self.vor();
            return Ok(Nutzlast::Nichts(t.span));
        }
        self.erwarte_z(Z::GeschweiftAuf)?;
        let liste = self.placelist()?;
        self.erwarte_z(Z::GeschweiftZu)?;
        Ok(Nutzlast::Orte(liste))
    }

    fn zuweisung_oder_ruf(&mut self) -> Erg<StmtArt> {
        // A call carries a path, an assignment a place. Both start with an identifier; the
        // parenthesis decides.
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
                    .mit_notiz("E2: an assignment is not an expression"),
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
                    "a publication sits on `=`, not on a compound assignment",
                ));
                return Err(Abbruch);
            }
            return Ok(StmtArt::Publish(PublishStmt {
                ziel,
                wert,
                nutzlast,
            }));
        }
        self.kein_verbundliteral(wert.span);
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
            // «B35»: since 2026-08-15 `Some`/`None` are words of the vocabulary and thus no
            // longer identifiers -- as the variant name of an `option` pattern they stand
            // nonetheless, and at exactly this place.
            let variante = match self.blick().art {
                Art::Wort(k @ (Kw::Some | Kw::None)) => {
                    let sp = self.blick().span;
                    self.pos += 1;
                    Ident {
                        text: k.text().to_string(),
                        span: sp,
                    }
                }
                _ => self.erwarte_ident()?,
            };
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

    // -- 8. Loops ---------------------------------------------------------------------

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

    // -- 9. Tables, formats -------------------------------------------------------------

    fn table(&mut self) -> Erg<Tabelle> {
        let anfang = self.erwarte_kw(Kw::Table)?;
        let name = self.erwarte_ident()?;
        let kapazitaet = if self.friss_kw(Kw::Count) {
            Some(self.expr()?)
        } else {
            None
        };
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut konstanten = Vec::new();
        let mut slot = None;
        let mut invarianten = Vec::new();
        let mut ops = Vec::new();
        while !self.ist_z(Z::GeschweiftZu) && !self.ende() {
            match self.blick().art {
                // **Too strict, closed (2026-08-15).** The `table` body carries `constdecl`,
                // and `constdecl` carries `[ "pub" ]` -- `pub const` inside a table body is
                // therefore derivable and was unwritable all the same. The one place where
                // the parser was stricter than the grammar.
                Art::Wort(Kw::Pub) if matches!(self.blick_n(1).art, Art::Wort(Kw::Const)) => {
                    self.pos += 1;
                    konstanten.push(self.constdecl(true)?)
                }
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
            kapazitaet,
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
            // `by ops` -- two existing words, zero growth of the vocabulary.
            let nur_ops = if self.ist_kw(Kw::By) {
                self.pos += 1;
                self.erwarte_kw(Kw::Ops)?;
                true
            } else {
                false
            };
            self.erwarte_z(Z::Komma)?;
            felder.push(SlotFeld {
                span: name.span.bis_zu(self.vorheriger_span()),
                name,
                typ,
                nur_ops,
            });
        }
        let ende = self.erwarte_z(Z::GeschweiftZu)?;
        Ok(SlotDecl {
            felder,
            span: anfang.bis_zu(ende),
        })
    }

    fn slottype(&mut self) -> Erg<SlotTyp> {
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

    /// `costexpr = "O" "(" expr ")"` -- `O` is a capital letter and therefore no word of the
    /// vocabulary; here it stands as an identifier in a fixed position.
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
                    "the `node` of a `walk` declaration is an array `[T; N]`",
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

    // -- 10. Devices ----------------------------------------------------------------------

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
                                "`mirrors` appears ONCE per device",
                            )
                            .mit_notiz("SYNTAX.md §10: not per transition"),
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
        // «B32»: the intended wraparound sits at the declaration, not at the computation.
        let umlaufend = self.friss_kw(Kw::Wrapping);
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
            umlaufend,
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
            // **G3, now in the grammar instead of in a parser decision.** To the left of a
            // transition stands `shiftplace` -- a place WITHOUT a `->` suffix. Otherwise, in
            // `ST: ACK -> ACK`, the sequence `ACK -> ACK` would be both pointer access and
            // transition arrow, and the parser would settle an ambiguity the EBNF does not
            // even carry as one. A `transition` describes register fields, not pointer chains
            // -- that is the intended side.
            self.pfeil_ist_suffix = false;
            let ort_erg = self.place();
            self.pfeil_ist_suffix = true;
            let ort = ort_erg?;
            self.erwarte_z(Z::Kolon)?;
            // From here `->` is the transition arrow and not a place suffix -- see
            // `pfeil_ist_suffix`. **The restore must not be skipped by a `?`.** When it was,
            // the switch stayed set after an error in the FIRST expression and made `->` a
            // non-suffix for the rest of the translation unit -- one typo in a `transition`
            // produced phantom refusals on every later line.
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

    // -- 11. Concurrency -------------------------------------------------------------

    fn atomicdecl(&mut self, oeffentlich: bool) -> Erg<AtomicDecl> {
        let anfang = self.erwarte_kw(Kw::Atomic)?;
        let name = self.erwarte_ident()?;
        self.erwarte_z(Z::Kolon)?;
        let typ = self.typeexpr()?;
        // **G1 closed (2026-08-15).** Until then the parser accepted the clause and reported
        // `P031`, because `atomicdecl` did not carry it. The EBNF carries it now -- in the
        // order of the CORPUS (`publishes` before the ordering, as in SYNTAX.md:603 and four
        // times in FRAGMENTE.md F6), not in the one I had written down first.
        let obermenge = if self.friss_kw(Kw::Publishes) {
            Some(self.nutzlast()?)
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

    /// `group N over { A, B };` -- the carrier group.
    ///
    /// **Two members are the minimum, and the parser does not hold that** -- it cannot:
    /// `over { A }` is grammatically the same list. The refusal comes from the pass (`U004`),
    /// where it belongs; here it would be a length check in the parser and thus a second
    /// place carrying the same rule.
    fn gruppedecl(&mut self) -> Erg<GruppeDecl> {
        let anfang = self.erwarte_kw(Kw::Group)?;
        let name = self.erwarte_ident()?;
        self.erwarte_kw(Kw::Over)?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let mut traeger = vec![self.erwarte_ident()?];
        while self.friss_z(Z::Komma) {
            if self.ist_z(Z::GeschweiftZu) {
                break; // Schlusskomma -- dieselbe Regel wie ueberall seit 2026-08-16
            }
            traeger.push(self.erwarte_ident()?);
        }
        let mut zu = self.erwarte_z(Z::GeschweiftZu)?;
        // **The body is optional, the invariant is not meaningless.** `group N over
        // { A, B };` declares the group and lets `U003`/`U005`/`U006` bite -- the LOCK
        // FOOTPRINT and the MOVE. Only the body carries the connecting statement itself.
        let mut invarianten = Vec::new();
        if self.friss_z(Z::GeschweiftAuf) {
            while !self.ist_z(Z::GeschweiftZu) {
                invarianten.push(self.invariant()?);
            }
            zu = self.erwarte_z(Z::GeschweiftZu)?;
        } else {
            self.erwarte_z(Z::Semi)?;
        }
        Ok(GruppeDecl {
            name,
            traeger,
            invarianten,
            span: anfang.bis_zu(zu),
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
        // `shared held <= K ops` -- the separate branch of the shared side (N3).
        let geteilte_haltezeit = if self.friss_kw(Kw::Shared) {
            self.erwarte_kw(Kw::Held)?;
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
            geteilte_haltezeit,
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
                    .mit_notiz("the set is closed: max min add or and"),
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

    // -- 12. Assumptions and axioms ----------------------------------------------------------

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
        // G2: an axiom may yield a value and carry a precondition.
        let rueckgabe = if self.friss_z(Z::Pfeil) {
            Some(self.typeexpr()?)
        } else {
            None
        };
        let mut requires = Vec::new();
        while self.friss_kw(Kw::Requires) {
            requires.push(self.pred()?);
        }
        let effects = self.effects_block()?;
        let klasse = self.annahmeklasse()?;
        self.erwarte_z(Z::Semi)?;
        Ok(Axiom {
            name,
            parameter,
            rueckgabe,
            requires,
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

    // -- 14. Entry and boot ------------------------------------------------------------

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
        let preserves = self.identlist_leer_erlaubt()?;
        self.erwarte_z(Z::GeschweiftZu)?;
        self.erwarte_kw(Kw::Clobbers)?;
        self.erwarte_z(Z::GeschweiftAuf)?;
        let clobbers = self.identlist_leer_erlaubt()?;
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
            liste.push((reg, typ));
            // G4: the trailing comma is optional -- no example in the folder wrote it.
            if !self.friss_z(Z::Komma) {
                break;
            }
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

/// The forms of the prohibition list, each with its replacement. Without this table
/// `while (x) {}` falls as "`;` expected" -- a knock-on error that hides the reason.
fn abgeschaffte_form(wort: &str) -> Option<&'static str> {
    match wort {
        "while" | "for" | "do" | "loop" => Some(
            "es gibt drei Schleifenformen und nur diese: `traverse … over … by …`, \
             `retry … bounded … ops on_exceeded …`, `forever per_pass bounded … ops`",
        ),
        "break" => Some("die geordnete Abschaltung heisst `leave <marke>;`"),
        "continue" => Some("der naechste Durchgang heisst `next <marke>;`"),
        "goto" => Some("there is no jump -- control flow lives in the form"),
        "switch" => Some("`match` is exhaustive and has no catch-all branch"),
        "unsafe" => Some(
            "unsichere Fenster gibt es nicht; was die Maschine anfasst, steht in `axiom`, \
             `raw fn` oder `prim fn` -- benannt und gezaehlt",
        ),
        _ => None,
    }
}

/// Does an item start with this word? Recovery and the corpus run ask this too.
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
