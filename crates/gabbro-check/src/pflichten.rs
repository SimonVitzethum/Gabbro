//! **Das Pflichtenregister -- P6, die Messsonde (2026-08-19).**
//!
//! Die Kennzahl dieses Ordners ist am 2026-08-19 zurueckgezogen worden: sie war an
//! **Verus**-Zeilen gemessen, und Gabbro beweist in Isabelle/HOL. Die neue Buchung lautet
//! `unbekannt, > 0,5`. **Was zwischen den beiden Zustaenden liegt, ist nicht ein Ablesefehler,
//! sondern P6** -- die *erzeugte* Verfeinerungspflicht.
//!
//! ## Warum das der erste Schritt ist und nicht der letzte
//!
//! Ein Isabelle-verankertes `w` braucht **eine W-Pflicht, die ENTSTANDEN ist.** Ohne P6
//! muesste man sich eine ausdenken -- und was man erfindet, bevor man es misst, ist die
//! Bewegung, gegen die R7 und W3 stehen.
//!
//! **Dieses Modul loest keine Pflicht ein. Es ZAEHLT sie.** Und Zaehlen ist der Schritt, der
//! den Abstand zu 0,5 ueberhaupt sichtbar macht:
//!
//! ```text
//! E  Erhaltung     je `maintains I` an einem `impl fn`: I(vorher) und requires  =>  I(nachher)
//! N  Nachbedingung je `ensures P` an einem Rumpf, den Gabbro sieht
//! F  Fremdpflicht  je `ensures P` an einem Rumpf, den Gabbro NICHT sieht
//! ```
//!
//! ## Und die Grenze steht im selben Satz
//!
//! **Eine gezaehlte Pflicht ist keine bewiesene.** Das Register sagt, was ein Mensch schuldet,
//! nicht dass er es geleistet hat. *Es ist die Gegenrichtung zum Zeugnis:* jenes zaehlt auf,
//! worauf die Uebersetzung ruht, dieses, was der Programmierer noch schuldet.
//!
//! **Die K/A/W-Einordnung steht ausdruecklich NICHT hier.** Sie ist ein Urteil -- die
//! Kipp-Regeln verlangen je Pflicht einen Satz Begruendung, und ein Werkzeug, das raet, waere
//! genau die stille Antwort, gegen die dieser Ordner sonst schreibt. *Gezaehlt wird die ART,
//! geurteilt wird von Hand.*

use gabbro_syntax::ast::*;

pub struct Pflicht {
    pub art: Art,
    pub funktion: String,
    pub gegenstand: String,
    /// Hat Gabbro den Rumpf? *Ohne Rumpf ist die Pflicht eine ANNAHME ueber Fremdcode.*
    pub rumpf_da: bool,
    /// **The material a PROVER needs -- carried by the same walk that COUNTS** (P6,
    /// 2026-08-21).
    ///
    /// It sits in `Pflicht` and not in a second walk of its own, and that is the whole
    /// point: `refinement.rs` writes the Isabelle form of exactly the obligations this
    /// register counts, so the two numbers cannot drift. *Two walks over the same thing are
    /// two registers, and that is the class this folder writes against.*
    pub material: Material,
}

/// **What each kind of obligation offers a prover -- exhaustively, no catch-all.**
///
/// A new obligation kind is a compile error at every site that turns one into a goal, not a
/// silent omission. *An output that forgets one kind looks complete* (`messung/ABI.md`, the
/// `lock` line that was missing from the ABI for a day).
#[derive(Clone)]
pub enum Material {
    /// `E` and `N`: the obligation speaks about the world AFTER a body ran.
    Body,
    /// `F`: the `ensures` sits at a body Gabbro never sees.
    Foreign,
    /// `V`: everything the CALL SITE offers -- callee contract, actual arguments, and what
    /// the caller may assume about its own parameters.
    Call(Box<CallSite>),
}

/// The call site of a `V` obligation, with everything a goal needs and nothing more.
#[derive(Clone)]
pub struct CallSite {
    /// The callee as it stood in the source.
    pub callee: String,
    /// The ONE `requires` of the callee this obligation is about.
    pub condition: Pred,
    /// The callee's parameter names, in order -- the left side of the substitution.
    pub callee_params: Vec<String>,
    /// The actual arguments at this call site -- the right side of the substitution.
    pub arguments: Vec<Expr>,
    /// What the CALLER may assume at entry: its own `requires`.
    pub caller_requires: Vec<Pred>,
    /// The caller's parameters, with the bounds their declared type gives and whether the
    /// body leaves them alone.
    pub caller_params: Vec<CallerParam>,
}

/// One parameter of the CALLING function.
#[derive(Clone)]
pub struct CallerParam {
    pub name: String,
    /// The closed integer bounds of the declared type, when it has any. **`None` is not
    /// `unbounded`, it is `not known here`** -- and a goal that needs it is refused.
    pub bounds: Option<(i128, i128)>,
    /// **Does the body leave this name alone from entry to the call?**
    ///
    /// `requires k < 64` speaks about `k` AT ENTRY. If the body writes `k`, rebinds it or
    /// shadows it, that sentence says nothing at the call site -- and using it anyway would
    /// be a hypothesis nobody granted. *That is the quiet weakening this gate exists for:
    /// an obligation proved under a false hypothesis is a green proof of nothing.*
    ///
    /// The answer is computed conservatively over the WHOLE body, not up to the call: a
    /// write anywhere disqualifies the name.
    pub untouched: bool,
}

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Art {
    Erhaltung,
    Nachbedingung,
    Fremdpflicht,
    /// **`V` -- die Vorbedingung am RUFORT, und sie fehlte in diesem Register (2026-08-20).**
    ///
    /// `M115` weist ab, wo der Bereich des Arguments die Vorbedingung **ausschliesst**, und
    /// schweigt sonst. *Eine untere Schranke, und sie steht als solche da.* **Was das
    /// Register bis heute verschwieg: die Gegenseite dieser Schranke ist keine leere Menge.**
    /// Jede Rufstelle einer Funktion mit `requires` traegt eine Bedingung, die der Rufer
    /// herstellen muesste und die niemand nachhaelt.
    ///
    /// > Die starke Fassung von `M115` -- *der Rufer BEWEIST die Vorbedingung* -- braucht eine
    /// > Entscheidungsprozedur, und M1 hat keine: er stellt Fakten HER, er entscheidet keine
    /// > Praedikate. **Solange sie fehlt, ist diese Zahl der Preis**, und ein Preis, der
    /// > nirgends steht, sieht aus wie null.
    ///
    /// *Sie steht bewusst NEBEN `E`/`N`/`F` und nicht in ihnen:* jene drei sind Pflichten,
    /// die eine Deklaration ERZEUGT, diese eine, die ein Ruf VERERBT. Die Zahl waechst mit
    /// den Rufstellen, nicht mit den Deklarationen.
    Vorbedingung,
    /// **`R` -- the REFINEMENT obligation, and it is the head form of P6** (2026-08-24).
    ///
    /// `impl fn f … refines g` says: *what this body establishes is exactly what `g`
    /// describes.* **Until today this obligation could not arise at all** -- there was no
    /// form in which a body names its specification (`messung/VERFEINERUNG.md`), and so P6
    /// produced `K` obligations exclusively.
    ///
    /// *It stands beside `N` and not inside it:* an `ensures` names a SINGLE statement about
    /// the post-state, a `refines` names the WHOLE specification. Both need the same missing
    /// thing -- the meaning of the body -- but they are not the same obligation, and a
    /// register that merges them cannot separate the metric.
    Verfeinerung,
    /// **`D` -- the DEVICE PROMISE, and until today it was a silent drop** (2026-08-24).
    ///
    /// `reg QUEUE_SIZE : u16 @0x18 class rw requires QUEUE_SIZE <= QMAX` -- the clause has
    /// always parsed and was read by **no pass at all**. `RegDecl::requires` stood in the
    /// tree and nobody descended into it. *The same shape as `ensures` on an `extern fn`,
    /// and the same answer: do not refuse it, do not pretend to check it -- COUNT it.*
    ///
    /// **It is neither a postcondition nor a foreign duty.** A foreign duty sits at CODE
    /// Gabbro does not see; this one sits at HARDWARE Gabbro does not see. *Both are
    /// assumptions, but their falsifiers are different things* -- one a foreign body, the
    /// other a probe at the device.
    ///
    /// > **And it will never become a fact.** The register is volatile, and a hostile device
    /// > may report whatever it likes («B33»). *What is booked here is the promise -- not
    /// > that it holds.*
    Geraetezusage,
    /// **`S` -- the LOOP INVARIANT** (2026-08-28).
    ///
    /// `traverse … invariant P { … }` says: *P holds across the passes.* Until today the
    /// clause did not exist, and the body channel refused 23 routines with `loop` for the
    /// reason that the measure was carried and the STATEMENT was not
    /// (`messung/SCHLEIFENINVARIANTE.md`).
    ///
    /// *It stands beside `E` and not inside it:* a table invariant is declared once at the
    /// table and quantified over its slots; a loop invariant is declared at ONE loop and
    /// quantified over its passes. Both need the meaning of a body -- they are not the same
    /// duty, and a register that merged them could not separate the two prices.
    Schleifeninvariante,
}

impl Art {
    pub fn marke(self) -> &'static str {
        match self {
            Art::Erhaltung => "E",
            Art::Nachbedingung => "N",
            Art::Fremdpflicht => "F",
            Art::Vorbedingung => "V",
            Art::Verfeinerung => "R",
            Art::Geraetezusage => "D",
            Art::Schleifeninvariante => "S",
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Art::Erhaltung => "Preservation",
            Art::Nachbedingung => "Postcondition",
            Art::Fremdpflicht => "Foreign duty",
            Art::Vorbedingung => "Precondition at the call site (undercounts: see `vorbedingungen`)",
            Art::Verfeinerung => "Refinement of a specification",
            Art::Geraetezusage => "Device promise at a register",
            Art::Schleifeninvariante => "Invariant across the passes of a loop",
        }
    }
}

pub fn sammle(baum: &Programm) -> Vec<Pflicht> {
    let mut aus = Vec::new();
    lauf(&baum.items, &mut aus);
    vorbedingungen(baum, &mut aus);
    aus
}

/// **Jede Rufstelle einer Funktion mit `requires` -- gezaehlt, nicht entschieden.**
///
/// Gemessen 2026-08-20, ausgeloest von der Buchung *„vorher zaehlen, an wie vielen Rufstellen
/// eine Vorbedingung heute unbewiesen bleibt"*. Die Zahl ist der Preis der schwachen Fassung
/// von `M115`: was dort schweigt, steht hier.
///
/// **Die Zahl ist eine OBERE Schranke der offenen Pflichten und eine UNTERE der Rufstellen.**
/// Obere, weil manche Vorbedingung am Rufort trivial gilt (`requires n < 8` mit `n : u32 in
/// 0 .. 7`) -- das entscheidet heute nichts, also zaehlt es mit. Untere, weil ein Ruf, dessen
/// Pfad sich nicht aufloest, gar nicht erst gefunden wird. *Beide Richtungen benannt, sonst
/// waere sie ein Urteil im Gewand einer Messung (W19).*
/// **`V` UNDERSTATES since 2026-08-28, and it understates by a growing amount.**
///
/// This walk resolves a call through `Umgebung::funktion`, and that map is built from the
/// `FnDecl`s of the tree. **A GENERATED operation is not one.** Since `ops` ships bodies
/// (`emit.rs::ops`, cut (c)) and `D012` holds their premises at the call site
/// (`opsruf.rs`), every such call carries real preconditions that this register does not
/// count -- one per `insert` with a `tree`, two without, one per `remove`.
///
/// > **The gap grows with every generated operation**, so it is not a rounding error but a
/// > number drifting parallel to the truth. *That is the shape a booked figure takes right
/// > before it stops being one* -- the same class the `@version` finding named.
///
/// It is booked here rather than repaired here because the repair is a decision, not a
/// patch: either `Umgebung` learns the generated heads (then `E008`, `K003` and this walk
/// all see them, and the cost is one map with two producers), or `pflichten` grows a second
/// source (and then two registers stand over one thing, which is `W7`). **Until that is
/// decided, the number carries this note and `gabbro pflichten` is read with it.**
fn vorbedingungen(baum: &Programm, aus: &mut Vec<Pflicht>) {
    let u = crate::umgebung::Umgebung::sammle(baum);
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else { return };
        if f.klasse == Some(FnKlasse::Spec) {
            return;
        }
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let mut rufe = Vec::new();
        rufe_im_block(b, &mut rufe);
        for r in rufe {
            let Some(sig) = r.path().and_then(|p| u.funktion(modul, p)) else { continue };
            for (n, bed) in sig.requires.iter().enumerate() {
                aus.push(Pflicht {
                    art: Art::Vorbedingung,
                    funktion: f.name.text.clone(),
                    gegenstand: format!("{} requires #{}", r.target_text(), n + 1),
                    rumpf_da: sig.rumpf_da,
                    material: Material::Call(Box::new(CallSite {
                        callee: r.target_text(),
                        condition: bed.clone(),
                        callee_params: sig.parameter.iter().map(|(n, _)| n.clone()).collect(),
                        arguments: r.argumente.clone(),
                        caller_requires: f.requires.clone(),
                        caller_params: caller_params(f, b, &u, modul),
                    })),
                });
            }
        }
    });
}

/// **What the CALLER may assume about its own parameters at the call site.**
///
/// Two facts per parameter, and both are needed before a single hypothesis may be written
/// down: the bounds its declared type gives, and whether the body leaves the name alone.
///
/// > *`requires k < 64` is a sentence about `k` AT ENTRY.* At a call site inside a body that
/// > has since written `k`, that sentence is not available -- and a goal that assumes it
/// > anyway is proved under a hypothesis nobody granted. **A weakened obligation is worse
/// > than no obligation: the prover then says "proved" about something else.**
fn caller_params(
    f: &FnDecl,
    rumpf: &Block,
    u: &crate::umgebung::Umgebung,
    modul: &str,
) -> Vec<CallerParam> {
    let mut touched = Vec::new();
    for a in &rumpf.anweisungen {
        bound_or_written(a, &mut touched);
    }
    let pfad = Pfad {
        teile: vec![f.name.clone()],
        span: f.name.span,
    };
    let sig = u.funktion(modul, &pfad);
    f.parameter
        .iter()
        .enumerate()
        .map(|(i, p)| CallerParam {
            name: p.name.text.clone(),
            bounds: sig
                .and_then(|s| s.parameter.get(i))
                .and_then(|(_, t)| integer_bounds(t)),
            untouched: !touched.contains(&p.name.text),
        })
        .collect()
}

/// **The closed integer bounds a declared type gives -- or nothing.**
///
/// `None` is the safe answer and the frequent one. A missing bound drops a hypothesis, and
/// a dropped hypothesis can only make a goal HARDER; a wrong bound would make a false goal
/// provable. **That is why this direction may be conservative and the goal may not.**
///
/// Two decisions stand in the arms rather than in a comment somewhere else:
///
/// * **`u32 wrapping` gives nothing.** The declared overflow is the point of the type, and
///   a bound on a value that is allowed to wrap is a sentence about a moment, not a value.
/// * **An `opaque` new type gives nothing.** Its representation is not visible outside its
///   module (D1), and reading the bound off it here would be exactly the implicit conversion
///   the language refuses. *A transparent one does give its range* -- `type Klein = u32 in
///   0 .. 9` is a range with a name, and the name is not a wall.
fn integer_bounds(t: &crate::typen::Typ) -> Option<(i128, i128)> {
    match t {
        crate::typen::Typ::Ganzzahl(b) => Some((b.min, b.max)),
        crate::typen::Typ::Benannt {
            undurchsichtig: false,
            unter,
            ..
        } => integer_bounds(unter),
        // Everything else -- pointers, sums, records, tables, registers, `wrapping`,
        // floats, `never` -- gives no integer bound here. **Fail-closed on purpose:** the
        // cost is a refused or harder goal, never a false one.
        _ => None,
    }
}

/// **Every name a statement may BIND or WRITE -- and the `match` has no catch-all.**
///
/// This walk is the fifth of its kind in this folder, and the four before it were all found
/// the same way: a walker entered a body and not one of its arms (`H007` in `geteilt.rs`,
/// standing in an `observes`; the
/// RCU walker in loops, `typ_von_ort` against `index_pruefen`, the `retry` body). *Every
/// time the body was entered and one branch of it was not.* A `_ =>` arm here would hand
/// the class back: a statement kind nobody listed writes a parameter, the parameter still
/// counts as untouched, and the goal gets a hypothesis that does not hold.
///
/// **It over-approximates on purpose.** A `let` in a branch that never runs still
/// disqualifies the name; the price is a refused goal, and the alternative price is a false
/// one.
fn bound_or_written(s: &Stmt, out: &mut Vec<String>) {
    match &s.art {
        StmtArt::Let(l) => out.push(l.name.text.clone()),
        StmtArt::LetSonst(l) => {
            out.push(l.name.text.clone());
            out.push(l.fehlername.text.clone());
        }
        StmtArt::Zuweisung(z) => out.push(z.ziel.basis.text.clone()),
        StmtArt::Narrow(n) => out.push(n.ort.basis.text.clone()),
        StmtArt::Publish(p) => out.push(p.ziel.basis.text.clone()),
        StmtArt::AwaitLoad(a) => out.push(a.name.text.clone()),
        StmtArt::Exchange(x) => out.push(x.name.text.clone()),
        StmtArt::Match(m) => {
            for z in &m.zweige {
                if let Some(b) = &z.binder {
                    out.push(b.text.clone());
                }
            }
        }
        StmtArt::Schleife(l) => match l.as_ref() {
            Schleife::Traverse(t) => out.push(t.variable.text.clone()),
            // A `retry`/`forever` binds no name of its own -- its label is not a value.
            Schleife::Retry(_) | Schleife::Forever(_) => {}
        },
        // These carry blocks and bind nothing themselves; the recursion below enters them.
        StmtArt::Wenn(_)
        | StmtArt::Bricht(_)
        | StmtArt::Sperrt(_)
        | StmtArt::Observiert(_)
        | StmtArt::Leave(_)
        | StmtArt::Next(_)
        | StmtArt::Return(_)
        | StmtArt::Ruf(_) => {}
    }
    for k in crate::unterbloecke(s) {
        for a in &k.anweisungen {
            bound_or_written(a, out);
        }
    }
}

/// Jeder Ruf eines Blocks, samt Unterbloecken und Unterausdruecken.
///
/// *Ohne `unterbloecke` faende die Zaehlung nur die oberste Ebene* -- und ein Ruf unter einer
/// Sperre oder in einem `observes`-Block ist derselbe Ruf. **Dieselbe Lehre wie `pruefe-
/// abstieg.py`, nur an einer Zaehlung statt an einem Pass.**
fn rufe_im_block<'a>(b: &'a Block, aus: &mut Vec<&'a Ruf>) {
    for s in &b.anweisungen {
        if let StmtArt::Ruf(r) = &s.art {
            aus.push(r);
        }
        for e in crate::eigene_ausdruecke(s) {
            for x in crate::alle_ausdruecke(e) {
                if let ExprArt::Ruf(r) = &x.art {
                    aus.push(r);
                }
            }
        }
        for k in crate::unterbloecke(s) {
            rufe_im_block(k, aus);
        }
    }
}

/// Every loop of a body that carries an `invariant`, in source order.
fn schleifeninvarianten(b: &Block, n: &mut usize, funktion: &str, aus: &mut Vec<Pflicht>) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Schleife(sch) => {
                let (inv, rumpf) = match sch.as_ref() {
                    Schleife::Traverse(x) => (&x.invariante, &x.rumpf),
                    Schleife::Retry(x) => (&x.invariante, &x.rumpf),
                    Schleife::Forever(x) => (&x.invariante, &x.rumpf),
                };
                if inv.is_some() {
                    *n += 1;
                    aus.push(Pflicht {
                        art: Art::Schleifeninvariante,
                        funktion: funktion.to_string(),
                        gegenstand: format!("loop invariant #{n}"),
                        rumpf_da: true,
                        material: Material::Body,
                    });
                }
                schleifeninvarianten(rumpf, n, funktion, aus);
            }
            StmtArt::Wenn(w) => {
                for (_, blk) in &w.zweige {
                    schleifeninvarianten(blk, n, funktion, aus);
                }
                if let Some(blk) = &w.sonst {
                    schleifeninvarianten(blk, n, funktion, aus);
                }
            }
            StmtArt::Match(m) => {
                for z in &m.zweige {
                    schleifeninvarianten(&z.rumpf, n, funktion, aus);
                }
            }
            StmtArt::Sperrt(x) => schleifeninvarianten(&x.rumpf, n, funktion, aus),
            StmtArt::Observiert(x) => schleifeninvarianten(&x.rumpf, n, funktion, aus),
            StmtArt::Bricht(x) => schleifeninvarianten(&x.rumpf, n, funktion, aus),
            StmtArt::LetSonst(x) => schleifeninvarianten(&x.sonst, n, funktion, aus),
            // **No catch-all.** A statement kind that carries a block and is not listed here
            // would hide every loop inside it, and the register would be short by a duty
            // nobody could see was missing.
            StmtArt::Let(_)
            | StmtArt::Zuweisung(_)
            | StmtArt::Narrow(_)
            | StmtArt::Leave(_)
            | StmtArt::Next(_)
            | StmtArt::Publish(_)
            | StmtArt::AwaitLoad(_)
            | StmtArt::Exchange(_)
            | StmtArt::Return(_)
            | StmtArt::Ruf(_) => {}
        }
    }
}

fn lauf(items: &[Item], aus: &mut Vec<Pflicht>) {
    for item in items {
        match &item.art {
            ItemArt::Modul(m) => lauf(&m.items, aus),
            ItemArt::Funktion(f) => {
                // Eine `spec fn` schuldet nichts -- sie IST die Aussage (`M113`).
                if f.klasse == Some(FnKlasse::Spec) {
                    continue;
                }
                let rumpf_da = matches!(f.rumpf, FnRumpf::Block(_));
                for i in &f.maintains {
                    aus.push(Pflicht {
                        art: Art::Erhaltung,
                        funktion: f.name.text.clone(),
                        gegenstand: i.text.clone(),
                        rumpf_da,
                        material: Material::Body,
                    });
                }
                // **`refines g` -- the head form of P6.** It stands BEFORE the `ensures`, as
                // in the grammar: the specification brings its statement along, the `ensures`
                // adds to it. *Only at a body Gabbro sees* -- a `refines` at a foreign body
                // would be an assumption and not an obligation, and `M130` lets it stand at
                // an `impl fn` only anyway.
                if let Some(g) = &f.verfeinert {
                    aus.push(Pflicht {
                        art: Art::Verfeinerung,
                        funktion: f.name.text.clone(),
                        gegenstand: format!(
                            "refines {}",
                            g.teile.last().map(|i| i.text.as_str()).unwrap_or("?")
                        ),
                        rumpf_da,
                        material: if rumpf_da { Material::Body } else { Material::Foreign },
                    });
                }
                // **Every loop that carries an `invariant` owes one.** A promise that
                // stands in no register is not a debt but a claim -- the same reason
                // `refines` was given the art `R` when it got its word.
                if let FnRumpf::Block(b) = &f.rumpf {
                    let mut n = 0usize;
                    schleifeninvarianten(b, &mut n, &f.name.text, aus);
                }
                for (n, _) in f.ensures.iter().enumerate() {
                    aus.push(Pflicht {
                        art: if rumpf_da { Art::Nachbedingung } else { Art::Fremdpflicht },
                        funktion: f.name.text.clone(),
                        gegenstand: format!("ensures #{}", n + 1),
                        rumpf_da,
                        // **An `ensures` at a body Gabbro never sees is not a goal**, and an
                        // `ensures` at one it does see needs that body's effect. The two sit
                        // in different arms because a prover treats them differently: the
                        // first is an ASSUMPTION, the second an open obligation.
                        material: if rumpf_da { Material::Body } else { Material::Foreign },
                    });
                }
            }
            // **`requires` at a `reg` -- the device promise** (2026-08-24, «B26»).
            //
            // Until today nobody read this clause: `PFLICHTEN.md` carried it as a hanging
            // plumbing duty with the note *"no pass reads `RegDecl::requires` at all. The
            // clause parses and is then dropped -- the same shape as `ensures` on an
            // `extern fn`."* **The comparison was the pointer to the cure:** that one became
            // a counted foreign duty, this one becomes a counted device promise.
            ItemArt::Device(d) => {
                let nimm = |r: &RegDecl, aus: &mut Vec<Pflicht>| {
                    if r.requires.is_some() {
                        aus.push(Pflicht {
                            art: Art::Geraetezusage,
                            funktion: d.name.text.clone(),
                            gegenstand: format!("reg {} requires", r.name.text),
                            // Gabbro never sees the device -- as with a foreign body.
                            rumpf_da: false,
                            material: Material::Foreign,
                        });
                    }
                };
                for r in &d.register {
                    nimm(r, aus);
                }
                for b in &d.baenke {
                    for r in &b.register {
                        nimm(r, aus);
                    }
                }
                // **And the SAME silent drop stood at `transition`, thirteenfold**
                // (2026-08-26). `RegDecl::requires` was counted from 2026-08-24; the clause
                // at an `Uebergang` was not, and it is the one the corpus actually writes:
                //
                //     reg … requires            1 site   (`messung/fragmente/F04.gab`:41)
                //     transition … requires    13 sites  (beispiele/02, 09, 20, 45,
                //                                         F02 five times, virtio-net)
                //
                // *A clause that parses and is dropped* -- the same shape, at thirteen times
                // the surface, and `gabbro pflichten` printed `0 device` over files full of
                // them. **The guard could not see it either:** `pruefe-klauseln.py` matches
                // `\.<field>\b` textually, and five different structures carry a `requires`.
                //
                // > It stays `Material::Foreign` and `rumpf_da: false` for the same reason
                // > the register clause does: **Gabbro never sees the device.** Booking is
                // > not discharging -- it is giving the duty a name and a number (W10).
                for ue in &d.uebergaenge {
                    if ue.requires.is_some() {
                        aus.push(Pflicht {
                            art: Art::Geraetezusage,
                            funktion: d.name.text.clone(),
                            gegenstand: format!("transition {} requires", ue.name.text),
                            rumpf_da: false,
                            material: Material::Foreign,
                        });
                    }
                }
            }
            _ => {}
        }
    }
}

pub fn zeige(baum: &Programm, datei: &str) -> String {
    let p = sammle(baum);
    let mut s = String::new();
    s.push_str(&format!("-- Obligation register: {datei}\n"));
    s.push_str("-- What a HUMAN still owes here. Counted, not discharged.\n\n");
    if p.is_empty() {
        s.push_str("   no generated proof obligation in this unit\n\n");
    }
    for art in [Art::Verfeinerung, Art::Erhaltung, Art::Nachbedingung, Art::Fremdpflicht,
               Art::Vorbedingung, Art::Geraetezusage, Art::Schleifeninvariante] {
        let eigene: Vec<&Pflicht> = p.iter().filter(|x| x.art == art).collect();
        if eigene.is_empty() {
            continue;
        }
        s.push_str(&format!("{}  {} ({})\n", art.marke(), art.name(), eigene.len()));
        for x in &eigene {
            s.push_str(&format!("     {} :: {}\n", x.funktion, x.gegenstand));
        }
        s.push('\n');
    }
    let e = p.iter().filter(|x| x.art == Art::Erhaltung).count();
    let n = p.iter().filter(|x| x.art == Art::Nachbedingung).count();
    let f = p.iter().filter(|x| x.art == Art::Fremdpflicht).count();
    let v = p.iter().filter(|x| x.art == Art::Vorbedingung).count();
    let r = p.iter().filter(|x| x.art == Art::Verfeinerung).count();
    let dz = p.iter().filter(|x| x.art == Art::Geraetezusage).count();
    let si = p.iter().filter(|x| x.art == Art::Schleifeninvariante).count();
    // **The header line MUST add up** -- `r + e + n + f + v == p.len()`. The first version of
    // this line did not carry the refinement and reported `1 obligations: 0, 0, 0, 0`.
    // *A balance that does not add up is the class `zaehle-p6.py` is built against* -- and it
    // arose here on exactly the day a new kind was added.
    //
    // **And it arose a SECOND time, on 2026-08-28, when `S` came.** The same assertion caught
    // it before any report was read. *That is what a balance is for: a new kind does not get
    // to be quietly uncounted, and the check does not depend on anyone noticing.*
    debug_assert_eq!(r + e + n + f + v + dz + si, p.len(), "the obligation balance does not add up");
    s.push_str(&format!(
        "== {} obligations: {r} refinement, {e} preservation, {n} postcondition, \
         {f} foreign, {v} precondition, {dz} device, {si} loop invariant ==\n",
        p.len()
    ));
    s.push_str("   And what that does NOT mean: a counted obligation is not a proved one.\n");
    s.push_str("   The K/A/W classification is a JUDGEMENT and deliberately does not stand here --\n");
    s.push_str("   the tipping rules demand one sentence of reasoning per obligation.\n");
    if f > 0 {
        s.push_str(&format!(
            "   The {f} foreign ones sit at bodies Gabbro never sees: they are\n\x20\
                ASSUMPTIONS about foreign code and do not dissolve even under\n\x20  \"all \
                of Gabbro verified\".\n"
        ));
    }
    if v > 0 {
        s.push_str(&format!(
            "   The {v} preconditions are the price of the WEAK reading of `M115`: it\n   \
                refuses only where the range of the argument EXCLUDES the condition, and\n   \
                is silent otherwise. Silence is not confirmation -- these sites are\n   \
                counted, not settled.\n"
        ));
    }
    s
}

/// **Wie viele Rufe ruhen auf einem fremden Vertrag? -- Punkt 4, 2026-08-19.**
///
/// Seit heute verengt die Nachbedingung eines Gerufenen sein Ergebnis beim Rufer
/// (`m1::aus_ensures`). Bei einem `impl fn` ist das eine Ableitung, die Gabbro einmal selbst
/// nachrechnen wird; **bei einem `extern fn` ist es Glaube.**
///
/// > *Wer nicht pruefen kann, EXPORTIERT.* Dieselbe Konstruktion wie die `entrust`-Zeile in
/// > Abschnitt E des Zeugnisses -- eine Vertrauensflaeche, die gezaehlt dasteht statt
/// > stillschweigend zu wirken.
pub fn fremde_vertraege(baum: &Programm) -> Vec<String> {
    let mut aus = Vec::new();
    sammle_vertraege(&baum.items, &mut aus);
    aus
}

fn sammle_vertraege(items: &[Item], aus: &mut Vec<String>) {
    for item in items {
        match &item.art {
            ItemArt::Modul(m) => sammle_vertraege(&m.items, aus),
            ItemArt::Funktion(f) => {
                if matches!(f.rumpf, FnRumpf::Block(_)) || f.ensures.is_empty() {
                    continue;
                }
                aus.push(f.name.text.clone());
            }
            _ => {}
        }
    }
}
