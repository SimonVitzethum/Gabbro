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
    /// **Where the obligation ARISES** -- the anchor of `AUFTRAG-GABBROV.md` §4, and the same
    /// notion `PFLICHTEN.md` puts in its `Line` column.
    ///
    /// For seven of the eight kinds this is the clause itself. **For `V` it is the CALL
    /// SITE**, and that is not a slip: a body with two calls to the same callee produces two
    /// obligations whose names are byte-identical (`caller :: callee requires #1` twice), and
    /// then the anchor is the only field that tells them apart. *Measured over the whole
    /// corpus on 2026-09-03: no unit has such a pair today -- so this is a latent duplicate,
    /// not a live one, and the field closes it before it is written.*
    pub span: gabbro_syntax::span::Span,
    /// **The clause whose WORDING the manifest prints** -- `None` where there is none.
    ///
    /// It is a second field and not the same one because for `V` the two differ: the
    /// obligation arises at the call site, and what it SAYS is the callee's `requires`.
    /// *One field with two meanings would make the manifest unable to say which it meant* --
    /// the same argument `manifest.rs` makes for `voraussetzungen` beside
    /// `voraussetzung_text`.
    ///
    /// For `maintains I` and `refines g` the wording is not at the clause at all: the clause
    /// carries a NAME, and the statement is the body of the `spec fn` it names. That body is
    /// looked up in the same unit ([`spezpraedikate`]) -- a lookup, not a computation. Where
    /// the name resolves to no `spec fn` with a predicate body, this is `None` and
    /// [`kein_text`] says so.
    ///
    /// [`kein_text`]: Pflicht::kein_text
    pub textspan: Option<gabbro_syntax::span::Span>,
    /// **Why there is no wording -- named, never silent.**
    ///
    /// `AUFTRAG-GABBROV.md` §4 and the mandate behind it: *an anchor that points at the wrong
    /// line is worse than none.* The same holds one field over. An empty cell with a reason
    /// beside it is a statement; an empty cell alone is a guess waiting to be made.
    pub kein_text: Option<&'static str>,
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
    /// **`W` -- the invariant of a `walk`, and until today it was a C COMMENT** (2026-08-31).
    ///
    /// `walk Seitentabelle levels 4 { … invariant wx_getrennt cost O(n) runs online : … }`
    /// parses, and the emitter writes it into the artefact as
    /// *"COMPILE TIME (W6), not re-checked here"*. **Measured: nothing decides it.** An
    /// unsatisfiable one --
    ///
    /// ```text
    /// invariant geteilt_bleibt_lesbar cost O(n) runs online :
    ///     forall m in mappings of Inodebaum : m.block == 1 && m.block == 2;
    /// ```
    ///
    /// -- passes with `0 errors, 0 hints`, produces no obligation, and appears in the
    /// certificate under DIRECT lowering, not under a template. *W6 says the pass decided it;
    /// no pass did.*
    ///
    /// **The cure is the one `D` got** (`messung/PFLICHTEN.md`, the register clause): do not
    /// refuse it, do not pretend to check it -- COUNT it. A refusal was weighed and dropped:
    /// `runs online` at a `table … ops` IS carried (by `table.ops.erhaltung`), and at a
    /// `table` without `ops` it becomes an `E` per `maintains` -- *a rule over the word
    /// `online` would hit two registers that work in order to reach the one that does not.*
    ///
    /// > **BERICHTIGT 2026-09-03: the second half of that sentence is measurably false, and
    /// > the gap it hides is the LARGER one.** A `table`/`group` invariant becomes an `E`
    /// > only if some function names it in `maintains`, and a `table … ops` carries its own
    /// > under `table.ops.erhaltung`. One that has neither is booked by NOTHING.
    /// >
    /// > **GEBAUT 2026-09-04, and the refusal that stood here was wrong on its own terms.**
    /// > Yesterday this block named the gap and refused the repair with one sentence -- *"a
    /// > ninth `Art` moves the header line"*. **The premise does not hold.** The paragraph
    /// > below says the case IS this kind's argument, *"one construct over"* -- and a
    /// > statement that is this obligation needs no new kind to be booked under. What a
    /// > ninth `Art` would have bought is a separate LETTER, not a separate duty.
    /// >
    /// > So `lauf` grew an `ItemArt::Tabelle` and an `ItemArt::Gruppe` arm, and the repair is
    /// > the one `D` got two days earlier: **the kind stayed, the HEADING was corrected to
    /// > name what stands under it** (see `Art::name`). *Checked before the word moved, not
    /// > after:* the three readers of the closing line -- `pruefe-manifest.py`,
    /// > `manifest-lage.sh`, `pruefe-zahlen.py` -- match `== N obligations:` and, in the last
    /// > case, a prefix ending at `precondition`. **None reads the last word.**
    /// > `MANIFESTFASSUNG` stays at 2.
    ///
    /// **The census, re-measured 2026-09-04 over the 145 of 196 `.gab` under `beispiele/`
    /// and `messung/` that emit a register**, and every one of yesterday's five numbers had
    /// moved:
    ///
    /// ```text
    ///   named `table`/`group` invariants                 22   (was 19)
    ///     a function `maintains` it   -> `E`              4   (was  2)
    ///     under a `table … ops`       -> U-3              4   (was  2)
    ///     NOTHING maintains it        -> booked here     14   (was 15)
    ///   (`walk` invariants:                               6   (was  4))
    /// ```
    ///
    /// *Three of yesterday's fifteen were MAINTAINED* -- `53-zwei-orte.gab`:47,
    /// `55-kindkette.gab`:72 and `messung/netz/udp-echo.gab`:135, all three already at the
    /// commit that wrote the census -- **and `spezpraedikate` a hundred lines below named
    /// exactly those three (plus F03's) the same day, as the `maintains` lines whose wording
    /// sat at a `table`/`group` invariant.** Two registers over one set, written together,
    /// disagreeing. The measurement stands in `PFLICHTEN-KORRESPONDENZ.md` §7, taken twice --
    /// once from the source and once from the artefact -- and both say 14.
    ///
    /// *It stands beside `E` and not inside it:* an `E` is owed by a FUNCTION that names the
    /// invariant in `maintains`. A `walk` invariant is owed by no function at all -- it is a
    /// statement about the whole mapping domain, and there is no `maintains` for it. **The
    /// same holds one construct over**, and that is why both stand here: a `table`/`group`
    /// invariant nobody maintains is owed by no function either.
    ///
    /// **And `down`/`leaf` stand here for the third time of the same reason.**
    /// `down : roh when !it.PS` is compiled into a CLASSIFIER (`emit.rs`, `_steigt_ab`) and
    /// decided by nothing: that an entry with `!PS` really points at a next level of that
    /// node type is a statement about the hardware table, owed by no function.
    Walkinvariante,
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
            Art::Walkinvariante => "W",
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Art::Erhaltung => "Preservation",
            Art::Nachbedingung => "Postcondition",
            Art::Fremdpflicht => "Foreign duty",
            Art::Vorbedingung => "Precondition at the call site (undercounts: see `vorbedingungen`)",
            Art::Verfeinerung => "Refinement of a specification",
            // **The heading named the wrong construct, and the register itself said so**
            // (2026-09-02). `pflichten.rs` has booked BOTH device clauses since 2026-08-26
            // -- `reg … requires` and `transition … requires` -- and printed all of them
            // under *"Device promise at a register"*. Measured over the corpus that day:
            // **15 entries, of which 13 are `transition`s.** Every line under the heading
            // spelled `transition <name> requires` while the heading said `reg`.
            //
            // *A label that names a construct the entries are not is the `W16` shape at the
            // report layer:* a reader who counted registers from this heading counted
            // thirteen that are not there. The one word that covers both is the one the
            // clause is called by everywhere else in this file.
            Art::Geraetezusage => "Device promise (`reg` or `transition`)",
            Art::Schleifeninvariante => "Invariant across the passes of a loop",
            // **The heading named ONE construct and the kind covers three**
            // (2026-09-04) -- the same repair `D` got on 2026-09-02, and for the same
            // reason. `W` is not *"the invariant of a `walk`"*; it is **the invariant
            // NO FUNCTION OWES**, which is exactly the sentence the variant's own
            // docstring gives as its reason for standing beside `E`. A `walk`
            // invariant is one such; a `table`/`group` invariant that no `maintains`
            // names is another, and the corpus carries fifteen of the second against
            // six of the first.
            //
            // *The variant keeps its identifier on purpose:* renaming it would move
            // `LeanReason::WalkInvariant` and `zaehle-lean.py`'s reason table with it
            // -- three lists over one set, as `zaehle-lean.py` says in its own words --
            // and none of that is visible in the artefact a stranger reads. **What IS
            // visible is this line**, and it now says what the entries under it are.
            Art::Walkinvariante => "Invariant owed by NO function -- a `walk`, \
                                    or a `table`/`group` that no `maintains` names",
        }
    }
}

pub fn sammle(baum: &Programm) -> Vec<Pflicht> {
    let spez = spezpraedikate(baum);
    let gehalten = erhaltene(baum);
    let mut aus = Vec::new();
    lauf(&baum.items, &spez, &gehalten, &mut aus);
    vorbedingungen(baum, &mut aus);
    aus
}

/// **Every invariant name some function of the unit names in `maintains`.**
///
/// The set that decides whether a `table`/`group` invariant is already OWED. One that a
/// `maintains` names is an `E` at that function and must not be booked a second time here;
/// one that no `maintains` names is owed by nobody, and that is the case `W` exists for.
///
/// *The lookup is per UNIT, exactly like [`spezpraedikate`].* A `maintains` in another
/// translation unit is not visible here, and this register does not pretend otherwise --
/// it books what the unit in front of it says.
fn erhaltene(baum: &Programm) -> std::collections::BTreeSet<String> {
    let mut m = std::collections::BTreeSet::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        if let ItemArt::Funktion(f) = &i.art {
            if f.klasse == Some(FnKlasse::Spec) {
                return;
            }
            for inv in &f.maintains {
                m.insert(inv.text.clone());
            }
        }
    });
    m
}

/// **Every `spec fn` of the unit with a predicate body, by name.**
///
/// `maintains baum_wohlgeformt` and `refines g` name a statement instead of making one, and
/// the statement is the body of the `spec fn` they name. **A manifest line that prints the
/// name has printed a pointer, not an obligation** -- which is the same complaint
/// `OFFEN.md` `O3` makes about the ordinal, one clause over.
///
/// *This is a LOOKUP and not a computation.* It resolves nothing the source does not already
/// say in one place, it crosses no unit boundary, and where the name resolves to nothing the
/// manifest says so instead of inventing a wording.
///
/// **THREE producers, and the first cut had only one** (measured 2026-09-03). With `spec fn`
/// alone, four `maintains` lines of the corpus came out with `--` as their text --
/// `antwortpflicht_paarig` (twice), `kind_zeigt_zurueck`, `belegt_hat_adresse`. None of them
/// is a missing statement: all four are `invariant <name> cost … runs … : <pred>` at a
/// `table` or a `group`, and the wording sat two constructs away. *An empty field with a
/// reason is honest; an empty field whose reason is that the lookup was too narrow is a
/// hole wearing a reason's clothes.*
fn spezpraedikate(baum: &Programm) -> std::collections::HashMap<String, gabbro_syntax::span::Span> {
    let mut m = std::collections::HashMap::new();
    crate::fuer_jedes_item(baum, &mut |i| match &i.art {
        ItemArt::Funktion(f) if f.klasse == Some(FnKlasse::Spec) => {
            if let FnRumpf::Pred(p) = &f.rumpf {
                m.insert(f.name.text.clone(), p.span);
            }
        }
        ItemArt::Tabelle(t) => {
            for inv in &t.invarianten {
                m.insert(inv.name.text.clone(), inv.pred.span);
            }
        }
        ItemArt::Gruppe(g) => {
            for inv in &g.invarianten {
                m.insert(inv.name.text.clone(), inv.pred.span);
            }
        }
        _ => {}
    });
    m
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
                    // **The anchor is the CALL, the wording is the CALLEE's clause.** The
                    // only kind where the two part company -- see `Pflicht::span`.
                    span: r.span,
                    textspan: Some(bed.span),
                    kein_text: None,
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

/// Every call of a block, sub-blocks and sub-expressions included.
///
/// *Without `unterbloecke` the count would find only the top level* -- and a call under a
/// lock or in an `observes` block is the same call. **The same lesson as `pruefe-abstieg.py`,
/// at a count instead of at a pass.**
///
/// ## `let x = f(…) else (e) { … }` was NOT among them, and that is measured (2026-09-03)
///
/// `eigene_ausdruecke` returns `Vec::new()` for a `LetSonst` and says why in its own comment:
/// *"`let x = f() else …` carries its call in the source, not in an `Expr`."* **So this walk
/// entered the body and missed one of its arms** -- the fifth time this folder records that
/// shape, and the first at the obligation register.
///
/// The consequence is not a smaller number, it is a SILENT one: every `requires` of a callee
/// reached through `let … else` produced no `V` line at all. Measured at
/// `messung/fragmente/F01.gab`:426 -- `revoke` calls `delete_leaf` that way, and
/// `delete_leaf` carries four `requires`; `PFLICHTEN.md` books two of them as LOGIC
/// obligations (`236` *the cap has no children*, `337` *every `victim` is a leaf when
/// `delete_leaf` sees it* -- *"the load-bearing statement of `revoke`"*). **Both were absent
/// from the manifest and nothing said so.**
///
/// `LetSonst::als_ruf()` exists for exactly this -- *"the passes that only care about calls
/// ask this way, instead of each of them having to know the new form"*. Nine passes ask;
/// this one did not.
fn rufe_im_block<'a>(b: &'a Block, aus: &mut Vec<&'a Ruf>) {
    for s in &b.anweisungen {
        if let StmtArt::Ruf(r) = &s.art {
            aus.push(r);
        }
        // **The `let … else` call, and it is a call like any other.** `als_ruf()` answers
        // `None` for the `place` form («B14b»), which unpacks an atomic and calls nothing --
        // so this arm adds no edge where there is none.
        if let StmtArt::LetSonst(l) = &s.art {
            if let Some(r) = l.als_ruf() {
                aus.push(r);
            }
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
                if let Some(p) = inv {
                    *n += 1;
                    aus.push(Pflicht {
                        art: Art::Schleifeninvariante,
                        funktion: funktion.to_string(),
                        gegenstand: format!("loop invariant #{n}"),
                        span: p.span,
                        textspan: Some(p.span),
                        kein_text: None,
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

type Spez = std::collections::HashMap<String, gabbro_syntax::span::Span>;

/// **The wording of a NAMED statement, or the reason there is none.**
///
/// `maintains I` and `refines g` carry a name; the statement is the `spec fn` body it names.
/// Two ways this comes back empty, and both are said out loud rather than papered over with
/// the name itself.
fn benannte_aussage(spez: &Spez, name: &str) -> (Option<gabbro_syntax::span::Span>, Option<&'static str>) {
    match spez.get(name) {
        Some(s) => (Some(*s), None),
        None => (
            None,
            Some(
                "the named statement is no `spec fn` with a predicate body, and no \
                 `table` or `group` invariant, in this unit",
            ),
        ),
    }
}

fn lauf(
    items: &[Item],
    spez: &Spez,
    gehalten: &std::collections::BTreeSet<String>,
    aus: &mut Vec<Pflicht>,
) {
    for item in items {
        match &item.art {
            ItemArt::Modul(m) => lauf(&m.items, spez, gehalten, aus),
            ItemArt::Funktion(f) => {
                // Eine `spec fn` schuldet nichts -- sie IST die Aussage (`M113`).
                if f.klasse == Some(FnKlasse::Spec) {
                    continue;
                }
                let rumpf_da = matches!(f.rumpf, FnRumpf::Block(_));
                for i in &f.maintains {
                    let (textspan, kein_text) = benannte_aussage(spez, &i.text);
                    aus.push(Pflicht {
                        art: Art::Erhaltung,
                        funktion: f.name.text.clone(),
                        gegenstand: i.text.clone(),
                        span: i.span,
                        textspan,
                        kein_text,
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
                    let ziel = g.teile.last().map(|i| i.text.as_str()).unwrap_or("?");
                    let (textspan, kein_text) = benannte_aussage(spez, ziel);
                    aus.push(Pflicht {
                        art: Art::Verfeinerung,
                        funktion: f.name.text.clone(),
                        gegenstand: format!("refines {ziel}"),
                        span: g.span,
                        textspan,
                        kein_text,
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
                for (n, e) in f.ensures.iter().enumerate() {
                    aus.push(Pflicht {
                        art: if rumpf_da { Art::Nachbedingung } else { Art::Fremdpflicht },
                        funktion: f.name.text.clone(),
                        gegenstand: format!("ensures #{}", n + 1),
                        // **The ordinal's cure, and it was a DROPPED FIELD** (`OFFEN.md`
                        // `O3`, 2026-09-03). Swap two `ensures` conjuncts and the register
                        // was byte-identical apart from the file name; the same binary in
                        // the same run already prints the terms apart under `--lean`. Here
                        // the wording comes out of the SOURCE, where the reader can check it.
                        span: e.span,
                        textspan: Some(e.span),
                        kein_text: None,
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
                    if let Some(p) = &r.requires {
                        aus.push(Pflicht {
                            art: Art::Geraetezusage,
                            funktion: d.name.text.clone(),
                            gegenstand: format!("reg {} requires", r.name.text),
                            span: p.span,
                            textspan: Some(p.span),
                            kein_text: None,
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
                    if let Some(p) = &ue.requires {
                        aus.push(Pflicht {
                            art: Art::Geraetezusage,
                            funktion: d.name.text.clone(),
                            gegenstand: format!("transition {} requires", ue.name.text),
                            span: p.span,
                            textspan: Some(p.span),
                            kein_text: None,
                            rumpf_da: false,
                            material: Material::Foreign,
                        });
                    }
                    // **And the STEP itself is a promise, `requires` or not** (2026-09-04).
                    //
                    // Until today a `transition` reached the register only through its
                    // `requires`, so the four `transition`s of `messung/fragmente/F04.gab`
                    // -- which carry none -- stood in no line at all
                    // (`PFLICHTEN-KORRESPONDENZ.md` rows 36-39, `DROPPED`).
                    //
                    // **The pre-state is ASSUMED, and that is measured, not argued.**
                    // `transition ack { DEVICE_STATUS: 0 -> ACK }` lowers to
                    //
                    // ```c
                    // static inline void VirtioPci_ack(VirtioPci *d) {
                    //     (*(volatile uint8_t *)(d->basis + 20)) = (uint8_t)1u;
                    // }
                    // ```
                    //
                    // -- the `0` on the left of the arrow is never read and never checked.
                    // *That the register WAS in the from-state, and that writing the word
                    // puts the device in the to-state, is a promise at hardware Gabbro
                    // never sees* -- which is this kind's defining property and not a
                    // widening of it. The `requires` is the GUARD; the step is the MOVE,
                    // and the two are different statements, so they get different lines.
                    if let (Some(erster), Some(letzter)) =
                        (ue.schritte.first(), ue.schritte.last())
                    {
                        aus.push(Pflicht {
                            art: Art::Geraetezusage,
                            funktion: d.name.text.clone(),
                            gegenstand: format!("transition {}", ue.name.text),
                            span: ue.span,
                            // The wording is the `transset` -- `DEVICE_STATUS: 0 -> ACK` --
                            // and not the whole item, whose `effects` say something else.
                            textspan: Some(erster.span.bis_zu(letzter.span)),
                            kein_text: None,
                            rumpf_da: false,
                            material: Material::Foreign,
                        });
                    }
                }
            }
            // **`walk … invariant` -- and until 2026-08-31 it stood in a C COMMENT.**
            //
            // The emitter writes *"COMPILE TIME (W6), not re-checked here"* into the
            // artefact. Measured that day: an unsatisfiable walk invariant passes with
            // `0 errors, 0 hints` -- no pass decides it, no template carries it, and the
            // certificate lists `walk` under DIRECT lowering. **W6 says the pass decided it;
            // no pass did.**
            //
            // The same shape as `reg … requires` before 2026-08-24, and the same cure: do
            // not refuse it, do not pretend to check it -- COUNT it. *A price that stands
            // nowhere looks like zero.*
            //
            // `rumpf_da: false` because there is no body at all: the statement is about the
            // mapping domain of the structure, not about what some function leaves behind.
            ItemArt::Walk(w) => {
                // **`down` and `leaf` -- the two predicates the descent RESTS on**
                // (2026-09-04, `PFLICHTEN-KORRESPONDENZ.md` rows 59 and 60).
                //
                // `down : roh when !it.PS` and `leaf : it.PS` are not checked anywhere.
                // The emitter compiles them into CLASSIFIERS --
                // `static inline bool <n>_steigt_ab(const <elem> *it) { return !it->PS; }`
                // (`emit.rs`) -- so the generated walk USES them and nothing decides
                // whether they describe the format correctly. *That an entry with `!PS`
                // really points at a next level of that node type is a statement about the
                // hardware table, owed by no function and settled by no pass* -- the same
                // standing as the `invariant` two lines below, and the reason `W` exists.
                //
                // The two are separate lines because they are separate statements: one
                // says what a NON-leaf is, the other what a leaf is, and a register that
                // merged them could not say which of the two a prover had taken up.
                aus.push(Pflicht {
                    art: Art::Walkinvariante,
                    funktion: w.name.text.clone(),
                    gegenstand: "down".to_string(),
                    span: w.ab.span,
                    // From the node type to the end of the guard: `roh when !it.PS`. The
                    // type is half the statement -- *which* level the entry points at --
                    // and a text that carried only the guard would drop it.
                    textspan: Some(w.ab.span.bis_zu(w.ab_wenn.span)),
                    kein_text: None,
                    rumpf_da: false,
                    material: Material::Foreign,
                });
                aus.push(Pflicht {
                    art: Art::Walkinvariante,
                    funktion: w.name.text.clone(),
                    gegenstand: "leaf".to_string(),
                    span: w.blatt.span,
                    textspan: Some(w.blatt.span),
                    kein_text: None,
                    rumpf_da: false,
                    material: Material::Foreign,
                });
                for i in &w.invarianten {
                    aus.push(Pflicht {
                        art: Art::Walkinvariante,
                        funktion: w.name.text.clone(),
                        gegenstand: format!("invariant {}", i.name.text),
                        // The `Invariante` carries its predicate, so the wording is HERE and
                        // not behind a name -- unlike `maintains`.
                        span: i.span,
                        textspan: Some(i.pred.span),
                        kein_text: None,
                        rumpf_da: false,
                        material: Material::Foreign,
                    });
                }
            }
            // **A `table` invariant that NO function maintains -- and it was the larger
            // hole of the two** (2026-09-04).
            //
            // The `W` docstring below carried the measurement since 2026-09-03 and refused
            // the repair for one reason: *"a ninth `Art` moves the header line."* **That
            // premise does not hold, and the refusal's own argument is why.** It says the
            // case is `W`'s argument *"one construct over"* -- and a statement that IS this
            // kind needs no new kind to be booked under it. What the ninth `Art` would have
            // bought is a separate LETTER, not a separate obligation.
            //
            // The rule has two conditions and each is the discharge it stands for:
            //
            //   * **no `maintains` names it** -- else the invariant is already an `E` at
            //     that function, and booking it here would be the same debt twice;
            //   * **the table carries no `ops`** -- else the generated mutations preserve
            //     it under the machine-checked template `table.ops.erhaltung`
            //     (`beweise/Table_Ops_Erhaltung.thy`), and a discharged duty is not open.
            //
            // *Neither condition is a filter over a hole; both name where the duty went.*
            ItemArt::Tabelle(t) => {
                if !t.ops.is_empty() {
                    continue;
                }
                for i in &t.invarianten {
                    if gehalten.contains(&i.name.text) {
                        continue;
                    }
                    aus.push(Pflicht {
                        art: Art::Walkinvariante,
                        funktion: t.name.text.clone(),
                        gegenstand: format!("invariant {}", i.name.text),
                        span: i.span,
                        textspan: Some(i.pred.span),
                        kein_text: None,
                        rumpf_da: false,
                        material: Material::Foreign,
                    });
                }
            }
            // **And a `group` invariant, for which there is no `ops` at all.** A group is
            // the construct for a statement that quantifies over SEVERAL carriers, so no
            // single `table … ops` could ever carry it -- the `maintains` test is the whole
            // rule here.
            ItemArt::Gruppe(g) => {
                for i in &g.invarianten {
                    if gehalten.contains(&i.name.text) {
                        continue;
                    }
                    aus.push(Pflicht {
                        art: Art::Walkinvariante,
                        funktion: g.name.text.clone(),
                        gegenstand: format!("invariant {}", i.name.text),
                        span: i.span,
                        textspan: Some(i.pred.span),
                        kein_text: None,
                        rumpf_da: false,
                        material: Material::Foreign,
                    });
                }
            }
            _ => {}
        }
    }
}

/// **The FORMAT of the emitted register, and it stands on line one.**
///
/// `CLAUDE.md` holds what happens when a document moves ahead of its readers: seven read
/// along and four go silently blind. A manifest has the same shape and a worse consequence
/// -- `SPRACHE.md` §15 calls it the artefact by which Gabbro carries its promise OUTWARD,
/// and `GABBROV.md` §2 rests a whole tool on it: *"GabbroV does not read the Gabbro program.
/// It reads the manifest."*
///
/// **So the order is: version field, then every reader on both versions, then the format.**
/// Without the field a reader that meets a newer manifest does not fail -- it MISREADS, and
/// a wrong number is worse than an absent one. *A field that costs one line buys every later
/// format change the right to be noticed.*
///
/// The three readers of this text, counted on 2026-09-03 before the field was written:
/// `crates/gabbro-check/tests/beispiele.rs`, `instrumente/pruefe-zahlen.py` and
/// `messung/gabbrov/manifest-lage.sh`. The `--isabelle` and `--lean` channels serialise the
/// SAME register ([`sammle`]) and are untouched by a change here.
/// **Fassung 2 -- the line carries what §15 promised it would** (2026-09-03).
///
/// `AUFTRAG-GABBROV.md` §4 names the target per line: **name · obligation text · anchor
/// (`file:line`) · class · state**, and `SPRACHE.md` §15 sketched exactly that shape:
///
/// ```text
/// obligation revoke.functional  "ensures !exists k in descendants of s: k.used"  offen
/// ```
///
/// Fassung 1 carried the name alone, and `OFFEN.md` `O3` measured what that is worth: swap
/// the first and third `ensures` conjunct of `beispiele/01-tabelle.gab` and the two registers
/// are byte-identical apart from the file name in the header. **`ensures #1` named one thing
/// before the swap and another after, and nothing reported the change.**
///
/// *It was a DROPPED FIELD, not a missing computation* -- the same binary in the same run
/// already prints the terms apart under `--lean` (`post_duty_2` … `post_duty_4`).
pub const MANIFESTFASSUNG: u32 = 2;

/// **The state of every obligation in this register, and there is exactly one.**
///
/// The register's second line has said it since the day it existed: *"What a HUMAN still owes
/// here. Counted, not discharged."* A field that can only take one value looks like waste --
/// but the reader on the other side is `GABBROV.md`'s tool, which writes `passed`/`refuted`/
/// `open` BACK, and a field that appears only once something is written into it cannot be
/// read before then.
const ZUSTAND: &str = "open";

/// **Where the text field stops -- and the number is measured, not chosen.**
///
/// The longest obligation text in the tree on 2026-09-03 is **106 characters**
/// (`einreihen :: ensures #2`, the queue's pairwise-distinct clause), so nothing is truncated
/// today and the limit is a bolt against a pathological clause rather than a working cut.
/// *It stands at nearly four times the longest one on purpose:* a limit set flush against
/// today's maximum starts cutting on the next clause somebody writes, and does it silently.
///
/// **Why not the certificate's 72:** measured, six of 110 texts were cut mid-clause there,
/// and `AUFTRAG-GABBROV.md` §4 wants the line readable without the source.
const TEXTGRENZE: usize = 400;

pub fn zeige(baum: &Programm, datei: &str, quelle: &str) -> (String, bool) {
    let p = sammle(baum);
    let index = gabbro_syntax::span::Zeilenindex::neu(quelle);
    // **`quelle` is not always there**, and the two cases must not read alike: a run without
    // the source has no wording and no line to give, and says so once instead of printing an
    // empty cell per line. *An anchor that points at the wrong line is worse than none* --
    // and so is a wording invented to fill a column.
    let ohne_quelle = quelle.is_empty();
    let mut s = String::new();
    // **Line one, before the file name.** A reader that cannot place the version has to be
    // able to stop at the FIRST line, not after parsing a header it may already misread.
    s.push_str(&format!("-- manifest-version {MANIFESTFASSUNG}\n"));
    s.push_str(&format!("-- Obligation register: {datei}\n"));
    s.push_str("-- What a HUMAN still owes here. Counted, not discharged.\n");
    s.push_str("-- obligation<TAB>name<TAB>class<TAB>anchor<TAB>state<TAB>obligation text\n");
    s.push_str(
        "--   anchor: where the obligation ARISES. For `V` that is the CALL SITE, and the \
         text is\n--   the callee's clause -- the one kind where the two differ. \
         `--` in a field: this run\n--   does not have it, and the reason stands beside \
         the closing count.\n\n",
    );
    if p.is_empty() {
        s.push_str("   no generated proof obligation in this unit\n\n");
    }
    let mut geschrieben = 0usize;
    let mut ohne_text = 0usize;
    // **The reasons come out of the DATA, not out of a sentence written here.** A closing
    // note that states the reason itself is a second register over the same thing: it stays
    // right while `Pflicht::kein_text` changes underneath it, and then the manifest explains
    // an emptiness by a cause that is no longer the cause.
    let mut gruende: Vec<&'static str> = Vec::new();
    for art in [Art::Verfeinerung, Art::Erhaltung, Art::Nachbedingung, Art::Fremdpflicht,
               Art::Vorbedingung, Art::Geraetezusage, Art::Schleifeninvariante,
               Art::Walkinvariante] {
        let eigene: Vec<&Pflicht> = p.iter().filter(|x| x.art == art).collect();
        if eigene.is_empty() {
            continue;
        }
        s.push_str(&format!("{}  {} ({})\n", art.marke(), art.name(), eigene.len()));
        for x in &eigene {
            let anker = if ohne_quelle {
                "--".to_string()
            } else {
                format!("{datei}:{}", index.stelle(quelle, x.span.von).zeile)
            };
            let text = match (ohne_quelle, x.textspan) {
                (true, _) => "--".to_string(),
                (false, Some(sp)) => crate::zeremonie::schnitt_bis(quelle, sp, TEXTGRENZE),
                (false, None) => "--".to_string(),
            };
            if text == "--" {
                ohne_text += 1;
                if let Some(g) = x.kein_text {
                    if !gruende.contains(&g) {
                        gruende.push(g);
                    }
                }
            }
            s.push_str(&format!(
                "obligation\t{} :: {}\t{}\t{}\t{}\t{}\n",
                x.funktion,
                x.gegenstand,
                art.marke(),
                anker,
                ZUSTAND,
                text
            ));
            geschrieben += 1;
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
    let wi = p.iter().filter(|x| x.art == Art::Walkinvariante).count();
    // **The header line MUST add up** -- `r + e + n + f + v == p.len()`. The first version of
    // this line did not carry the refinement and reported `1 obligations: 0, 0, 0, 0`.
    // *A balance that does not add up is the class `zaehle-p6.py` is built against* -- and it
    // arose here on exactly the day a new kind was added.
    //
    // **And it arose a SECOND time, on 2026-08-28, when `S` came.** The same assertion caught
    // it before any report was read. *That is what a balance is for: a new kind does not get
    // to be quietly uncounted, and the check does not depend on anyone noticing.*
    //
    // **A THIRD time on 2026-08-31, when `W` came** -- and again before the first report was
    // read. *Three for three: the line has now caught every kind that was added after it.*
    debug_assert_eq!(
        r + e + n + f + v + dz + si + wi,
        p.len(),
        "the obligation balance does not add up"
    );
    // **`unowned invariant` and not `walk invariant` since 2026-09-04.** The kind covers
    // three constructs (see `Art::name`), and a label that names one of them is the shape
    // this file already repaired at the `D` heading. *Measured before the word moved:* the
    // three readers of this line -- `pruefe-manifest.py`, `manifest-lage.sh` and
    // `pruefe-zahlen.py` -- match `^== N obligations:` and, in the last case, a prefix that
    // stops at `precondition`. **None of them reads this word**, so the change is a
    // correction to the artefact and not a format change; `MANIFESTFASSUNG` stays at 2.
    s.push_str(&format!(
        "== {} obligations: {r} refinement, {e} preservation, {n} postcondition, \
         {f} foreign, {v} precondition, {dz} device, {si} loop invariant, \
         {wi} unowned invariant ==\n",
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
    // **The empty fields, counted and given their reason -- never left to be guessed.**
    if ohne_quelle && !p.is_empty() {
        s.push_str(
            "   ANCHOR AND TEXT ARE `--` FOR EVERY LINE: this run was given no source.\n   \
             The obligations are the same ones; what is missing is the wording and the\n   \
             line, and a manifest that invented either would be worse than one that says\n   \
             it has neither.\n",
        );
    } else if ohne_text > 0 {
        s.push_str(&format!(
            "   {ohne_text} line(s) carry `--` as their text, and the reason is named:\n"
        ));
        for g in &gruende {
            s.push_str(&format!("     * {g}\n"));
        }
        s.push_str(
            "   *The name is in the second column; the wording is nowhere this run can see,\n   \
             and the field is left empty rather than filled with the name a second time.*\n",
        );
    }
    // **E1, INSIDE the tool** (`AUFTRAG-GABBROV.md` §5: *"wired in, not hung beside it. A tool
    // that does not check its own completeness has none."*).
    //
    // The loop above prints by KIND, out of a fixed list of eight. A ninth kind added to
    // `Art` and forgotten there would be counted by the header line and printed nowhere --
    // **the silent loss `SPRACHE.md` §15 promises against, inside the artefact that carries
    // the promise.** The `debug_assert` above catches an unbalanced header; it does not catch
    // a balanced header over a short body, and that is a different hole.
    //
    // *It is a hard check and not a `debug_assert`,* because a release build that loses a
    // kind loses it in the artefact a stranger reads.
    let vollstaendig = geschrieben == p.len();
    if !vollstaendig {
        s.push_str(&format!(
            "== E1 FAILED: {geschrieben} obligation line(s) written, {} counted ==\n   \
             A kind is counted in the header and printed in no line. Nothing here may be\n   \
             read as a complete register -- the missing lines are not visible from the\n   \
             outside, which is exactly why this comparison stands inside the run.\n",
            p.len()
        ));
    }
    (s, vollstaendig)
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
