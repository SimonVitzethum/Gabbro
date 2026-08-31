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
    sichtbarkeit(baum, absagen);
    fehlerkanal(baum, absagen);
    namenstypen(baum, absagen);
    beobachter(baum, absagen);
    formatklauseln(baum, absagen);
    bootschritte(baum, absagen);
    asm_versiegelt(baum, absagen);
    geltungsbereich(&baum.items, absagen);
    entrust_annahme(baum, absagen);
    verweigerte_zahltypen(baum, absagen);
    geister_haben_keinen_speicher(baum, absagen);
    pro_kern_und_gegenprobe(baum, absagen);
    dispatch_loest_auf(baum, absagen);
    maschineneigenschaft(baum, absagen);
    verbund_ohne_groesse(baum, absagen);
    check_traegt_seine_pflicht(baum, absagen);
    spiegel_und_sonde(baum, absagen);
    fnptr_traegt_seinen_vertrag(baum, absagen);
    name_gehoert_schon_c(baum, absagen);
    erzeugter_name_zweimal(baum, absagen);
}

/// **`N042` -- two declarations, one C name, and the generator formed both.**
///
/// `N041` next door holds the names **C** has taken. This one holds the names **Gabbro
/// itself** forms -- and they are a different population, because they do not exist until two
/// declarations stand next to each other:
///
/// ```text
/// format Eintrag endian little { gueltig : bool @0, rest : u64 @[63:1] reserved }
/// ```
///
/// `gueltig` is no C name, and it duplicates nothing at the Gabbro level. It becomes a
/// collision only because the emitter writes `Eintrag_gueltig` for the field reader **and**
/// `Eintrag_gueltig` for the validity predicate. *Measured against the unchanged checker*
/// (`messung/ERZEUGERNAMEN.md` §2): `gabbro pruefe` said `3 items, 0 errors, 0 hints`,
/// `gabbro emit` wrote the unit **without** a `C001`, and `cc` answered *redefinition of
/// `Eintrag_gueltig`*.
///
/// **Nine forms are measured, not one** -- inside a carrier (a field `gueltig`; a field
/// `setz_a` next to a field `a`; a variant `marke`; a bank register `setz_LO` next to `LO`)
/// and across two (`table Kappe` next to `const Kappe_NONE`; `walk Baum` next to `type
/// Baum_knoten`; `reason Fehler { Leer … }` next to `const Fehler_Leer`; `format Eintrag { a
/// … }` next to `extern fn Eintrag_a`). *A refusal that only knows `gueltig` moves the defect
/// to the next word.*
///
/// **And a tenth that `cc` does NOT catch, which is why this rule cannot be left to `cc`.**
/// `lock TOR` next to `extern fn TOR_nimm()` compiles clean: `void TOR_nimm(void);` twice
/// with the same type is a legal repetition in C. Two Gabbro declarations become **one
/// symbol**, the lock's acquire call lands in the foreign function at link time, and nothing
/// in the chain says a word. *A checker that only re-derives what `cc` finds does not find
/// it.*
///
/// **Why the CHECKER and not the generator** -- the same answer `N041` gives. A generator
/// that quietly disambiguates moves the explanation into an artefact nobody reads. The name
/// belongs to the writer, and so does the refusal.
///
/// > **What it costs, measured before it was built** (`messung/ERZEUGERNAMEN.md` §6): over
/// > the whole corpus the enumeration yields the collisions of the probes and **nothing
/// > else**. A rule whose first run over the clean corpus is silent is not a tightening of
/// > the tree; it is an answer to a case that had not been written down.
fn erzeugter_name_zweimal(baum: &Programm, absagen: &mut Absagen) {
    use std::collections::BTreeMap;
    let gebildet = crate::erzeugernamen::erzeugte_namen(baum);
    // **Sorted, and that is not taste.** Two collisions in one unit must come out in the same
    // order on every run, or the probe that pins the message is pinning a coin toss.
    let mut nach_namen: BTreeMap<&str, Vec<&crate::erzeugernamen::Gebildet>> = BTreeMap::new();
    for g in &gebildet {
        nach_namen.entry(g.name.as_str()).or_default().push(g);
    }
    for (name, gruppe) in nach_namen {
        if gruppe.len() < 2 {
            continue;
        }
        // **At least one side must be a name the GENERATOR built.** Two plain declared names
        // that are equal are a Gabbro duplicate, and `geltungsbereich` above already says so
        // -- W7: what one register holds, a second does not hold again. And where they are
        // NOT a defect (a prototype next to its definition in another module, two `prim fn`
        // separated by `arch`) this rule has no business at all. *Both were measured over the
        // corpus before the rule was narrowed* -- see `Gebildet::angehaengt`.
        if !gruppe.iter().any(|g| g.angehaengt) {
            continue;
        }
        // The refusal sits at the SECOND one: the first is the declaration that was there,
        // and a message at the first would ask the writer to move the wrong line.
        let erst = gruppe[0];
        for g in &gruppe[1..] {
            absagen.schiebe(
                Absage::fehler(
                    "N042",
                    g.span,
                    format!("`{name}` is the C name of two different declarations"),
                )
                .mit_notiz(format!(
                    "the generator forms `{name}` here as `{}` -- {}",
                    g.muster, g.was
                ))
                .mit_notiz(format!(
                    "and it forms the same name as `{}` -- {}",
                    erst.muster, erst.was
                ))
                .mit_notiz(
                    "the lowering goes to C and there is no renaming in between -- what \
                     stands in Gabbro stands in C, plus a suffix the generator adds",
                )
                .mit_notiz(
                    "measured 2026-08-31 with `cc -std=c11 -O0 -Wall -Wextra -Werror`; \
                     the nine forms and their probes stand in `messung/ERZEUGERNAMEN.md`",
                )
                .mit_notiz(
                    "rename one of the two -- the name is fine everywhere except where the \
                     other declaration stands next to it",
                ),
            );
        }
    }
}

/// **`N041` -- a name C has already taken.**
///
/// The generator writes the Gabbro name into C UNCHANGED -- there is no `fn c_name` in
/// `emit.rs`. So a declaration named `exit` becomes `_Noreturn void exit(void);`, and `cc`
/// answers *conflicting types for built-in function 'exit'; expected 'void(int)'*. **Measured
/// against the UNCHANGED checker before this rule existed** (`W24`, `messung/C-NAMEN.md` §1):
/// `gabbro pruefe` said `3 items, 0 errors, 0 hints`, `gabbro emit` wrote 20 lines of C, and
/// the third tool refused them. *That is exactly the state `PLAN-VOLLSTAENDIGKEIT.md` §2
/// forbids -- the checker accepts and there is no C.*
///
/// **Why the CHECKER and not the generator.** A generator that quietly renames `exit` to
/// `gabbro_exit` fixes the compile and moves the explanation into an artefact nobody reads.
/// The name belongs to the writer, and so does the refusal.
///
/// **And the refusal names the finding site.** A user who writes `fn exit()` did nothing
/// wrong -- they only do not know the lowering goes to C. `Klasse::fundort` says which side
/// of C owns the name and where it comes from; without that the message moves an explanation
/// into an error list.
///
/// > **What it costs, measured before it was built:** over the 418 `.gab` files and their 743
/// > distinct top-level item names, the 558-name table has **exactly one** hit -- `exit` in
/// > `messung/fragmente/F05.gab`, the file this rule was measured on. *A rule that forbids 558
/// > names and touches one line is not a tightening of the tree; it is an answer to a case
/// > nobody had written down.*
///
/// The rule holds every named item except `module` and `use`: a module declares no C
/// identifier, and `use` declares no name at all.
fn name_gehoert_schon_c(baum: &Programm, absagen: &mut Absagen) {
    crate::fuer_jedes_item(baum, &mut |item| {
        if matches!(item.art, ItemArt::Modul(_) | ItemArt::Use(_)) {
            return;
        }
        let Some(name) = item.art.name() else { return };
        let Some(klasse) = crate::cnamen::vergeben(&name.text) else { return };
        absagen.schiebe(
            Absage::fehler(
                "N041",
                name.span,
                format!("`{}` is a name C has already taken", name.text),
            )
            .mit_notiz(format!(
                "the lowering goes to C, and this declaration becomes `{}` in the generated \
                 unit -- the generator writes the name unchanged",
                name.text
            ))
            .mit_notiz(klasse.fundort(&name.text))
            .mit_notiz(
                "measured 2026-08-31 with `cc -std=c11 -O0 -Wall -Wextra -Werror`; \
                 the table and its command stand in `messung/C-NAMEN.md`",
            )
            .mit_notiz(
                "the name is fine everywhere except at the boundary -- rename the \
                 declaration, and nothing else has to move",
            ),
        );
    });
}

/// **The words an effect line may use at a function pointer type -- and why the list is
/// SHORTER than the one at an `fn` declaration.**
///
/// Nine pass files resolve the callee statically. At an indirect call there is no callee to
/// resolve, so each of them needs an answer -- and the answers are not equally cheap:
///
/// | effect | who reads it | does it cross an indirect call? |
/// |---|---|---|
/// | `reads` `writes` `allocs` `pure` `diverges` | `wirkungen`, via the hull | **yes** -- `aufrufgraph` folds the contract in and substitutes the arguments |
/// | `locks` `locks shared` | `geteilt` (`H005`, `H012`) | no -- the rank order is keyed by the callee's NAME |
/// | `masks` | `kontexte` (`H013`) | no -- same |
/// | `consumes` | `m2` (`L101`-`L105`) | no -- the position of a linear parameter comes from the callee's signature |
/// | `publishes` | `paarung` (`V001`-`V004`) | no -- the pairing matches two named sides |
///
/// **So the four in the lower half are refused at the TYPE, not ignored at the call.** That
/// is the whole difference between this and a silent hole: a program that would need the lock
/// order to cross an indirect call does not pass and is told why. *A gap that refuses is a
/// gap; a gap that passes is a false green.*
///
/// > **This is a measured NO, not an oversight.** Carrying the lock rank across an indirect
/// > call means ranking a callee that is chosen at run time -- and Caprock's four indirect
/// > call sites take no lock (`(t.senden)`, `(t.bereit)`, `(self.fence)` ×2, measured
/// > 2026-08-21). *The construct that would need it does not exist in the measured code.*
const TRAGBARE_WIRKUNGEN: [&str; 5] = ["reads", "writes", "allocs", "pure", "diverges"];

/// **`N035`/`N036`/`N037` -- a function pointer type carries its contract, or it is refused.**
///
/// Three rules, and the first is the one the whole item turns on:
///
/// * **`N035` -- no `effects`, or no `costs`.** Without `effects` the effect hull ends at
///   every indirect call; without `costs` an indirect call costs nothing and `K001` computes
///   with a number nobody promised. *Measured before the build: a `fn() -> bool` field
///   typechecked as `u32`, as `bool` and as a pointer in one file, 0 errors* (`probe/p8.gab`).
/// * **`N036` -- an effect no pass can carry across an indirect call.** See
///   `TRAGBARE_WIRKUNGEN` for the table and the reason per word.
/// * **`N037` -- a `requires` at the pointer type.** A precondition has to be checked at the
///   call site against the caller's state; the passes that do that (`geteilt` for
///   `Held(…)`, `m1` for the rest) are keyed by the callee's name. *Promising it here and
///   checking it nowhere is exactly the shape this item stands against.*
fn fnptr_traegt_seinen_vertrag(baum: &Programm, absagen: &mut Absagen) {
    crate::fuer_jedes_item_im_modul(baum, &mut |item, _modul| {
        crate::jeder_typausdruck_im_item(item, &mut |t| {
            let TypExpr::FnZeiger(f) = t else { return };
            // **One rule, one refusal site** -- the two missing clauses are two halves of
            // "this type carries no contract", not two rules. See `fnptr_passt` in `m1.rs`
            // for the same decision and `instrumente/pruefe-vergabe.py` for why it matters.
            let fehlt = match (f.effects.is_none(), f.costs.is_none()) {
                (true, true) => Some("`effects` and no `costs`"),
                (true, false) => Some("`effects`"),
                (false, true) => Some("`costs`"),
                (false, false) => None,
            };
            if let Some(fehlt) = fehlt {
                absagen.schiebe(
                    Absage::fehler(
                        "N035",
                        f.span,
                        format!("`{}` declares no {fehlt}", f.shape()),
                    )
                    .mit_notiz(
                        "a call through this pointer would end the effect hull -- `E008` \
                         became compositional on 2026-08-15, and an indirect call without a \
                         contract takes that back; without a bound the call would cost \
                         nothing and `K001` would hold a body against a number nobody \
                         promised",
                    )
                    .mit_notiz(
                        "the contract stands at the TYPE because that is the only thing a \
                         call site knows about a callee it cannot name",
                    ),
                );
            }
            for e in f.effects.iter().flat_map(|w| &w.liste) {
                let wort = e.art.text();
                let kopf = wort.split(' ').next().unwrap_or("");
                if TRAGBARE_WIRKUNGEN.contains(&kopf) {
                    continue;
                }
                absagen.schiebe(
                    Absage::fehler(
                        "N036",
                        e.span,
                        format!("`{kopf}` cannot be promised at a function pointer type"),
                    )
                    .mit_notiz(
                        "the pass that reads this effect resolves the callee by NAME, and an \
                         indirect call has none -- `locks`, `masks`, `consumes` and \
                         `publishes` therefore do not cross one",
                    )
                    .mit_notiz(
                        "this is a refusal and not an omission: the alternative was to let \
                         the promise through and check it nowhere",
                    ),
                );
            }
            // **`requires` and `ensures` are refused at a function pointer type -- and
            // `ensures` was ADDED to this refusal on 2026-08-21, one day after the type was
            // built.** It parsed, it stood in the grammar, and no pass read it. *A clause
            // without a reader is the shape this folder found four times in three days*
            // (`@version`, `nested masked`, `lock … masks irqs`, and this one).
            //
            // > **The alternative would have been to build a reader, and that was refused
            // > with a number**: the four indirect call sites in `caprock-messbasis` do not
            // > even take a lock, so the measured need for a postcondition at the pointer
            // > type is ZERO. *Rescuing a clause for a need nobody measured is the movement
            // > that killed `locks ordered`.*
            for (wort, span) in [
                ("requires", f.requires.first().map(|p| p.span)),
                ("ensures", f.ensures.first().map(|p| p.span)),
            ] {
                let Some(s) = span else { continue };
                absagen.schiebe(
                    Absage::fehler(
                        "N037",
                        s,
                        format!("a function pointer type carries no `{wort}`"),
                    )
                    .mit_notiz(
                        "a precondition is checked at the CALL SITE and a postcondition \
                         AFTER the call, and the passes that do either are keyed by the \
                         callee's name -- written here, both are promises checked nowhere",
                    ),
                );
            }
        });
    });
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
            ExprArt::Ruf(r) if r.heisst("Has") => {
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
                if let Some(n) = r.path().and_then(|p| p.teile.last()) {
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
                // An indirect call has no NAME here -- what it names is a place, and this
                // collector is asking after callee names.
                if let Some(n) = r.path().and_then(|p| p.teile.last()) {
                    aus.push((n.text.clone(), r.span));
                }
            }
            _ => {}
        }
        // **Der Abstieg über `crate::unterbloecke`** — erschöpfend über `StmtArt`. Vorher
        // fehlte der `exchange`-Rumpf: ein Ruf in einem `update(x) { … }` war unsichtbar.
        for e in crate::eigene_ausdruecke(s) {
            ex(e, aus);
        }
        for k in crate::unterbloecke(s) {
            sammle_rufe(k, aus);
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
    // **`N040` hangs here because the `Umgebung` already stands here.** Collecting it once
    // costs a walk over the whole tree; collecting it twice would cost two.
    typname_bekannt(baum, &u, absagen);
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
/// **`N040` -- a type name that does not exist, and the checker CONFIRMED it.**
///
/// Measured 2026-08-25 on `messung/fragmente/F01.gab`: `Allok` (:311) and `PhysAllocator`
/// (:200, :265) stand there as pointer targets and are **declared nowhere**.
///
/// ```text
/// extern fn nimm(a : ptr<normal, rw> Allok) …
/// impl fn f(a : ptr<normal, rw+own> PhysAllocator) … { nimm(a); }
///
/// $ gabbro pruefe ptr.gab      ->  3 Items, 0 Fehler, 0 Hinweise
/// $ gabbro emit  ptr.gab       ->  struct Allok;  struct PhysAllocator;  (kein C001)
/// $ cc -Werror -c ptr.c        ->  incompatible pointer type
/// ```
///
/// **This is not a false rejection but its counterpart: a false CONFIRMATION.** The checker
/// says "fine", the emitter writes C, and only the foreign compiler finds the mistake. *A
/// pass that holds two DIFFERENT undeclared names to be compatible has looked at neither.*
///
/// The cause sits in `umgebung::typexpr`: the `find_map` over `Traegerart::ALLE` falls back
/// to `Typ::Unbekannt` when no kind matches -- and **`Unbekannt` fell nowhere, it rode along
/// as an empty entry.** The comment at that site says it itself about an earlier case: *"a
/// filled map is no evidence of a complete map."*
///
/// **Reported at the MENTION, not at the declaration** -- there is none there.
fn typname_bekannt(baum: &Programm, u: &crate::umgebung::Umgebung, absagen: &mut Absagen) {
    fn im_typ(
        t: &TypExpr,
        modul: &str,
        u: &crate::umgebung::Umgebung,
        absagen: &mut Absagen,
    ) {
        match t {
            TypExpr::Pfad(p) => {
                if !matches!(u.typ_von_ausdruck_decl(modul, t), crate::typen::Typ::Unbekannt) {
                    return;
                }
                let Some(letzt) = p.teile.last() else { return };
                absagen.schiebe(
                    Absage::fehler(
                        "N040",
                        letzt.span,
                        format!("`{}` names no type", p.text()),
                    )
                    .mit_notiz(
                        "a type name resolves to a `type`, a `table`, a `format`, a \
                         `device`, a `walk` bound or a `reason` -- and this one to none of \
                         them",
                    )
                    .mit_notiz(
                        "without this the emitter writes a C forward declaration and the \
                         mistake surfaces at the foreign compiler, as an incompatible \
                         pointer -- a checker that CONFIRMS is worse than one that refuses",
                    ),
                );
            }
            TypExpr::Feld(a) => im_typ(&a.element, modul, u, absagen),
            TypExpr::Zeiger(z) => im_typ(&z.ziel, modul, u, absagen),
            TypExpr::Verbund(fs, _) => {
                for f in fs {
                    im_typ(&f.typ.typ, modul, u, absagen);
                }
            }
            _ => {}
        }
    }
    crate::fuer_jedes_item_im_modul(baum, &mut |i, modul| match &i.art {
        ItemArt::Funktion(f) => {
            for pa in &f.parameter {
                im_typ(&pa.typ, modul, u, absagen);
            }
            if let Some(e) = &f.ergebnis {
                im_typ(e, modul, u, absagen);
            }
        }
        ItemArt::Statisch(x) => im_typ(&x.typ, modul, u, absagen),
        _ => {}
    });
}

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
    // **Und ein LINEARER Wert gehoert genauso wenig in einen Speicherplatz** (2026-08-20).
    //
    // `gabbro blindstellen` nannte `linear in position slot field` als leer in BEIDEN
    // Korpora -- also weder ausgeloest noch bewacht -- und ein `linear type Parked` in einem
    // Slot ging mit null Fehlern durch. Die Geisthaelfte fiel seit jeher.
    //
    // **Der Grund ist ein anderer als beim Geist, und er ist der schaerfere.** Ein Geist hat
    // keinen SPEICHER; ein linearer Wert hat welchen (`SPRACHE.md`:721 -- *echte Ressource:
    // Bytes im Erzeugnis*). Was ihm fehlt, ist der PFAD: *„genau einmal verbraucht" ist eine
    // Aussage ueber einen Kontrollflusspfad, nicht ueber ein Feld.* Wer ihn in einen von
    // NSLOTS Plaetzen legt, hat ihn aus der Buchfuehrung genommen -- und M2 sagt darueber
    // nichts, weil es nichts sagen kann.
    //
    // > **Die Alternative steht im Korpus**: `beispiele/27-freiliste.gab` fuehrt Besitz in
    // > einer Tabelle als `bool` plus `option index into T`, und die Linearitaet lebt an den
    // > FUNKTIONEN, die den Platz vergeben und zurueckgeben. Das ist die Stelle, an der M2
    // > sie halten kann.
    sammle_lineare(&baum.items, &mut geister);
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
            Absage::fehler(
                "N011",
                span,
                format!("`{g}` is a ghost or linear type and cannot lie in {wo}"),
            )
            .mit_notiz(
                "a ghost value does not exist at run time -- the generator erases it, and an \
                 erased field shifts every field after it",
            )
            .mit_notiz(
                "a LINEAR value has storage but no PATH there: `consumed exactly once` is a \
                 statement about a control-flow path, not about a field -- in one of N slots \
                 it is out of the bookkeeping, and M2 says nothing because it CAN say nothing",
            )
            .mit_notiz(
                "both belong where the checker threads them: a parameter, a result, a `let`. \
                 For ownership IN a table see beispiele/27-freiliste.gab -- a `bool` plus an \
                 `option index into T`, and the linearity lives at the FUNCTIONS",
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
                "on most targets `f16` is a storage form plus a conversion, not native \
                 arithmetic. „Fully\" would mean emulation or computing in `f32` -- and then \
                 the DOUBLE ROUNDING f16 -> f32 -> f16 is a new trap, not a smaller edition \
                 of the same one. As a pure storage form it belongs to `format`",
            ),
            "f80" | "f128" | "float128" | "longdouble" | "long_double" => Some(
                "that is not a type but a platform lottery: 80 bit x87 on x86-Linux, \
                 128 bit elsewhere, equal to `double` on others again -- and the x87 rounds \
                 TWICE. Whoever needs more than `f64` names a precision; the corpus builds \
                 a ladder of software types for it (FRAGMENTE.md, «F0»/FF2)",
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
    for (name, _, _) in &r.felder {
        doppelt(&mut gesehen, &name.text, name.span, "Registerfeld", absagen);
    }
    // **Und die andere Haelfte von «B24», seit 2026-08-19: liegt das Bit im Register?**
    //
    // `N003` prueft die Ueberlappung seit dem 2026-08-14 -- dass ein Bit ueberhaupt IN sein
    // Wort passt, prueft bis heute niemand. Gemessen: `reg R : u32 fields { A @40, }` ging
    // mit 0 Fehlern durch. *Dieselbe Zeile, die am `format` `N007` heisst.*
    let (breite, wort) = crate::bitlage::aus_intty(&r.typ);
    let wortname = format!("{wort:?}").to_lowercase();
    for (i, (name, bp, _)) in r.felder.iter().enumerate() {
        if let Some(b) = crate::bitlage::lage_pruefen(bp, breite * 8, i, &name.text, &wortname) {
            absagen.schiebe(Absage::fehler(b.kennung, name.span, b.text).mit_notiz(b.notiz));
        }
    }

    // Ueberlappung der Bitlagen.
    let mut belegt: Vec<(u128, u128, &Ident)> = Vec::new();
    for (name, bp, _) in &r.felder {
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

/// **`N019` — ein Verbund, der sich selbst DEM WERT NACH enthält, hat keine Größe.**
///
/// Gefunden am 2026-08-19 von aussen, und der Befund hatte zwei Hälften:
///
/// ```gabbro
/// type Knoten = { a : u32, b : Knoten, };
/// ```
///
/// 1. Der Prüfer starb daran — *„thread 'main' has overflowed its stack"*. `typ_von_feld`
///    legte einen frischen Rekursionsschutz an, statt den mitgeführten zu nehmen.
/// 2. **Nach der Reparatur war es schlimmer:** null Fehler, und der Erzeuger schrieb
///    `typedef struct { uint32_t a; Knoten b; } Knoten;` — **kein gültiges C**. Ein
///    unvollständiger Typ in seinem eigenen `typedef`.
///
/// > *Der Absturz war laut und der Nachfolger still* — dieselbe Bewegung wie bei der
/// > Kostenarithmetik am selben Tag. **Ein Erzeuger, der etwas Unübersetzbares schreibt,
/// > macht jede Zusage der zwölf Pässe davor wertlos.**
///
/// **Der Zeiger ist die Ausnahme, und er ist die Antwort:** `b : ptr<normal, rw> Knoten`
/// hat eine Größe, `index into T` auch. Was hier fällt, ist ausschliesslich die Einbettung
/// DEM WERT NACH — und in Gabbro ist die verkettete Struktur ohnehin die Tabelle mit
/// `index into`, nicht der Zeigerknoten (`beispiele/09`).
fn verbund_ohne_groesse(baum: &Programm, absagen: &mut Absagen) {
    // Name -> die Typnamen, die seine Felder DEM WERT NACH nennen.
    let mut wert_kanten: std::collections::BTreeMap<String, Vec<Ident>> = std::collections::BTreeMap::new();
    let mut orte: std::collections::BTreeMap<String, Span> = std::collections::BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Typ(t) = &i.art else { return };
        let Some(TypExpr::Verbund(felder, _)) = &t.rumpf else {
            return;
        };
        orte.insert(t.name.text.clone(), t.name.span);
        let mut kanten = Vec::new();
        for f in felder {
            wertnamen(&f.typ.typ, &mut kanten);
        }
        wert_kanten.insert(t.name.text.clone(), kanten);
    });

    for (start, span) in &orte {
        // Erreicht der Typ sich selbst über lauter Wertkanten? Breitensuche, damit auch der
        // Ring über zwei und drei Namen fällt -- **ein Zyklus ist nicht nur Selbstbezug.**
        let mut offen = vec![start.clone()];
        let mut gesehen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        let mut weg: Option<String> = None;
        while let Some(n) = offen.pop() {
            for k in wert_kanten.get(&n).into_iter().flatten() {
                if &k.text == start {
                    weg = Some(n.clone());
                    offen.clear();
                    break;
                }
                if gesehen.insert(k.text.clone()) {
                    offen.push(k.text.clone());
                }
            }
        }
        let Some(ueber) = weg else { continue };
        let wie = if &ueber == start {
            format!("`{start}` contains itself")
        } else {
            format!("`{start}` contains itself through `{ueber}`")
        };
        absagen.schiebe(
            Absage::fehler("N019", *span, format!("{wie} by value -- that has no size"))
                .mit_notiz(
                    "a field of this type would have to be as large as the type it stands \
                     in -- there is no layout, and C has no way to write one",
                )
                .mit_notiz(
                    "the pointer is the exception: `ptr<…> T` and `index into T` have a \
                     size -- and in Gabbro the linked structure is the TABLE with `index \
                     into`, not the pointer node (`beispiele/09`)",
                ),
        );
    }
}

/// Die Typnamen, die ein Typausdruck **dem Wert nach** nennt — Zeiger und Index enden hier.
fn wertnamen(t: &TypExpr, aus: &mut Vec<Ident>) {
    match t {
        TypExpr::Pfad(p) => {
            if let Some(n) = p.teile.last() {
                aus.push(n.clone());
            }
        }
        // Ein Feld traegt seine Elemente dem Wert nach; `[Knoten; 4]` ist genauso unmoeglich.
        TypExpr::Feld(a) => wertnamen(&a.element, aus),
        TypExpr::Verbund(felder, _) => {
            for f in felder {
                wertnamen(&f.typ.typ, aus);
            }
        }
        TypExpr::Varianten(v, _) => {
            for va in v {
                if let Some(n) = &va.nutzlast {
                    wertnamen(n, aus);
                }
            }
        }
        // **Hier endet der Wert.** Ein Zeiger und ein Index haben eine Groesse, gleich was
        // am anderen Ende steht -- und das ist der ganze Unterschied.
        TypExpr::Zeiger(_)
        | TypExpr::Index { .. }
        | TypExpr::Int(_)
        | TypExpr::Float(_)
        | TypExpr::Bool(_)
        | TypExpr::Never(_)
        | TypExpr::FnZeiger(_) => {}
    }
}

/// **`N020`–`N022` — das `check`-Konstrukt bekommt seine Übersetzungsfehler.**
///
/// `SYNTAX.md` §13 verspricht **vier**: *„`gates` fehlt → die Pflicht wird nie verbraucht;
/// `can_fail` fehlt → dito; eine Grösse unter `measures`, die der gemessene Pfad SCHREIBT →
/// Schreibrecht; eine einseitige Schwelle ohne `floor` → die Grösse hat keinen Bereich."*
///
/// **Keiner davon existierte**, weil die `linear ghost Duty(check)` nirgends erzeugt wird —
/// `pruefe-klauseln.py` führte `gates` deshalb als ZUSAGE, und das ganze Konstrukt war das
/// einzige ohne Giftprobe: *eine Probe fiele an nichts.*
///
/// Die ersten beiden fallen heute schon **im Parser** — die Grammatik macht `gates` und
/// `can_fail` pflichtig (keine eckigen Klammern). Was fehlte, sind die anderen zwei und die
/// Frage, ob `gates` überhaupt jemanden nennt:
///
/// * **`N020`** — ein `gates`-Name, hinter dem keine Funktion steht. *Dann kann die Pflicht
///   von niemandem verbraucht werden, und das ist der erste der vier Fehler in der Form, in
///   der er ohne erzeugte `Duty` überhaupt fallen kann.*
/// * **`N021`** — eine Grösse unter `measures`, die der `can_fail`-Block **schreibt**.
///   *Der gemessene Pfad verändert seine eigene Messung.*
/// * **`N022`** — eine Grösse, gegen die der Block **einseitig** vergleicht, ohne dass
///   `floor` sie nennt. Dann hat sie nach unten keinen Bereich, und die Schwelle sagt nichts.
fn check_traegt_seine_pflicht(baum: &Programm, absagen: &mut Absagen) {
    // **Ein `gates`-Name ist eine Funktion ODER ein anderer `check`** -- und das hat der
    // Korpus berichtigt, nicht ich. Der erste Anlauf verlangte eine Funktion und meldete
    // `FRAGMENTE.md`:1167: `check kstack_eichung { … gates kstack }` gattert die EICHUNG des
    // Messgeraets vor die Messung. *Eine Pflicht kann von einer anderen Pflicht verbraucht
    // werden -- und genau so liest sich die Zeile: erst eichen, dann messen.*
    let mut traeger: Vec<String> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |i| match &i.art {
        ItemArt::Funktion(f) => traeger.push(f.name.text.clone()),
        ItemArt::Check(c) => traeger.push(c.name.text.clone()),
        _ => {}
    });
    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Check(c) = &i.art else { return };

        // **`N027` — ein `can_fail`-Block ist eine PROBE, kein Programm** (Rezension
        // 2026-08-20).
        //
        // Ein `check`-Item traegt keine `effects`-Liste, keine `costs`-Zusage und keine
        // `locks`-Deklaration -- es ist kein Vertrag. Die Paesse laufen ueber
        // `ItemArt::Funktion` und sahen diesen Block darum nie -- **M1 seit dem 2026-08-20
        // und der Wirkungspass seit dem 2026-08-25 nicht mehr**, der Rest weiterhin:
        //
        // ```gabbro
        // check c { … can_fail { a = 1; schreibt(); } … }   -- ohne H007/E005/E008
        // ```
        //
        // > **Ein Rumpf ohne Vertrag darf nichts tun, wofuer es einen Vertrag braucht.** Die
        // > Alternative waere, dem `check` eine Wirkungsliste zu geben -- das ist eine
        // > Sprachaenderung, und *aus der strengen Lesart kann man lockern, nie umgekehrt.*
        //
        // Was bleibt: lesen, rechnen, vergleichen, `return`. Genau das tut der Korpus
        // (`beispiele/06-annahmen.gab`), und genau das ist eine Gegenprobe.
        {
            fn probenrein(b: &Block, absagen: &mut Absagen) {
                for s in &b.anweisungen {
                    let (was, span) = match &s.art {
                        StmtArt::Zuweisung(z) => ("an assignment", z.ziel.span),
                        StmtArt::Sperrt(l) => ("a `locks` block", l.sperre.span),
                        StmtArt::Publish(pb) => ("a `publishes`", pb.ziel.span),
                        StmtArt::Exchange(e) => ("an `exchange`", e.ort.span),
                        _ => {
                            for k in crate::unterbloecke(s) {
                                probenrein(k, absagen);
                            }
                            continue;
                        }
                    };
                    absagen.schiebe(
                        Absage::fehler(
                            "N027",
                            span,
                            format!("a `can_fail` block contains {was}"),
                        )
                        .mit_notiz(
                            "a `check` carries no `effects`, no `costs` and no `locks` -- \
                             most passes walk functions and never see this block, so what \
                             stands here is unchecked",
                        )
                        .mit_notiz(
                            "a counterprobe reads, computes, compares and returns -- \
                             changing the world is what it is a probe ABOUT",
                        ),
                    );
                }
            }
            probenrein(&c.can_fail, absagen);
        }

        // -- N020: wer verbraucht die Pflicht?
        for g in &c.gates {
            if !traeger.iter().any(|f| f == &g.text) {
                absagen.schiebe(
                    Absage::fehler(
                        "N020",
                        g.span,
                        format!("`gates {}` names no declared function and no `check`", g.text),
                    )
                    .mit_notiz(
                        "the compiler generates a `linear ghost Duty(check)`, and `gates` \
                         names who consumes it -- a name behind which nothing stands means \
                         the obligation is never discharged",
                    )
                    .mit_notiz(
                        "a `check` may gate another one: `gates kstack` at the calibration \
                         says CALIBRATE FIRST, THEN MEASURE (`FRAGMENTE.md`:1167)",
                    ),
                );
            }
        }

        // -- N021: schreibt der gemessene Pfad seine eigene Messung?
        let mut ziele: Vec<Ort> = Vec::new();
        for s in &c.can_fail.anweisungen {
            crate::schreibziele(s, &mut ziele);
        }
        for m in &c.measures {
            let name = m.basis.text.clone();
            if let Some(z) = ziele.iter().find(|z| z.basis.text == name) {
                absagen.schiebe(
                    Absage::fehler(
                        "N021",
                        z.span,
                        format!("`{name}` stands under `measures` and the measured path writes it"),
                    )
                    .mit_notiz(
                        "then the check changes what it is measuring -- the report line \
                         would describe a state the run itself produced",
                    ),
                );
            }
        }

        // -- N022: eine einseitige Schwelle ohne `floor`.
        let mut verglichen: Vec<(String, Span)> = Vec::new();
        for s in &c.can_fail.anweisungen {
            einseitige_vergleiche(s, &mut verglichen);
        }
        for (name, span) in &verglichen {
            if !c.measures.iter().any(|m| &m.basis.text == name) {
                continue;
            }
            let genannt = c.floor.iter().any(|p| {
                let mut n = Vec::new();
                crate::gruppe::pred_namen_oeffentlich(p, &mut n);
                n.contains(name)
            });
            if !genannt {
                absagen.schiebe(
                    Absage::fehler(
                        "N022",
                        *span,
                        format!("`{name}` is compared one-sidedly and no `floor` names it"),
                    )
                    .mit_notiz(
                        "a one-sided threshold says nothing without a lower bound -- the \
                         quantity has no range, and `0 >= 0` passes every check",
                    ),
                );
            }
        }
    });
}

/// Die Grundnamen, gegen die ein Block **einseitig** vergleicht (`>=`, `>`, `<=`, `<`).
fn einseitige_vergleiche(s: &Stmt, aus: &mut Vec<(String, Span)>) {
    fn ex(e: &Expr, aus: &mut Vec<(String, Span)>) {
        if let ExprArt::Binaer(op, a, b) = &e.art {
            if matches!(
                op,
                BinOp::Kleiner | BinOp::KleinerGleich | BinOp::Groesser | BinOp::GroesserGleich
            ) {
                for seite in [a, b] {
                    let mut n = Vec::new();
                    namen_flach(seite, &mut n);
                    for x in n {
                        aus.push((x, e.span));
                    }
                }
            }
            ex(a, aus);
            ex(b, aus);
        }
    }
    for e in crate::eigene_ausdruecke(s) {
        ex(e, aus);
    }
    for k in crate::unterbloecke(s) {
        for i in &k.anweisungen {
            einseitige_vergleiche(i, aus);
        }
    }
}

fn namen_flach(e: &Expr, aus: &mut Vec<String>) {
    match &e.art {
        ExprArt::Ort(o) => aus.push(o.basis.text.clone()),
        ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => namen_flach(x, aus),
        ExprArt::Binaer(_, a, b) => {
            namen_flach(a, aus);
            namen_flach(b, aus);
        }
        _ => {}
    }
}

/// **`N023`/`N024` — `mirrors` und `counterprobe` bekommen ihre Leser.**
///
/// Die letzten zwei ZUSAGE-Klauseln aus `pruefe-klauseln.py`.
///
/// ## `mirrors` — die x86-Fassung von Falle 4
///
/// `mirrors GCMD from GSTS;` sagt: *der Zustand dieses Registers steht in jenem.* Der Grund
/// steht in `MESSUNGEN.md`: **ein Schreiben auf ein einzelnes Bit ist ein Lese-Ändere-Schreib-
/// Zug auf dem GANZEN Register** — und bei `class w` ist das unmöglich, weil sich das
/// Register nicht lesen lässt.
///
/// Damit ist die Zeile nur dann eine Aussage, wenn die **Richtung stimmt**:
///
/// * **`N023`** — beide Namen sind Register **dieses** Geräts, das gespiegelte ist **nicht
///   lesbar** und die Quelle **ist es**. *Steht es andersherum, sagt die Zeile nichts: ein
///   lesbares Register braucht keinen Spiegel, und aus einem unlesbaren kann keiner lesen.*
///
/// ## `counterprobe` — und hier stand zuerst eine ENTSCHEIDUNG
///
/// `SYNTAX.md`:975 sagte nicht, **wo** der `ident` hinter `expects` deklariert wird, und
/// darum stand die Klausel als ZUSAGE. *Erst die Entscheidung, dann der Pass* — sie lautet:
///
/// > **`expects` nennt eine äussere Sonde, genau wie `assume … falsifier`.** Sie steht nicht
/// > in Gabbro, weil sie LÄUFT; was Gabbro über sie sagen kann, ist, dass sie **genau einer**
/// > Verpflichtung gehört.
///
/// * **`N024`** — ein Sondenname trägt genau eine Verpflichtung. *Zwei Pflichten an einer
///   Sonde heisst: ein grüner Lauf entlastet beide, und eine davon hat nie jemand geprüft.*
///   Dieselbe Bauart wie die Doppelnamen an `walk`, `state` und `entry`.
fn spiegel_und_sonde(baum: &Programm, absagen: &mut Absagen) {
    // -- N023
    crate::fuer_jedes_item(baum, &mut |i| {
        let ItemArt::Device(d) = &i.art else { return };
        let Some(m) = &d.mirrors else { return };
        let klasse = |o: &Ort| {
            d.register
                .iter()
                .find(|r| r.name.text == o.basis.text)
                .map(|r| r.klasse)
        };
        for (o, wort) in [(&m.ziel, "mirrors"), (&m.quelle, "from")] {
            if klasse(o).is_none() {
                absagen.schiebe(
                    Absage::fehler(
                        "N023",
                        o.span,
                        format!("`{wort} {}` names no register of this device", o.text()),
                    )
                    .mit_notiz("`mirrors <reg> from <reg>` stands once per device and speaks about ITS registers"),
                );
            }
        }
        let lesbar = |k: RegKlasse| matches!(k, RegKlasse::Lesen | RegKlasse::LesenSchreiben | RegKlasse::Rc);
        if let (Some(z), Some(q)) = (klasse(&m.ziel), klasse(&m.quelle)) {
            if lesbar(z) {
                absagen.schiebe(
                    Absage::fehler(
                        "N023",
                        m.ziel.span,
                        format!("`{}` is readable and needs no mirror", m.ziel.text()),
                    )
                    .mit_notiz(
                        "`mirrors` exists for the write-only case: a single-bit write is a \
                         read-modify-write on the WHOLE register, and `class w` cannot be read",
                    ),
                );
            }
            if !lesbar(q) {
                absagen.schiebe(
                    Absage::fehler(
                        "N023",
                        m.quelle.span,
                        format!("`{}` is not readable, so nothing can be mirrored FROM it", m.quelle.text()),
                    )
                    .mit_notiz("the source of a mirror is the register that carries the state and can be read"),
                );
            }
        }
    });

    // -- N024: eine Sonde traegt genau eine Verpflichtung.
    let mut sonden: Vec<(String, Span, &'static str)> = Vec::new();
    crate::fuer_jedes_item(baum, &mut |i| match &i.art {
        ItemArt::Assume(a) => {
            if let AnnahmeKlasse::Falsifizierbar(n) = &a.klasse {
                sonden.push((n.text.clone(), n.span, "falsifier"));
            }
        }
        ItemArt::Axiom(a) => {
            if let AnnahmeKlasse::Falsifizierbar(n) = &a.klasse {
                sonden.push((n.text.clone(), n.span, "falsifier"));
            }
        }
        ItemArt::Check(c) => {
            if let Some((_, n)) = &c.counterprobe {
                sonden.push((n.text.clone(), n.span, "counterprobe"));
            }
        }
        _ => {}
    });
    for i in 0..sonden.len() {
        if let Some(j) = (0..i).find(|j| sonden[*j].0 == sonden[i].0) {
            absagen.schiebe(
                Absage::fehler(
                    "N024",
                    sonden[i].1,
                    format!(
                        "the probe `{}` already carries a {} obligation",
                        sonden[i].0, sonden[j].2
                    ),
                )
                .mit_notiz(
                    "a probe belongs to exactly ONE obligation -- two on one probe means a \
                     green run discharges both, and one of them nobody ever checked",
                )
                .mit_notiz(
                    "`expects` names an EXTERNAL probe, like `assume … falsifier`: it does \
                     not stand in Gabbro because it RUNS (SYNTAX.md §13, decided 2026-08-19)",
                ),
            );
        }
    }
}


/// **`N025` — `pub` war Zierde.**
///
/// `Umgebung::kandidaten_aufloesbar` trägt das Wort im Namen und reicht an `kandidaten`
/// durch, **ohne das Flag je anzusehen**. Gemessen 2026-08-19:
///
/// ```gabbro
/// module a { impl fn heimlich() … }        -- kein `pub`
/// module b { use a::heimlich; … }          -- 0 Fehler
/// ```
///
/// Sieben Deklarationsarten trugen `oeffentlich` — **seit dem 2026-08-25 sind es elf**, denn
/// `table`, `device`, `format` und `lock` haben das Wort dazubekommen (siehe
/// [`crate::bindung`]) —, und **keine einzige Stelle las es**. Das
/// ist nicht nur eine tote Klausel: `D004` — die Wand um einen `opaque type` — begründet sich
/// ausdrücklich mit *„die Tür ist die MODULGRENZE"*. **Eine Grenze, die niemand prüft, ist
/// keine**, und die Regel darüber stand auf einem Wort, das nichts hielt.
///
/// Die Sichtbarkeitsregel, wie sie jeder erwartet: ein Item aus Modul `M` ist sichtbar in `M`
/// selbst und in allem, was **in** `M` liegt; nach draussen nur mit `pub`.
///
/// *Gemeldet wird an der Bezugsstelle, nicht an der Deklaration* — dort steht der Fehler.
fn sichtbarkeit(baum: &Programm, absagen: &mut Absagen) {
    // Wer ist öffentlich? Schlüssel qualifiziert, wie überall.
    let mut offen: std::collections::HashMap<String, bool> = std::collections::HashMap::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let (name, oeff) = match &item.art {
            ItemArt::Funktion(f) => (&f.name, f.oeffentlich),
            ItemArt::Konst(k) => (&k.name, k.oeffentlich),
            ItemArt::Statisch(x) => (&x.name, x.oeffentlich),
            ItemArt::Typ(t) => (&t.name, t.oeffentlich),
            ItemArt::Atomic(a) => (&a.name, a.oeffentlich),
            // **The four carriers, since 2026-08-25.** Until then they carried no `pub`,
            // so this map could not hold them -- a `use a::T;` on a foreign table was
            // unobjectionable because `T` COULD not be private at all. *Now it can, and the
            // map holds it.*
            ItemArt::Tabelle(x) => (&x.name, x.oeffentlich),
            ItemArt::Lock(x) => (&x.name, x.oeffentlich),
            ItemArt::Format(x) => (&x.name, x.oeffentlich),
            ItemArt::Device(x) => (&x.name, x.oeffentlich),
            _ => return,
        };
        offen.insert(crate::umgebung::qualifiziere(modul, &name.text), oeff);
    });

    // Sichtbar in `von`? Im eigenen Modul und in allem, was DARIN liegt.
    let sieht = |offen: &std::collections::HashMap<String, bool>, ziel: &str, von: &str| {
        if offen.get(ziel).copied().unwrap_or(true) {
            return true;
        }
        let heim = crate::umgebung::modul_von(ziel);
        von == heim || von.starts_with(&format!("{heim}::"))
    };

    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let mut melde = |ziel: &str, span: Span, wie: &str| {
            if sieht(&offen, ziel, modul) {
                return;
            }
            absagen.schiebe(
                Absage::fehler(
                    "N025",
                    span,
                    format!(
                        "`{ziel}` is not `pub`, and `{}` is outside `{}`",
                        if modul.is_empty() { "the root" } else { modul },
                        crate::umgebung::modul_von(ziel)
                    ),
                )
                .mit_notiz(wie)
                .mit_notiz(
                    "an item is visible in its own module and in everything nested INSIDE it; \
                     outward only with `pub`",
                ),
            );
        };
        match &item.art {
            ItemArt::Use(u) => melde(&u.pfad.text(), u.pfad.teile[0].span, "a `use` line names it"),
            ItemArt::Funktion(f) => {
                if let FnRumpf::Block(b) = &f.rumpf {
                    let mut rufe: Vec<(String, Span)> = Vec::new();
                    sammle_qualifizierte_rufe(b, &mut rufe);
                    for (pfad, span) in rufe {
                        melde(&pfad, span, "this call names it");
                    }
                }
            }
            _ => {}
        }
    });
}

/// Die Rufe mit einem QUALIFIZIERTEN Pfad — nur die können eine Modulgrenze überschreiten.
fn sammle_qualifizierte_rufe(b: &Block, aus: &mut Vec<(String, Span)>) {
    fn aus_expr(e: &Expr, aus: &mut Vec<(String, Span)>) {
        if let ExprArt::Ruf(r) = &e.art {
            if r.path().is_some_and(|p| p.teile.len() > 1) {
                let p = r.path().expect("just checked");
                aus.push((p.text(), p.teile[0].span));
            }
            for a in &r.argumente {
                aus_expr(a, aus);
            }
        }
        match &e.art {
            ExprArt::Klammer(x) | ExprArt::Unaer(_, x) => aus_expr(x, aus),
            ExprArt::Binaer(_, a, b) => {
                aus_expr(a, aus);
                aus_expr(b, aus);
            }
            _ => {}
        }
    }
    for s in &b.anweisungen {
        for e in crate::eigene_ausdruecke(s) {
            aus_expr(e, aus);
        }
        if let StmtArt::Ruf(r) = &s.art {
            // A QUALIFIED call is `a::f(…)`; a place is never qualified, so an indirect call
            // is not one of these.
            if let Some(p) = r.path().filter(|p| p.teile.len() > 1) {
                aus.push((p.text(), p.teile[0].span));
            }
            for a in &r.argumente {
                aus_expr(a, aus);
            }
        }
        for k in crate::unterbloecke(s) {
            sammle_qualifizierte_rufe(k, aus);
        }
    }
}


/// **`A001`–`A004` — die Versiegelung eines `asm`-Rumpfes** («OPT3», 2026-08-19).
///
/// Ein Assemblerblock ist ein **Loch in jedem der zwölf Pässe**: M1 kennt die Bereiche
/// nicht, `effects` sieht die Berührungen nicht, `costs` kennt die Zahl nicht, M2 sieht den
/// Verbrauch nicht. Wer ihn ohne Pflichten einlässt, macht jede Zusage des Übersetzers zu
/// einer Aussage über das, was **vor** dem Block stand.
///
/// Geprüft wird deshalb nicht der Befehlstext — *den liest Gabbro nicht, und das ist der Kern
/// der Versiegelung* — sondern **dass die Pflichten dastehen**:
///
/// | | |
/// |---|---|
/// | `A001` | kein `arch` — auf einer anderen Maschine tut derselbe Text still etwas anderes |
/// | `A002` | kein `effects` — der Rufer trägt nichts, und der Rahmen endet hier |
/// | `A003` | kein `costs` — die Terminierungskette reisst |
/// | `A004` | ein Operand, der kein Parameter ist |
///
/// **`clobbers memory` ist die Vorgabe und keine Ausnahme** (`N026` als Hinweis): wer sie
/// weglässt, spart eine Zeile und verliert eine Zusage.
fn asm_versiegelt(baum: &Programm, absagen: &mut Absagen) {
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let FnRumpf::Asm(a) = &f.rumpf else {
            return;
        };
        if f.arch.is_none() {
            absagen.schiebe(
                Absage::fehler(
                    "A001",
                    f.name.span,
                    format!("`{}` has an `asm` body but names no `arch`", f.name.text),
                )
                .mit_notiz(
                    "the same instruction text does something else on another machine -- \
                     without `arch` this unit is silently wrong there",
                )
                .mit_notiz("`aarch64` is sealed in this folder: `arch aarch64` is an error, not a gap"),
            );
        }
        if f.effects.is_none() {
            absagen.schiebe(
                Absage::fehler(
                    "A002",
                    f.name.span,
                    format!("`{}` has an `asm` body but no `effects`", f.name.text),
                )
                .mit_notiz(
                    "the caller carries the effects of a call -- without the clause the frame \
                     ends at this function and every `pure` above it means nothing",
                ),
            );
        }
        if f.costs.is_none() {
            absagen.schiebe(
                Absage::fehler(
                    "A003",
                    f.name.span,
                    format!("`{}` has an `asm` body but no `costs`", f.name.text),
                )
                .mit_notiz("without it the termination chain tears at this call"),
            );
        }
        for (n, _) in a.ein.iter().chain(a.aus.iter()) {
            // **`result` ist der Rueckgabewert** -- gueltig genau dann, wenn es einen gibt.
            if n.text == "result" {
                if f.ergebnis.is_none() {
                    absagen.schiebe(
                        Absage::fehler(
                            "A004",
                            n.span,
                            format!("`{}` names `result` but returns nothing", f.name.text),
                        )
                        .mit_notiz("an `asm` operand named `result` needs a return type"),
                    );
                }
                continue;
            }
            if !f.parameter.iter().any(|p| p.name.text == n.text) {
                absagen.schiebe(
                    Absage::fehler(
                        "A004",
                        n.span,
                        format!("`{}` is not a parameter of `{}`", n.text, f.name.text),
                    )
                    .mit_notiz(
                        "an `asm` operand names a place the caller handed in; Gabbro does not \
                         read the instruction text and can check nothing else here",
                    ),
                );
            }
        }
        // **Die Vorgabe ist `memory`, nicht ihr Fehlen.** Ein Hinweis und keine Absage: es
        // gibt Befehle, die wirklich nichts anfassen -- aber wer das behauptet, soll es
        // sehen. *Wer die Vorgabe umdreht, spart eine Zeile und verliert eine Zusage.*
        if !a.zerstoert.iter().any(|z| z.text == "memory") {
            absagen.schiebe(
                Absage::hinweis(
                    "N026",
                    a.span,
                    "this `asm` block declares no `clobbers memory`".to_string(),
                )
                .mit_notiz(
                    "`memory` is the DEFAULT here, not the exception -- without it the C \
                     compiler may move memory accesses across the block",
                ),
            );
        }
    });
}

/// **Der Fehlerkanal, in beide Richtungen** («C3a», 2026-08-20).
///
/// `-> T or R` sagt, dass eine Funktion scheitern kann und woran. Zwei Regeln halten die
/// Aussage zusammen, und sie sind einander die Gegenprobe:
///
/// * **`N028`** -- ein `let x = f() else (e) { … }`, dessen `f` **kein** `or R` erklaert.
///   Der `else`-Zweig koennte nie laufen, und `e` benennt nichts. *Das ist dieselbe Klasse
///   wie `gates` ohne Torfunktion (`N020`) und `on_exceeded` ohne Namen (`S007`): eine
///   Klausel, deren Gegenstand nirgends steht.*
/// * **`N029`** -- ein Ruf auf ein `f` MIT `or R`, das nicht in einem `let … else` steht.
///   Der Fehler faellt dort auf den Boden. Der Rufer bekommt ihn nicht einmal zu sehen --
///   *und das ist genau das versteckte Kontrollflussloch, gegen das die Grammatik
///   `let … else` als EINZIGE Fehlerweitergabe fuehrt* (`SPRACHE.md` §8.1).
///
/// > **Ohne `N029` waere `or R` eine Zusage mit einem Schlupfloch daneben.** Der Erzeuger
/// > faenge den Fall an der Stelligkeit -- aber erst beim Absenken, und das ist die Lehre
/// > aus «B24»: *eine Regel, die nur auf der Erzeugerflaeche steht, beruehren die meisten
/// > Programme nie.*
fn fehlerkanal(baum: &Programm, absagen: &mut Absagen) {
    let mut kann_scheitern: std::collections::BTreeMap<String, String> = std::collections::BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            if let Some(r) = &f.fehler {
                kann_scheitern.insert(f.name.text.clone(), r.text.clone());
            }
        }
    });
    fn im_block(b: &Block, k: &std::collections::BTreeMap<String, String>, absagen: &mut Absagen) {
        for s in &b.anweisungen {
            if let StmtArt::LetSonst(l) = &s.art {
                if let Some(r) = l.als_ruf() {
                    let Some(n) = r.path().map(|p| p.text()) else { continue };
                    if !k.contains_key(&n) {
                        absagen.schiebe(
                            Absage::fehler(
                                "N028",
                                s.span,
                                format!(
                                    "`{n}` declares no `or <reason>`, so this `else` branch \
                                     can never run"
                                ),
                            )
                            .mit_notiz(
                                "`-> T or R` is where a function says that it can fail and at \
                                 what -- without it `e` names nothing",
                            ),
                        );
                    }
                }
            }
            // **Jeder ANDERE Ruf auf eine scheiternde Funktion faellt.** Auch der in einem
            // gewoehnlichen `let`, auch der als blosse Anweisung.
            let mut rufe = Vec::new();
            for e in crate::eigene_ausdruecke(s) {
                for x in crate::alle_ausdruecke(e) {
                    if let ExprArt::Ruf(r) = &x.art {
                        rufe.push((r.target_text(), x.span));
                    }
                }
            }
            if let StmtArt::Ruf(r) = &s.art {
                rufe.push((r.target_text(), s.span));
            }
            for (n, span) in rufe {
                if let Some(r) = k.get(&n) {
                    absagen.schiebe(
                        Absage::fehler(
                            "N029",
                            span,
                            format!(
                                "`{n}` can fail with `{r}`, and this call does not stand in a \
                                 `let … else`"
                            ),
                        )
                        .mit_notiz(
                            "`let … else` is the ONE form of error propagation in this \
                             language (SPRACHE.md 8.1) -- anywhere else the reason falls on \
                             the floor, unseen",
                        ),
                    );
                }
            }
            for u in crate::unterbloecke(s) {
                im_block(u, k, absagen);
            }
        }
    }
    // **`N034` -- ein eigener Rumpf erklaert `or R` und kann nie scheitern** (Stufe 7,
    // 2026-08-21).
    //
    // Der dritte Zahn derselben Zange, und er fehlte, weil es bis heute gar keine
    // Schreibform gab: *jede `-> T or R`-Signatur des Korpus stand an einem `extern fn`*,
    // also an einem Rumpf, den Gabbro nie sieht. Gemessen vor dem Bau:
    //
    // ```text
    // impl fn hol(x : u32) -> u32 or HolFehler … { return x; }
    //   ->  0 Fehler, 0 Hinweise      (gabbro pruefe, 2026-08-21)
    // ```
    //
    // Der Erzeuger schrieb dazu `(void)_grund;` mit dem Befund als Kommentar -- das Loch
    // stand im erzeugten C und in keiner Absage. **Jetzt steht es in einer.**
    //
    // > `extern fn` und `prim fn` sind ausgenommen und muessen es sein: dort IST die
    // > Deklaration alles, was Gabbro hat. *Die Regel spricht ueber Ruempfe, die dieser
    // > Uebersetzer sieht* -- W10, nicht abgewiesen ist nicht bestaetigt.
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let Some(r) = &f.fehler else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        // **Two shapes produce a reason, not one** (2026-08-30). `return R::C;` is the one
        // this rule was written for; `return e;` inside the `else` branch of a `let … else`
        // is the other, and `e` is the name that branch BINDS. Measured against the
        // unchanged checker: `return e;` was counted as no reason at all, so a body that
        // hands its caller the device's lie was told it never fails.
        //
        // *The test is syntactic on purpose:* which reason `e` carries is a question for M1,
        // but WHETHER this `return` goes out the error channel is decided by the binder
        // standing above it -- and that is right here in the tree.
        fn scheitert(b: &Block) -> bool {
            scheitert_mit(b, &mut Vec::new())
        }
        fn scheitert_mit(b: &Block, gebunden: &mut Vec<String>) -> bool {
            b.anweisungen.iter().any(|s| {
                if let StmtArt::Return(Some(e)) = &s.art {
                    if matches!(e.art, ExprArt::Grund { .. }) {
                        return true;
                    }
                    if let ExprArt::Ort(o) = &e.art {
                        if o.suffixe.is_empty() && gebunden.iter().any(|n| *n == o.basis.text) {
                            return true;
                        }
                    }
                }
                if let StmtArt::LetSonst(l) = &s.art {
                    gebunden.push(l.fehlername.text.clone());
                    let t = scheitert_mit(&l.sonst, gebunden);
                    gebunden.pop();
                    if t {
                        return true;
                    }
                    // Every OTHER sub-block of this statement stands outside the binding.
                    return crate::unterbloecke(s)
                        .into_iter()
                        .filter(|k| !std::ptr::eq(*k, &l.sonst))
                        .any(|k| scheitert_mit(k, gebunden));
                }
                crate::unterbloecke(s)
                    .into_iter()
                    .any(|k| scheitert_mit(k, gebunden))
            })
        }
        if !scheitert(b) {
            absagen.schiebe(
                Absage::fehler(
                    "N034",
                    f.name.span,
                    format!(
                        "`{}` declares `or {}`, and its body never returns a reason",
                        f.name.text, r.text
                    ),
                )
                .mit_notiz(
                    "`return <R>::<case>;` is how a body produces a reason -- without one \
                     the channel is a promise with no redeemer",
                )
                .mit_notiz(
                    "the lowering gives this function a `*_grund` out-parameter that no \
                     path ever writes",
                ),
            );
        }
    });
    // **Kein fruehes Aussteigen, wenn die Karte leer ist** -- `N028` ist gerade DANN faellig:
    // ein `let … else` in einer Einheit, in der keine Funktion scheitern kann, ist ein
    // `else`-Zweig ohne jeden Weg dorthin. *Die Abkuerzung haette die Regel um ihren
    // haeufigsten Fall gebracht.*
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            if let FnRumpf::Block(b) = &f.rumpf {
                im_block(b, &kann_scheitern, absagen);
            }
        }
        if let ItemArt::Check(c) = &item.art {
            im_block(&c.can_fail, &kann_scheitern, absagen);
        }
    });
}

/// **`N030` -- am Ruf wird der BEREICH gehalten und der NAME nicht** (2026-08-20).
///
/// Gefunden beim Schreiben von Caprocks Blockiergruenden. `SPRACHE.md` fuehrt den Fall als
/// Musterbeispiel:
///
/// > | **Lost wakeup** | **Z24** (ein Bit fuer vier Gruende) | **M2**: der Wecker verbraucht
/// > **genau seinen** Grund |
///
/// Sechs `linear ghost type`-Zeugen, je einer pro Grund, und `resume` nimmt `WartetPause`.
/// **Ein `resume`, das den IPC-Zeugen nimmt und an `pause_grund_weg` weiterreicht, ging mit
/// null Fehlern durch.** Dasselbe fuer zwei `opaque type` ueber demselben Traeger und fuer
/// `u32` an einem `bool`-Parameter.
///
/// M1 haelt den Bereich scharf -- `nimm_klein(4000)` faellt an `M101`. Was es nicht hat, ist
/// die NOMINALE Gleichheit: `Typ` ist ein Bereichsmodell, und zwei Namen ueber demselben
/// Traeger sind darin dasselbe.
///
/// ## Welche Typen nominal sind, und warum nicht alle
///
/// **`opaque`, `linear`, `ghost`, `tagged`** -- bei allen vieren ist die Nichtaustauschbarkeit
/// der ganze Zweck. `D003` sagt es fuer `opaque` schon: *ein `opaque type` hat nicht die
/// Arithmetik seines Traegers.*
///
/// **Ein Bereichsalias nicht.** `type Zaehler = u32 in 0 .. 65535` senkt zu seinem Traeger ab
/// und ist bauartbedingt durchsichtig; ihn nominal zu nehmen waere eine Sprachaenderung und
/// keine Luecke. *Aus der strengen Lesart kann man lockern, nie umgekehrt* -- hier steht die
/// engere Fassung derjenigen Menge, fuer die die Sprache die Unterscheidung behauptet.
///
/// ## Und die Regel schweigt, wo sie nichts weiss
///
/// Verglichen wird nur, wenn **beide** Seiten einen nominalen Namen tragen. Eine Zahl, eine
/// Rechnung, ein Feldzugriff liefern keinen -- und **W10: nicht abgewiesen ist nicht
/// bestaetigt.**
fn namenstypen(baum: &Programm, absagen: &mut Absagen) {
    use std::collections::BTreeMap;
    // Welche Namen sind NOMINAL? Siehe oben.
    let mut nominal: std::collections::BTreeSet<String> = Default::default();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Typ(t) = &item.art {
            if t.opaque || t.linear || t.ghost || t.tagged {
                nominal.insert(t.name.text.clone());
            }
        }
    });
    if nominal.is_empty() {
        return;
    }
    let nam = |t: &TypExpr| -> Option<String> {
        match t {
            TypExpr::Pfad(p) => p
                .teile
                .last()
                .map(|i| i.text.clone())
                .filter(|n| nominal.contains(n)),
            _ => None,
        }
    };
    // Je Funktion: die nominalen Typen ihrer Parameter und ihr nominaler Rueckgabetyp.
    let mut sig: BTreeMap<String, (Vec<Option<String>>, Option<String>)> = BTreeMap::new();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Funktion(f) = &item.art {
            sig.insert(
                f.name.text.clone(),
                (
                    f.parameter.iter().map(|p| nam(&p.typ)).collect(),
                    f.ergebnis.as_ref().and_then(&nam),
                ),
            );
        }
    });
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        // Die nominalen Bindungen DIESER Funktion -- Parameter und `let`.
        let mut lokal: BTreeMap<String, String> = BTreeMap::new();
        for p in &f.parameter {
            if let Some(n) = nam(&p.typ) {
                lokal.insert(p.name.text.clone(), n);
            }
        }
        fn sammle_lets(
            b: &Block,
            lokal: &mut BTreeMap<String, String>,
            sig: &BTreeMap<String, (Vec<Option<String>>, Option<String>)>,
            nam: &dyn Fn(&TypExpr) -> Option<String>,
        ) {
            for s in &b.anweisungen {
                if let StmtArt::Let(l) = &s.art {
                    let n = l.typ.as_ref().and_then(|t| nam(t)).or_else(|| {
                        let ExprArt::Ruf(r) = &l.wert.art else { return None };
                        r.path().and_then(|p| sig.get(&p.text())).and_then(|(_, e)| e.clone())
                    });
                    if let Some(n) = n {
                        lokal.insert(l.name.text.clone(), n);
                    }
                }
                for k in crate::unterbloecke(s) {
                    sammle_lets(k, lokal, sig, nam);
                }
            }
        }
        sammle_lets(b, &mut lokal, &sig, &nam);

        fn im_block(
            b: &Block,
            lokal: &BTreeMap<String, String>,
            sig: &BTreeMap<String, (Vec<Option<String>>, Option<String>)>,
            nam: &dyn Fn(&TypExpr) -> Option<String>,
            rueck: &Option<String>,
            absagen: &mut Absagen,
        ) {
            // Der nominale Name eines Ausdrucks -- **nur ein blanker Name**, und sonst
            // nichts. Eine Rechnung, eine Zahl, ein Feldzugriff liefern keinen, und dann
            // schweigt die Regel (W10).
            let von = |e: &Expr| -> Option<String> {
                let ExprArt::Ort(o) = &e.art else { return None };
                if !o.suffixe.is_empty() {
                    return None;
                }
                lokal.get(&o.basis.text).cloned()
            };
            let melde = |absagen: &mut Absagen, was: &str, hat: &str, erwartet: &str, span| {
                absagen.schiebe(
                    Absage::fehler(
                        "N030",
                        span,
                        format!("{was}: a `{hat}` where a `{erwartet}` is required"),
                    )
                    .mit_notiz(
                        "`opaque`, `linear`, `ghost` and `tagged` are NOMINAL -- that they \
                         are not interchangeable is the whole point of the four words. A \
                         range alias is transparent and is not compared here",
                    ),
                );
            };
            for s in &b.anweisungen {
                // **`let x : A = b;`** -- die Klausel steht da, also wird sie gehalten.
                if let StmtArt::Let(l) = &s.art {
                    if let (Some(erwartet), Some(hat)) =
                        (l.typ.as_ref().and_then(|t| nam(t)), von(&l.wert))
                    {
                        if hat != erwartet {
                            melde(absagen, "the binding", &hat, &erwartet, l.wert.span);
                        }
                    }
                }
                // **`return b;`** gegen den erklaerten Rueckgabetyp.
                if let StmtArt::Return(Some(w)) = &s.art {
                    if let (Some(erwartet), Some(hat)) = (rueck.clone(), von(w)) {
                        if hat != erwartet {
                            melde(absagen, "the return", &hat, &erwartet, w.span);
                        }
                    }
                }
                // **`a == b` ueber zwei verschiedenen nominalen Typen.** Was zwei
                // undurchsichtige Werte gemeinsam haben, ist ihr TRAEGER -- und genau den
                // verbirgt `opaque`. *Ein Vergleich darueber ist die Frage, die die
                // Deklaration nicht beantwortet.*
                for e in crate::eigene_ausdruecke(s) {
                    for x in crate::alle_ausdruecke(e) {
                        let ExprArt::Binaer(op, a, c) = &x.art else { continue };
                        if !matches!(op, BinOp::Gleich | BinOp::Ungleich) {
                            continue;
                        }
                        if let (Some(l), Some(r)) = (von(a), von(c)) {
                            if l != r {
                                melde(absagen, "the comparison", &l, &r, x.span);
                            }
                        }
                    }
                }
                let mut rufe: Vec<&Ruf> = Vec::new();
                for e in crate::eigene_ausdruecke(s) {
                    for x in crate::alle_ausdruecke(e) {
                        if let ExprArt::Ruf(r) = &x.art {
                            rufe.push(r);
                        }
                    }
                }
                if let StmtArt::Ruf(r) = &s.art {
                    rufe.push(r);
                }
                for r in rufe {
                    let Some((ps, _)) = r.path().and_then(|p| sig.get(&p.text())) else { continue };
                    for (i, a) in r.argumente.iter().enumerate() {
                        let Some(Some(erwartet)) = ps.get(i) else { continue };
                        let ExprArt::Ort(o) = &a.art else { continue };
                        if !o.suffixe.is_empty() {
                            continue;
                        }
                        let Some(hat) = lokal.get(&o.basis.text) else { continue };
                        if hat == erwartet {
                            continue;
                        }
                        absagen.schiebe(
                            Absage::fehler(
                                "N030",
                                a.span,
                                format!(
                                    "`{}` is a `{hat}`, and `{}` takes a `{erwartet}` there",
                                    o.basis.text,
                                    r.target_text()
                                ),
                            )
                            .mit_notiz(
                                "`opaque`, `linear`, `ghost` and `tagged` are NOMINAL -- that \
                                 they are not interchangeable is the whole point of the four \
                                 words. A range alias is transparent and is not compared here",
                            ),
                        );
                    }
                }
                for k in crate::unterbloecke(s) {
                    im_block(k, lokal, sig, nam, rueck, absagen);
                }
            }
        }
        let rueck = f.ergebnis.as_ref().and_then(&nam);
        im_block(b, &lokal, &sig, &nam, &rueck, absagen);
    });
}

/// **`N031` -- `observed by` ist kein Freibrief, sondern eine EINTRAGUNG.**
///
/// Die Klausel nimmt einem Atomic die Paarungspflicht ab («V9»), weil seine Gegenseite in
/// Silizium steht. **Damit wandert die Zusage in die Annahmenschicht, und dort gilt die
/// Regel, die dort seit jeher gilt:** eine Annahme muss erklaert und FALSIFIZIERBAR sein
/// (`N004`/`N005`, dieselbe Regel wie an `progress` und an `entrust`).
///
/// > *Eine Annahme, der keine Sonde je widersprechen kann, ist keine Isolation, sondern ein
/// > Wunsch* -- `beispiele/25` sagt den Satz ueber `entrust`, und er gilt hier woertlich.
///
/// Ohne diese Regel waere `observed by irgendwas` der bequemste Weg, `V001` loszuwerden --
/// und die Paarung haette ein Schlupfloch mit einem Namen darauf.
fn beobachter(baum: &Programm, absagen: &mut Absagen) {
    let annahmen = crate::annahmen(baum);
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Atomic(a) = &item.art else { return };
        let Some(b) = &a.beobachtet else { return };
        match annahmen.get(&b.text) {
            Some(true) => {}
            Some(false) => absagen.schiebe(
                Absage::fehler(
                    "N031",
                    b.span,
                    format!("`observed by {}` names an assumption without a falsifier", b.text),
                )
                .mit_notiz(
                    "the clause moves the pairing obligation into the ASSUMPTION layer, and \
                     there it must be refutable -- an assumption no probe can ever \
                     contradict is not isolation but a wish (beispiele/25)",
                ),
            ),
            None => absagen.schiebe(
                Absage::fehler(
                    "N031",
                    b.span,
                    format!("`observed by {}` names no `assume` and no `axiom`", b.text),
                )
                .mit_notiz(
                    "without it the clause would be the cheapest way to get rid of `V001` -- \
                     a loophole with a name on it",
                ),
            ),
        }
    });
}

/// **`N032` -- eine `where`-Klausel eines `format` nennt einen Namen, den es nicht gibt.**
///
/// Gefunden am 2026-08-20 von `pruefe-reichweite.py`, dem Gegenstueck zu
/// `gabbro blindstellen`: dort ist die Null *„diese Form schreibt niemand"*, hier *„diesen
/// Rumpf liest kein Pass"*. `Format` war eine von zwei Item-Arten mit Rumpf, die **genau ein
/// Pass** kannte -- und der kannte die Felder, nicht die Klauseln.
///
/// ```gabbro
/// format K endian big {
///     a : u32 where a <= nirgends_erklaert,   -- 0 Fehler
/// }
/// ```
///
/// > Die Klausel ist keine Verzierung: `PFLICHTEN.md` F10 begruendet mit ihr, warum **nach
/// > einem `format`-Zugriff keine Laengenpruefung mehr noetig ist** -- *„der Leser liefert
/// > NIE eine Struktur, die sie verletzt."* Eine Zusage, auf die andere Regeln bauen, und ihr
/// > Inhalt war ungelesen.
///
/// Erlaubt sind: die FELDER dieses Formats, `Self`, `lenof`/`sizeof`/`aligned` und die
/// Konstanten der Einheit. Alles andere steht nirgends.
fn formatklauseln(baum: &Programm, absagen: &mut Absagen) {
    let mut konstanten: std::collections::BTreeSet<String> = Default::default();
    crate::fuer_jedes_item(baum, &mut |item| {
        if let ItemArt::Konst(k) = &item.art {
            konstanten.insert(k.name.text.clone());
        }
    });
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Format(f) = &item.art else { return };
        let felder: std::collections::BTreeSet<&str> =
            f.felder.iter().map(|x| x.name.text.as_str()).collect();
        for feld in &f.felder {
            let Some(b) = &feld.bedingung else { continue };
            // **Erschoepfend ueber das Praedikat** -- `ausdruecke_im_praedikat` ist die
            // Fassung ohne Sammelzweig-Blindheit, die am 2026-08-20 gebaut wurde.
            let mut namen: std::collections::BTreeSet<String> = Default::default();
            for e in crate::ausdruecke_im_praedikat(b) {
                for x in crate::alle_ausdruecke(e) {
                    if let ExprArt::Ort(o) = &x.art {
                        namen.insert(o.basis.text.clone());
                    }
                    if let ExprArt::Ruf(r) = &x.art {
                        namen.insert(r.target_text());
                    }
                }
            }
            for n in &namen {
                if felder.contains(n.as_str())
                    || konstanten.contains(n)
                    || matches!(n.as_str(), "Self" | "lenof" | "sizeof" | "aligned" | "result")
                {
                    continue;
                }
                absagen.schiebe(
                    Absage::fehler(
                        "N032",
                        feld.span,
                        format!(
                            "the `where` clause of `{}.{}` names `{n}`, which is neither a \
                             field of this format nor a constant",
                            f.name.text, feld.name.text
                        ),
                    )
                    .mit_notiz(
                        "the clause is what PFLICHTEN.md F10 rests on -- after a `format` \
                         access no length check is needed because the reader NEVER delivers \
                         a structure that violates it. A promise other rules build on",
                    ),
                );
            }
        }
    });
}

/// **`O007` -- die Schritte einer Bootstrecke stehen in der Reihenfolge, die ihre
/// `advances`-Klauseln vorschreiben.**
///
/// Gefunden am selben Tag und vom selben Werkzeug. `Boot` war die zweite Item-Art mit einem
/// Rumpf, den genau ein Pass kannte -- und der kannte den `dispatch`, nicht die Schritte:
///
/// ```gabbro
/// boot multiboot1 arch x86_64 {
///     step caps_an();     -- advances mmu -> caps
///     step mmu_an();      -- advances roh -> mmu
/// }                       -- 0 Fehler
/// ```
///
/// **Das Konstrukt, das fuer die Bootreihenfolge da ist, prueft seine eigene Reihenfolge
/// nicht.** «B37» hat die Ordnung auf linearen Marken gebaut, weil *ein linearer Wert eine
/// Kette erzwingt, aber nicht WELCHE* -- und genau diese Frage blieb an der Stelle offen, an
/// der sie herkam.
///
/// *Fuer die Regel braucht es keine Marke*: die Schritte tragen keine Argumente, aber die von
/// ihnen gerufenen Funktionen tragen ihre `advances`-Klausel. Die Kette muss schliessen.
///
/// Ein Schritt, dessen Funktion diese Einheit nicht erklaert, faellt an **`N033`** -- das ist
/// dieselbe Klasse wie `on_exceeded` ohne Namen (`S007`) und `gates` ohne Torfunktion
/// (`N020`).
fn bootschritte(baum: &Programm, absagen: &mut Absagen) {
    let mut advances: std::collections::BTreeMap<String, (String, String)> = Default::default();
    let mut bekannt: std::collections::BTreeSet<String> = Default::default();
    crate::fuer_jedes_item(baum, &mut |item| {
        match &item.art {
            ItemArt::Funktion(f) => {
                bekannt.insert(f.name.text.clone());
                if let Some((von, nach)) = &f.advances {
                    advances.insert(f.name.text.clone(), (von.text.clone(), nach.text.clone()));
                }
            }
            // **Ein Bootschritt darf ein AXIOM nennen, und das ist der Normalfall.**
            //
            // `beispiele/07` schreibt `step write_cr3(BOOT_IDENTITAET);` -- und `write_cr3`
            // ist ein `axiom` mit Falsifikator, kein `fn`. *Ein privilegierter Befehl ist
            // genau das, was eine Bootstrecke tut*, und `SPRACHE.md` fuehrt ihn als die
            // groesste unbewiesene Flaeche der Sprache, deshalb zaehlbar.
            //
            // > Die erste Fassung dieser Regel meldete darauf zwei Fehler im eigenen
            // > Korpus -- und die Regel war es, die falsch lag, nicht die Datei.
            ItemArt::Axiom(a) => {
                bekannt.insert(a.name.text.clone());
            }
            ItemArt::Assume(a) => {
                bekannt.insert(a.name.text.clone());
            }
            _ => {}
        }
    });
    crate::fuer_jedes_item(baum, &mut |item| {
        let ItemArt::Boot(b) = &item.art else { return };
        let mut stand: Option<String> = None;
        for s in &b.schritte {
            let BootSchritt::Ruf(r) = s else { continue };
            let n = r.target_text();
            if !bekannt.contains(&n) {
                absagen.schiebe(
                    Absage::fehler(
                        "N033",
                        r.span,
                        format!("`step {n}` names nothing this unit declares"),
                    )
                    .mit_notiz(
                        "the same class as `on_exceeded` without a name (`S007`) and `gates` \
                         without a gate function (`N020`) -- a clause whose subject stands \
                         nowhere",
                    ),
                );
                continue;
            }
            let Some((von, nach)) = advances.get(&n) else { continue };
            if let Some(hier) = &stand {
                if hier != von {
                    absagen.schiebe(
                        Absage::fehler(
                            "O007",
                            r.span,
                            format!(
                                "`step {n}` advances `{von} -> {nach}`, and the sequence \
                                 stands at `{hier}`"
                            ),
                        )
                        .mit_notiz(
                            "«B37»: a linear value forces a CHAIN but not WHICH one -- the \
                             order is what the `advances` clauses say, and here they do not \
                             chain",
                        ),
                    );
                }
            }
            stand = Some(nach.clone());
        }
    });
}

/// Die **linearen** Typnamen ohne `ghost` -- siehe `geister_haben_keinen_speicher`.
fn sammle_lineare(items: &[Item], aus: &mut Vec<String>) {
    for i in items {
        match &i.art {
            ItemArt::Modul(m) => sammle_lineare(&m.items, aus),
            ItemArt::Typ(t) if t.linear && !t.ghost => aus.push(t.name.text.clone()),
            _ => {}
        }
    }
}
