//! **The names the GENERATOR forms -- the other half of the question `cnamen.rs` asks.**
//!
//! `cnamen.rs` holds the names **C** has already taken; `N041` refuses a declaration that
//! spells one of them. This module holds the names **Gabbro itself** forms -- and they are a
//! different population, because they do not exist until two declarations stand next to each
//! other:
//!
//! ```text
//! format Eintrag endian little { gueltig : bool @0, … }
//! ```
//!
//! `gueltig` is no C name and no duplicate. It becomes one only because the emitter writes
//! `Eintrag_gueltig` for the field AND `Eintrag_gueltig` for the validity predicate.
//! **`gabbro pruefe` said `0 errors, 0 hints`, `gabbro emit` wrote the unit without a `C001`,
//! and `cc` answered *redefinition of `Eintrag_gueltig`*.** (`C001` is the generator's own
//! refusal and lives in `emit.rs`; it stayed silent here, which is the point.)
//!
//! **Nine such forms are measured, not two** (`messung/ERZEUGERNAMEN.md` §2), and they fall
//! into two sorts that are one sentence:
//!
//! | sort | example | what meets what |
//! |---|---|---|
//! | inside one carrier | a field named `gueltig`; a field `setz_a` next to a field `a`; a variant named `marke`; a bank register `setz_LO` next to `LO` | two SUFFIXES of the same carrier |
//! | across two carriers | `table Kappe` next to `const Kappe_NONE`; `walk Baum` next to `type Baum_knoten`; `reason Fehler { Leer }` next to `const Fehler_Leer` | a second declaration spells a suffix of the first |
//!
//! *Two different Gabbro declarations get the same C name.* That is the whole rule, and it is
//! why this module enumerates instead of forbidding words. **A word list would be wrong in
//! both directions at once:** it would forbid `gueltig` where no `format` stands nearby, and
//! it would not know `Kappe_NONE`, because that word only exists next to the table.
//!
//! There is no renaming in between -- `cnamen.rs` says it in its first line: *there is no
//! `fn c_name` in `emit.rs`.* What stands in Gabbro stands in C, plus a suffix.

use gabbro_syntax::ast::*;
use gabbro_syntax::span::Span;

/// One C name the emitter forms, and the Gabbro identifier it was formed from.
pub struct Gebildet {
    pub name: String,
    /// The span of the user identifier that seeded it -- the one place the writer can change.
    pub span: Span,
    /// The shape, with the seed spelled out. The writer cannot read it off anywhere else.
    pub muster: &'static str,
    /// What stands behind the name in the generated unit.
    pub was: String,
    /// **Did the GENERATOR add anything?** `false` means the C name is the declared name,
    /// letter for letter -- a `fn`, a `const`, the struct of a `format`. `true` means a
    /// suffix or a prefix the writer never wrote.
    ///
    /// **This is the cut that keeps `N042` off two things that are not its business** --
    /// the rule itself is issued next door in `namen.rs`, this field only feeds it -- and
    /// both were measured over the corpus before the rule was narrowed:
    ///
    /// * `beispiele/29-undurchsichtig.gab` -- `pub impl fn pa_aus_zahl` in one module and
    ///   `extern fn pa_aus_zahl` in the next. Two declarations, one C symbol **on purpose**:
    ///   the second names the first. The emitter writes the prototype exactly once, and `cc`
    ///   is happy.
    /// * `messung/fragmente/F05.gab` -- `prim fn invoke … arch x86_64` and the same name
    ///   `arch aarch64`. One of the two is emitted per build; `arch` selects.
    ///
    /// And the same cut answers W7: five poison samples in `beispiele/gift/` are plain
    /// duplicate Gabbro names (`06-doppelt`, `31`, `32`, `140`, `274`). **`geltungsbereich`
    /// says those already**, and a second register over one thing is a second register.
    pub angehaengt: bool,
}

fn schiebe(v: &mut Vec<Gebildet>, name: String, span: Span, muster: &'static str, was: String) {
    v.push(Gebildet { name, span, muster, was, angehaengt: true });
}

/// The declared name itself -- no suffix, no prefix. See [`Gebildet::angehaengt`].
fn eigen(v: &mut Vec<Gebildet>, name: String, span: Span, muster: &'static str, was: String) {
    v.push(Gebildet { name, span, muster, was, angehaengt: false });
}

/// **Every C name the emitter forms from a user name -- read off `emit.rs`, not guessed.**
/// `messung/ERZEUGERNAMEN.md` §1 carries the line number for every arm below.
///
/// **What it deliberately leaves out, and one reason each** (W10):
///
/// * `{T}_speicher` (`emit.rs`:2244) -- written only where the source addresses the table BY
///   NAME. That set lives in the generator's `Namen`, not in the tree; a name listed here
///   that the emitter never writes would be a refusal without a defect.
/// * `{marke}_wachhund` (`emit.rs`:6191) -- a block label. Labels are not top-level names,
///   two functions may carry the same one, and the emitted marker is per block.
/// * Bodies. A `let` lowers to a local, and a local shadowing a file-scope name is legal C --
///   the same boundary `N041` draws, and for the same measured reason.
pub fn erzeugte_namen(baum: &Programm) -> Vec<Gebildet> {
    let mut v = Vec::new();
    crate::fuer_jedes_item(baum, &mut |item| match &item.art {
        // A struct, a reader and a writer per field, and ONE validity predicate over all
        // `where` clauses (`emit.rs`:3064, :3109, :3117, :3406).
        ItemArt::Format(f) => {
            let n = &f.name.text;
            eigen(&mut v, n.clone(), f.name.span, "{Format}", "the access struct".into());
            schiebe(
                &mut v,
                format!("{n}_gueltig"),
                f.name.span,
                "{Format}_gueltig",
                "the validity predicate over the `where` clauses".into(),
            );
            for g in &f.felder {
                schiebe(
                    &mut v,
                    format!("{n}_{}", g.name.text),
                    g.name.span,
                    "{Format}_{field}",
                    format!("the reader of `{}`", g.name.text),
                );
                // **The writer is conditional on `scale`, and that condition stands IN THE
                // TREE** -- unlike `{T}_speicher`, so it can be answered here.
                if g.typ.scale.is_none() {
                    schiebe(
                        &mut v,
                        format!("{n}_setz_{}", g.name.text),
                        g.name.span,
                        "{Format}_setz_{field}",
                        format!("the writer of `{}`", g.name.text),
                    );
                }
            }
        }
        // A `tagged type` is a tag enum plus a struct (`emit.rs`:2181-:2204); a plain `type`
        // is a name and nothing else.
        ItemArt::Typ(t) => {
            let n = &t.name.text;
            eigen(&mut v, n.clone(), t.name.span, "{Typ}", "the type name".into());
            if let Some(TypExpr::Varianten(varianten, _)) = &t.rumpf {
                schiebe(
                    &mut v,
                    format!("{n}_marke"),
                    t.name.span,
                    "{Tagged}_marke",
                    "the tag enum".into(),
                );
                for x in varianten {
                    schiebe(
                        &mut v,
                        format!("{n}_{}", x.name.text),
                        x.name.span,
                        "{Tagged}_{variant}",
                        format!("the tag value of `{}`", x.name.text),
                    );
                }
            }
        }
        ItemArt::Tabelle(t) => {
            let n = &t.name.text;
            eigen(&mut v, n.clone(), t.name.span, "{Tabelle}", "the carrier struct".into());
            schiebe(
                &mut v,
                format!("{n}_slot"),
                t.name.span,
                "{Tabelle}_slot",
                "the slot struct".into(),
            );
            // `{T}_NONE` falls away only above `2^32`, and that case is refused at the
            // generator (`emit.rs`:2265) -- so here it always stands.
            schiebe(
                &mut v,
                format!("{n}_NONE"),
                t.name.span,
                "{Tabelle}_NONE",
                "the `option index into` sentinel".into(),
            );
            for o in &t.ops {
                schiebe(
                    &mut v,
                    format!("{n}_{}", o.text),
                    o.span,
                    "{Tabelle}_{op}",
                    format!("the generated `{}` operation", o.text),
                );
            }
        }
        ItemArt::Reason(r) => {
            let n = &r.name.text;
            eigen(&mut v, n.clone(), r.name.span, "{Reason}", "the enum".into());
            for f in &r.faelle {
                schiebe(
                    &mut v,
                    format!("{n}_{}", f.name.text),
                    f.name.span,
                    "{Reason}_{case}",
                    format!("the enum value of `{}`", f.name.text),
                );
            }
        }
        ItemArt::Device(d) => {
            let n = &d.name.text;
            eigen(&mut v, n.clone(), d.name.span, "{Device}", "the handle struct".into());
            for b in &d.baenke {
                for r in &b.register {
                    schiebe(
                        &mut v,
                        format!("{n}_{}_{}", b.name.text, r.name.text),
                        r.name.span,
                        "{Device}_{bank}_{reg}",
                        format!("the bank reader of `{}`", r.name.text),
                    );
                    schiebe(
                        &mut v,
                        format!("{n}_{}_setz_{}", b.name.text, r.name.text),
                        r.name.span,
                        "{Device}_{bank}_setz_{reg}",
                        format!("the bank writer of `{}`", r.name.text),
                    );
                }
            }
            for x in &d.uebergaenge {
                schiebe(
                    &mut v,
                    format!("{n}_{}", x.name.text),
                    x.name.span,
                    "{Device}_{transition}",
                    format!("the transition `{}`", x.name.text),
                );
            }
        }
        ItemArt::Walk(w) => {
            let n = &w.name.text;
            for (anhang, was) in [
                ("EBENEN", "the level count"),
                ("WEITE", "the node width"),
                ("knoten", "the node struct"),
                ("ist_blatt", "the leaf predicate"),
                ("steigt_ab", "the descent predicate"),
                ("absteigen", "the descent function"),
            ] {
                schiebe(&mut v, format!("{n}_{anhang}"), w.name.span, "{Walk}_…", was.into());
            }
        }
        ItemArt::Lock(l) => {
            let n = &l.name.text;
            schiebe(&mut v, format!("{n}_nimm"), l.name.span, "{Lock}_nimm", "the acquire primitive".into());
            schiebe(&mut v, format!("{n}_gib"), l.name.span, "{Lock}_gib", "the release primitive".into());
            if l.geteilte_haltezeit.is_some() {
                schiebe(&mut v, format!("{n}_nimm_geteilt"), l.name.span, "{Lock}_nimm_geteilt", "the shared acquire primitive".into());
                schiebe(&mut v, format!("{n}_gib_geteilt"), l.name.span, "{Lock}_gib_geteilt", "the shared release primitive".into());
            }
        }
        ItemArt::Rcu(r) => {
            let n = &r.name.text;
            schiebe(&mut v, format!("{n}_lese_start"), r.name.span, "{Rcu}_lese_start", "the read-side entry".into());
            schiebe(&mut v, format!("{n}_lese_ende"), r.name.span, "{Rcu}_lese_ende", "the read-side exit".into());
        }
        ItemArt::Atomic(a) => {
            let n = &a.name.text;
            eigen(&mut v, n.clone(), a.name.span, "{Atomic}", "the atomic object".into());
            schiebe(&mut v, format!("{n}_ORDER"), a.name.span, "{Atomic}_ORDER", "the declared ordering".into());
        }
        ItemArt::Entry(e) => {
            let n = &e.name.text;
            schiebe(&mut v, format!("gabbro_eintritt_{n}"), e.name.span, "gabbro_eintritt_{Entry}", "the stub prototype".into());
            schiebe(&mut v, format!("gabbro_eintritt_{n}_VEKTOR"), e.name.span, "gabbro_eintritt_{Entry}_VEKTOR", "the vector number".into());
            schiebe(&mut v, format!("gabbro_eintritt_{n}_verteiler"), e.name.span, "gabbro_eintritt_{Entry}_verteiler", "the dispatch reference".into());
        }
        ItemArt::Boot(b) => {
            let n = &b.name.text;
            for (i, s) in b.schritte.iter().enumerate() {
                match s {
                    BootSchritt::Ruf(_) => schiebe(
                        &mut v,
                        format!("gabbro_boot_{n}_s{}", i + 1),
                        b.name.span,
                        "gabbro_boot_{Boot}_s{i}",
                        format!("the reference of step {}", i + 1),
                    ),
                    BootSchritt::Setzt { name, .. } => schiebe(
                        &mut v,
                        format!("gabbro_boot_{n}_{}", name.text),
                        name.span,
                        "gabbro_boot_{Boot}_{setzt}",
                        format!("the constant `{}`", name.text),
                    ),
                }
            }
        }
        // A function, a constant and a `static` form nothing from their name -- but the name
        // enters the pool, because five of the nine measured collisions are exactly of that
        // shape: a second declaration spelling a suffix of the first.
        ItemArt::Funktion(f) => {
            eigen(&mut v, f.name.text.clone(), f.name.span, "{fn}", "the function".into());
        }
        ItemArt::Konst(k) => {
            eigen(&mut v, k.name.text.clone(), k.name.span, "{const}", "the constant".into());
        }
        ItemArt::Statisch(s) => {
            eigen(&mut v, s.name.text.clone(), s.name.span, "{static}", "the object".into());
        }
        _ => {}
    });
    v
}
