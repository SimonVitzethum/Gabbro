//! **Lever 3 of `dokumente/PLAN-EINFACHHEIT.md`: explicitness as a VIEW.**
//!
//! `gabbro fmt --explicit` writes every derived clause out (for review, for the
//! certifier, for the unfamiliar reader); `gabbro fmt --elide` removes every
//! clause equal to what would be derived (for writing). Both run the same
//! checker on the same program; there is no second language.
//!
//! ## The one rule
//!
//! Both views draw on exactly the derivation the checker itself runs: the
//! effect fixpoint (`crate::ableitung::leite_ab`, wide) and the cost derivation
//! (`crate::kosten::abgeleitete_kosten`). Nothing is reimplemented here —
//! neither the deeds walk nor the pricing. Where the derivation stays a lower
//! bound, or where the callees promise more than the deeds cover (the two arms
//! of `N305`), there is nothing to write and nothing to remove: the views keep
//! their hands off.
//!
//! ## What `--explicit` writes
//!
//! For a function with a block body (never `spec`, never bodiless, never
//! `divergent` — see below) and an omitted clause the derivation settles:
//! `effects { … }` from the derived set, `costs <= N ops` from the derived
//! number. Entries render sorted, `pure` exactly when the set is empty beside
//! it. A written bound stays the enforced bound: nothing here is re-checked,
//! nothing is weakened.
//!
//! ## What `--elide` removes
//!
//! A written `effects` clause is removed where the derivation settles and the
//! written entries equal the derived ones (order-insensitive, `pure`
//! normalised on both sides). A written `costs <= N` bound is removed where
//! `N` is a plain number equal to what the body derives with this very clause
//! lifted (the hypothetical tree — the same derivation, not a second one),
//! and where no caller that promises a bound relies on it (see below).
//!
//! A written bound TIGHTER than the derived one is kept: it is a requirement,
//! not ceremony. So is a symbolic bound (`64 + 12 * lenof(m)` has no single
//! number to compare): it stands, always.
//!
//! ## Why the caller closure (costs)
//!
//! An omitted `costs` is silent (lane 191: no promise, no check), while a call
//! prices the DECLARED costs of the callee. Removing a bound a caller with a
//! written bound relies on moves the `K003` refusal to the caller: the clause
//! is load-bearing there, whatever it says here. So a bound goes only where
//! every in-unit caller that promises a bound goes too (direct edges and
//! `@lib#f` edges; indirect calls price the pointer contract, never the
//! callee's declaration).
//!
//! ## Why `divergent` stands outside both views
//!
//! `E003` reads the WRITTEN clause: a `divergent fn` without `diverges` among
//! its effects carries the hint, omitted or written-narrow alike. Writing the
//! derived set out would silence it; removing a written `diverges` would raise
//! it. Either way the diagnostics move, so both views skip `divergent` fns.
//!
//! ## What neither view touches, ever
//!
//! `ensures`, `requires`, invariants (`invariant`, `maintains`, loop
//! invariants), `decreases`, `deadline`, `by`, `section`, `arch`, `when`,
//! `payload`, `refines`, `advances`, `retires`, `maintains`, and every
//! function-pointer contract (`N035` owns the omission there). What a function
//! SHOULD do cannot be inferred (PLAN-EINFACHHEIT §2); everything else above
//! is either a proof hint or a promise no body could derive.
//!
//! ## Surgery, not printing
//!
//! Both views are byte-span edits over the source given: insertions at the
//! E4-ordered anchor (before the first clause behind the slot, else before the
//! body), deletions of the clause span plus trailing whitespace. Everything
//! untouched stays byte-identical, comments included. An edit whose anchor or
//! keyword scan fails is skipped, never guessed: a view that invents syntax
//! is not a view.

use gabbro_syntax::ast::*;
use std::collections::{BTreeMap, BTreeSet};

/// One planned edit: replace `[von, bis)` with `ersatz` (`von == bis` inserts).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Art {
    EffectsHinzu,
    CostsHinzu,
    EffectsWeg,
    CostsWeg,
    EffectsRewritten,
    CostsRewritten,
}

#[derive(Debug, Clone)]
pub struct Edit {
    pub art: Art,
    pub von: u32,
    pub bis: u32,
    pub ersatz: String,
}

/// One clause text waiting at an insertion anchor: a pure addition
/// (`ersatz: false`, the clause was omitted) or the second half of a
/// normalisation (`ersatz: true`, the written clause is deleted by a
/// companion edit and re-inserted here canonically). The distinction
/// keeps the counts honest: a normalised clause is one rewrite, not an
/// addition.
#[derive(Debug, Clone)]
struct Einsatz {
    text: String,
    ersatz: bool,
}

/// The corpus-wide count of what `--elide` would remove (and `--explicit`
/// would write): one planning run, counted by edit kind. No second register.
#[derive(Debug, Default)]
pub struct Zaehlung {
    pub effects_hinzu: usize,
    pub costs_hinzu: usize,
    pub effects_weg: usize,
    pub costs_weg: usize,
    /// Written clauses `--explicit` normalises to canonical form (same set,
    /// same bound — spacing, order and index abstraction only). The round
    /// trip closes over them: what `--elide` removes, `--explicit` writes
    /// back byte-identical.
    pub effects_rewritten: usize,
    pub costs_rewritten: usize,
    /// Functions neither view touches, with the reason (`divergent`, `spec`,
    /// bodiless, unsettled derivation, symbolic bound, relied-upon bound …).
    /// Bounded by the function count; it names the blind spot instead of
    /// leaving it silent.
    pub ausgelassen: Vec<(String, String)>,
}

impl Zaehlung {
    fn dazu(&mut self, edits: &[Edit]) {
        for e in edits {
            match e.art {
                Art::EffectsHinzu => self.effects_hinzu += 1,
                Art::CostsHinzu => self.costs_hinzu += 1,
                Art::EffectsWeg => self.effects_weg += 1,
                Art::CostsWeg => self.costs_weg += 1,
                Art::EffectsRewritten => self.effects_rewritten += 1,
                Art::CostsRewritten => self.costs_rewritten += 1,
            }
        }
    }
}

/// The derivation both views read: exactly what the checker runs over this
/// tree (wide effects fixpoint, cost derivation, filled call graph for the
/// hull behind `deckungsluecke` and `E009`, environment for written bounds).
struct Sicht {
    ab: crate::ableitung::Ableitung,
    kosten: BTreeMap<String, i128>,
    voll: crate::aufrufgraph::Graph,
    u: crate::umgebung::Umgebung,
}

fn sicht(baum: &Programm) -> Sicht {
    Sicht {
        ab: crate::ableitung::leite_ab(baum, true),
        kosten: crate::kosten::abgeleitete_kosten(baum),
        voll: crate::aufrufgraph::erhebe(baum),
        u: crate::umgebung::Umgebung::sammle(baum),
    }
}

/// The derived effect set where one stands: settled fixpoint, callees promise
/// nothing beyond the deeds (the `N305` arms), and the filled hull is complete
/// (else writing the clause would raise `E009` where the omission is silent,
/// and removing it would take the hint away — same diagnostics either way).
fn satz(s: &Sicht, key: &str) -> Option<BTreeSet<String>> {
    let a = s.ab.je.get(key)?;
    if a.unvollstaendig.is_some() {
        return None;
    }
    let h = s.voll.huelle(key);
    if h.unvollstaendig.is_some() {
        return None;
    }
    if crate::ableitung::deckungsluecke(&a.wirkungen, &h).is_some() {
        return None;
    }
    Some(a.wirkungen.clone())
}

/// `pure` normalised away on both sides of an equality: a derived set carries
/// the word over call edges (`ersetze` leaves it untouched), a written list
/// never stands it beside another entry (`E002`). `{"pure"}` and `{}` are the
/// same clause.
fn normiere(menge: &BTreeSet<String>) -> BTreeSet<String> {
    menge.iter().filter(|w| w.as_str() != "pure").cloned().collect()
}

fn geschrieben_normiert(w: &Wirkungen) -> BTreeSet<String> {
    w.liste.iter().map(|e| e.art.text()).filter(|t| t != "pure").collect()
}

/// Whether a derived set is writable verbatim: no entry carries an
/// abstracted index. The checker spells indices as `[…]` (`Ort::text`), which
/// no reader parses back — and writing the prefix instead would WIDEN the
/// clause (a wider `eigen` over a narrower derivation narrows nothing, but a
/// removed-then-rewritten wider clause does not come back byte-identical, and
/// `H011` compares lock places exactly). What is not writable stays as it
/// stands, in both views: the round trip closes over untouched bytes.
fn schreibbar(menge: &BTreeSet<String>) -> bool {
    !menge.iter().any(|e| e.contains('['))
}

/// The clause an elaborator would write: sorted entries, `pure` exactly where
/// nothing else stands. `diverges` is kept where the derivation carries it —
/// dropping it would narrow the clause behind the reader's back. Only called
/// where `schreibbar` holds, so every entry stands as derived.
fn formuliere(menge: &BTreeSet<String>) -> String {
    let eintraege: Vec<&str> =
        menge.iter().filter(|w| w.as_str() != "pure").map(|s| s.as_str()).collect();
    if eintraege.is_empty() {
        "effects { pure }".to_string()
    } else {
        format!("effects {{ {} }}", eintraege.join(", "))
    }
}

// ---------------------------------------------------------------------------------------
// Byte surgery helpers
// ---------------------------------------------------------------------------------------

fn ist_wortzeichen(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// The keyword `wort` ending at `pos` (whitespace before `pos` skipped),
/// with word boundaries on both sides. `None` where it does not stand —
/// the caller skips the function instead of guessing.
fn schluesselwort_rueckwaerts(quelle: &str, mut pos: usize, wort: &str) -> Option<usize> {
    let b = quelle.as_bytes();
    while pos > 0 && b[pos - 1].is_ascii_whitespace() {
        pos -= 1;
    }
    if pos < wort.len() {
        return None;
    }
    let anfang = pos - wort.len();
    if quelle.get(anfang..pos) != Some(wort) {
        return None;
    }
    if anfang > 0 && ist_wortzeichen(b[anfang - 1]) {
        return None;
    }
    Some(anfang)
}

/// The keyword `wort` starting at `pos` (whitespace skipped); returns its end.
fn schluesselwort_vorwaerts(quelle: &str, mut pos: usize, wort: &str) -> Option<usize> {
    let b = quelle.as_bytes();
    while pos < b.len() && b[pos].is_ascii_whitespace() {
        pos += 1;
    }
    if quelle.get(pos..pos + wort.len()) != Some(wort) {
        return None;
    }
    let nach = pos + wort.len();
    if nach < b.len() && ist_wortzeichen(b[nach]) {
        return None;
    }
    Some(nach)
}

/// The whole `costs <= EXPR ops` clause around a bound expression: backwards
/// over `<=` to the keyword, forwards over the `ops` word. Parser-anchored on
/// both sides — the expression span comes out of the parse, never guessed.
fn kosten_spanne(quelle: &str, e: &Expr) -> Option<(usize, usize)> {
    let b = quelle.as_bytes();
    let mut pos = e.span.von as usize;
    while pos > 0 && b[pos - 1].is_ascii_whitespace() {
        pos -= 1;
    }
    if pos < 2 || quelle.get(pos - 2..pos) != Some("<=") {
        return None;
    }
    let anfang = schluesselwort_rueckwaerts(quelle, pos - 2, "costs")?;
    let nach = schluesselwort_vorwaerts(quelle, e.span.bis as usize, "ops")?;
    Some((anfang, nach))
}

/// Clause span plus the whitespace run behind it, so no double space and no
/// orphaned blank line stays behind a removal.
fn mit_folge_ws(quelle: &str, bis: usize) -> usize {
    let b = quelle.as_bytes();
    let mut p = bis;
    while p < b.len() && b[p].is_ascii_whitespace() {
        p += 1;
    }
    p
}

/// Insertion anchor in E4 order: before the first clause behind the slot
/// (`costs` only for `effects`), else before the body. Every keyword scan is
/// local (the word stands directly before its content); a failed scan skips
/// the function.
fn einfuegepunkt(quelle: &str, f: &FnDecl, rumpf_von: usize, fuers_effects: bool) -> Option<usize> {
    let mut punkte = vec![rumpf_von];
    if fuers_effects {
        if let Some(c) = &f.costs {
            punkte.push(kosten_spanne(quelle, c)?.0);
        }
    }
    if let Some(d) = &f.deadline {
        punkte.push(d.span.von as usize);
    }
    if let Some(e) = &f.decreases {
        punkte.push(schluesselwort_rueckwaerts(quelle, e.span.von as usize, "decreases")?);
    }
    if let Some(e) = f.by.first() {
        punkte.push(schluesselwort_rueckwaerts(quelle, e.span.von as usize, "by")?);
    }
    if let Some(e) = &f.section {
        punkte.push(schluesselwort_rueckwaerts(quelle, e.span.von as usize, "section")?);
    }
    if let Some(e) = &f.arch {
        punkte.push(schluesselwort_rueckwaerts(quelle, e.span.von as usize, "arch")?);
    }
    if let Some(e) = &f.when {
        punkte.push(schluesselwort_rueckwaerts(quelle, e.span.von as usize, "when")?);
    }
    punkte.into_iter().min()
}

// ---------------------------------------------------------------------------------------
// Planning
// ---------------------------------------------------------------------------------------

/// A function body the views may touch: block-bodied, not `spec` (a proof
/// body derives nothing), not `divergent` (`E003` reads the written word).
/// Returns the key and the body start (the insertion anchor base).
fn kandidat(
    item: &Item,
    modul: &str,
    zaehlung: &mut Zaehlung,
) -> Option<(String, FnDecl, usize)> {
    let ItemArt::Funktion(f) = &item.art else {
        return None;
    };
    let key = crate::umgebung::qualifiziere(modul, &f.name.text);
    if f.klasse == Some(FnKlasse::Spec) {
        zaehlung.ausgelassen.push((key, "spec fn carries no runtime effect".to_string()));
        return None;
    }
    if f.klasse == Some(FnKlasse::Divergent) {
        zaehlung
            .ausgelassen
            .push((key, "`E003` reads the written `diverges`".to_string()));
        return None;
    }
    let FnRumpf::Block(b) = &f.rumpf else {
        zaehlung.ausgelassen.push((key, "no body to derive from".to_string()));
        return None;
    };
    Some((key, f.clone(), b.span.von as usize))
}

/// Whether the effects side is the translator's own word: `N202` demands the
/// WRITTEN `effects { pure }` there, so the views keep their hands off it
/// (removing it refuses, rewriting it is pointless — it already stands
/// canonical where it stands).
fn ist_uebersetzer(f: &FnDecl) -> bool {
    f.translator_fuer.is_some()
}

/// The hypothetical bound: what the body derives with this very clause
/// lifted. `None` where nothing settles or the written bound is symbolic.
fn hypothetisch(baum: &Programm, s: &Sicht, modul: &str, key: &str, c: &Expr) -> Option<i128> {
    let n = s.u.konst_wert(modul, c)?;
    let hypo = ohne_kosten(baum, key);
    let m = crate::kosten::abgeleitete_kosten(&hypo).get(key).copied()?;
    if m == n {
        Some(n)
    } else {
        None
    }
}

/// The caller closure over written `costs` bounds, shared by both planners:
/// which functions carry a written bound (`geschrieben`), and who calls whom
/// (`rufer`: direct edges plus `@lib#f` edges; indirect calls price the
/// pointer contract, never the declaration).
struct RufKante {
    rufer: BTreeMap<String, BTreeSet<String>>,
    geschrieben: BTreeSet<String>,
}

fn rufkante(baum: &Programm, s: &Sicht) -> RufKante {
    let mut rufer: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (rufer_key, knoten) in &s.voll.knoten {
        for (ziel, _) in &knoten.rufe {
            rufer.entry(ziel.clone()).or_default().insert(rufer_key.clone());
        }
        for ziel in &knoten.ruft {
            if !knoten.rufe.iter().any(|(t, _)| t == ziel) {
                rufer.entry(ziel.clone()).or_default().insert(rufer_key.clone());
            }
        }
    }
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else { return };
        let FnRumpf::Block(b) = &f.rumpf else { return };
        let caller = crate::umgebung::qualifiziere(modul, &f.name.text);
        let mut ziele = Vec::new();
        bibliotheksrufe(b, modul, &s.u, &mut ziele);
        for z in ziele {
            rufer.entry(z).or_default().insert(caller.clone());
        }
    });
    let mut geschrieben: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else { return };
        if f.costs.is_some() && matches!(f.rumpf, FnRumpf::Block(_)) {
            geschrieben.insert(crate::umgebung::qualifiziere(modul, &f.name.text));
        }
    });
    RufKante { rufer, geschrieben }
}

/// Shrink a cost-removal candidate set to the caller closure: a bound goes
/// only where every in-unit caller that promises a bound goes too. Skipped
/// functions are named in `zaehlung.ausgelassen` with the relying caller,
/// not left silent.
fn kosten_schluss(
    kante: &RufKante,
    kandidaten: &BTreeSet<String>,
    zaehlung: &mut Zaehlung,
) -> BTreeSet<String> {
    let mut menge = kandidaten.clone();
    loop {
        let mut raus: Option<String> = None;
        for k in &menge {
            let rufer_mit_kosten = kante.rufer.get(k).map(|r| {
                r.iter().filter(|g| kante.geschrieben.contains(*g)).collect::<Vec<_>>()
            });
            if let Some(rs) = rufer_mit_kosten {
                if let Some(g) = rs.into_iter().find(|g| !menge.contains(*g)) {
                    zaehlung.ausgelassen.push((
                        k.clone(),
                        format!("caller `{g}` promises a bound over this call"),
                    ));
                    raus = Some(k.clone());
                    break;
                }
            }
        }
        match raus {
            Some(k) => {
                menge.remove(&k);
            }
            None => break,
        }
    }
    menge
}

/// `gabbro fmt --explicit`: every settled omission written out at its
/// E4-ordered anchor, every removable written clause normalised to canonical
/// form (same set, same bound — the round trip closes over it).
///
/// A removable written clause is DELETED and re-inserted at the anchor,
/// never rewritten in place: what `--elide` removes, `--explicit` writes
/// back byte-identical, so `explicit(elide(F)) == explicit(F)`. An in-place
/// rewrite would keep the original position and padding while the
/// remove-and-insert path normalises both (measured on F10: `effects`
/// written on its own line vs inserted beside `costs`). A relied-upon
/// `costs` bound (the caller closure keeps it) is neither omitted nor
/// removable, so `--explicit` leaves it alone entirely — not even spacing
/// (measured on `13-zeuge-mit-staerke`: any rewrite moves
/// `elide(explicit(F))` with no removal to meet it).
///
/// Insertions at one anchor fuse into one edit, effects before costs; padding
/// is inverse to `--elide`'s trailing-whitespace eat (leading space where the
/// text before runs on, trailing where the text behind runs on).
pub fn plane_explicit(baum: &Programm, quelle: &str, zaehlung: &mut Zaehlung) -> Vec<Edit> {
    let s = sicht(baum);
    // First pass: per-function decisions. Costs candidates carry their span;
    // the closure shrink below is global, so it runs between the passes.
    struct Beschluss {
        key: String,
        f: FnDecl,
        rumpf_von: usize,
        effects_ersatz: Option<(BTreeSet<String>, usize, usize)>,
        effects_text: Option<String>,
        costs_text: Option<String>,
        /// The written bound where it equals the hypothetical derivation
        /// (`hypothetisch`); the closure shrink below decides remove-and
        /// re-insert vs in-place rewrite.
        costs_n: Option<i128>,
    }
    let mut beschluesse: Vec<Beschluss> = Vec::new();
    let mut kosten_kandidaten: BTreeSet<String> = BTreeSet::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let Some((key, f, rumpf_von)) = kandidat(item, modul, zaehlung) else {
            return;
        };
        let mut b = Beschluss {
            key: key.clone(),
            f: f.clone(),
            rumpf_von,
            effects_ersatz: None,
            effects_text: None,
            costs_text: None,
            costs_n: None,
        };
        match &f.effects {
            None if !ist_uebersetzer(&f) => match satz(&s, &key) {
                Some(m) if schreibbar(&m) => b.effects_text = Some(formuliere(&m)),
                Some(_) => zaehlung
                    .ausgelassen
                    .push((key.clone(), "derived place not writable".to_string())),
                None => zaehlung
                    .ausgelassen
                    .push((key.clone(), "effects derivation unsettled".to_string())),
            },
            None => zaehlung
                .ausgelassen
                .push((key.clone(), "translator owns the written `pure`".to_string())),
            Some(w) if !ist_uebersetzer(&f) => match satz(&s, &key) {
                // The canonical rewrite as delete + anchor insert: same
                // entries, same coverage — what `--elide` removes comes back
                // byte-identical.
                Some(m)
                    if schreibbar(&m) && normiere(&m) == geschrieben_normiert(w) =>
                {
                    let bis = mit_folge_ws(quelle, w.span.bis as usize);
                    b.effects_ersatz =
                        Some((m, w.span.von as usize, bis));
                }
                _ => {}
            },
            Some(_) => {}
        }
        match &f.costs {
            None => match s.kosten.get(&key) {
                Some(n) => b.costs_text = Some(format!("costs <= {n} ops")),
                None => zaehlung
                    .ausgelassen
                    .push((key.clone(), "costs derivation unsettled".to_string())),
            },
            Some(c) => {
                if let Some(n) = hypothetisch(baum, &s, modul, &key, c) {
                    b.costs_n = Some(n);
                    kosten_kandidaten.insert(key.clone());
                }
            }
        }
        beschluesse.push(b);
    });
    // The same caller closure `--elide` shrinks to: a relied-upon bound is
    // load-bearing there, whatever it says here.
    let kante = rufkante(baum, &s);
    let menge = kosten_schluss(&kante, &kosten_kandidaten, zaehlung);
    // anchor -> (effects insert?, costs insert?)
    let mut anker: BTreeMap<usize, (Option<Einsatz>, Option<Einsatz>)> = BTreeMap::new();
    let mut edits: Vec<Edit> = Vec::new();
    for b in &beschluesse {
        if let Some((_, von, bis)) = &b.effects_ersatz {
            edits.push(Edit {
                art: Art::EffectsRewritten,
                von: *von as u32,
                bis: *bis as u32,
                ersatz: String::new(),
            });
            zaehlung.effects_rewritten += 1;
        }
        let effects_einsatz = match (&b.effects_ersatz, &b.effects_text) {
            (Some((m, _, _)), _) => Some(Einsatz { text: formuliere(m), ersatz: true }),
            (None, Some(t)) => Some(Einsatz { text: t.clone(), ersatz: false }),
            (None, None) => None,
        };
        let mut costs_einsatz = b.costs_text.clone().map(|text| Einsatz { text, ersatz: false });
        if let (Some(c), Some(n)) = (&b.f.costs, b.costs_n) {
                if menge.contains(&b.key) {
                    // Removable: delete + anchor insert, like `--elide` plus
                    // the write-back. The number is the written one, which
                    // `hypothetisch` proved equal to the derived.
                    match kosten_spanne(quelle, c) {
                        Some((von, bis)) => {
                            edits.push(Edit {
                                art: Art::CostsRewritten,
                                von: von as u32,
                                bis: mit_folge_ws(quelle, bis) as u32,
                                ersatz: String::new(),
                            });
                            zaehlung.costs_rewritten += 1;
                            costs_einsatz = Some(Einsatz {
                                text: format!("costs <= {n} ops"),
                                ersatz: true,
                            });
                        }
                        None => zaehlung
                            .ausgelassen
                            .push((b.key.clone(), "costs clause span not found".to_string())),
                    }
                } else {
                    // Relied-upon: `--elide` keeps the clause, so
                    // `--explicit` keeps its hands off it too — not even
                    // spacing. An in-place rewrite would move
                    // `elide(explicit(F))` away from `elide(F)` with no
                    // removal on the other side to meet it (measured on
                    // `13-zeuge-mit-staerke`: `costs    <= 2 ops` kept by
                    // `--elide`, rewritten by `--explicit`).
                    zaehlung.ausgelassen.push((
                        b.key.clone(),
                        "relied-upon bound is a requirement, not ceremony".to_string(),
                    ));
                }
        }
        if effects_einsatz.is_none() && costs_einsatz.is_none() {
            continue;
        }
        let ein = match einfuegepunkt(
            quelle,
            &b.f,
            b.rumpf_von,
            effects_einsatz.is_some(),
        ) {
            Some(p) => p,
            None => {
                zaehlung.ausgelassen.push((b.key.clone(), "no insertion anchor found".to_string()));
                continue;
            }
        };
        let e = anker.entry(ein).or_insert((None, None));
        // Two functions never share an anchor: Byte spans of distinct headers
        // are disjoint, and each anchor lies inside its own header. If it ever
        // happened, the second write would silently win — so it does not stay
        // silent: overlapping anchors abort this function.
        if effects_einsatz.is_some() && e.0.is_some() || costs_einsatz.is_some() && e.1.is_some() {
            zaehlung.ausgelassen.push((b.key.clone(), "anchor already taken".to_string()));
            continue;
        }
        if effects_einsatz.is_some() {
            e.0 = effects_einsatz;
        }
        if costs_einsatz.is_some() {
            e.1 = costs_einsatz;
        }
    }
    for (pos, (eff, kos)) in anker {
        let b = quelle.as_bytes();
        let mut text = String::new();
        if !(pos == 0 || b[pos - 1].is_ascii_whitespace()) {
            text.push(' ');
        }
        if let Some(e) = eff {
            text.push_str(&e.text);
            if !e.ersatz {
                zaehlung.effects_hinzu += 1;
            }
        }
        if let Some(k) = kos {
            if text.ends_with(|c: char| !c.is_whitespace()) {
                text.push(' ');
            }
            text.push_str(&k.text);
            if !k.ersatz {
                zaehlung.costs_hinzu += 1;
            }
        }
        if pos >= b.len() || !b[pos].is_ascii_whitespace() {
            text.push(' ');
        }
        edits.push(Edit { art: Art::EffectsHinzu, von: pos as u32, bis: pos as u32, ersatz: text });
    }
    edits.sort_by_key(|e| (e.von, e.bis));
    edits
}

/// The hypothetical tree with one written `costs` lifted: what the body
/// derives where the clause stood. The same derivation, not a second one.
fn ohne_kosten(baum: &Programm, ziel: &str) -> Programm {
    fn geh(items: &mut [Item], pfad: &str, ziel: &str) {
        for i in items {
            match &mut i.art {
                ItemArt::Funktion(f) => {
                    if crate::umgebung::qualifiziere(pfad, &f.name.text) == ziel {
                        f.costs = None;
                    }
                }
                ItemArt::Modul(m) => {
                    let innen =
                        if pfad.is_empty() { m.pfad.text() } else { format!("{pfad}::{}", m.pfad.text()) };
                    geh(&mut m.items, &innen, ziel);
                }
                _ => {}
            }
        }
    }
    let mut b = baum.clone();
    geh(&mut b.items, "", ziel);
    b
}

/// Every `@lib#f` edge of a body, resolved to callee keys (lane E2: a
/// resolved library call prices the declared costs like any call).
fn bibliotheksrufe(
    b: &Block,
    modul: &str,
    u: &crate::umgebung::Umgebung,
    aus: &mut Vec<String>,
) {
    fn geh(
        b: &Block,
        modul: &str,
        u: &crate::umgebung::Umgebung,
        aus: &mut Vec<String>,
    ) {
        for s in &b.anweisungen {
            if let StmtArt::LibraryCall(l) = &s.art {
                if let Some(z) = u.bibliothek(modul, &l.library.text, &l.function.text) {
                    aus.push(z.name);
                }
            }
            for k in crate::unterbloecke(s) {
                geh(k, modul, u, aus);
            }
        }
    }
    geh(b, modul, u, aus);
}

/// `gabbro fmt --elide`: every clause equal to what would be derived removed.
/// Effects compare written against settled-derived; costs compare the written
/// number against the hypothetical derivation, then shrink to the caller
/// closure (a relied-upon bound is load-bearing, wherever it stands).
pub fn plane_elide(baum: &Programm, quelle: &str, zaehlung: &mut Zaehlung) -> Vec<Edit> {
    let s = sicht(baum);
    // (key, written const bound, clause span) for the costs shrink below.
    let mut kosten_kandidaten: Vec<(String, i128, usize, usize)> = Vec::new();
    let mut edits: Vec<Edit> = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let Some((key, f, _)) = kandidat(item, modul, zaehlung) else {
            return;
        };
        if let Some(w) = &f.effects {
            if ist_uebersetzer(&f) {
                zaehlung
                    .ausgelassen
                    .push((key.clone(), "translator owns the written `pure`".to_string()));
            } else {
                match satz(&s, &key) {
                    Some(m)
                        if schreibbar(&m) && normiere(&m) == geschrieben_normiert(w) =>
                    {
                        let bis = mit_folge_ws(quelle, w.span.bis as usize);
                        edits.push(Edit {
                            art: Art::EffectsWeg,
                            von: w.span.von,
                            bis: bis as u32,
                            ersatz: String::new(),
                        });
                    }
                    Some(m) if !schreibbar(&m) => zaehlung
                        .ausgelassen
                        .push((key.clone(), "derived place not writable".to_string())),
                    Some(_) => zaehlung.ausgelassen.push((
                        key.clone(),
                        "written effects wider than derived".to_string(),
                    )),
                    None => zaehlung
                        .ausgelassen
                        .push((key.clone(), "effects derivation unsettled".to_string())),
                }
            }
        }
        if let Some(c) = &f.costs {
            match s.u.konst_wert(modul, c) {
                Some(_) => match hypothetisch(baum, &s, modul, &key, c) {
                    Some(n) => match kosten_spanne(quelle, c) {
                        Some((von, bis)) => kosten_kandidaten.push((
                            key.clone(),
                            n,
                            von,
                            mit_folge_ws(quelle, bis),
                        )),
                        None => zaehlung
                            .ausgelassen
                            .push((key.clone(), "costs clause span not found".to_string())),
                    },
                    None => zaehlung.ausgelassen.push((
                        key.clone(),
                        "written bound tighter or looser than derived".to_string(),
                    )),
                },
                None => zaehlung
                    .ausgelassen
                    .push((key.clone(), "symbolic bound is a requirement".to_string())),
            }
        }
    });
    // The caller closure: a bound goes only where every in-unit caller that
    // promises a bound goes too. Direct edges plus `@lib#f` edges; indirect
    // calls price the pointer contract, never this declaration.
    let kante = rufkante(baum, &s);
    let kandidaten: BTreeSet<String> =
        kosten_kandidaten.iter().map(|(k, _, _, _)| k.clone()).collect();
    let menge = kosten_schluss(&kante, &kandidaten, zaehlung);
    for (k, _, von, bis) in kosten_kandidaten {
        if menge.contains(&k) {
            edits.push(Edit {
                art: Art::CostsWeg,
                von: von as u32,
                bis: bis as u32,
                ersatz: String::new(),
            });
        }
    }
    zaehlung.dazu(&edits);
    edits.sort_by_key(|e| (e.von, e.bis));
    edits
}

/// Apply rear-to-front so earlier offsets stay valid. Edits come out of one
/// planning run over this source; overlapping edits keep the first and skip
/// the rest, never trusted twice.
fn anwenden(quelle: &str, edits: &[Edit]) -> String {
    let mut sortiert = edits.to_vec();
    sortiert.sort_by(|a, b| (b.von, b.bis).cmp(&(a.von, a.bis)));
    let mut out = quelle.to_string();
    let mut belegt: Vec<(u32, u32)> = Vec::new();
    for e in &sortiert {
        let (von, bis) = (e.von as usize, e.bis as usize);
        if e.von > e.bis || bis > out.len() {
            continue;
        }
        if !out.is_char_boundary(von) || !out.is_char_boundary(bis) {
            continue;
        }
        if belegt.iter().any(|(a, b)| von.max(*a as usize) < bis.min(*b as usize)) {
            continue;
        }
        out.replace_range(von..bis, &e.ersatz);
        belegt.push((e.von, e.bis));
    }
    out
}

/// `gabbro fmt --explicit FILE`: the program with every settled derived clause
/// written out. Pure view: same diagnostics, same register, same C.
pub fn explicit(baum: &Programm, quelle: &str) -> String {
    let mut z = Zaehlung::default();
    let edits = plane_explicit(baum, quelle, &mut z);
    anwenden(quelle, &edits)
}

/// `gabbro fmt --elide FILE`: the program with every derivable clause removed.
/// Pure view: same diagnostics, same register, same C.
pub fn elide(baum: &Programm, quelle: &str) -> String {
    let mut z = Zaehlung::default();
    let edits = plane_elide(baum, quelle, &mut z);
    anwenden(quelle, &edits)
}

/// The corpus-wide count of what the views would do: clauses `--explicit`
/// would write and `--elide` would remove, plus every function skipped with
/// its reason.
pub fn zaehle(baum: &Programm, quelle: &str) -> Zaehlung {
    let mut z = Zaehlung::default();
    let e = plane_explicit(baum, quelle, &mut z);
    let l = plane_elide(baum, quelle, &mut z);
    // Counted inside the planners via `dazu`; this only keeps the signature
    // honest: both runs happened, both counts stand. The skip list is
    // deduplicated: both planners name the same functions.
    let _ = (e, l);
    z.ausgelassen.sort();
    z.ausgelassen.dedup();
    z
}

#[cfg(test)]
mod tests {
    use super::*;

    fn plan_e(q: &str) -> String {
        let (baum, _) = gabbro_syntax::lies("probe.gab", q);
        explicit(&baum, q)
    }

    fn plan_l(q: &str) -> String {
        let (baum, _) = gabbro_syntax::lies("probe.gab", q);
        elide(&baum, q)
    }

    /// **The derivable omission is written out, canonically.**
    ///
    /// `f` touches nothing and adds two numbers: `effects { pure }` and the
    /// counted bound land before the body, in E4 order.
    #[test]
    fn auslassung_wird_kanonisch_geschrieben() {
        let out = plan_e("impl fn f(a : u32, b : u32) -> u32 { return a + b; }");
        assert!(out.contains("effects { pure }"), "{out}");
        assert!(out.contains("costs <="), "{out}");
    }

    /// **Counter-direction: the settled written clause goes, byte-clean.**
    ///
    /// The same body with both lines written loses both, and no double space
    /// stays behind.
    #[test]
    fn gesetzte_klausel_geht_spurlos() {
        let q = "impl fn f(a : u32, b : u32) -> u32 effects { pure } costs <= 3 ops { return a + b; }";
        let out = plan_l(q);
        assert!(!out.contains("effects"), "{out}");
        assert!(!out.contains("costs"), "{out}");
        assert!(!out.contains("  "), "{out}");
    }

    /// **A tighter bound is a requirement, not ceremony.**
    ///
    /// `costs <= 3 ops` over a body costing 3 derives 3 — equal, so it goes.
    /// The twin with a violated bound keeps it: removing it would take the
    /// `K001` refusal with it.
    #[test]
    fn engere_schranke_bleibt() {
        let q = "impl fn f(a : u32) -> u32 effects { pure } costs <= 1 ops { return a + a; }";
        let out = plan_l(q);
        assert!(out.contains("costs <="), "{out}");
    }

    /// **The refused omission stays omitted.**
    ///
    /// The callee promises more than it does; the caller's omission is `N305`.
    /// `--explicit` has nothing settled to write — the view does not paper
    /// over a refusal.
    #[test]
    fn offene_auslassung_bleibt_ausgelassen() {
        let q = "static mut W : u32 = 0;\n\
                 impl fn geber() effects { writes W } costs <= 100 ops { }\n\
                 impl fn rufer() { geber(); }";
        let out = plan_e(q);
        assert!(!out.contains("rufer() effects"), "{out}");
    }

    /// **`ensures` is never derived and never removed.**
    ///
    /// PLAN-EINFACHHEIT §2: what a function SHOULD do cannot be inferred. The
    /// derivable half goes, the contract stays.
    #[test]
    fn vertrag_wird_nicht_angefasst() {
        let q = "impl fn f(a : u32, b : u32) -> u32 ensures result == a + b effects { pure } costs <= 3 ops { return a + b; }";
        assert_eq!(plan_e(q), q, "nothing omitted, nothing written");
        let out = plan_l(q);
        assert!(out.contains("ensures result =="), "the contract stays: {out}");
        assert!(!out.contains("effects"), "the derivable clause goes: {out}");
    }
}
