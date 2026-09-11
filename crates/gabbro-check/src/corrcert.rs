//! **The per-run correspondence certificate — `CorrSite` rows collected into a
//! `CorrCert` beside each emission.**
//!
//! ## What this is
//!
//! Every emission lowers Gabbro evaluation sites to C sites. This module collects one
//! row per lowered site — `(gabbro_site, c_site, form)` — into the certificate that
//! travels beside the emitted C. It mirrors the Lean shapes in
//! `grammatik/Grammatik/Erhaltung.lean` §1 and §6 (read-only reference, not imported):
//!
//! | Lean | Here |
//! |---|---|
//! | `CorrSite { gabbroSite, cSite, form }` | [`CorrSite`] |
//! | `CorrCert { sites }` | [`CorrCert`] |
//! | `vollB` (completeness, §4.1) | [`vollstaendig`] |
//! | `geordnetCertB` (order, §4.2) | [`geordnet`] |
//! | `geschlossenB` (closure, §4.3) | [`geschlossen`] |
//! | `ohneExtraB` (no extra effect, §4.4) | [`ohne_extra`] |
//! | `pruefeKorrespondenz` (all four legs) | [`pruefe`] → [`CorrPruefung`] |
//!
//! The four legs are **checkable fields** on [`CorrPruefung`], not prose: a run's
//! certificate is re-checked instead of believed, the same direction as `vollB_sound`
//! and `korrespondenz_sound` Lean-side.
//!
//! ## What this is NOT
//!
//! * It does not prove the lowering. It records which site went where, so the
//!   recomputer (cut C1 in `BEWEIS.md`) can check completeness, order, closure and
//!   no-extra per run.
//! * Site ids are plain numbers. Binding them to source spans is the recomputer's job —
//!   the Lean `CorrSite` doc says so word for word, and this module keeps the same
//!   boundary.
//! * Closure is structurally total: every [`CForm`] variant is a ruled (tabled) shape,
//!   mirroring `ruledB_voll` / `geschlossen_immer`. [`geschlossen`] still re-checks each
//!   row, so a future form that is not tabled fails loudly instead of silently passing.
//!
//! ## NOTE — the ONE hook point (landed 2026-09-11, lane p20)
//!
//! Wire-up belongs in exactly one place:
//! `crates/gabbro-check/src/emit.rs`, function `emittiere_mit`, AFTER the gate filter
//! (`ohne_gatter`) has handed over the tree and BEFORE/WHILE the twenty walks lower it.
//! The emitter threads a [`CorrCertBuilder`] through the lowering, calls
//! [`CorrCertBuilder::aufzeichnen`] at each site it lowers, and emits
//! [`CorrCert::to_json`] beside the C output. One hook point, not one per walk — the
//! same reason the gate is a filter in front of the emitter and not a branch inside it.
//! Until that hook lands, this module is inert: collected by nothing, checked by its
//! own unit tests below.
//!
//! Update (p20, 2026-09-11): the first half of the hook has landed, beside the walks
//! rather than inside them. `emit.rs` now owns the call site `emittiere_mit_corr` with
//! the total item mapper `korr_form`: one row per lowered item whose top-level C shape
//! is one of the 19 named forms, in lowering order, returned beside the C string — the
//! C itself is byte-identical. Statement- and expression-level rows (the evaluation
//! sites of §1) stay booked: they need the builder threaded through the body walks,
//! which is one function (`funktion`), not twenty, and belongs to the follow-up lane.
//! `messung/CORRCERT-ANBINDUNG.md` carries the threading table with the arm behind
//! every row. The word-level recorder [`CorrCertBuilder::aufzeichnen_wort`] and the
//! sidecar path [`sidecar_path`] below are the boundary the follow-up lane reuses.
//!
//! ## The C forms
//!
//! [`CForm`] mirrors `Ziel.lean`'s `CForm` one for one: 19 named shapes, no closed-list
//! claim beyond the enum itself. A form the emitter writes that is not in this enum is
//! a compile error at the hook point, not a row that quietly stops being checked — the
//! lesson of the 78 holes behind `unterbloecke` in `lib.rs`.

/// **The target shapes the lowering contract speaks about** — 19 named forms, mirroring
/// `Ziel.lean` `CForm` (`statisch | extern | zuweisung | wenn | schalter |
/// zaehlSchleife | rueckgabe | sprungAlsSchleifenende | ruf | literal | name | feld |
/// index | wahlLesen | atomar | beschraenkt | fluechtig | noreturn | asmEins`).
///
/// The order of the variants is the order of the Lean inductive; `as_str` spells each
/// variant exactly as Lean names it, so certificate JSON and Lean rows use one word.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CForm {
    Statisch,
    Extern,
    Zuweisung,
    Wenn,
    Schalter,
    ZaehlSchleife,
    Rueckgabe,
    SprungAlsSchleifenende,
    Ruf,
    Literal,
    Name,
    Feld,
    Index,
    WahlLesen,
    Atomar,
    Beschraenkt,
    Fluechtig,
    Noreturn,
    AsmEins,
}

impl CForm {
    /// The Lean spelling of this form — the word a certificate row carries.
    pub fn as_str(self) -> &'static str {
        match self {
            CForm::Statisch => "statisch",
            CForm::Extern => "extern",
            CForm::Zuweisung => "zuweisung",
            CForm::Wenn => "wenn",
            CForm::Schalter => "schalter",
            CForm::ZaehlSchleife => "zaehlSchleife",
            CForm::Rueckgabe => "rueckgabe",
            CForm::SprungAlsSchleifenende => "sprungAlsSchleifenende",
            CForm::Ruf => "ruf",
            CForm::Literal => "literal",
            CForm::Name => "name",
            CForm::Feld => "feld",
            CForm::Index => "index",
            CForm::WahlLesen => "wahlLesen",
            CForm::Atomar => "atomar",
            CForm::Beschraenkt => "beschraenkt",
            CForm::Fluechtig => "fluechtig",
            CForm::Noreturn => "noreturn",
            CForm::AsmEins => "asmEins",
        }
    }

    /// Parses a Lean-spelled form. Returns `None` for anything outside the 19 named
    /// shapes — an unknown word is no row, never a silent pass.
    pub fn from_str(s: &str) -> Option<CForm> {
        Some(match s {
            "statisch" => CForm::Statisch,
            "extern" => CForm::Extern,
            "zuweisung" => CForm::Zuweisung,
            "wenn" => CForm::Wenn,
            "schalter" => CForm::Schalter,
            "zaehlSchleife" => CForm::ZaehlSchleife,
            "rueckgabe" => CForm::Rueckgabe,
            "sprungAlsSchleifenende" => CForm::SprungAlsSchleifenende,
            "ruf" => CForm::Ruf,
            "literal" => CForm::Literal,
            "name" => CForm::Name,
            "feld" => CForm::Feld,
            "index" => CForm::Index,
            "wahlLesen" => CForm::WahlLesen,
            "atomar" => CForm::Atomar,
            "beschraenkt" => CForm::Beschraenkt,
            "fluechtig" => CForm::Fluechtig,
            "noreturn" => CForm::Noreturn,
            "asmEins" => CForm::AsmEins,
            _ => return None,
        })
    }

    /// All 19 named shapes, in inductive order.
    pub fn alle() -> [CForm; 19] {
        [
            CForm::Statisch,
            CForm::Extern,
            CForm::Zuweisung,
            CForm::Wenn,
            CForm::Schalter,
            CForm::ZaehlSchleife,
            CForm::Rueckgabe,
            CForm::SprungAlsSchleifenende,
            CForm::Ruf,
            CForm::Literal,
            CForm::Name,
            CForm::Feld,
            CForm::Index,
            CForm::WahlLesen,
            CForm::Atomar,
            CForm::Beschraenkt,
            CForm::Fluechtig,
            CForm::Noreturn,
            CForm::AsmEins,
        ]
    }

    /// Whether this form stands in the ruled list — mirrors Lean `ruledB`.
    /// True for every named shape (mirroring `ruledB_voll`: each of the 19 is tabled),
    /// so closure over a well-formed certificate always holds — and a form that ever
    /// stops being tabled fails here instead of passing silently.
    pub fn ist_entschieden(self) -> bool {
        matches!(
            self,
            CForm::Statisch
                | CForm::Extern
                | CForm::Zuweisung
                | CForm::Wenn
                | CForm::Schalter
                | CForm::ZaehlSchleife
                | CForm::Rueckgabe
                | CForm::SprungAlsSchleifenende
                | CForm::Ruf
                | CForm::Literal
                | CForm::Name
                | CForm::Feld
                | CForm::Index
                | CForm::WahlLesen
                | CForm::Atomar
                | CForm::Beschraenkt
                | CForm::Fluechtig
                | CForm::Noreturn
                | CForm::AsmEins
        )
    }
}

/// **One evaluation site on each side, joined by its form** — the row of the per-run
/// certificate. Mirrors Lean `CorrSite { gabbroSite : Nat, cSite : Nat, form : CForm }`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CorrSite {
    /// The Gabbro evaluation site this row covers.
    pub gabbro_site: u32,
    /// The C site the emitter wrote for it.
    pub c_site: u32,
    /// The C shape the emitter wrote there.
    pub form: CForm,
}

impl CorrSite {
    /// One row: this Gabbro site lowered to this C site in this form.
    pub fn neu(gabbro_site: u32, c_site: u32, form: CForm) -> CorrSite {
        CorrSite {
            gabbro_site,
            c_site,
            form,
        }
    }
}

/// **The per-run certificate: the list of joined sites.** Mirrors Lean
/// `CorrCert { sites : List CorrSite }`. Row order is emission order — the order leg
/// ([`geordnet`]) reads it directly, so the hook point must record in lowering order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CorrCert {
    /// The joined sites, in the order the emitter lowered them.
    pub sites: Vec<CorrSite>,
}

impl CorrCert {
    /// An empty certificate — covers no site; valid only against no sites.
    pub fn leer() -> CorrCert {
        CorrCert { sites: Vec::new() }
    }

    /// The rows this certificate carries.
    pub fn zeilen(&self) -> &[CorrSite] {
        &self.sites
    }

    /// The per-run check in method form — mirrors [`pruefe`]: all four legs, each in
    /// its own field so a rejection names the failed leg. The call site
    /// (`emittiere_mit_corr` in `emit.rs`) reads the obligation off its own rows,
    /// but the recomputer passes its own list — same function, both readers.
    pub fn pruefe_gegen(&self, gabbro_sites: &[u32]) -> CorrPruefung {
        pruefe(gabbro_sites, self)
    }

    /// The sidecar path beside an emitted C file — `<stem>.corrcert`, mirroring
    /// `kostenledger::sidecar_path` (`<stem>.kostenledger`) so the two sidecars
    /// share one convention: beside the C, never inside it.
    pub fn sidecar_path(c_path: &str) -> String {
        match c_path.rfind('.') {
            Some(i) => format!("{}.corrcert", &c_path[..i]),
            None => format!("{c_path}.corrcert"),
        }
    }

    /// Renders the certificate beside an emission: one JSON object with the row list.
    /// Hand-rolled on purpose — this crate has no JSON dependency, and the shape is
    /// three fixed fields per row. Field names follow the Lean fields word for word
    /// (`gabbroSite`, `cSite`, `form`) so rows compare equal across the boundary.
    pub fn to_json(&self) -> String {
        let mut aus = String::from("{\"sites\":[");
        for (i, s) in self.sites.iter().enumerate() {
            if i > 0 {
                aus.push(',');
            }
            aus.push_str(&format!(
                "{{\"gabbroSite\":{},\"cSite\":{},\"form\":\"{}\"}}",
                s.gabbro_site,
                s.c_site,
                s.form.as_str()
            ));
        }
        aus.push_str("]}");
        aus
    }
}

/// **The collector the hook point threads through the lowering.** One builder per
/// emission; [`aufzeichnen`](CorrCertBuilder::aufzeichnen) at each lowered site, in
/// lowering order; [`zertifikat`](CorrCertBuilder::zertifikat) beside the C output.
#[derive(Debug, Clone, Default)]
pub struct CorrCertBuilder {
    sites: Vec<CorrSite>,
}

impl CorrCertBuilder {
    /// A fresh collector for one emission run.
    pub fn neu() -> CorrCertBuilder {
        CorrCertBuilder { sites: Vec::new() }
    }

    /// Records one lowered site. Call in lowering order — the order leg reads the row
    /// order, and a builder that re-sorted would certify an order it did not emit.
    pub fn aufzeichnen(&mut self, gabbro_site: u32, c_site: u32, form: CForm) {
        self.sites.push(CorrSite::neu(gabbro_site, c_site, form));
    }

    /// Records one lowered site from its Lean-spelled form word — the boundary the
    /// probes and the recomputer speak. An unknown word records NO row and returns
    /// `false`: an unparsable shape is a loud refusal, never a silent pass (the same
    /// rule `CForm::from_str` already keeps — `None` is no row).
    pub fn aufzeichnen_wort(&mut self, gabbro_site: u32, c_site: u32, wort: &str) -> bool {
        match CForm::from_str(wort) {
            Some(form) => {
                self.aufzeichnen(gabbro_site, c_site, form);
                true
            }
            None => false,
        }
    }

    /// The certificate for this run's rows.
    pub fn zertifikat(self) -> CorrCert {
        CorrCert { sites: self.sites }
    }
}

/// **The four checkable legs of one certificate** — mirrors Lean `pruefeKorrespondenz`
/// (`vollB && geschlossenB && ohneExtraB && geordnetCertB`), split into fields so a
/// rejection names the leg that failed instead of just saying no.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CorrPruefung {
    /// §4.1 Completeness: every Gabbro evaluation site appears at least once.
    pub vollstaendig: bool,
    /// §4.2 Order: the C sites stand in non-decreasing certificate order.
    pub geordnet: bool,
    /// §4.3 Closure: every row's form stands in the ruled list.
    pub geschlossen: bool,
    /// §4.4 No additional effect: no row without a Gabbro preimage.
    pub ohne_extra: bool,
}

impl CorrPruefung {
    /// All four legs hold — mirrors Lean `GueltigKorrespondenz`
    /// (`pruefeKorrespondenz … = true`).
    pub fn gueltig(self) -> bool {
        self.vollstaendig && self.geordnet && self.geschlossen && self.ohne_extra
    }
}

/// §4.1 Completeness — mirrors Lean `vollB`: every Gabbro site has a joined row.
pub fn vollstaendig(gabbro_sites: &[u32], cert: &CorrCert) -> bool {
    gabbro_sites
        .iter()
        .all(|g| cert.sites.iter().any(|s| s.gabbro_site == *g))
}

/// §4.2 Order — mirrors Lean `geordnetCertB` over the projected C sites: adjacent
/// non-decreasing check, which transitivity (`Nat.le_trans` Lean-side) lifts to every
/// pair. Reads emission order — never re-sorts.
pub fn geordnet(cert: &CorrCert) -> bool {
    cert.sites
        .iter()
        .map(|s| s.c_site)
        .collect::<Vec<_>>()
        .windows(2)
        .all(|w| w[0] <= w[1])
}

/// §4.3 Closure — mirrors Lean `geschlossenB`: every row's form is ruled. Total today
/// (mirroring `geschlossen_immer`: all 19 named shapes are tabled), and still checked
/// row by row, so a form that ever leaves the ruled list fails here.
pub fn geschlossen(cert: &CorrCert) -> bool {
    cert.sites.iter().all(|s| s.form.ist_entschieden())
}

/// §4.4 No additional effect — mirrors Lean `ohneExtraB`: every row has a preimage in
/// the Gabbro sites.
pub fn ohne_extra(gabbro_sites: &[u32], cert: &CorrCert) -> bool {
    cert.sites
        .iter()
        .all(|s| gabbro_sites.contains(&s.gabbro_site))
}

/// The per-run check — mirrors Lean `pruefeKorrespondenz`: all four legs, each in its
/// own field so a rejection names the failed leg.
pub fn pruefe(gabbro_sites: &[u32], cert: &CorrCert) -> CorrPruefung {
    CorrPruefung {
        vollstaendig: vollstaendig(gabbro_sites, cert),
        geordnet: geordnet(cert),
        geschlossen: geschlossen(cert),
        ohne_extra: ohne_extra(gabbro_sites, cert),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn zwei_zeilen() -> CorrCert {
        let mut b = CorrCertBuilder::neu();
        b.aufzeichnen(0, 0, CForm::Literal);
        b.aufzeichnen(1, 1, CForm::Name);
        b.zertifikat()
    }

    #[test]
    fn nimmt_zwei_stellen_in_ordnung_ueber_benannten_formen_an() {
        // Mirrors the Lean accept example: two sites, in order, named forms, nothing more.
        let cert = zwei_zeilen();
        let p = pruefe(&[0, 1], &cert);
        assert!(p.vollstaendig, "completeness leg must hold");
        assert!(p.geordnet, "order leg must hold");
        assert!(p.geschlossen, "closure leg must hold");
        assert!(p.ohne_extra, "no-extra leg must hold");
        assert!(p.gueltig(), "all four legs must assemble");
    }

    #[test]
    fn lehnt_fehlende_stelle_laut_ab() {
        // Mirrors the Lean reject example: Gabbro site 1 has no row.
        let mut b = CorrCertBuilder::neu();
        b.aufzeichnen(0, 0, CForm::Literal);
        let cert = b.zertifikat();
        let p = pruefe(&[0, 1], &cert);
        assert!(!p.vollstaendig, "missing site 1 must fail completeness");
        assert!(!p.gueltig(), "a failed leg must fail the certificate");
        assert!(p.geordnet, "order still holds on one row");
        assert!(p.ohne_extra, "no-extra still holds without foreign rows");
    }

    #[test]
    fn lehnt_umgekehrte_c_ordnung_ab() {
        let mut b = CorrCertBuilder::neu();
        b.aufzeichnen(0, 5, CForm::Ruf);
        b.aufzeichnen(1, 3, CForm::Rueckgabe);
        let cert = b.zertifikat();
        let p = pruefe(&[0, 1], &cert);
        assert!(!p.geordnet, "falling C sites must fail the order leg");
        assert!(!p.gueltig(), "a failed leg must fail the certificate");
        assert!(p.vollstaendig, "completeness still holds");
        assert!(p.ohne_extra, "no-extra still holds");
    }

    #[test]
    fn lehnt_zeile_ohne_urbild_ab() {
        let mut b = CorrCertBuilder::neu();
        b.aufzeichnen(0, 0, CForm::Literal);
        b.aufzeichnen(7, 1, CForm::Name);
        let cert = b.zertifikat();
        let p = pruefe(&[0, 1], &cert);
        assert!(!p.ohne_extra, "row 7 without a preimage must fail no-extra");
        assert!(!p.vollstaendig, "site 1 still uncovered");
        assert!(!p.gueltig(), "a failed leg must fail the certificate");
    }

    #[test]
    fn leeres_zertifikat_gilt_nur_gegen_leere_stellen() {
        let leer = CorrCert::leer();
        assert!(pruefe(&[], &leer).gueltig(), "nothing emitted, nothing owed");
        assert!(
            !pruefe(&[0], &leer).gueltig(),
            "an owed site with no row must fail"
        );
    }

    #[test]
    fn jede_benannte_form_ist_entschieden() {
        // Mirrors `ruledB_voll`: all 19 shapes tabled, so closure holds structurally.
        for f in CForm::alle() {
            assert!(f.ist_entschieden(), "form {} must be ruled", f.as_str());
        }
        let mut b = CorrCertBuilder::neu();
        for (i, f) in CForm::alle().into_iter().enumerate() {
            b.aufzeichnen(i as u32, i as u32, f);
        }
        let cert = b.zertifikat();
        assert!(geschlossen(&cert), "closure must hold over all 19 forms");
    }

    #[test]
    fn formworte_ueberleben_den_weg_hin_und_zurueck() {
        for f in CForm::alle() {
            assert_eq!(
                CForm::from_str(f.as_str()),
                Some(f),
                "form word must round-trip"
            );
        }
        assert_eq!(CForm::from_str("zeigerarithmetik"), None);
        assert_eq!(CForm::from_str(""), None);
    }

    #[test]
    fn json_traegt_jede_zeile_mit_leanfeldnamen() {
        let cert = zwei_zeilen();
        let j = cert.to_json();
        assert_eq!(
            j,
            concat!(
                "{\"sites\":[{\"gabbroSite\":0,\"cSite\":0,\"form\":\"literal\"},",
                "{\"gabbroSite\":1,\"cSite\":1,\"form\":\"name\"}]}"
            )
        );
    }

    #[test]
    fn pruefe_gegen_stimmt_mit_pruefe_ueberein() {
        // The method form is the same function both readers call: the call site with
        // its own rows, the recomputer with its own list.
        let cert = zwei_zeilen();
        assert_eq!(cert.pruefe_gegen(&[0, 1]), pruefe(&[0, 1], &cert));
        assert!(cert.pruefe_gegen(&[0, 1]).gueltig());
        assert!(!cert.pruefe_gegen(&[0, 1, 2]).gueltig());
    }

    #[test]
    fn wort_zeichnet_benannte_form_auf_unbekannte_nicht() {
        let mut b = CorrCertBuilder::neu();
        assert!(b.aufzeichnen_wort(0, 0, "literal"));
        assert!(b.aufzeichnen_wort(1, 1, "statisch"));
        assert!(!b.aufzeichnen_wort(2, 2, "zeigerarithmetik"));
        assert!(!b.aufzeichnen_wort(2, 2, ""));
        let cert = b.zertifikat();
        assert_eq!(cert.zeilen().len(), 2);
        // The refused word left no row: completeness against [0, 1] still holds,
        // and the missing site 2 fails loudly instead of passing silently.
        assert!(cert.pruefe_gegen(&[0, 1]).gueltig());
        assert!(!cert.pruefe_gegen(&[0, 1, 2]).vollstaendig);
    }

    #[test]
    fn seitenwagenpfad_teilt_die_konvention_des_ledgers() {
        assert_eq!(
            CorrCert::sidecar_path("out/einheit.c"),
            "out/einheit.corrcert"
        );
        assert_eq!(CorrCert::sidecar_path("einheit.c"), "einheit.corrcert");
        assert_eq!(CorrCert::sidecar_path("einheit"), "einheit.corrcert");
    }
}
