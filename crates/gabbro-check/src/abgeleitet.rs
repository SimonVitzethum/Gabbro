//! **Lane 191: the derived contract, readable in one place.**
//!
//! Lever 1 of `PLAN-EINFACHHEIT.md`: an omitted `effects` clause is derived
//! from the body (the hull the checker computes) and an omitted `costs` from
//! `kosten.rs` — and both are treated exactly like a written clause by every
//! pass. A written clause stays the enforced bound: the body must stay inside
//! it (`E005`/`E008`/`E010`, `K001`).
//!
//! This module owns no refusal. It owns the VIEW: per function, what the
//! checker derives, whether the line is written or omitted, and where the
//! derivation stays a lower bound (with the code that then refuses the
//! omission: `N305` at `effects`; at `costs` an omission is never refused,
//! so the view names the shape instead of a code).

use gabbro_syntax::ast::*;
use std::collections::BTreeSet;

/// What the checker derives for one function — beside what it declares.
pub struct Vertrag {
    pub schluessel: String,
    pub geschrieben_effects: bool,
    /// The written bound where one stands: a number, or `None` for a
    /// symbolic promise (`64 + 12 * lenof(m)` has no single number).
    pub geschrieben_kosten: Option<Option<i128>>,
    pub effects: BTreeSet<String>,
    /// `None` where the fixpoint stays a lower bound, with the reason.
    pub effects_offen: Option<String>,
    /// The derived cost, or the reason none follows.
    pub costs: Option<i128>,
    pub costs_offen: Option<String>,
}

/// The derived contract of every function in a unit.
pub fn ertraege(baum: &Programm) -> Vec<Vertrag> {
    let u = crate::umgebung::Umgebung::sammle(baum);
    let ab = crate::ableitung::leite_ab(baum, true);
    let kosten = crate::kosten::abgeleitete_kosten(baum);
    let g = crate::aufrufgraph::erhebe_roh(baum);
    let syscalls = crate::kosten::syscall_namen(baum);
    let kein_total = crate::kosten::ohne_total(baum, &g);
    let mut aus = Vec::new();
    crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
        let ItemArt::Funktion(f) = &item.art else {
            return;
        };
        let key = crate::umgebung::qualifiziere(modul, &f.name.text);
        let (effects, mut effects_offen) = match ab.je.get(&key) {
            Some(a) => (a.wirkungen.clone(), a.unvollstaendig.clone()),
            None => (BTreeSet::new(), Some("unknown to the derivation".to_string())),
        };
        // **The same two arms as the refusal:** a settled fixpoint still
        // refuses the omission where the callees promise more than the deeds
        // cover (`N305`). The view shows the lower bound exactly there.
        if effects_offen.is_none()
            && f.effects.is_none()
            && f.klasse != Some(FnKlasse::Spec)
            && matches!(f.rumpf, FnRumpf::Block(_))
        {
            effects_offen = crate::ableitung::deckungsluecke(&effects, &g.huelle(&key));
        }
        let geschrieben_kosten =
            f.costs.as_ref().map(|c| u.konst_wert(modul, c));
        let (costs, costs_offen) = match &f.rumpf {
            FnRumpf::Block(_) => match kosten.get(&key) {
                Some(n) => (Some(*n), None),
                // A written bound is enforced (`K001`), not open — only an
                // omission without a number carries the reason.
                None if f.costs.is_some() => (None, None),
                None => (None, costs_grund(f, &key, &g, &syscalls, &kein_total)),
            },
            _ => (None, Some("no body to derive from".to_string())),
        };
        aus.push(Vertrag {
            schluessel: key,
            geschrieben_effects: f.effects.is_some(),
            geschrieben_kosten,
            effects,
            effects_offen,
            costs,
            costs_offen,
        });
    });
    aus
}

/// Why no cost follows for a bodied function. The pass never refuses an
/// omitted `costs` — the omission keeps its old meaning (no promise, no
/// check) — so these are view-only reasons, not refusing codes: no
/// total behind `forever` (`per_pass` world), the cost-opaque `syscall`
/// edge (no `costs` clause exists on `syscall` by grammar), a recursion
/// without `decreases` (unbounded through the cycle), an indirect call
/// without a pointer-type cost, or anything else the body leaves unsettled.
fn costs_grund(
    f: &FnDecl,
    key: &str,
    g: &crate::aufrufgraph::Graph,
    syscalls: &BTreeSet<String>,
    kein_total: &BTreeSet<String>,
) -> Option<String> {
    if kein_total.contains(key) {
        return Some("no total cost: `forever` promises `per_pass`, not `costs`".to_string());
    }
    if crate::kosten::ruft_syscall(g, &key, syscalls) {
        return Some("cost-opaque `syscall` edge (tolerated)".to_string());
    }
    if f.decreases.is_none() && g.im_zyklus(&key) {
        return Some("recursion without `decreases` (unbounded through the cycle)".to_string());
    }
    if g.knoten.get(key).is_some_and(|k| k.indirect.iter().any(|i| !i.has_contract)) {
        return Some("indirect call without a pointer-type cost".to_string());
    }
    Some("the body settles no number".to_string())
}

/// One derived line per function: the clause an elaborator would write.
pub fn zeige(baum: &Programm, datei: &str) -> String {
    let mut s = String::new();
    s.push_str(&format!("-- Derived contract: {datei}\n"));
    s.push_str(
        "-- Every omitted `effects`/`costs` the checker derives, as the line\n\
         -- an elaborator would write. A written line stays the enforced bound;\n\
         -- `(written)` marks it, `(derived)` the settled omission, `(lower bound)`\n\
         -- the omission nothing settles — with the code that refuses it.\n\n",
    );
    for v in ertraege(baum) {
        s.push_str(&format!("{}\n", v.schluessel));
        let eintraege: Vec<String> =
            v.effects.iter().filter(|w| w.as_str() != "pure").cloned().collect();
        let effects_zeile = if eintraege.is_empty() {
            "effects { pure }".to_string()
        } else {
            format!("effects {{ {} }}", eintraege.join(", "))
        };
        let e_stand = if v.geschrieben_effects {
            "written"
        } else if v.effects_offen.is_none() {
            "derived"
        } else {
            "lower bound"
        };
        s.push_str(&format!("    {effects_zeile}  [{e_stand}]\n"));
        if let Some(g) = &v.effects_offen {
            if !v.geschrieben_effects {
                s.push_str(&format!("    -- LOWER BOUND (R16): {g}\n"));
            }
        }
        match (v.geschrieben_kosten, v.costs) {
            (Some(Some(z)), _) => {
                s.push_str(&format!("    costs <= {z} ops  [written]\n"));
            }
            (Some(None), _) => {
                s.push_str("    costs <= <symbolic> ops  [written]\n");
            }
            (None, Some(n)) => {
                s.push_str(&format!("    costs <= {n} ops  [derived]\n"));
            }
            (None, None) => {
                if let Some(g) = &v.costs_offen {
                    s.push_str(&format!("    -- no cost follows: {g}\n"));
                }
            }
        }
    }
    s
}

#[cfg(test)]
mod tests {
    //! **The view measures what the passes decide.**
    //!
    //! The twin rule (R14): every derived figure below would be SILENT without
    //! the pass that enforces it — an omitted `pure` body is green because
    //! `E005`/`E010` hold the written line, an omitted cost because `K001`
    //! holds the written bound. *A view that cannot turn red measures nothing,
    //! so each direction stands beside its counter-direction.*

    use super::*;

    fn ertrag(q: &str, name: &str) -> Vertrag {
        let baum = gabbro_syntax::lies("probe.gab", q).0;
        ertraege(&baum).into_iter().find(|v| v.schluessel == name).expect(name)
    }

    /// **The derivable omission: no line, no refusal, full view.**
    ///
    /// `f` touches nothing and adds two numbers. The derived set is empty
    /// (`pure`), the derived cost is the addition — and neither is open.
    #[test]
    fn ableitbare_auslassung_steht_voll_da() {
        let v = ertrag(
            "impl fn f(a : u32, b : u32) -> u32 { return a + b; }",
            "f",
        );
        assert!(!v.geschrieben_effects);
        assert!(v.geschrieben_kosten.is_none());
        assert!(v.effects.is_empty(), "{:?}", v.effects);
        assert!(v.effects_offen.is_none());
        assert!(v.costs.is_some(), "one addition settles a number");
        assert!(v.costs_offen.is_none());
    }

    /// **Counter-direction: a written line is marked, not derived.**
    ///
    /// The same body with both lines written shows `(written)` in the view —
    /// and the written bound stands beside the derivation above (which the
    /// `kosten::bericht` holds against the body). *A view that called
    /// everything derived would measure nothing about the bound.*
    #[test]
    fn geschriebene_zeile_heisst_geschrieben() {
        let v = ertrag(
            "impl fn f(a : u32, b : u32) -> u32 effects { pure } costs <= 3 ops \
             { return a + b; }",
            "f",
        );
        assert!(v.geschrieben_effects);
        assert_eq!(v.geschrieben_kosten, Some(Some(3)));
        assert!(v.effects.is_empty());
        // The derivation map holds omissions only — a written bound is
        // enforced (`K001`), not re-derived.
        assert!(v.costs.is_none());
        assert!(v.costs_offen.is_none());
    }

    /// **Where nothing settles the view says so — with the refusing code.**
    ///
    /// The callee promises more than it does; the caller's omission is the
    /// `N305` of `wirkungen.rs`, and the view carries the same lower bound —
    /// one check, two readers. The cost derives regardless (the callee
    /// declares its price): *one open leg does not close the other.*
    #[test]
    fn offene_haelfte_nennt_den_code() {
        let v = ertrag(
            "static mut W : u32 = 0;\n\
             impl fn geber() effects { writes W } costs <= 100 ops { }\n\
             impl fn rufer() { geber(); }",
            "rufer",
        );
        assert!(
            v.effects_offen.as_deref().is_some_and(|s| s.contains("callee promises")),
            "the padding the derivation must not inherit: {:?}",
            v.effects_offen
        );
        assert!(v.costs.is_some());
        let g = ertrag(
            "extern fn fremd() effects { pure };",
            "fremd",
        );
        assert!(g.costs.is_none());
        assert!(
            g.costs_offen.as_deref().is_some_and(|s| s.contains("no body")),
            "{:?}",
            g.costs_offen
        );
    }
}
