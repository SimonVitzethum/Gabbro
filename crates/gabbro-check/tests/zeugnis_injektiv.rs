//! **Is the certificate injective?** -- measured, not asserted.
//!
//! A translation certificate names what the translation RESTS ON. The worth of such a list
//! hangs on one property no lowering can give it:
//!
//! > **A certificate that vouches for two different programs vouches for neither.**
//!
//! On 2026-08-31 that was violated. `messung/proben/probe-zeugnis-injektiv-{a,b}.gab` differ
//! in **exactly one line** -- `threads` against `queue r` --, both pass with
//! `0 errors, 0 hints`, and their certificates were **byte-identical** apart from the header
//! carrying the file name. Five of the nine traversal domains ran together on a
//! `_ => "traverse"` in `zeugnis.rs`.
//!
//! ## Why these probes TAKE AWAY the file name
//!
//! `zeige` puts the file name into the header. Two certificates that differ only there are
//! not different -- *they carry different labels on the same statement.* Every probe here
//! renders under the **same** name; what is left is the content.
//!
//! ## And the counter-direction stands beside it
//!
//! A probe that only demands "different" is satisfied by a certificate that prints a
//! timestamp. **Two equal programs must get equal certificates** -- only both directions
//! together measure injectivity instead of noise.

use std::path::{Path, PathBuf};

fn wurzel() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..")
}

/// The certificate of ONE source, rendered under a fixed file name.
fn zeugnis(quelle: &str) -> String {
    let (baum, _) = gabbro_syntax::lies("probe.gab", quelle);
    gabbro_check::zeugnis::zeige(&baum, "probe.gab", quelle)
}

fn lies(relativ: &str) -> String {
    let p = wurzel().join(relativ);
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()))
}

/// **The measured pair: one line of difference, and the certificate has to see it.**
#[test]
fn das_gemessene_paar_hat_verschiedene_zeugnisse() {
    let a = zeugnis(&lies("messung/proben/probe-zeugnis-injektiv-a.gab"));
    let b = zeugnis(&lies("messung/proben/probe-zeugnis-injektiv-b.gab"));
    assert_ne!(
        a, b,
        "`threads` and `queue r` get the same certificate -- and the file name is taken away \
         here, so it vouches for both programs equally well"
    );
    // And the difference must be the DOMAIN, not just anything.
    assert!(a.contains("traverse (threads)"), "{a}");
    assert!(b.contains("traverse (queue)"), "{b}");
}

/// **The counter-direction.** Without it a certificate carrying a random value would count as
/// "injective".
#[test]
fn zwei_gleiche_programme_geben_gleiche_zeugnisse() {
    let q = lies("messung/proben/probe-zeugnis-injektiv-a.gab");
    assert_eq!(zeugnis(&q), zeugnis(&q.clone()));
    // And a copy with different comment text is the same PROGRAM.
    let mit_kommentar = format!("-- a different comment, the same program\n{q}");
    assert_eq!(
        zeugnis(&q),
        zeugnis(&mit_kommentar),
        "a comment is no difference in the program -- the certificate must not see it"
    );
}

/// The nine domains, each in its own traversal. **The body is the same one** so that the
/// difference can come from nowhere but the domain.
///
/// The declarations are those of `messung/proben/probe-neun-domaenen.gab` -- the same carrier
/// set in a different position: there the nine stand in `ensures`, here in `traverse`.
const KOPF: &str = "module p {
const NK : u32 = 64;
const NR : u64 = 32;
type RingNr = u32 in 0 ..< 32;

table Knoten count NK {
    tree { parent elter, child kind, sibling gesch }
    slot {
        belegt : bool,
        elter  : option index into Knoten,
        kind   : option index into Knoten,
        gesch  : option index into Knoten,
    }
}

type Ring = { plaetze : [RingNr; NR], kopf : u32, };

format Wort endian little {
    gueltigkeit : bool @0,
    schreibbar  : bool @1,
    frei        : u64 @[11:2]  reserved,
    rahmen      : u64 embeds [51:12] scale 4096,
    hoch        : u64 @[63:52] reserved,
}

walk Baum levels 2 {
    node : [Wort; 512],
    down : rahmen when it.gueltigkeit && !it.schreibbar,
    leaf : it.gueltigkeit && it.schreibbar,
}

extern fn nie() -> never effects { diverges } costs <= 0 ops;

divergent fn f(k : ptr<normal, rw> Knoten, r : ptr<normal, rw> Ring,
               w : ptr<normal, rw> Baum, p : index into Knoten) -> never
    effects { writes k.slots, diverges }
{
";

/// The nine, in the order `Domaene` has in `ast.rs`.
const DOMAENEN: [&str; 9] = [
    "slots of k",
    "chain(kind, gesch) in k.slots[p]",
    "descendants of k.slots[p]",
    "ancestors of k.slots[p]",
    "queue r",
    "fields of Wort",
    "elems of r.plaetze",
    "threads",
    "mappings of w",
];

fn quelle_fuer(domaene: &str) -> String {
    format!(
        "{KOPF}    traverse t over {domaene} by unvisited touches writes k.slots {{
        k.slots[0].belegt = true;
    }}
    nie();
}}
}}"
    )
}

/// **All nine domains pairwise distinct -- and that is the actual promise.**
///
/// The measured pair shows ONE collision. This probe rules out the remaining thirty-five, and
/// it falls on the day somebody pulls two domains back onto one mark.
#[test]
fn alle_neun_domaenen_geben_verschiedene_zeugnisse() {
    let mut gesehen: Vec<(&str, String)> = Vec::new();
    for d in DOMAENEN {
        let quelle = quelle_fuer(d);
        let (baum, mut absagen) = gabbro_syntax::lies("probe.gab", &quelle);
        gabbro_check::pruefe(&baum, &mut absagen);
        // **The probe measures the CERTIFICATE, not the checking** -- the certificate reads
        // the TREE. But a parse error would be a fault of the probe itself, and that falls
        // here: a body that never parsed carries no traversal at all, and nine empty
        // certificates would compare equal for the wrong reason.
        assert!(
            !absagen.absagen.iter().any(|a| a.code.starts_with('P')),
            "the probe for `{d}` does not parse: {:?}",
            absagen.absagen.iter().map(|a| a.code).collect::<Vec<_>>()
        );
        let z = gabbro_check::zeugnis::zeige(&baum, "probe.gab", &quelle);
        for (vorher, zv) in &gesehen {
            assert_ne!(
                *zv, z,
                "`{vorher}` and `{d}` get THE SAME certificate -- two programs, one voucher"
            );
        }
        gesehen.push((d, z));
    }
    assert_eq!(gesehen.len(), 9);
}

/// **And none of the nine marks falls through the classification.** A mark without an entry
/// in `EINORDNUNG` lands on `unzugeordnet` -- it would be injective and still unvouched.
#[test]
fn jeder_domaenenausweis_steht_in_der_einordnung() {
    for d in DOMAENEN {
        let quelle = quelle_fuer(d);
        let (baum, _) = gabbro_syntax::lies("probe.gab", &quelle);
        let e = gabbro_check::zeugnis::erhebe(&baum);
        assert!(
            e.unzugeordnet.is_empty(),
            "`{d}`: {:?} stands in no classification",
            e.unzugeordnet
        );
        assert_eq!(
            e.posten.keys().filter(|k| k.starts_with("traverse")).count(),
            1,
            "`{d}`: exactly one traversal mark, counted {:?}",
            e.posten
        );
    }
}
