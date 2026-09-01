//! **R14 for the derivation: it proves first that it can measure.**
//!
//! Before the first derived figure comes (a) *it finds what it is supposed to find*, and (b)
//! *every assurance demonstrably hangs on the thing under test* -- change the callee's body
//! and it flips. **Without (b) a green probe is only a green screen.**
//!
//! And a third class joins here that the call graph does not have: **the derivation may draw
//! on no declaration.** The probe for that is a line that LIES -- a callee with an
//! over-wide `effects` whose body does less. The hull inherits the padding; the derivation
//! must not see it.

use gabbro_check::ableitung::{self, Weg};

fn ab(q: &str, weit: bool) -> ableitung::Ableitung {
    ableitung::leite_ab(&gabbro_syntax::lies("probe.gab", q).0, weit)
}

/// **The core: an over-wide declaration at the callee must NOT reach the caller.**
///
/// `tief` declares `writes Z` and never writes it. `aufrufgraph::huelle` takes the
/// **declaration** and carries `writes Z` up to the caller; the derivation goes over the
/// **body** and must not.
///
/// > *That is the whole difference between the two bases*, and the probe holds both side by
/// > side in one function -- otherwise one measures two runs instead of two registers.
#[test]
fn eine_zu_weite_deklaration_des_gerufenen_erbt_der_rufer_nicht() {
    let q = "module t {
static mut Y : u32 = 0;
static mut Z : u32 = 0;
impl fn tief() effects { writes Y, writes Z } costs <= 4 ops { Y = 1; }
impl fn oben() effects { writes Y, writes Z } costs <= 8 ops { tief(); }
}";
    let baum = gabbro_syntax::lies("probe.gab", q).0;
    let h = gabbro_check::aufrufgraph::erhebe(&baum).huelle_der_gerufenen("t::oben");
    assert!(
        h.wirkungen.contains("writes Z"),
        "the hull over the DECLARATIONS carries the padding -- without that this probe \
         does not measure the difference: {:?}",
        h.wirkungen
    );

    let a = ab(q, true);
    let oben = &a.je["t::oben"].wirkungen;
    assert!(oben.contains("writes Y"), "{oben:?}");
    assert!(
        !oben.contains("writes Z"),
        "the DERIVATION may draw on no declaration: {oben:?}"
    );
}

/// R14b: **does the assurance hang on the body?** If `tief` really writes `Z`, it has to
/// arrive up top. *Otherwise the probe above only measures that the derivation finds
/// nothing at all.*
#[test]
fn schreibt_der_gerufene_es_wirklich_kommt_es_oben_an() {
    let q = "module t {
static mut Y : u32 = 0;
static mut Z : u32 = 0;
impl fn tief() effects { writes Y, writes Z } costs <= 4 ops { Y = 1; Z = 2; }
impl fn oben() effects { writes Y, writes Z } costs <= 8 ops { tief(); }
}";
    let a = ab(q, true);
    assert!(a.je["t::oben"].wirkungen.contains("writes Z"), "{:?}", a.je["t::oben"]);
}

/// **The order must not matter.** The fixpoint runs over a `BTreeMap`; if the caller sorts
/// BEFORE the callee it needs a second round. *A result that depends on key order is not a
/// fixpoint but a pass.*
#[test]
fn die_kette_traegt_auch_gegen_die_schluesselordnung() {
    // `aaa` calls `mmm` calls `zzz` -- the caller always sorts BEFORE the callee.
    let q = "module t {
static mut W : u32 = 0;
impl fn zzz() effects { writes W } costs <= 2 ops { W = 1; }
impl fn mmm() effects { writes W } costs <= 4 ops { zzz(); }
impl fn aaa() effects { writes W } costs <= 8 ops { mmm(); }
}";
    let a = ab(q, true);
    assert!(a.je["t::aaa"].wirkungen.contains("writes W"), "{:?}", a.je["t::aaa"]);
    assert!(
        a.runden >= 2,
        "a chain against the order needs more than one round: {}",
        a.runden
    );

    // And the same chain WITH the order -- same result, fewer rounds.
    let r = "module t {
static mut W : u32 = 0;
impl fn aaa() effects { writes W } costs <= 2 ops { W = 1; }
impl fn mmm() effects { writes W } costs <= 4 ops { aaa(); }
impl fn zzz() effects { writes W } costs <= 8 ops { mmm(); }
}";
    let b = ab(r, true);
    assert!(b.je["t::zzz"].wirkungen.contains("writes W"), "{:?}", b.je["t::zzz"]);
}

/// **A cycle does NOT tear the derivation** -- and that is the one point where it can do
/// more than the hull. `aufrufgraph::gehe` stops at the path cut and yields a lower bound
/// with `cycle over ...`; the fixpoint converges.
#[test]
fn der_zyklus_reisst_die_ableitung_nicht() {
    let q = "module t {
const T : u32 = 512;
static mut summe : u32 = 0;
impl fn gerade(n : u32 in 0 .. T) -> u32 effects { writes summe } costs <= 64 ops decreases n {
    summe = n;
    if n >= 1 { return ungerade(n - 1); }
    return 0;
}
impl fn ungerade(n : u32 in 0 .. T) -> u32 effects { writes summe } costs <= 64 ops decreases n {
    summe = n;
    if n >= 1 { return gerade(n - 1); }
    return 0;
}
}";
    let baum = gabbro_syntax::lies("probe.gab", q).0;
    let h = gabbro_check::aufrufgraph::erhebe(&baum).huelle_der_gerufenen("t::gerade");
    assert!(
        h.unvollstaendig.is_some(),
        "the hull MUST tear here -- otherwise the line below measures nothing"
    );

    let a = ab(q, true);
    assert_eq!(a.je["t::gerade"].unvollstaendig, None, "{:?}", a.je["t::gerade"]);
    assert!(a.je["t::gerade"].wirkungen.contains("writes summe"));
}

/// **The origin is retrievable, and the path ends at the body** (§25).
///
/// The error arises at the body and is reported elsewhere -- *"a refusal that cannot quote
/// the line it is about."* This probe records that the way back is there.
#[test]
fn der_ursprung_nennt_den_rumpf_zwei_ebenen_tiefer() {
    let q = "module t {
static mut W : u32 = 0;
impl fn tief() effects { writes W } costs <= 2 ops { W = 1; }
impl fn mitte() effects { writes W } costs <= 4 ops { tief(); }
impl fn oben() effects { writes W } costs <= 8 ops { mitte(); }
}";
    let a = ab(q, true);
    let p = a.pfad("t::oben", "writes W");
    assert_eq!(p.len(), 3, "oben -> mitte -> tief: {p:?}");
    assert_eq!(p[0].0, "t::oben");
    assert_eq!(p[1].0, "t::mitte");
    assert_eq!(p[2].0, "t::tief");
    assert!(matches!(p[2].2, Weg::Rumpf(_)), "the path ends at the deed: {:?}", p[2].2);
}

/// **An `extern fn` is the edge, and the origin says so.** Its line stays the source even
/// after the derivation -- *the trust surface is not bookkeeping.*
#[test]
fn am_extern_heisst_der_weg_rand_und_nicht_ueber() {
    let q = "module t {
static mut W : u32 = 0;
extern fn fremd() effects { writes W } costs <= 2 ops;
impl fn oben() effects { writes W } costs <= 8 ops { fremd(); }
}";
    let a = ab(q, true);
    // **The path is ONE hop long, and that is the statement.** The hop names the callee and
    // its line; going further would mean stepping into a body that does not exist. *That is
    // exactly where the checked world stops.*
    let p = a.pfad("t::oben", "writes W");
    assert_eq!(p.len(), 1, "{p:?}");
    assert!(
        matches!(&p[0].2, Weg::Rand { gerufener, .. } if gerufener == "t::fremd"),
        "{:?}",
        p[0].2
    );
}

/// **The widening fires, and it is counted.**
///
/// §24 says the lattice is finite. **It is not:** `ersetze` creates new places when it
/// carries one across the call boundary, and in a cycle the place expression grows without
/// bound. This probe builds exactly that case -- *without it the widening would be a piece
/// of code nobody knows ever runs.*
#[test]
fn die_verbreiterung_greift_bei_einer_wachsenden_ortskette() {
    let q = "module t {
table K count 64 { slot { kind : option index into K, wert : u32 in 0 .. 100, } }
impl fn geh(k : ptr<normal, rw> K, n : u32 in 0 .. 8) -> u32
    effects { writes k.slots }
    costs <= 64 ops
    decreases n
{
    k.slots[0].wert = 0;
    if n >= 1 { return geh(k, n - 1); }
    return 0;
}
}";
    // This chain does NOT grow -- the argument is the same place. The assertions below are
    // the real case; this one records that a harmless recursion does NOT trip the widening.
    // *A guard that always fires measures nothing.*
    let a = ab(q, true);
    assert_eq!(a.verbreitert, 0, "no growth, no widening: {}", a.verbreitert);

    // And here it grows: `writes p.a` at the callee becomes `writes p.b.a` at the caller,
    // then `writes p.b.b.a`, ... The widening cuts at `TIEFE_MAX` steps.
    let w = ableitung::verbreitere_fuer_probe("writes p.b.b.b.b.b.a");
    assert_eq!(w.as_deref(), Some("writes p.b.b.b.b"), "{w:?}");
    assert_eq!(
        ableitung::verbreitere_fuer_probe("writes p.b.a"),
        None,
        "shallow enough -- nothing to cut"
    );
    // **Never inside a name.** `a.bcd` must not become `a.b`: a prefix that is no place
    // covers nothing and would DROP the effect instead of widening it.
    assert_eq!(
        ableitung::verbreitere_fuer_probe("writes a.bcd[i].efg.hij.klm"),
        Some("writes a.bcd[i].efg.hij".to_string())
    );
}

/// **`--eng` and `--weit` are two questions, and they have to give two answers.** *Were the
/// answers the same, one of the two flags would be dead and every measurement taken with it
/// counted twice.*
#[test]
fn eng_und_weit_unterscheiden_sich_am_parameterlesen() {
    let q = "module t {
table K count 64 { slot { wert : u32 in 0 .. 100, } }
impl fn lies(k : ptr<normal, r> K, i : index into K) -> u32
    effects { reads k.slots }
    costs <= 4 ops
{ return k.slots[i].wert; }
}";
    let weit = ab(q, true);
    let eng = ab(q, false);
    assert!(
        weit.je["t::lies"].wirkungen.iter().any(|w| w.starts_with("reads k.slots")),
        "{:?}",
        weit.je["t::lies"].wirkungen
    );
    assert!(
        eng.je["t::lies"].wirkungen.is_empty(),
        "`E010` leaves parameter reads out, with a reason: {:?}",
        eng.je["t::lies"].wirkungen
    );
}
