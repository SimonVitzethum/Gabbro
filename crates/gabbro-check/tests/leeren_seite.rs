//! F2 (2026-10-07, legacy C backend): the page-return helper of `reset X at i count n;` must test
//! the ABSOLUTE rounded addresses (`lo < hi`) before it forms any offset. The first version formed
//! `bis = (a + bytes) / seite * seite - a` in `uint64_t` first, which wraps for a range inside one
//! page and zeroed far past the buffer (example 175 with `reset RING at 10 count 100;` exited 139).
//! Template `region.leeren`, `leeren_in_einer_seite` / `leeren_alt_bricht` in `SchablonenArena.lean`.
//! The run-time half (corrected helper exits 0, the first-version twin dies) is stage 4 of
//! `instrumente/pruefe-seiten-zurueck.sh`.

#[test]
fn die_seitenrueckgabe_prueft_absolute_adressen_vor_dem_versatz() {
    let q = "module t { static mut R : [u8; 8192] = 0 aligned 4096; \
             impl fn f() effects { writes R } costs <= 9999 ops { reset R at 200 count 100; } }";
    let (baum, mut a) = gabbro_syntax::lies("p.gab", q);
    assert_eq!(a.fehler_zahl(), 0, "the probe itself does not parse:\n{}", a.zeige(q));
    let c = gabbro_check::emit::emittiere(&baum, &mut a);
    assert!(c.contains("if (lo < hi) {"), "the corrected test is missing:\n{c}");
    assert!(c.contains("von = lo - a;") && c.contains("bis = hi - a;"));
    // the poison: either of the two lines of the first version brings the wrap back
    assert!(!c.contains("bis = (a + bytes) / seite * seite - a;"), "the wrapping form is back");
    assert!(!c.contains("if (von < bis) {"), "the wrapping test is back");
}
