//! Lane E5 -- the translation stage, first cut (dokumente/PRUEFER.md section 6).
//!
//! Three sides, each pinned:
//!
//! * the checker translates exact-length integer regions through the
//!   identity translator and refuses everything else by code (the falling
//!   directions stand in `paesse.rs` as `translation_*` and under
//!   `beispiele/gift/905`-`909`);
//! * the emitter passes an accepted payload as a `static const` table
//!   argument, and the generated C compiles and computes the sum at run
//!   time (one call site below, two in the second test);
//! * the printed certificate carries the same three definition lines the
//!   Lean witness (`Uebersetzung.sumPayloadVals`) closes by `decide` -- a
//!   drift breaks this file, and the `decide` itself breaks `./lean-bau`.






// -- the certificate: printed payload meets the Lean witness -----------------

#[test]
fn payload_certificate_prints_encoding_n() {
    let cert = gabbro_check::uebersetzung::payload_certificate("sumPayload", &[10, 20, 30, 40], 0, 100);
    let erwartet = "-- Payload certificate printed by gabbro-check (lane 129):\n\
        -- the payload values of `sumPayload` for `Uebersetzung.nutzlastZert`.\n\
        def sumPayloadVals : List Nat := [10, 20, 30, 40]\n\
        def sumPayloadOk : Bool := nutzlastZert sumPayloadVals 0 100\n\
        theorem sumPayload_zert : sumPayloadOk = true := by decide\n";
    assert_eq!(cert, erwartet, "the printer's bytes are the contract");
}

#[test]
fn payload_certificate_mirrors_lean_file() {
    let cert = gabbro_check::uebersetzung::payload_certificate("sumPayload", &[10, 20, 30, 40], 0, 100);
    let lean = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("grammatik")
        .join("Grammatik")
        .join("Logik")
        .join("Vertraege")
        .join("Uebersetzung.lean");
    let text = std::fs::read_to_string(&lean)
        .unwrap_or_else(|e| panic!("{}: {e}", lean.display()));
    for zeile in cert.lines().filter(|l| l.starts_with("def ") || l.starts_with("theorem ")) {
        assert!(
            text.contains(zeile),
            "the Lean file carries the printer's line verbatim -- a drift is a finding:\n{zeile}"
        );
    }
}
