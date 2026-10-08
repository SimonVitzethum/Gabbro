//! ADVERSARIAL REVIEW, agent 05 task 5c: attacks against four just-added
//! checker rules (R1 M147 selector refinement, R2 static initializer
//! lists, R3 whole-array copy, R4 string cells).
//!
//! Method: each attack asserts the CURRENT behaviour (green by
//! construction); the classification stands in the `// FINDING:` line:
//! `sound` (accepted/refused as the rule's sentence promises),
//! `ACCEPTS-UNSOUND` (accepted, guarantee violated -- reported in
//! REPORT-05.md with program, reason and fix proposal),
//! `REFUSES-SOUND` (refused where a sound rule would accept).
//! The `gabbro check` CLI is lane-blocked; behaviour is measured through
//! `gabbro_check::pruefe`, the same function the CLI drives.

use gabbro_syntax::diag::Stufe;

fn fehler(quelle: &str) -> Vec<String> {
    let (baum, mut absagen) = gabbro_syntax::lies("attack_5c", quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

fn sauber(quelle: &str) {
    let f = fehler(quelle);
    assert!(f.is_empty(), "expected 0 errors, got {f:?} for:\n{quelle}");
}

fn faellt(quelle: &str, code: &str) {
    let f = fehler(quelle);
    assert!(
        f.iter().any(|c| c == code),
        "expected {code}, got {f:?} for:\n{quelle}"
    );
}

// --- R1: M147 selector refinement -------------------------------------------
// Sentence `m1.frische`: no decision (branch/match condition, call
// argument, return, `narrow` subject, index) reads a stale-named local;
// the carriers of an INDEX expression do not taint the value read
// through it, unless the index mentions an expired local.

fn r1_einheit(rumpf: &str) -> String {
    format!(
        "module r1 {{
static mut RING : [u32 in 0 .. 255; 256] = 0;
static mut DATA : [u32 in 0 .. 255; 256] = 0;
impl fn f(i : u32 in 0 ..< 256) -> u32
    effects {{ reads RING, writes RING, reads DATA, writes DATA }}
    costs <= 64 ops
{{
{rumpf}
    return 0;
}}
}}"
    )
}

fn r1_sauber(rumpf: &str) {
    sauber(&r1_einheit(rumpf));
}

fn r1_faellt(rumpf: &str, code: &str) {
    faellt(&r1_einheit(rumpf), code);
}

#[test]
fn r1_schattenblock_toetet_staint() {
    // FINDING: sound (shadow rebind keeps the outer taint: M147 fires).
    r1_faellt(
        "    let e : u32 = RING[0];\n    RING[0] = 5;\n    { let e : u32 = 0; }\n    if e == 0 { return 1; }",
        "M147",
    );
}

#[test]
fn r1_zwei_griffe_gleiche_tabelle() {
    // FINDING: FIXED by agent 05 (was ACCEPTS-UNSOUND): carriers key by table
    // since task 5d, so the write through `u` expires the `t` read and the
    // decision falls as M147.
    faellt(
        "module r1a {
table T count 4 { slot { x : u32, } }
impl fn f(t : ptr<normal, rw> T, u : ptr<normal, rw> T, i : index into T) -> u32
    effects { reads t.slots, writes u.slots } costs <= 64 ops
{
    let v : u32 = t.slots[i].x;
    u.slots[i].x = 1;
    if v == 0 { return 1; }
    return 0;
}
}",
        "M147",
    );
}

#[test]
fn r1_verschachtelter_waehler() {
    // FINDING: sound (nested selector stays silent by design: snapshot).
    r1_sauber(
        "    let x : u32 = DATA[RING[0]];\n    RING[0] = 9;\n    if x == 0 { return 1; }",
    );
}

#[test]
fn r1_waehler_inhalt_erneut_gelesen() {
    // FINDING: sound (content write still expires: M147).
    r1_faellt(
        "    let x : u32 = DATA[RING[0]];\n    DATA[0] = 1;\n    if x == 0 { return 1; }",
        "M147",
    );
}

#[test]
fn r1_veralteter_waehler() {
    // FINDING: sound (expired selector keeps the old behaviour: M147).
    r1_faellt(
        "    let e : u32 = RING[0];\n    RING[0] = 1;\n    let b : u32 = DATA[e];\n    DATA[0] = 2;\n    if b == 0 { return 1; }",
        "M147",
    );
}

#[test]
fn r1_ruf_im_waehler() {
    // FINDING: sound (callee reads-hull in the selector dropped by design).
    sauber(
        "module r1c {
static mut RING : [u32 in 0 .. 255; 256] = 0;
static mut DATA : [u32 in 0 .. 255; 256] = 0;
impl fn hole(j : u32 in 0 ..< 256) -> u32 in 0 ..< 256
    effects { reads RING } costs <= 8 ops
{
    return RING[j];
}
impl fn f() -> u32
    effects { reads RING, writes RING, reads DATA } costs <= 64 ops
{
    let b : u32 = DATA[hole(0)];
    RING[0] = 7;
    if b == 0 { return 1; }
    return 0;
}
}",
    );
}

#[test]
fn r1_gleicher_traeger_waehler_und_inhalt() {
    // FINDING: sound (content taint survives the selector drop: M147).
    r1_faellt(
        "    let b : u32 = RING[RING[0]];\n    RING[0] = 1;\n    if b == 0 { return 1; }",
        "M147",
    );
}

#[test]
fn r1_zweistufige_tabelle() {
    // FINDING: sound (same-basis write expires: M147, conservative).
    faellt(
        "module r1t {
table Paket count 8 { slot { quelle : u32, ziel : u32, } }
impl fn f(k : ptr<normal, rw> Paket, i : index into Paket) -> u32
    effects { reads k.slots, writes k.slots } costs <= 64 ops
{
    let v : u32 = k.slots[i].quelle;
    k.slots[i].ziel = 1;
    if v == 0 { return 1; }
    return 0;
}
}",
        "M147",
    );
}

#[test]
fn r1_schleife_toetet_alles() {
    // FINDING: sound (loop kills all taints: M147).
    faellt(
        "module r1s {
table T count 4 { slot { x : u32, } }
impl fn f(t : ptr<normal, rw> T, i : index into T) -> u32
    effects { reads t.slots, writes t.slots } costs <= 64 ops
{
    let v : u32 = t.slots[i].x;
    traverse s over slots of t by unvisited touches writes t.slots {
        t.slots[s].x = 1;
    }
    if v == 0 { return 1; }
    return 0;
}
}",
        "M147",
    );
}

#[test]
fn r1_rueckgabe_veraltet() {
    // FINDING: sound (return is a decision: M147).
    r1_faellt(
        "    let e : u32 = RING[0];\n    RING[0] = 1;\n    return e;",
        "M147",
    );
}

#[test]
fn r1_rufargument_veraltet() {
    // FINDING: sound (call argument is a decision: M147).
    faellt(
        "module r1d {
static mut RING : [u32 in 0 .. 255; 256] = 0;
impl fn nimm(x : u32) -> u32 effects { pure } costs <= 8 ops { return x; }
impl fn f() -> u32
    effects { reads RING, writes RING } costs <= 64 ops
{
    let e : u32 = RING[0];
    RING[0] = 1;
    return nimm(e);
}
}",
        "M147",
    );
}

#[test]
fn r1_index_veraltet() {
    // FINDING: sound (index is a decision: M147).
    r1_faellt(
        "    let e : u32 = RING[0];\n    RING[0] = 1;\n    let y : u32 = DATA[e];\n    return y;",
        "M147",
    );
}

#[test]
fn r1_frische_kontrolle() {
    // FINDING: sound (no write, no expiry: silent).
    r1_sauber("    let e : u32 = RING[0];\n    if e == 0 { return 1; }");
}

#[test]
fn r1_neulesung_kontrolle() {
    // FINDING: sound (re-read is fresh: silent).
    r1_sauber(
        "    let e : u32 = RING[0];\n    RING[0] = 1;\n    let f : u32 = RING[0];\n    if f == 0 { return 1; }",
    );
}

#[test]
fn r1_speichern_erlaubt() {
    // FINDING: sound (storing is no decision: silent).
    r1_sauber("    let e : u32 = RING[0];\n    RING[0] = 1;\n    RING[1] = e;");
}

// --- R2: static initializer lists -------------------------------------------
// Rule: `static mut A : [u32 in 0 .. 255; 4] = [0, 85, 170, 255]` is held
// like a const table (parse.rs `staticdecl`, konstanten.rs `pass`):
// element out of range (K194), wrong length (K191), wrong nesting
// (N285/N286), non-constant elements (K190/K192).

fn r2_modul(gegenstand: &str) -> String {
    format!("module r2 {{\n{gegenstand}\n}}\n")
}

#[test]
fn r2_element_ausserhalb() {
    // FINDING: sound (256 past `0 .. 255`: K194).
    faellt(
        &r2_modul("static mut A : [u32 in 0 .. 255; 4] = [0, 85, 170, 256];"),
        "K194",
    );
}

#[test]
fn r2_laenge_falsch() {
    // FINDING: sound (3 entries for [4]: K191).
    faellt(
        &r2_modul("static mut A : [u32 in 0 .. 255; 4] = [0, 85, 170];"),
        "K191",
    );
}

#[test]
fn r2_wert_wo_zeile() {
    // FINDING: sound (value where a row stands: N285; outer length is
    // checked first, so a flat 4-for-[2;2] falls as K191 instead -- one
    // fault, one refusal).
    faellt(
        &r2_modul(
            "static mut M : [[u32 in 0 .. 255; 2]; 2] = [[1, 2], 3];",
        ),
        "N285",
    );
}

#[test]
fn r2_zeile_wo_wert() {
    // FINDING: sound (row where a value stands: N285).
    faellt(
        &r2_modul("static mut A : [u32 in 0 .. 255; 2] = [[1, 2], 3];"),
        "N285",
    );
}

#[test]
fn r2_zeile_krumm() {
    // FINDING: sound (ragged inner row: N286).
    faellt(
        &r2_modul(
            "static mut M : [[u32 in 0 .. 255; 2]; 2] = [[1, 2], [3]];",
        ),
        "N286",
    );
}

#[test]
fn r2_nicht_konstant() {
    // FINDING: sound (another static's cell is no translation-time
    // value: K190).
    faellt(
        &r2_modul(
            "static mut B : [u32 in 0 .. 255; 4] = [0, 0, 0, 0];\nstatic mut A : [u32 in 0 .. 255; 4] = [B[0], 1, 2, 3];",
        ),
        "K190",
    );
}

#[test]
fn r2_ohne_mut() {
    // FINDING: sound (accepted: a list in read-only memory is fine).
    sauber(&r2_modul(
        "static A : [u32 in 0 .. 255; 4] = [0, 85, 170, 255];",
    ));
}

#[test]
fn r2_liste_ohne_feld() {
    // FINDING: sound (refused; remark for the lead: K190 speaks of
    // constness, the fault here is shape -- no sound accept exists, so
    // the refusal itself is sound).
    faellt(&r2_modul("static mut X : u32 = [1, 2];"), "K190");
}

#[test]
fn r2_reiner_ruf() {
    // FINDING: sound (`const fn` call folds: silent).
    sauber(
        "module r2p {
const fn verdopple(x : u32 in 0 .. 100) -> u32 in 0 .. 200
{
    return x + x;
}
static mut A : [u32 in 0 .. 255; 4] = [verdopple(21), 1, 2, 3];
}",
    );
}

#[test]
fn r2_unreiner_ruf() {
    // FINDING: sound (non-pure call refused: K192).
    faellt(
        "module r2q {
static mut RING : [u32 in 0 .. 255; 8] = 0;
impl fn lies(j : u32 in 0 ..< 8) -> u32
    effects { reads RING } costs <= 8 ops
{
    return RING[j];
}
static mut A : [u32 in 0 .. 255; 4] = [lies(0), 1, 2, 3];
}",
        "K192",
    );
}

#[test]
fn r2_negativ_vorzeichenlos() {
    // FINDING: sound (`-1` held against `0 .. 255`: K194).
    faellt(
        &r2_modul("static mut A : [u32 in 0 .. 255; 4] = [0, 0, 0, -1];"),
        "K194",
    );
}

#[test]
fn r2_liste_im_rumpf() {
    // FINDING: sound (table-body const held like a const table: K194).
    faellt(
        "module r2t {
table T count 4 { const C : [u32 in 0 .. 255; 2] = [1, 300]; slot { x : u32, } }
}",
        "K194",
    );
}

#[test]
fn r2_laenger_als_zaehlkonstante() {
    // FINDING: sound (3 entries for `[u32; N]`, N=2: K191).
    faellt(
        &r2_modul(
            "const N : u32 = 2;\nstatic mut A : [u32 in 0 .. 255; N] = [1, 2, 3];",
        ),
        "K191",
    );
}

#[test]
fn r2_gleitkomma_element() {
    // FINDING: FIXED by the lead (was ACCEPTS-UNSOUND, now K190; float element accepted with 0 errors:
    // `has_float` returns silent and no other pass holds the element, so a
    // non-integer initialises a `u32` cell).
    faellt(
        &r2_modul("static mut A : [u32 in 0 .. 255; 4] = [0.5, 1, 2, 3];"),
        "K190",
    );
}

#[test]
fn r2_bitneg_element() {
    // FINDING: ACCEPTS-UNSOUND (`~1` element accepted with 0 errors:
    // `has_bitneg` returns silent and the value is never held against the
    // element range).
    sauber(&r2_modul(
        "static mut A : [u32 in 0 .. 255; 4] = [~1, 1, 2, 3];",
    ));
}

// --- R3: whole-array copy ----------------------------------------------------
// Sentence `m1.feldkopie_bereich`: same length at every depth, same machine
// word leaf (or `bool`); source range inside target's (else N579); other
// shapes N287; only plain `=` from an array place copies (compound,
// call result, atomic keep N287).

fn r3_einheit(rumpf: &str) -> String {
    format!(
        "module r3 {{
static mut A : [u32 in 0 .. 255; 4] = 0;
static mut B : [u32 in 0 .. 100; 4] = 0;
static mut C : [u32 in 0 .. 255; 4] = 0;
static mut M : [[u32 in 0 .. 255; 4]; 3] = 0;
static mut N : [[u32 in 0 .. 255; 4]; 3] = 0;
impl fn f(i : u32 in 0 ..< 3, j : u32 in 0 ..< 3) -> u32
    effects {{ reads A, writes A, reads B, writes B, reads C, writes C, reads M, writes M, reads N, writes N }}
    costs <= 64 ops
{{
{rumpf}
    return 0;
}}
}}"
    )
}

fn r3_sauber(rumpf: &str) {
    sauber(&r3_einheit(rumpf));
}

fn r3_faellt(rumpf: &str, code: &str) {
    faellt(&r3_einheit(rumpf), code);
}

#[test]
fn r3_bereich_passt() {
    // FINDING: sound (narrow into wide, same word: clean).
    r3_sauber("    A = B;");
}

#[test]
fn r3_bereich_zu_weit() {
    // FINDING: sound (wide into narrow: N579).
    r3_faellt("    B = A;", "N579");
}

#[test]
fn r3_bereich_gleich() {
    // FINDING: sound (equal ranges: clean).
    r3_sauber("    A = C;");
}

#[test]
fn r3_selbstkopie() {
    // FINDING: sound (row onto itself: clean; `memmove` is overlap-safe).
    r3_sauber("    M[i] = M[i];");
}

#[test]
fn r3_zeile_ueberlappt() {
    // FINDING: sound (overlapping rows: clean; overlap-safe by construction).
    r3_sauber("    M[i] = M[j];");
}

#[test]
fn r3_laenge_ungleich() {
    // FINDING: sound (different outer lengths: N287).
    faellt(
        "module r3l {
static mut A : [u32 in 0 .. 255; 4] = 0;
static mut K : [u32 in 0 .. 255; 3] = 0;
impl fn f() -> u32 effects { reads A, writes K } costs <= 16 ops
{
    K = A;
    return 0;
}
}",
        "N287",
    );
}

#[test]
fn r3_innen_ungleich() {
    // FINDING: sound (same outer, different inner lengths: N287).
    faellt(
        "module r3n {
static mut M : [[u32 in 0 .. 255; 4]; 3] = 0;
static mut W : [[u32 in 0 .. 255; 3]; 3] = 0;
impl fn f() -> u32 effects { reads M, writes W } costs <= 16 ops
{
    W = M;
    return 0;
}
}",
        "N287",
    );
}

#[test]
fn r3_bool_bool() {
    // FINDING: sound (bool onto bool: clean, the sentence's "or bool").
    sauber(
        "module r3b {
static mut P : [bool; 2] = 0;
static mut Q : [bool; 2] = 0;
impl fn f() -> u32 effects { reads P, writes Q } costs <= 16 ops
{
    Q = P;
    return 0;
}
}",
    );
}

#[test]
fn r3_bool_u8() {
    // FINDING: sound (bool onto u8 is no same word and no bool-bool:
    // N287, per sentence).
    faellt(
        "module r3c {
static mut P : [bool; 2] = 0;
static mut R : [u8 in 0 .. 255; 2] = 0;
impl fn f() -> u32 effects { reads P, writes R } costs <= 16 ops
{
    R = P;
    return 0;
}
}",
        "N287",
    );
}

#[test]
fn r3_vorzeichen_gleicher_text() {
    // FINDING: sound (sign is part of the word: N287, per sentence).
    faellt(
        "module r3d {
static mut S : [i8 in 0 .. 100; 2] = 0;
static mut U : [u8 in 0 .. 100; 2] = 0;
impl fn f() -> u32 effects { reads S, writes U } costs <= 16 ops
{
    U = S;
    return 0;
}
}",
        "N287",
    );
}

#[test]
fn r3_breite_ungleich() {
    // FINDING: sound (width is part of the word: N287, per sentence;
    // a widening copy would be sound but is not promised).
    faellt(
        "module r3e {
static mut W : [u16 in 0 .. 100; 2] = 0;
static mut U : [u32 in 0 .. 100; 2] = 0;
impl fn f() -> u32 effects { reads W, writes U } costs <= 16 ops
{
    U = W;
    return 0;
}
}",
        "N287",
    );
}

#[test]
fn r3_typ_alias() {
    // FINDING: sound (alias resolves to the same array: clean).
    sauber(
        "module r3f {
type V = [u32 in 0 .. 255; 4];
static mut VA : V = 0;
static mut VB : V = 0;
impl fn f() -> u32 effects { reads VB, writes VA } costs <= 16 ops
{
    VA = VB;
    return 0;
}
}",
    );
}

#[test]
fn r3_satz_element() {
    // FINDING: sound (record leaf has no range: N287).
    faellt(
        "module r3g {
type R = { x : u32, };
static mut RA : [R; 2] = 0;
static mut RB : [R; 2] = 0;
impl fn f() -> u32 effects { reads RB, writes RA } costs <= 16 ops
{
    RA = RB;
    return 0;
}
}",
        "N287",
    );
}

#[test]
fn r3_plus_gleich() {
    // FINDING: sound (no compound array operation: N287, per vorbehalt).
    r3_faellt("    B += A;", "N287");
}

#[test]
fn r3_rufergebnis() {
    // FINDING: sound (call result is no array place: N287, per vorbehalt).
    faellt(
        "module r3h {
static mut A : [u32 in 0 .. 255; 4] = 0;
static mut B : [u32 in 0 .. 100; 4] = 0;
impl fn gib() -> [u32 in 0 .. 100; 4] effects { reads B } costs <= 16 ops
{
    return B;
}
impl fn f() -> u32 effects { writes A } costs <= 16 ops
{
    A = gib();
    return 0;
}
}",
        "N287",
    );
}

#[test]
fn r3_zeiger_feld() {
    // FINDING: sound (`p.all` is no array place: N287).
    faellt(
        "module r3i {
static mut A : [u32 in 0 .. 255; 4] = 0;
impl fn f(p : ptr<normal, rw> [u32 in 0 .. 255; 4]) -> u32
    effects { reads A, writes p } costs <= 16 ops
{
    A = p.all;
    return 0;
}
}",
        "N287",
    );
}

// --- R4: string cells ----------------------------------------------------------
// Discipline (N581, SPRACHE-EFFIZIENZ #13 + task 5b): a cell -- slot field
// or static array element -- is read WHOLE into a local and written WHOLE;
// every other use falls (N581); copies hold N455.

fn r4_tabelle(rumpf: &str) -> String {
    format!(
        "module r4 {{
table Namen count 4 {{ slot {{ name : string max 8, }} }}
lock K protects {{ Namen }} rank 0 held <= 100 ops;
impl fn f(t : ptr<normal, rw> Namen, i : index into Namen, s : string max 8, k : string max 16) -> u32
    requires Held(K)
    effects {{ reads t.slots, writes t.slots, locks K }}
    costs <= 64 ops
{{
{rumpf}
    return 0;
}}
}}"
    )
}

fn r4_feld(rumpf: &str) -> String {
    format!(
        "module r4f {{
static mut NAMEN : [string max 8; 4] = 0;
impl fn f(i : u32 in 0 ..< 4, s : string max 8, k : string max 16) -> u32
    effects {{ reads NAMEN, writes NAMEN }}
    costs <= 64 ops
{{
{rumpf}
    return 0;
}}
}}"
    )
}

#[test]
fn r4_lenof_zelle() {
    // FINDING: sound (length in place: N581, slot and array alike).
    faellt(
        "module r4a {
table Namen count 4 { slot { name : string max 8, } }
lock K protects { Namen } rank 0 held <= 100 ops;
static mut NAMEN : [string max 8; 4] = 0;
impl fn f(t : ptr<normal, rw> Namen, i : index into Namen, j : u32 in 0 ..< 4) -> u32
    requires Held(K)
    effects { reads t.slots, locks K, reads NAMEN }
    costs <= 64 ops
{
    let a = lenof(t.slots[i].name);
    let b = lenof(NAMEN[j]);
    return a + b;
}
}",
        "N581",
    );
}

#[test]
fn r4_vergleich_zelle() {
    // FINDING: sound (comparison in place: N581, both shapes).
    faellt(
        &r4_tabelle("    if t.slots[i].name == s { return 1; }"),
        "N581",
    );
    faellt(&r4_feld("    if NAMEN[i] == s { return 1; }"), "N581");
}

#[test]
fn r4_concat_zelle() {
    // FINDING: sound (concat in place: N581, both shapes).
    faellt(
        &r4_tabelle("    let m = t.slots[i].name + s;"),
        "N581",
    );
    faellt(&r4_feld("    let m = NAMEN[i] + s;"), "N581");
}

#[test]
fn r4_argument_zelle() {
    // FINDING: sound (cell into a string parameter: N581 -- only a local
    // travels; both shapes).
    faellt(
        "module r4b {
table Namen count 4 { slot { name : string max 8, } }
lock K protects { Namen } rank 0 held <= 100 ops;
static mut NAMEN : [string max 8; 4] = 0;
impl fn nimm(s : string max 8) -> u32 effects { pure } costs <= 8 ops { return lenof(s); }
impl fn f(t : ptr<normal, rw> Namen, i : index into Namen, j : u32 in 0 ..< 4) -> u32
    requires Held(K)
    effects { reads t.slots, locks K, reads NAMEN }
    costs <= 64 ops
{
    return nimm(t.slots[i].name) + nimm(NAMEN[j]);
}
}",
        "N581",
    );
}

#[test]
fn r4_rueckgabe_zelle() {
    // FINDING: sound (cell as return value: N581, both shapes).
    faellt(
        "module r4c {
table Namen count 4 { slot { name : string max 8, } }
lock K protects { Namen } rank 0 held <= 100 ops;
static mut NAMEN : [string max 8; 4] = 0;
impl fn f(t : ptr<normal, rw> Namen, i : index into Namen, j : u32 in 0 ..< 4) -> string max 8
    requires Held(K)
    effects { reads t.slots, locks K, reads NAMEN }
    costs <= 64 ops
{
    return t.slots[i].name;
}
}",
        "N581",
    );
    faellt(
        "module r4d {
static mut NAMEN : [string max 8; 4] = 0;
impl fn g(j : u32 in 0 ..< 4) -> string max 8
    effects { reads NAMEN }
    costs <= 64 ops
{
    return NAMEN[j];
}
}",
        "N581",
    );
}

#[test]
fn r4_fakten_leben_am_lokal() {
    // FINDING: sound (facts follow the copied-out local across a rewrite of
    // the cell: clean -- the discipline's core claim).
    sauber(&r4_feld(
        "    let a : string max 8 = NAMEN[i];\n    NAMEN[i] = \"hi\";\n    let m = lenof(a);",
    ));
    sauber(
        "module r4m {
table Namen count 4 { slot { name : string max 8, } }
lock K protects { Namen } rank 0 held <= 100 ops;
impl fn f(t : ptr<normal, rw> Namen, i : index into Namen) -> u32
    requires Held(K)
    effects { reads t.slots, writes t.slots, locks K }
    costs <= 64 ops
{
    let a : string max 8 = t.slots[i].name;
    t.slots[i].name = \"hi\";
    return lenof(a);
}
}",
    );
}

#[test]
fn r4_locks_zelle() {
    // FINDING: sound (locks blocks are walked like any block: N581).
    faellt(
        "module r4e {
table Namen count 4 { slot { name : string max 8, } }
lock K protects { Namen } rank 0 held <= 100 ops;
impl fn f(t : ptr<normal, rw> Namen, i : index into Namen) -> u32
    requires Held(K)
    effects { reads t.slots, writes t.slots, locks K }
    costs <= 64 ops
{
    locks K {
        let m = lenof(t.slots[i].name);
        return m;
    }
}
}",
        "N581",
    );
}

#[test]
fn r4_lokal_wie_feld() {
    // FINDING: sound (the place resolves to the cell, the same-named
    // local is untouched: clean).
    sauber(
        "module r4g {
table Namen count 4 { slot { name : string max 8, } }
lock K protects { Namen } rank 0 held <= 100 ops;
impl fn f(t : ptr<normal, rw> Namen, i : index into Namen) -> u32
    requires Held(K)
    effects { reads t.slots, locks K }
    costs <= 64 ops
{
    let name : u32 = 1;
    let a : string max 8 = t.slots[i].name;
    return lenof(a) + name;
}
}",
    );
}

#[test]
fn r4_parameter_wie_statik() {
    // FINDING: sound (the indexed use resolves to the static in both
    // passes -- M101 silence proves M1 sees the cell too -- while the bare
    // name resolves to the parameter; each position is consistent).
    sauber(
        "module r4h {
static mut NAMEN : [string max 8; 4] = 0;
impl fn f(NAMEN : u32, i : u32 in 0 ..< 4) -> u32
    effects { reads NAMEN }
    costs <= 64 ops
{
    let a : string max 8 = NAMEN[i];
    return lenof(a);
}
}",
    );
}

#[test]
fn r4_parameter_blosser_name() {
    // FINDING: sound (twin: the bare name resolves to the parameter).
    sauber(
        "module r4o {
static mut NAMEN : [string max 8; 4] = 0;
impl fn f(NAMEN : u32, i : u32 in 0 ..< 4) -> u32
    effects { reads NAMEN }
    costs <= 64 ops
{
    return NAMEN;
}
}",
    );
}

#[test]
fn r4_selbstkopie_zelle() {
    // FINDING: sound (cell onto itself: N581 -- the read is already in place).
    faellt(&r4_feld("    NAMEN[i] = NAMEN[i];"), "N581");
    faellt(
        &r4_tabelle("    t.slots[i].name = t.slots[i].name;"),
        "N581",
    );
}

#[test]
fn r4_let_else_zelle() {
    // FINDING: FIXED by the lead (was ACCEPTS-UNSOUND, now N581) (door: a cell flows into a let-else binding
    // with no N581 and no fit check; the sharp instance is below).
    faellt(&r4_feld(
        "    let a = NAMEN[i] else (e) { return 1; }\n    return 0;",
    ), "N581");
}

#[test]
fn r4_let_else_zelle_nutzung() {
    // FINDING: FIXED by the lead (was ACCEPTS-UNSOUND, now N581) (sharp: `string max 4` annotation over a max-8
    // cell, returned as max 4, zero errors -- the N455 copy rule is bypassed
    // and a value past its type flows on; unannotated use is equally silent).
    faellt(&r4_feld(
        "    let a = NAMEN[i] else (e) { return 1; }\n    return lenof(a);",
    ), "N581");
    faellt(
        "module r4n {
static mut NAMEN : [string max 8; 4] = 0;
impl fn g(i : u32 in 0 ..< 4) -> string max 8
    effects { reads NAMEN }
    costs <= 64 ops
{
    let a = NAMEN[i] else (e) { return \"leer\"; }
    return a;
}
}",
        "N581",
    );
    faellt(
        "module r4p {
static mut NAMEN : [string max 8; 4] = 0;
impl fn g(i : u32 in 0 ..< 4) -> string max 4
    effects { reads NAMEN }
    costs <= 64 ops
{
    let a : string max 4 = NAMEN[i] else (e) { return \"leer\"; }
    return a;
}
}",
        "N581",
    );
}

#[test]
fn r4_zwei_tabellen_gleiches_feld() {
    // FINDING: sound (each table resolves by its own name: clean).
    sauber(
        "module r4i {
table A count 4 { slot { n : u32, } }
table B count 4 { slot { n : string max 8, } }
lock K protects { A, B } rank 0 held <= 100 ops;
impl fn f(a : ptr<normal, rw> A, b : ptr<normal, rw> B, i : index into A, j : index into B) -> u32
    requires Held(K)
    effects { reads a.slots, reads b.slots, locks K }
    costs <= 64 ops
{
    let x : u32 = a.slots[i].n;
    let s : string max 8 = b.slots[j].n;
    return x + lenof(s);
}
}",
    );
}

#[test]
fn r4_index_mit_zelle() {
    // FINDING: sound (string where an index stands: N455).
    faellt(
        "module r4j {
static mut NAMEN : [string max 8; 4] = 0;
static mut A : [u32 in 0 .. 255; 8] = 0;
impl fn f(i : u32 in 0 ..< 4) -> u32
    effects { reads NAMEN, reads A }
    costs <= 64 ops
{
    return A[NAMEN[i]];
}
}",
        "N455",
    );
}

#[test]
fn r4_requires_zelle() {
    // FINDING: sound (predicates walk expressions too: N581).
    faellt(
        "module r4k {
static mut NAMEN : [string max 8; 4] = 0;
impl fn f(i : u32 in 0 ..< 4) -> u32
    requires lenof(NAMEN[i]) > 3
    effects { reads NAMEN }
    costs <= 64 ops
{
    return 0;
}
}",
        "N581",
    );
}

#[test]
fn r4_vergleich_lokal_sauber() {
    // FINDING: sound (control: copied-out local compares clean).
    sauber(&r4_feld(
        "    let a : string max 8 = NAMEN[i];\n    if a == s { return 1; }",
    ));
}

// __APPEND_END__
