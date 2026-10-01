//! **`N463`/`N464` -- the transfer bound `x <= lenof(p)`** (fix lane F5, review G04 F3,
//! 2026-09-22).
//!
//! Poison and positive twins for both rules: the declaration demand at a `syscall` byte
//! buffer (`N464`) and the decided bound at every call (`N463`) -- an array where it decays,
//! a forwarded pointer under the caller's own clause.

use gabbro_syntax::diag::Stufe;

const GRUND: &str = "reason ReadError {
    BadFd = 9 \"the file descriptor is not open\"
    exhaustive
}
assume linux_read_contract
    \"Read keeps its contract on this machine.\"
    falsifier sonde_read;
static mut EIMER : [u8; 64] = 0;
static mut WORTE : [u32; 64] = 0;
const CAP : u64 = 64;";

fn gate(requires: &str, pointee: &str) -> String {
    format!(
        "syscall gate_read(fd : u32, buf : ptr<normal, w> {pointee}, len : u64) -> u64 or ReadError
    abi linux arch x86_64 number 0
    regs in {{ rdi = fd, rsi = buf, rdx = len }}
    regs out {{ rax }}
    clobbers {{ rcx, r11 }}
    errors {{ EBADF => BadFd }}
    requires {requires}
    ensures result <= len
    effects {{ writes buf }}
    costs <= 40 ops
    assume linux_read_contract falsifier sonde_read;"
    )
}

const LIES: &str = "impl fn lies(fd : u32, buf : ptr<normal, w> u8, len : u64) -> u64 or ReadError
    requires len <= lenof(buf)
    effects { writes buf }
{
    let n = gate_read(fd, buf, len) else (e) { return e; }
    return n;
}";

fn codes(teile: &[&str]) -> Vec<String> {
    let quelle = format!("module t {{\n{GRUND}\n{}\n}}\n", teile.join("\n"));
    let (baum, mut absagen) = gabbro_syntax::lies("rahmenlaenge", &quelle);
    let _ = gabbro_check::pruefe(&baum, &mut absagen);
    absagen
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

fn faellt(teile: &[&str], code: &str) {
    let c = codes(teile);
    assert!(c.iter().any(|x| x == code), "expected {code}, fell with {c:?}");
}

fn sauber(teile: &[&str]) {
    let c = codes(teile);
    assert!(c.is_empty(), "the positive twin must check clean, fell with {c:?}");
}

fn rufer(ruf: &str) -> String {
    format!(
        "impl fn zaehle(fd : u32) -> u64 or ReadError
    effects {{ writes EIMER }}
{{
    let n = {ruf} else (e) {{ return e; }}
    return n;
}}"
    )
}

// ---- N464: the declaration ----------------------------------------------------------

#[test]
fn n464_puffer_ohne_klausel() {
    faellt(&[&gate("len <= 1024", "u8")], "N464");
}

#[test]
fn n464_puffer_mit_klausel_ist_sauber() {
    sauber(&[&gate("len <= 1024, len <= lenof(buf)", "u8")]);
}

#[test]
fn n464_wortpuffer() {
    faellt(&[&gate("len <= lenof(buf)", "u32")], "N464");
}

#[test]
fn n464_klausel_ueber_den_falschen_zeiger_zaehlt_nicht() {
    // `lenof(fd)` names no buffer: `buf` is still unbounded.
    faellt(&[&gate("len <= lenof(fd)", "u8")], "N464");
}

// ---- N463: an array where it decays -------------------------------------------------

#[test]
fn n463_konstante_im_feld_ist_sauber() {
    sauber(&[&gate("len <= lenof(buf)", "u8"), LIES, &rufer("lies(fd, EIMER, CAP)")]);
}

#[test]
fn n463_literal_im_feld_ist_sauber() {
    sauber(&[&gate("len <= lenof(buf)", "u8"), &rufer("gate_read(fd, EIMER, 17)")]);
}

#[test]
fn n463_literal_ueber_dem_feld() {
    faellt(&[&gate("len <= lenof(buf)", "u8"), LIES, &rufer("lies(fd, EIMER, 1024)")], "N463");
}

#[test]
fn n463_strikt_an_der_grenze() {
    // `len < lenof(buf)` over 64 elements admits 63, not 64.
    faellt(&[&gate("len < lenof(buf)", "u8"), &rufer("gate_read(fd, EIMER, 64)")], "N463");
    sauber(&[&gate("len < lenof(buf)", "u8"), &rufer("gate_read(fd, EIMER, 63)")]);
}

#[test]
fn n463_voller_bereich_ist_keine_schranke() {
    faellt(
        &[
            &gate("len <= lenof(buf)", "u8"),
            "impl fn zaehle(fd : u32, k : u64) -> u64 or ReadError
    effects { writes EIMER }
{
    let n = gate_read(fd, EIMER, k) else (e) { return e; }
    return n;
}",
        ],
        "N463",
    );
}

// ---- N463: the forwarding chain -----------------------------------------------------

#[test]
fn n463_weiterreichen_ohne_klausel() {
    faellt(
        &[
            &gate("len <= lenof(buf)", "u8"),
            "impl fn lies(fd : u32, buf : ptr<normal, w> u8, len : u64) -> u64 or ReadError
    effects { writes buf }
{
    let n = gate_read(fd, buf, len) else (e) { return e; }
    return n;
}",
        ],
        "N463",
    );
}

#[test]
fn n463_weiterreichen_mit_klausel_ist_sauber() {
    sauber(&[&gate("len <= lenof(buf)", "u8"), LIES]);
}

#[test]
fn n463_weiterreichen_vertauscht() {
    // The caller's clause bounds `len` by `buf`; forwarding a different length parameter
    // leaves the gate's bound unanswered.
    faellt(
        &[
            &gate("len <= lenof(buf)", "u8"),
            "impl fn lies(fd : u32, buf : ptr<normal, w> u8, len : u64, k : u64) -> u64 or ReadError
    requires len <= lenof(buf)
    effects { writes buf }
{
    let n = gate_read(fd, buf, k) else (e) { return e; }
    return n;
}",
        ],
        "N463",
    );
}

#[test]
fn n463_geschatteter_parameter_zaehlt_nicht() {
    // A nested binder reusing the parameter's name drops it out (no scopes, fail-closed).
    faellt(
        &[
            &gate("len <= lenof(buf)", "u8"),
            "impl fn lies(fd : u32, buf : ptr<normal, w> u8, len : u64) -> u64 or ReadError
    requires len <= lenof(buf)
    effects { writes buf }
{
    if fd > 3 {
        let len : u64 = 9;
        let m = gate_read(fd, buf, len) else (e) { return e; }
        return m;
    }
    let n = gate_read(fd, buf, len) else (e) { return e; }
    return n;
}",
        ],
        "N463",
    );
}

#[test]
fn n463_feld_aus_breiteren_elementen() {
    // `[u32; 64]` decays to `ptr u8` (shape only), and 64 words are no bound on 64 counted
    // bytes' worth of `lenof(buf)` elements of another type.
    faellt(&[&gate("len <= lenof(buf)", "u8"), &rufer("gate_read(fd, WORTE, 4)")], "N463");
}

// ---- N506: the declaration at an `extern fn` (lane 262, OFFEN O23) --------------------

fn fremd(requires: &str, pointee: &str) -> String {
    format!(
        "extern fn write(fd : i32, p : ptr<normal, r> {pointee}, n : u64) -> i64
    requires {requires}
    effects {{ reads p }}
    costs <= 16 ops;"
    )
}

#[test]
fn n506_extern_puffer_ohne_klausel() {
    faellt(&[&fremd("n <= 64", "u8")], "N506");
}

#[test]
fn n506_extern_puffer_mit_klausel_ist_sauber() {
    sauber(&[&fremd("n <= 64, n <= lenof(p)", "u8")]);
}

#[test]
fn n506_extern_wortpuffer() {
    faellt(&[&fremd("n <= lenof(p)", "u32")], "N506");
}

#[test]
fn n506_extern_klausel_ueber_den_falschen_zeiger_zaehlt_nicht() {
    // `lenof(fd)` names no buffer: `p` is still unbounded.
    faellt(&[&fremd("n <= lenof(fd)", "u8")], "N506");
}

#[test]
fn n506_extern_konstante_klausel_bindet_ein_festes_objekt() {
    // C-free lane, 2026-09-30 (`N464`'s twin): a lock blob of fixed size beside an integer
    // parameter is bound by a CONSTANT clause; without any clause it still falls, and a
    // clause over another pointer does not count.
    let blob = |req: &str| {
        format!(
            "extern fn gib(s : ptr<normal, rw> u8, flaggen : u64)
    {req}
    effects {{ writes s }}
    costs <= 16 ops;"
        )
    };
    sauber(&[&blob("requires 256 <= lenof(s)")]);
    faellt(&[&blob("requires flaggen <= 64")], "N506");
    faellt(&[&blob("requires 0 <= lenof(s)")], "N506");
}

#[test]
fn n506_konstante_klausel_haelt_den_rufer_n463() {
    // The call half: a 64-byte array handed to a 256-byte clause falls at `N463`.
    faellt(
        &[
            "extern fn gib(s : ptr<normal, rw> u8, flaggen : u64)
    requires 256 <= lenof(s)
    effects { writes s }
    costs <= 16 ops;",
            "static mut KLEIN : [u8; 64] = 0;
pub fn main() -> i32 in 0 .. 1
    effects { writes KLEIN }
    costs <= 200 ops
{
    gib(KLEIN, 0);
    return 0;
}",
        ],
        "N463",
    );
}

#[test]
fn n506_extern_ohne_laengenparameter_bleibt_still() {
    // One object, not a transfer: no integer parameter beside the pointer, so
    // no length the caller could set past it and no clause that could tie one
    // (`beispiele/22`'s `melde_roh` shape).
    sauber(&[
        "extern fn melde(text : ptr<code, r> u8) -> u32 effects { reads text } costs <= 8 ops;",
    ]);
}

#[test]
fn n506_extern_ruf_ueber_dem_feld_faellt_n463() {
    // The call-site half already held for every callee: the clause an `extern fn`
    // writes is decided where its array decays, by `N463`, not `N506`.
    faellt(
        &[
            &fremd("n <= lenof(p)", "u8"),
            "static mut PUFFER : [u8; 64] = 0;
pub fn main() -> i32 in 0 .. 1
    effects { reads PUFFER, writes ausgabe }
    costs <= 200 ops
{
    write(1, PUFFER, 1024);
    return 0;
}",
        ],
        "N463",
    );
}

#[test]
fn n506_extern_ruf_im_feld_ist_sauber() {
    sauber(&[
        &fremd("n <= lenof(p)", "u8"),
        "pub static mut PUFFER : [u8; 64] = 0;
pub static mut LAENGE : u32 in 0 .. 64 = 0;
pub fn main() -> i32 in 0 .. 1
    effects { reads PUFFER, writes PUFFER, reads LAENGE, writes LAENGE, writes ausgabe }
    costs <= 200 ops
{
    write(1, PUFFER, LAENGE);
    return 0;
}",
    ]);
}

// ---- N573: the variadic marker `...` (C-free lane, C2) ---------------------------------

fn variadisch(kopf: &str, nach: &str) -> String {
    format!(
        "{kopf} fn druck(fmt : ptr<normal, r> u8, ..., {nach}) -> i32
    requires 16 <= lenof(fmt)
    effects {{ reads fmt }}
    costs <= 64 ops;"
    )
}

#[test]
fn n573_extern_mit_zahlen_und_zeigern_ist_sauber() {
    // `p` is a byte pointer beside integers, so `N506` asks for its clause as everywhere.
    sauber(&["extern fn druck(fmt : ptr<normal, r> u8, ..., a : u64, b : i32, p : ptr<normal, r> u8) -> i32
    requires 16 <= lenof(fmt), 1 <= lenof(p)
    effects { reads fmt, reads p }
    costs <= 64 ops;"]);
}

#[test]
fn n573_marker_ohne_folgenden_parameter_ist_sauber() {
    sauber(&["extern fn druck(fmt : ptr<normal, r> u8, ...) -> i32
    requires 16 <= lenof(fmt)
    effects { reads fmt }
    costs <= 64 ops;"]);
}

#[test]
fn n573_marker_an_einer_gabbro_funktion() {
    faellt(
        &["pub fn summe(a : u64 in 0 .. 100, ..., b : u64 in 0 .. 100) -> u64 in 0 .. 200
    effects { pure }
    costs <= 8 ops
{
    return a + b;
}"],
        "N573",
    );
}

#[test]
fn n573_verbund_hinter_dem_marker() {
    faellt(
        &["type Paar = { a : u64, b : u64, };", &variadisch("extern", "p : Paar")],
        "N573",
    );
}

#[test]
fn n573_marker_mit_fehlerkanal() {
    faellt(
        &[
            "reason R { Nein = 1 \"no\" exhaustive }",
            "extern fn druck(fmt : ptr<normal, r> u8, ..., a : u64) -> i32 or R
    requires 16 <= lenof(fmt)
    effects { reads fmt }
    costs <= 64 ops;",
        ],
        "N573",
    );
}

// ---- N574: a foreign body takes no code (C-free lane, C2, OFFEN O39) -------------------

#[test]
fn n574_extern_mit_funktionszeiger() {
    faellt(
        &["extern fn starte(f : fn(d : u64) -> u32 in 0 .. 1 effects { pure } costs <= 8 ops, d : u64) -> u32
    effects { pure }
    costs <= 64 ops;"],
        "N574",
    );
}

#[test]
fn n574_verbund_mit_funktionszeiger_hinter_einem_zeiger() {
    faellt(
        &[
            "type Ops = { weiter : fn(t : u32) -> u32 in 0 .. 1 effects { pure } costs <= 8 ops, };",
            "extern fn plane(d : ptr<normal, r> Ops, t : u32) -> u32 effects { reads d } costs <= 16 ops;",
        ],
        "N574",
    );
}

#[test]
fn n574_gabbro_funktion_mit_funktionszeiger_ist_sauber() {
    // The positive twin: a Gabbro body that takes a function pointer is checked like any
    // indirect call (the type carries the contract) -- the rule is about FOREIGN code only.
    // (This scaffold draws other codes about the indirect call; `N574` is not among them.)
    let c = codes(&["fn rufe(f : fn(t : u32) -> u32 in 0 .. 1 effects { pure } costs <= 8 ops) -> u32 in 0 .. 1
    effects { pure }
    costs <= 16 ops
{
    let r = f(1);
    return r;
}"]);
    assert!(!c.iter().any(|x| x == "N574"), "a Gabbro body may take code: {c:?}");
}

#[test]
fn n574_extern_ohne_code_ist_sauber() {
    sauber(&["type Paar = { a : u64, b : u64, };",
        "extern fn nimm(p : ptr<normal, r> Paar) -> u64 effects { reads p } costs <= 8 ops;"]);
}
