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
