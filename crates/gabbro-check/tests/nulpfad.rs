//! **`N507` -- the NUL terminator where the program builds the buffer** (lane 262,
//! OFFEN O23).
//!
//! Poison and positive twins for the decided shapes: a proved `buf[L-1] = 0` store, an
//! untouched zeroed buffer, a forwarded parameter pair under the caller's own clause --
//! and the two refusals (an unproved buffer, a forwarding without the clause).

use gabbro_syntax::diag::Stufe;

const GRUND: &str = "reason OpenError {
    NotFound = 2 \"no entry under that path\"
    exhaustive
}
assume linux_open_contract
    \"Open keeps its contract on this machine.\"
    falsifier sonde_open;
const MAXLEN : u64 = 1024;
spec fn path_nul_terminated(path : ptr<normal, r> u8, pathlen : u64) -> bool
    effects { pure }
    = pathlen >= 1 && path[pathlen - 1] == 0;";

fn tor(requires: &str) -> String {
    format!(
        "syscall gate_open(path : ptr<normal, r> u8, pathlen : u64, flags : u64) -> u64 or OpenError
    abi linux arch x86_64 number 2
    regs in {{ rdi = path, rsi = flags, r10 = pathlen }}
    regs out {{ rax }}
    clobbers {{ rcx, r11 }}
    errors {{ ENOENT => NotFound }}
    requires {requires}
    ensures result <= 4294967295
    effects {{ reads path }}
    costs <= 40 ops
    assume linux_open_contract falsifier sonde_open;"
    )
}

fn codes(teile: &[&str]) -> Vec<String> {
    let quelle = format!("module t {{\n{GRUND}\n{}\n}}\n", teile.join("\n"));
    let (baum, mut absagen) = gabbro_syntax::lies("nulpfad", &quelle);
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

// ---- N507: the unproved buffer -----------------------------------------------------

#[test]
fn n507_puffer_ohne_terminator() {
    // A concrete buffer with no `0` store anywhere: the gate reads past the proof.
    faellt(
        &[
            &tor("pathlen <= MAXLEN, pathlen <= lenof(path), path_nul_terminated(path, pathlen)"),
            "static mut PFAD : [u8; 16] = 0;
impl fn aufruf() -> u64 or OpenError
    effects { reads PFAD }
    costs <= 100 ops
{
    PFAD[4] = 65;
    let n = gate_open(PFAD, 5, 0) else (e) { return e; }
    return n;
}",
        ],
        "N507",
    );
}

#[test]
fn n507_falscher_index_zaehlt_nicht() {
    // The `0` stands at index 2, the gate reads index 4: proved nowhere.
    faellt(
        &[
            &tor("pathlen <= MAXLEN, pathlen <= lenof(path), path_nul_terminated(path, pathlen)"),
            "static mut PFAD : [u8; 16] = 0;
impl fn aufruf() -> u64 or OpenError
    effects { reads PFAD, writes PFAD }
    costs <= 100 ops
{
    PFAD[2] = 0;
    PFAD[4] = 65;
    let n = gate_open(PFAD, 5, 0) else (e) { return e; }
    return n;
}",
        ],
        "N507",
    );
}

#[test]
fn n507_spaeteres_schreiben_loescht_den_beweis() {
    // `PFAD[4] = 0` stands, but a later unknown write clears it again.
    faellt(
        &[
            &tor("pathlen <= MAXLEN, pathlen <= lenof(path), path_nul_terminated(path, pathlen)"),
            "static mut PFAD : [u8; 16] = 0;
impl fn aufruf(k : u64) -> u64 or OpenError
    effects { reads PFAD, writes PFAD }
    costs <= 100 ops
{
    PFAD[4] = 0;
    PFAD[k] = 65;
    let n = gate_open(PFAD, 5, 0) else (e) { return e; }
    return n;
}",
        ],
        "N507",
    );
}

#[test]
fn n507_zweig_speichert_keinen_beweis() {
    // The store may not run: a branch never proves, though it still kills. (The
    // buffer is filled first: over a zeroed buffer the cell would read `0` on every
    // path with or without the branch.)
    faellt(
        &[
            &tor("pathlen <= MAXLEN, pathlen <= lenof(path), path_nul_terminated(path, pathlen)"),
            "static mut PFAD : [u8; 16] = 0;
impl fn aufruf(c : bool) -> u64 or OpenError
    effects { reads PFAD, writes PFAD }
    costs <= 100 ops
{
    PFAD[4] = 65;
    if c {
        PFAD[4] = 0;
    }
    let n = gate_open(PFAD, 5, 0) else (e) { return e; }
    return n;
}",
        ],
        "N507",
    );
}

// ---- N507: the forwarding chain ----------------------------------------------------

#[test]
fn n507_weiterreichen_ohne_klausel() {
    // The wrapper forwards `path`/`pathlen` and drops the obligation on the floor.
    faellt(
        &[
            &tor("pathlen <= MAXLEN, pathlen <= lenof(path), path_nul_terminated(path, pathlen)"),
            "impl fn oeffnen(path : ptr<normal, r> u8, pathlen : u64, flags : u64) -> u64 or OpenError
    requires pathlen <= MAXLEN, pathlen <= lenof(path)
    effects { reads path }
    costs <= 100 ops
{
    let n = gate_open(path, pathlen, flags) else (e) { return e; }
    return n;
}",
        ],
        "N507",
    );
}

#[test]
fn n507_weiterreichen_mit_klausel_ist_sauber() {
    // The obligation travels up: `beispiele/149`'s `oeffnen` shape.
    sauber(&[
        &tor("pathlen <= MAXLEN, pathlen <= lenof(path), path_nul_terminated(path, pathlen)"),
        "impl fn oeffnen(path : ptr<normal, r> u8, pathlen : u64, flags : u64) -> u64 or OpenError
    requires pathlen <= MAXLEN, pathlen <= lenof(path), path_nul_terminated(path, pathlen)
    effects { reads path }
    costs <= 100 ops
{
    let n = gate_open(path, pathlen, flags) else (e) { return e; }
    return n;
}",
    ]);
}

// ---- N507: the proved shapes --------------------------------------------------------

#[test]
fn n507_bewiesener_speicher_ist_sauber() {
    // `PFAD[4] = 0` dominates the call, nothing clears it: the gate reads a NUL.
    sauber(&[
        &tor("pathlen <= MAXLEN, pathlen <= lenof(path), path_nul_terminated(path, pathlen)"),
        "static mut PFAD : [u8; 16] = 0;
impl fn aufruf() -> u64 or OpenError
    effects { reads PFAD, writes PFAD }
    costs <= 100 ops
{
    PFAD[4] = 0;
    let n = gate_open(PFAD, 5, 0) else (e) { return e; }
    return n;
}",
    ]);
}

#[test]
fn n507_unberuehrter_nullpuffer_ist_sauber() {
    // A zero-initialised buffer with no store since: every index reads `0`, so any
    // length in range is proved -- here a runtime one.
    sauber(&[
        &tor("pathlen <= MAXLEN, pathlen <= lenof(path), path_nul_terminated(path, pathlen)"),
        "static mut PFAD : [u8; 16] = 0;
impl fn aufruf(n : u64 in 1 .. 16) -> u64 or OpenError
    effects { reads PFAD }
    costs <= 100 ops
{
    let m = gate_open(PFAD, n, 0) else (e) { return e; }
    return m;
}",
    ]);
}

#[test]
fn n507_kopie_traegt_den_beweis_weiter() {
    // `let ab = PFAD;` copies the bytes, and the proof rides along.
    sauber(&[
        &tor("pathlen <= MAXLEN, pathlen <= lenof(path), path_nul_terminated(path, pathlen)"),
        "static mut PFAD : [u8; 16] = 0;
impl fn aufruf() -> u64 or OpenError
    effects { reads PFAD, writes PFAD }
    costs <= 100 ops
{
    PFAD[4] = 0;
    let ab : [u8; 16] = PFAD;
    let n = gate_open(ab, 5, 0) else (e) { return e; }
    return n;
}",
    ]);
}

// ---- N507: what keeps the named obligation ------------------------------------------

#[test]
fn n507_ungesehener_zeiger_bleibt_still() {
    // A lone parameter is no buffer this pass sees built: the `V` row stays, and no
    // new code falls beside it. (The callee carries no length bound, so `N463` is
    // silent too; the obligation is counted, not decided.)
    sauber(&[
        "impl fn nimm(path : ptr<normal, r> u8, pathlen : u64) -> u64
    requires path_nul_terminated(path, pathlen)
    effects { reads path }
    costs <= 100 ops
{
    return 7;
}",
        "impl fn aufruf(pfad : ptr<normal, r> u8) -> u64
    effects { reads pfad }
    costs <= 300 ops
{
    let n = nimm(pfad, 5);
    return n;
}",
    ]);
}
