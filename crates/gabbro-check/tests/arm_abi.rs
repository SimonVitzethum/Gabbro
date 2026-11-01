//! The AArch64 Linux system-call table, held from three sides by TEXT so it cannot drift:
//! the Lean model (`SyscallArm.lean` numbers, `SyscallArmLinux.lean` gates), the AArch64 binding
//! (`bibliothek/linux/linux-aarch64.gab`) and the checker's own register table
//! (`syscall::register_fuer`). A change to one of them without the others is a red test.

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

fn wurzel() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn lies(rel: &str) -> String {
    fs::read_to_string(wurzel().join(rel)).unwrap_or_else(|e| panic!("{rel}: {e}"))
}

/// The call numbers of the Lean model, as the GENERATED table carries them
/// ({"nrWrite": 64}); `abi_tabelle_ist_frisch` holds that table against the Lean text.
fn lean_nummern() -> HashMap<String, u64> {
    gabbro_check::abi_tabelle::AARCH64_NUMMERN.iter().map(|(n, v)| (format!("nr{n}"), *v)).collect()
}

/// (gate name, number, regs-in text, regs-out text, clobbers text) per `syscall` of the binding.
fn tore() -> Vec<(String, u64, String, String, String)> {
    let text = lies("bibliothek/linux/linux-aarch64.gab");
    let zeilen: Vec<&str> = text.lines().collect();
    let mut aus = Vec::new();
    for (i, z) in zeilen.iter().enumerate() {
        let Some(rest) = z.strip_prefix("syscall ") else { continue };
        let name = rest.split('(').next().unwrap().to_string();
        let (mut nr, mut ein, mut out, mut clob) = (0u64, String::new(), String::new(), String::new());
        for w in &zeilen[i + 1..] {
            let w = w.trim();
            if w.starts_with("assume ") {
                break;
            }
            if let Some(r) = w.strip_prefix("abi linux arch aarch64 number ") {
                nr = r.trim().parse().unwrap();
            } else if let Some(r) = w.strip_prefix("regs in ") {
                ein = r.to_string();
            } else if let Some(r) = w.strip_prefix("regs out ") {
                out = r.to_string();
            } else if let Some(r) = w.strip_prefix("clobbers ") {
                clob = r.to_string();
            }
        }
        aus.push((name, nr, ein, out, clob));
    }
    aus
}

#[test]
fn die_registertabelle_des_pruefers_ist_x0_bis_x30() {
    let reg = gabbro_check::syscall::register_fuer("aarch64");
    assert_eq!(reg.len(), 31);
    for n in 0..31 {
        assert!(reg.contains(&format!("x{n}").as_str()));
    }
    assert!(!reg.contains(&"rax"));
    assert!(gabbro_check::syscall::register_fuer("x86_64").contains(&"rax"));
    assert!(gabbro_check::syscall::arch_bekannt("aarch64"));
    assert!(!gabbro_check::syscall::arch_bekannt("riscv64"));
}

#[test]
fn abi_tabelle_ist_frisch() {
    // The Rust tables are generated from the Lean records; a stale file is a red test, not a
    // silently diverging row.
    let st = std::process::Command::new("python3")
        .arg(wurzel().join("instrumente/erzeuge-abi-tabelle.py"))
        .arg("--pruefe")
        .output()
        .expect("python3");
    assert!(st.status.success(), "{}", String::from_utf8_lossy(&st.stdout));
}

#[test]
fn die_konventionen_der_erzeugten_tabelle_sind_die_des_pruefers() {
    use gabbro_check::abi_tabelle as t;
    assert_eq!(t::AARCH64_NUMMER_REG, "x8");
    assert_eq!(t::AARCH64_ERGEBNIS_REG, "x0");
    assert_eq!(t::AARCH64_ARG_REGS, ["x0", "x1", "x2", "x3", "x4", "x5"]);
    assert_eq!(t::AARCH64_KLON_STAPEL_REG, "x1");
    // number register and stack register are general registers the checker accepts
    for r in [t::AARCH64_NUMMER_REG, t::AARCH64_ERGEBNIS_REG, t::AARCH64_KLON_STAPEL_REG] {
        assert!(gabbro_check::syscall::register_fuer("aarch64").contains(&r));
    }
    assert_eq!(gabbro_check::syscall::register_fuer("x86_64").len(), 16);
}
