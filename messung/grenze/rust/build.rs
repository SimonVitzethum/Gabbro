//! Baut die C-Seite -- die erzeugte Einheit samt Schale -- und bindet sie statisch dazu.
//!
//! **Ohne `cc`-Kiste**, von Hand ueber `Command`: eine Abhaengigkeit im Pruefstand waere
//! genau das, was der Erzeuger sich selbst verbietet.
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let aus = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let hier = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let opt = std::env::var("GRENZE_COPT").unwrap_or_else(|_| "-O2".into());

    let o = aus.join("schale.o");
    let st = Command::new("cc")
        .args(["-std=c11", &opt, "-Wall", "-Wextra", "-Werror", "-pthread", "-c"])
        .arg(hier.join("schale.c"))
        .arg("-o").arg(&o)
        .status().expect("cc laeuft");
    assert!(st.success(), "cc ist gefallen");

    let a = aus.join("libgrenze.a");
    let _ = std::fs::remove_file(&a);
    let st = Command::new("ar").arg("rcs").arg(&a).arg(&o).status().expect("ar laeuft");
    assert!(st.success(), "ar ist gefallen");

    println!("cargo:rustc-link-search=native={}", aus.display());
    println!("cargo:rustc-link-lib=static=grenze");
    println!("cargo:rerun-if-changed={}", hier.join("schale.c").display());
    println!("cargo:rerun-if-changed={}", hier.join("grenze.c").display());
    println!("cargo:rerun-if-env-changed=GRENZE_COPT");
}
