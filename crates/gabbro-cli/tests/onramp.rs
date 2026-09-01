//! **`gabbro new` writes a skeleton that RUNS -- and this file is the only reason to believe
//! it.**
//!
//! *A skeleton that does not run is a seventh paper cut.* The eight attempts for "add two
//! numbers" were eight because every refusal was correct and none of them taught the shape;
//! a `new` command whose output does not build would put a ninth refusal in front of the
//! first minute instead of behind it.
//!
//! **Nothing here is asserted from reading the generator.** The command runs into a fresh
//! directory, the checker runs over what it wrote, the build runs, the binary runs, and the
//! bytes on stdout are compared. Four tools, one chain, no step assumed.
//!
//! > **And the reverse direction is held too:** `new` over an existing file writes NOTHING,
//! > and the check is against BOTH names before the first write. A run that overwrote one
//! > file and refused on the other would be a silent loss with an exit code of 2 over it.

use std::path::{Path, PathBuf};
use std::process::Command;

/// A directory of this run's own. **`std` has no `mkdtemp`, and the workspace has no
/// dependencies** -- so the name carries the process id and the probe name, and the
/// directory is removed first. Two probes never share one.
fn frisches_verzeichnis(marke: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("gabbro-onramp-{}-{marke}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).expect("a fresh directory");
    d
}

fn lauf(verzeichnis: &Path, argumente: &[&str]) -> (String, String, i32) {
    let aus = Command::new(env!("CARGO_BIN_EXE_gabbro"))
        .args(argumente)
        .current_dir(verzeichnis)
        .output()
        .expect("gabbro runs");
    (
        String::from_utf8_lossy(&aus.stdout).into_owned(),
        String::from_utf8_lossy(&aus.stderr).into_owned(),
        aus.status.code().unwrap_or(-1),
    )
}

/// **THE probe: `new`, `check`, `build`, run -- and the output compared.**
#[test]
fn was_new_schreibt_prueft_baut_und_laeuft() {
    let d = frisches_verzeichnis("laeuft");

    let (aus, fehler, code) = lauf(&d, &["new", "hallo"]);
    assert_eq!(code, 0, "`gabbro new hallo` runs:\n{aus}\n{fehler}");
    assert!(d.join("hallo.gab").exists(), "it wrote the source:\n{aus}");
    assert!(d.join("hallo.bau").exists(), "it wrote the manifest:\n{aus}");

    // **The checker over what it wrote.** `0 errors` and not "exit 0": a run that found
    // nothing because it read nothing would also exit 0.
    let (aus, fehler, code) = lauf(&d, &["check", "hallo.gab"]);
    assert_eq!(code, 0, "the skeleton checks:\n{aus}\n{fehler}");
    assert!(aus.contains("0 errors"), "and with 0 errors:\n{aus}");
    assert!(aus.contains("0 hints"), "and 0 hints:\n{aus}");

    // **`gabbro costs` answers over it.** The skeleton names that tool in its own comments;
    // a skeleton whose `costs` line the tool cannot read would be teaching a dead command.
    let (aus, fehler, code) = lauf(&d, &["costs", "hallo.gab"]);
    assert_eq!(code, 0, "`gabbro costs` runs over it:\n{aus}\n{fehler}");
    assert!(
        aus.lines().any(|z| z.starts_with("main\t")),
        "and it computes the entry's cost:\n{aus}"
    );

    // **The build.** `cc` is called here; a machine without it fails this probe loudly, which
    // is the right outcome -- the claim under test is that the skeleton RUNS.
    let (aus, fehler, code) = lauf(&d, &["build", "hallo.bau"]);
    assert_eq!(code, 0, "the build comes through:\n{aus}\n{fehler}");
    assert!(aus.contains("0 refused"), "and refuses nothing:\n{aus}");

    // **And the binary prints.** This is the assertion the whole file exists for.
    let binaer = d.join("target/hallo/hallo");
    assert!(binaer.exists(), "the linker wrote a binary: {}", binaer.display());
    let lauf = Command::new(&binaer).output().expect("the skeleton runs");
    assert_eq!(lauf.status.code(), Some(0), "it exits 0");
    assert_eq!(
        String::from_utf8_lossy(&lauf.stdout),
        "Hi\n",
        "and it prints what its own comment says it prints"
    );

    let _ = std::fs::remove_dir_all(&d);
}

/// **`new` over an existing file writes nothing, and it checks BOTH names first.**
#[test]
fn new_ueberschreibt_nichts() {
    let d = frisches_verzeichnis("bestand");
    // Only the MANIFEST is in the way. A generator that checked the source first would
    // already have written it by the time it noticed.
    std::fs::write(d.join("hallo.bau"), "-- a manifest of my own\n").expect("write");

    let (aus, fehler, code) = lauf(&d, &["new", "hallo"]);
    assert_eq!(code, 2, "it refuses:\n{aus}\n{fehler}");
    assert!(
        fehler.contains("is already here") && fehler.contains("nothing was written"),
        "and says so by name:\n{fehler}"
    );
    assert!(
        !d.join("hallo.gab").exists(),
        "and the source it would have written first is NOT there"
    );
    assert_eq!(
        std::fs::read_to_string(d.join("hallo.bau")).expect("read"),
        "-- a manifest of my own\n",
        "and the file that was in the way is untouched"
    );

    let _ = std::fs::remove_dir_all(&d);
}

/// **A name that is not a name is refused before anything is written.** The name becomes a
/// file name, a unit name and a directory name at once.
#[test]
fn new_nimmt_keinen_pfad_als_namen() {
    let d = frisches_verzeichnis("name");
    for schlecht in ["../weg", "a/b", "9zahl", ""] {
        let (aus, fehler, code) = lauf(&d, &["new", schlecht]);
        assert_eq!(code, 2, "`gabbro new {schlecht}` is refused:\n{aus}\n{fehler}");
    }
    // Nothing was written for any of them.
    let inhalt: Vec<_> = std::fs::read_dir(&d).expect("read dir").collect();
    assert!(inhalt.is_empty(), "and the directory is still empty");

    let _ = std::fs::remove_dir_all(&d);
}
