//! Execution witnesses for generic lowering rules, never a coverage denominator.
use super::Ziel;
use std::path::PathBuf;
use std::process::Command;

pub(super) fn run(name: &str, target: &Ziel, ir: &str, expected: i32) {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let dir = root
        .join(".claude/muse-arbeit/kratz/llvm-rule-tests")
        .join(format!("{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    for level in ["O0", "O3"] {
        let base = dir.join(format!("{}-{level}", target.name));
        let ll = base.with_extension("ll");
        let bc = base.with_extension("bc");
        let obj = base.with_extension("o");
        std::fs::write(&ll, ir).unwrap();
        for (tool, args) in [
            (
                "opt",
                vec![
                    format!("-{level}"),
                    ll.display().to_string(),
                    "-o".into(),
                    bc.display().to_string(),
                ],
            ),
            (
                "llc",
                vec![
                    format!("-{level}"),
                    "-filetype=obj".into(),
                    bc.display().to_string(),
                    "-o".into(),
                    obj.display().to_string(),
                ],
            ),
            (
                "ld.lld",
                vec![
                    "-static".into(),
                    "-e".into(),
                    "_start".into(),
                    obj.display().to_string(),
                    "-o".into(),
                    base.display().to_string(),
                ],
            ),
        ] {
            let out = Command::new(tool)
                .args(args)
                .output()
                .unwrap_or_else(|e| panic!("{tool}: {e}"));
            assert!(
                out.status.success(),
                "{name}/{}/{level}: {tool}: {}",
                target.name,
                String::from_utf8_lossy(&out.stderr)
            );
        }
        let mut cmd = Command::new("bash");
        let limits = if target.name == "x86_64" {
            "ulimit -s 128; ulimit -v 524288; exec timeout 30 \"$@\""
        } else {
            "ulimit -s 128; exec timeout 30 \"$@\""
        };
        cmd.args(["-c", limits, "llvm-rule-test"]);
        if target.name == "aarch64" {
            cmd.args(["qemu-aarch64", "-s", "131072"]);
        }
        let out = cmd.arg(&base).output().unwrap();
        assert_eq!(
            out.status.code(),
            Some(expected),
            "{name}/{}/{level}: {}",
            target.name,
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

pub(super) fn source(name: &str, source: &str, expected: i32) {
    source_with(name, source, expected, |ir, _| ir.into());
}

pub(super) fn source_with(
    name: &str,
    source: &str,
    expected: i32,
    transform: impl Fn(&str, &Ziel) -> String,
) {
    for target in [&super::ZIEL_X86_64, &super::ZIEL_AARCH64] {
        let (ast, mut diagnostics) = gabbro_syntax::lies(name, source);
        crate::pruefe(&ast, &mut diagnostics);
        assert_eq!(
            diagnostics.fehler_zahl(),
            0,
            "{name}: {}",
            diagnostics.zeige(source)
        );
        let ir = super::emittiere_llvm(
            &ast,
            &mut diagnostics,
            crate::gatter::Bau::Auslieferung,
            target,
        );
        assert_eq!(
            diagnostics.fehler_zahl(),
            0,
            "{name}: {}",
            diagnostics.zeige(source)
        );
        run(name, target, &transform(&ir, target), expected);
    }
}
