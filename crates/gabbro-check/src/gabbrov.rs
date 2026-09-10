//! **GabbroV §5 -- the harness (`gabbrov pruefe`), and it is pure logic.**
//!
//! `AUFTRAG-GABBROV.md` §5 names the call: **manifest + Lean specification → passed /
//! refuted / undecided**, with E1 wired in rather than hung beside the tool: *the run ends
//! by comparing the two line counts and aborts on a divergence.*
//!
//! This module holds that logic without touching the tree: it parses manifest lines in the
//! shape [`crate::pflichten::zeige`] writes (`obligation<TAB>name<TAB>class<TAB>anchor
//! <TAB>state<TAB>text`, Fassung 2), reads one verdict per line out of a specification
//! file, and judges every line. A line the specification says nothing about ends
//! **undecided with its name and a reason** -- never silently, never dropped.
//!
//! The specification file is deliberately small: one directive per line,
//! `passed<TAB><name>` or `refuted<TAB><name><TAB><counterexample as a concrete state>`.
//! It stands in for the Lean
//! specification of §5 until the solver channel (§6C) lands; the verdict SHAPE -- one per
//! manifest line, E1-checked -- is what this harness fixes, not the decision procedure.
//!
//! It reuses the manifest READER contract instead of duplicating it: the version line
//! comes first (`-- manifest-version N`), and an unknown version is REFUSED, never
//! misread -- the same order `AUFTRAG-GABBROV.md` §4 sets for the format change.

/// **The manifest version this reader accepts -- one place, and it is not this one.**
///
/// [`crate::pflichten::MANIFESTFASSUNG`] owns the number; this re-export keeps the two
/// from drifting into two registers over one format.
pub use crate::pflichten::MANIFESTFASSUNG as MANIFEST_VERSION;

/// One `obligation` line of the manifest: **name · class · text.**
///
/// The anchor travels in the file but is not part of the key: `messung/BERICHT-O3-
/// RATSCHE.md` decided the ratchet key as `(name, class, text)`, the anchor only as a
/// last resort -- swap two conjuncts and name, class, anchor and state are all unchanged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Obligation {
    pub name: String,
    pub class: String,
    pub text: String,
}

/// The three outcomes of `AUFTRAG-GABBROV.md` §5: **passed** (checked, not supposed) ·
/// **refuted** (with a counterexample as a concrete state) · **undecided** (with the
/// obligation name and a reason).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    Passed,
    Refuted { counterexample: String },
    Undecided { reason: String },
}

/// One manifest line, judged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Judgement {
    pub obligation: Obligation,
    pub verdict: Verdict,
}

/// One directive of the specification file.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Directive {
    Passed { name: String },
    Refuted { name: String, counterexample: String },
}

/// **Parse the manifest text into its obligation lines.**
///
/// Comment, header, section and closing lines are SKIPPED -- they carry no obligation.
/// Every line that starts with `obligation` MUST parse as six tab-separated fields
/// (`obligation`, name, class, anchor, state, text); one that does not is an `Err`, not
/// a skip. *A line that falls at the parser and vanishes from the count is exactly the
/// silent loss E1 exists to catch, so it fails the run instead of shrinking it.*
/// An unknown `-- manifest-version` is refused before anything is read.
pub fn parse_manifest(text: &str) -> Result<Vec<Obligation>, String> {
    let mut version: Option<u32> = None;
    let mut out = Vec::new();
    for (n, line) in text.lines().enumerate() {
        let nr = n + 1;
        if let Some(rest) = line.strip_prefix("-- manifest-version") {
            let v: u32 = rest.trim().parse().map_err(|_| {
                format!("line {nr}: the version field does not parse: `{line}`")
            })?;
            version = Some(v);
            continue;
        }
        if line.starts_with("obligation") {
            let seen = version.ok_or_else(|| {
                format!("line {nr}: an obligation line before any version field -- nothing is read before the version is known")
            })?;
            if seen != MANIFEST_VERSION {
                return Err(format!(
                    "unsupported manifest version {seen} (this reader takes {MANIFEST_VERSION}) -- refusing instead of misreading"
                ));
            }
            let fields: Vec<&str> = line.split('\t').collect();
            if fields.len() != 6 || fields[0] != "obligation" {
                return Err(format!(
                    "line {nr}: an obligation line with {} tab-separated field(s), not 6 -- refusing instead of dropping it",
                    fields.len()
                ));
            }
            out.push(Obligation {
                name: fields[1].to_string(),
                class: fields[2].to_string(),
                text: fields[5].to_string(),
            });
        }
    }
    match version {
        None => Err("no `-- manifest-version` line -- refusing instead of misreading".into()),
        Some(v) if v != MANIFEST_VERSION => Err(format!(
            "unsupported manifest version {v} (this reader takes {MANIFEST_VERSION}) -- refusing instead of misreading"
        )),
        Some(_) => Ok(out),
    }
}

/// **Parse the specification text into its directives.**
///
/// One directive per line, tab-separated like the manifest: `passed<TAB><name>` judges
/// the line passed; `refuted<TAB><name><TAB><counterexample>` judges it refuted with
/// the counterexample as a concrete state. The tabs are load-bearing: obligation names
/// carry spaces (`f :: ensures #1`), so a space-separated form could not tell where the
/// name ends. Blank lines and `--` / `#` comments are skipped. Anything else is an
/// `Err`: *a specification line the reader does not understand must not read as
/// approval.*
fn parse_spec(text: &str) -> Result<Vec<Directive>, String> {
    let mut out = Vec::new();
    for (n, raw) in text.lines().enumerate() {
        let nr = n + 1;
        let line = raw.trim();
        if line.is_empty() || line.starts_with("--") || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            ["passed", name] if !name.trim().is_empty() => {
                out.push(Directive::Passed { name: name.trim().to_string() })
            }
            ["refuted", name, gegen] if !name.trim().is_empty() && !gegen.trim().is_empty() => {
                out.push(Directive::Refuted {
                    name: name.trim().to_string(),
                    counterexample: gegen.trim().to_string(),
                })
            }
            _ => {
                return Err(format!(
                    "spec line {nr}: understood are `passed<TAB><name>` and \
                     `refuted<TAB><name><TAB><counterexample>`, not: `{raw}`"
                ));
            }
        }
    }
    Ok(out)
}

/// **Judge every manifest line against the specification.**
///
/// Each line ends with exactly one verdict: `passed` / `refuted` where the specification
/// says so, `undecided` with its name and reason where it says nothing -- the state the
/// line was already in. A directive that names no manifest line is an `Err`: *a verdict
/// about an obligation nobody emitted judges nothing.*
pub fn judge(manifest: &[Obligation], spec_text: &str) -> Result<Vec<Judgement>, String> {
    let directives = parse_spec(spec_text)?;
    let mut out = Vec::new();
    for o in manifest {
        let mut verdict = Verdict::Undecided {
            reason: "no verdict in the specification -- the line stays open".to_string(),
        };
        for d in &directives {
            match d {
                Directive::Passed { name } if *name == o.name => verdict = Verdict::Passed,
                Directive::Refuted { name, counterexample }
                    if *name == o.name =>
                {
                    verdict = Verdict::Refuted { counterexample: counterexample.clone() }
                }
                _ => {}
            }
        }
        out.push(Judgement { obligation: o.clone(), verdict });
    }
    for d in &directives {
        let name = match d {
            Directive::Passed { name } => name,
            Directive::Refuted { name, .. } => name,
        };
        if !manifest.iter().any(|o| &o.name == name) {
            return Err(format!(
                "the specification judges `{name}`, which no manifest line emits -- a verdict about nothing judges nothing"
            ));
        }
    }
    Ok(out)
}

/// **E1 -- the wired-in completeness check (`AUFTRAG-GABBROV.md` §1, §5).**
///
/// Every `obligation` line of the manifest gets a verdict: the count of lines read and
/// the count of lines judged MUST agree, in every run, not only at the end. A divergence
/// is a failure, not a note.
pub fn check_e1(manifest_lines: usize, verdict_lines: usize) -> Result<(), String> {
    if manifest_lines == verdict_lines {
        Ok(())
    } else {
        Err(format!(
            "E1 FAILED: {manifest_lines} obligation line(s) in the manifest, {verdict_lines} verdict line(s) -- a line went missing"
        ))
    }
}

/// **Render the report: one `verdict` line per judged obligation, then the E1 balance.**
pub fn render(report: &[Judgement], manifest_lines: usize) -> String {
    let mut s = String::new();
    for j in report {
        let (urteil, detail) = match &j.verdict {
            Verdict::Passed => ("passed".to_string(), "checked".to_string()),
            Verdict::Refuted { counterexample } => {
                ("refuted".to_string(), counterexample.clone())
            }
            Verdict::Undecided { reason } => ("undecided".to_string(), reason.clone()),
        };
        s.push_str(&format!("verdict\t{}\t{}\t{}\n", j.obligation.name, urteil, detail));
    }
    let passed = report.iter().filter(|j| j.verdict == Verdict::Passed).count();
    let refuted = report
        .iter()
        .filter(|j| matches!(j.verdict, Verdict::Refuted { .. }))
        .count();
    let undecided = report.len() - passed - refuted;
    s.push_str(&format!(
        "== {} verdicts over {manifest_lines} obligation line(s): {passed} passed, {refuted} refuted, {undecided} undecided ==\n",
        report.len()
    ));
    s
}

/// **Count the rendered verdict lines -- the second side of the E1 comparison.**
pub fn count_verdict_lines(rendered: &str) -> usize {
    rendered.lines().filter(|l| l.starts_with("verdict\t")).count()
}

/// **The run: parse, judge, render, and check E1 inside the run.**
///
/// Returns the rendered report. Any refusal -- no version, unknown version, an
/// unparsable obligation line, a verdict about nothing, an E1 divergence -- is an `Err`.
pub fn run(manifest_text: &str, spec_text: &str) -> Result<String, String> {
    let manifest = parse_manifest(manifest_text)?;
    let report = judge(&manifest, spec_text)?;
    let rendered = render(&report, manifest.len());
    check_e1(manifest.len(), count_verdict_lines(&rendered))?;
    Ok(rendered)
}
