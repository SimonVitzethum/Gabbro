//! **GabbroV §5 -- the harness tests, with speech probes in both directions.**
//!
//! Every probe below drives a case the tool must answer through the tool itself: a
//! passing manifest passes, and a silently dropped line fails. Fixtures are inline
//! manifest texts in Fassung 2 -- no tree files, no build, pure logic.

use gabbro_check::gabbrov::{
    check_e1, count_verdict_lines, judge, parse_manifest, render, run, Verdict,
};

/// Two obligation lines in the shape `pflichten::zeige` writes (Fassung 2).
fn manifest_two() -> String {
    "-- manifest-version 2\n\
     -- Obligation register: probe.gab\n\
     N  Postcondition (2)\n\
     obligation\tf :: ensures #1\tN\tprobe.gab:3\topen\tensures x > 0\n\
     obligation\tf :: ensures #2\tN\tprobe.gab:4\topen\tensures x < 100\n\
     \n\
     == 2 obligations: 0 refinement, 0 preservation, 2 postcondition, 0 foreign, 0 precondition, 0 device, 0 loop invariant, 0 unowned invariant ==\n"
        .to_string()
}

#[test]
fn a_passing_manifest_passes() {
    let out = run(&manifest_two(), "passed\tf :: ensures #1\npassed\tf :: ensures #2\n")
        .expect("a fully judged manifest runs");
    assert!(out.contains("2 passed"), "both lines judged passed: {out}");
    assert!(out.contains("== 2 verdicts over 2 obligation line(s)"), "E1 balance printed: {out}");
}

#[test]
fn comment_only_changes_do_not_move_the_count() {
    let with_noise = format!(
        "-- a new header line\n{}\n-- a trailing note\n",
        manifest_two()
    );
    let a = parse_manifest(&manifest_two()).expect("baseline parses");
    let b = parse_manifest(&with_noise).expect("comments are skipped, not counted");
    assert_eq!(a, b, "comment-only changes must not move the obligation count");
}

#[test]
fn a_silently_dropped_verdict_line_fails_e1() {
    let out = run(&manifest_two(), "passed\tf :: ensures #1\npassed\tf :: ensures #2\n")
        .expect("baseline runs");
    assert_eq!(count_verdict_lines(&out), 2, "baseline carries two verdict lines");
    // The dropped line: one `verdict` line removed from the rendered report.
    let dropped: String = out.lines().filter(|l| !l.contains("ensures #2")).collect::<Vec<_>>().join("\n");
    let e1 = check_e1(2, count_verdict_lines(&dropped));
    assert!(e1.is_err(), "E1 must fail when a verdict line goes missing: {dropped}");
}

#[test]
fn dropping_a_manifest_line_changes_the_population_not_the_verdict() {
    // The other direction: the manifest itself loses a line. E1 compares what is READ
    // against what is JUDGED, so a shorter manifest still balances -- and the missing
    // line is visible because the population moved, not because E1 fired.
    let short = manifest_two().lines().filter(|l| !l.contains("ensures #1")).collect::<Vec<_>>().join("\n");
    let manifest = parse_manifest(&short).expect("shorter manifest parses");
    assert_eq!(manifest.len(), 1, "one line read, not two");
    let report = judge(&manifest, "passed\tf :: ensures #2\n").expect("judged");
    assert_eq!(report.len(), manifest.len(), "every line read gets a verdict");
}

#[test]
fn one_obligation_through_all_three_outcomes() {
    let manifest = manifest_two();
    let passed = judge(&parse_manifest(&manifest).unwrap(), "passed\tf :: ensures #1\n").unwrap();
    assert_eq!(passed[0].verdict, Verdict::Passed, "passed where the spec says so");
    let refuted = judge(
        &parse_manifest(&manifest).unwrap(),
        "refuted\tf :: ensures #1\tx = 0 at entry\n",
    )
    .unwrap();
    assert!(
        matches!(&refuted[0].verdict, Verdict::Refuted { counterexample } if counterexample.contains("x = 0")),
        "refuted WITH a counterexample as a concrete state: {:?}",
        refuted[0].verdict
    );
    let undecided = judge(&parse_manifest(&manifest).unwrap(), "-- nothing judged\n").unwrap();
    assert!(
        matches!(&undecided[0].verdict, Verdict::Undecided { .. }),
        "undecided where the spec is silent: {:?}",
        undecided[0].verdict
    );
    assert_eq!(undecided.len(), 2, "silence judges nothing away -- both lines undecided");
}

#[test]
fn an_unknown_version_is_refused_never_misread() {
    let future = manifest_two().replacen("-- manifest-version 2", "-- manifest-version 3", 1);
    assert!(
        parse_manifest(&future).is_err(),
        "an unknown version must be refused, not misread"
    );
    assert!(parse_manifest("-- no version here\n").is_err(), "no version field: no reading");
}

#[test]
fn a_verdict_about_nothing_is_an_error() {
    let manifest = parse_manifest(&manifest_two()).unwrap();
    assert!(
        judge(&manifest, "passed\tnowhere :: ensures #9\n").is_err(),
        "a verdict about a line nobody emitted judges nothing"
    );
}

#[test]
fn an_unparsable_obligation_line_fails_instead_of_shrinking() {
    let broken = manifest_two() + "obligation\tthis line has no tabs\n";
    assert!(
        parse_manifest(&broken).is_err(),
        "a line that falls at the parser must fail the run, not shrink the count"
    );
}

#[test]
fn e1_counts_what_it_compares() {
    assert!(check_e1(3, 3).is_ok(), "equal counts hold");
    assert!(check_e1(3, 2).is_err(), "a missing verdict fails");
    assert!(check_e1(2, 3).is_err(), "an extra verdict fails too -- E1 is an equality, not a lower bound");
    let empty = render(&[], 0);
    assert_eq!(count_verdict_lines(&empty), 0, "an empty report carries no verdict lines");
}
