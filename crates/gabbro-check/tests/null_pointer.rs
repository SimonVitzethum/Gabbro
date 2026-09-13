//! **Immutable pointers starting at `0` (`N260`, lane 145) in both directions.**
//!
//! The file-level twin of the gift probe:
//! `beispiele/gift/931-null-pointer-through-an-immutable-static.gab` pins the
//! fall over a file, what stands here pins it over snippets -- poison and
//! positive twin side by side, so a rule that goes silent fails here even
//! where the gift corpus has no file for the shape. The `let` shapes and the
//! `const`-indirection shape have no gift file of their own: they live here,
//! beside the rule that owns them.
//!
//! What each row is:
//!
//! * an immutable `static` starting at `0` falls with `N260` ALONE;
//! * the same with `mut` stays silent -- the NULL-initialised global idiom,
//!   assignment may precede any use;
//! * an immutable `let` starting at `0` falls with `N260` ALONE, including
//!   inside a nested block;
//! * the same with `mut`, assigned from a parameter, stays silent;
//! * a `const` pointer starting at `0` falls with `N260` ALONE -- constants
//!   never carry `mut`;
//! * the zero through a `const` name falls the same way: the rule reads the
//!   value, not the spelling;
//! * a nonzero number at the same slot is `M140`'s, never `N260`'s;
//! * an array decaying into the pointer stays silent -- decay is not a number;
//! * rehanging the refused static still draws `M118` beside `N260`: the use
//!   refusal is not swallowed by the declaration refusal.

use gabbro_syntax::diag::Stufe;

fn errors(source: &str) -> Vec<String> {
    let (tree, mut refusals) = gabbro_syntax::lies("null_pointer", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

const HEAD: &str = "module test::null_pointer {\n\
    table T count 4 {\n\
        slot { a : u32 in 0 .. 1000, }\n\
    }\n";

fn unit(extra: &str) -> String {
    format!("{HEAD}{extra}}}\n")
}

#[test]
fn n260_immutable_static_zero_falls_alone() {
    let src = unit(
        "static tz : ptr<normal, rw> T = 0;\n\
         impl fn setz(i : index into T) effects { writes tz.slots } costs <= 3 ops \
         { tz.slots[i].a = 5; }\n",
    );
    assert_eq!(errors(&src), vec!["N260"], "an immutable static at `0`");
}

#[test]
fn n260_mutable_static_zero_stays_silent() {
    let src = unit(
        "static mut m : ptr<normal, rw> T = 0;\n\
         impl fn setz(i : index into T) effects { writes m.slots } costs <= 3 ops \
         { m.slots[i].a = 5; }\n",
    );
    assert_eq!(errors(&src), Vec::<String>::new(), "a mutable static at `0`");
}

#[test]
fn n260_immutable_let_zero_falls_alone() {
    let src = unit(
        "impl fn setz(i : index into T) effects { writes p.slots } costs <= 8 ops {\n\
         \x20   let p : ptr<normal, rw> T = 0;\n\
         \x20   p.slots[i].a = 5;\n\
         }\n",
    );
    assert_eq!(errors(&src), vec!["N260"], "an immutable `let` at `0`");
}

#[test]
fn n260_nested_let_zero_falls_alone() {
    let src = unit(
        "impl fn setz(i : index into T, b : bool) effects { writes p.slots } costs <= 12 ops {\n\
         \x20   if b {\n\
         \x20       let p : ptr<normal, rw> T = 0;\n\
         \x20       p.slots[i].a = 5;\n\
         \x20   }\n\
         }\n",
    );
    assert_eq!(errors(&src), vec!["N260"], "an immutable `let` at `0` in a nested block");
}

#[test]
fn n260_mutable_let_zero_assigned_stays_silent() {
    let src = unit(
        "impl fn setz(p : ptr<normal, rw> T, i : index into T) effects { writes p.slots } \
         costs <= 12 ops {\n\
         \x20   let mut q : ptr<normal, rw> T = 0;\n\
         \x20   q = p;\n\
         \x20   q.slots[i].a = 5;\n\
         }\n",
    );
    assert_eq!(
        errors(&src),
        Vec::<String>::new(),
        "a mutable `let` at `0`, assigned before use"
    );
}

#[test]
fn n260_const_zero_falls_alone() {
    let src = unit("const K : ptr<normal, rw> T = 0;\n");
    assert_eq!(errors(&src), vec!["N260"], "a `const` pointer at `0`");
}

#[test]
fn n260_zero_through_a_const_name_falls_alone() {
    let src = unit(
        "const NULL : u64 = 0;\n\
         static tz : ptr<normal, rw> T = NULL;\n\
         impl fn setz(i : index into T) effects { writes tz.slots } costs <= 3 ops \
         { tz.slots[i].a = 5; }\n",
    );
    assert_eq!(errors(&src), vec!["N260"], "the zero through a `const` name");
}

#[test]
fn n260_nonzero_number_is_m140_not_n260() {
    let src = unit(
        "static tz : ptr<normal, rw> T = 0x1000;\n\
         impl fn setz(i : index into T) effects { writes tz.slots } costs <= 3 ops \
         { tz.slots[i].a = 5; }\n",
    );
    assert_eq!(errors(&src), vec!["M140"], "a nonzero number is `M140`'s");
}

#[test]
fn n260_array_decay_stays_silent() {
    let src = unit(
        "static mut SPEICHER : [T; 4] = 0;\n\
         impl fn setz(i : index into T) effects { reads SPEICHER, writes SPEICHER } \
         costs <= 8 ops {\n\
         \x20   let tz : ptr<normal, rw> T = SPEICHER;\n\
         \x20   tz.slots[i].a = 5;\n\
         }\n",
    );
    assert_eq!(errors(&src), Vec::<String>::new(), "decay is not a number");
}

#[test]
fn n260_rehang_still_draws_m118_beside_it() {
    let src = unit(
        "static tz : ptr<normal, rw> T = 0;\n\
         impl fn setz(i : index into T) effects { writes tz.slots } costs <= 3 ops \
         { tz.slots[i].a = 5; }\n\
         impl fn haeng_um() effects { writes tz } costs <= 1 ops { tz = 0; }\n",
    );
    assert_eq!(
        errors(&src),
        vec!["N260", "M118"],
        "rehanging the refused static still draws `M118`"
    );
}
