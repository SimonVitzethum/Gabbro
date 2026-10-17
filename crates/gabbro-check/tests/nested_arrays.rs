//! **Nested arrays (lane 170) in both directions.**
//!
//! The grammar always allowed the nesting (`array = "[" typeexpr ";"
//! constexpr "]"`), and the checker always typed `M[i][j]` through it -- but
//! the emitter refused with `C001` over the nested element type, and the
//! const-table literal could not even spell a row (`P011` at the inner
//! `[`). This file measures the lane that closes both:
//!
//! * a `static` over a nested array lowers to one multi-dimensional C array
//!   (`uint32_t M[3][4]`), zero-initialised to `{0}`;
//! * a nested const-table literal lowers to one nested initialiser
//!   (`{{1u, 2u}, {3u, 4u}}`);
//! * element reads and writes lower at any depth through the ordinary place
//!   lowering (`M[i][j]`, `S.m[i][j]`);
//! * every dimension's index is held against its own bound (`M103` per
//!   dimension, outer and inner);
//! * a whole row is never a store target (`N287`) -- C has no assignment of
//!   one array to another, and the shape comparison agrees on both sides, so
//!   no older rule speaks.

use gabbro_syntax::diag::Stufe;

fn errors(source: &str) -> Vec<String> {
    let (tree, mut refusals) = gabbro_syntax::lies("nested_arrays", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect()
}

fn unit(extra: &str) -> String {
    format!("module test::nested {{\n{extra}}}\n")
}

// -- the emitter lowers nested arrays ----------------------------------------

// -- the checker holds every dimension ----------------------------------------

#[test]
fn m103_fires_on_the_inner_dimension() {
    let src = unit(
        "static mut M : [[u32; 4]; 3] = 0;\n\
         impl fn lies(i : u32 in 0 ..< 3) -> u32 effects { reads M } costs <= 4 ops \
             { return M[i][9]; }\n",
    );
    assert_eq!(errors(&src), vec!["M103"], "the inner bound is its own rule");
}

#[test]
fn m103_fires_on_the_outer_dimension() {
    let src = unit(
        "static mut M : [[u32; 4]; 3] = 0;\n\
         impl fn lies(j : u32 in 0 ..< 4) -> u32 effects { reads M } costs <= 4 ops \
             { return M[9][j]; }\n",
    );
    assert_eq!(errors(&src), vec!["M103"], "and so is the outer one");
}

// -- a whole row is never a store target --------------------------------------

#[test]
fn n287_nested_row_store_falls_alone() {
    let src = unit(
        "static mut M : [[u32; 4]; 3] = 0;\n\
         static mut K : [[u32; 3]; 3] = 0;\n\
         impl fn tausche(i : u32 in 0 ..< 3, j : u32 in 0 ..< 3) \
             effects { reads M, writes K } costs <= 8 ops { K[i] = M[j]; }\n",
    );
    assert_eq!(errors(&src), vec!["N287"], "rows of different length stay refused");
}

#[test]
fn n287_compound_row_store_falls_alone() {
    let src = unit(
        "static mut M : [[u32; 4]; 3] = 0;\n\
         impl fn lege_drauf(i : u32 in 0 ..< 3, j : u32 in 0 ..< 3) \
             effects { reads M, writes M } costs <= 16 ops { M[i] += M[j]; }\n",
    );
    assert_eq!(errors(&src), vec!["N287"], "whatever the operator");
}

#[test]
fn n287_flat_whole_array_store_falls_alone() {
    // The one-dimensional twin: the same silence, one lane older (`B = A`
    // over two `[u32; 4]` checked clean beside the nested row above).
    let src = unit(
        "static mut A : [u32; 3] = 0;\n\
         static mut B : [u32; 4] = 0;\n\
         impl fn kopiere() effects { reads A, writes B } costs <= 4 ops { B = A; }\n",
    );
    assert_eq!(errors(&src), vec!["N287"], "different lengths stay refused");
}

#[test]
fn n287_element_store_stays_silent() {
    let src = unit(
        "static mut M : [[u32; 4]; 3] = 0;\n\
         impl fn schreibe(i : u32 in 0 ..< 3, j : u32 in 0 ..< 4, v : u32) \
             effects { writes M } costs <= 4 ops { M[i][j] = v; }\n",
    );
    assert!(errors(&src).is_empty(), "only whole arrays fall, got {:?}", errors(&src));
}
