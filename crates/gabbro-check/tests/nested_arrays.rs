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

fn emitted(source: &str) -> (String, Vec<String>) {
    let (tree, mut refusals) = gabbro_syntax::lies("nested_arrays", source);
    let _ = gabbro_check::pruefe(&tree, &mut refusals);
    let fall: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    assert!(
        fall.is_empty(),
        "the positive probe does not check clean -- fell with {fall:?}"
    );
    let c = gabbro_check::emit::emittiere(&tree, &mut refusals);
    let nachher: Vec<String> = refusals
        .absagen
        .iter()
        .filter(|a| a.stufe == Stufe::Fehler)
        .map(|a| a.code.to_string())
        .collect();
    (c, nachher)
}

fn unit(extra: &str) -> String {
    format!("module test::nested {{\n{extra}}}\n")
}

// -- the emitter lowers nested arrays ----------------------------------------

#[test]
fn nested_static_lowers_to_multidimensional() {
    let src = unit("static mut M : [[u32; 4]; 3] = 0;\n");
    let (c, nachher) = emitted(&src);
    assert!(nachher.is_empty(), "emits without a refusal, got {nachher:?}");
    assert!(
        c.contains("static uint32_t M[3][4] __attribute__((unused)) = {0};"),
        "the declaration spells every dimension:\n{c}"
    );
}

#[test]
fn nested_static_reads_and_writes_lower_at_depth() {
    let src = unit(
        "static mut M : [[u32; 4]; 3] = 0;\n\
         impl fn schreibe(i : u32 in 0 ..< 3, j : u32 in 0 ..< 4, v : u32) \
             effects { writes M } costs <= 4 ops { M[i][j] = v; }\n\
         impl fn lies(i : u32 in 0 ..< 3, j : u32 in 0 ..< 4) -> u32 \
             effects { reads M } costs <= 3 ops { return M[i][j]; }\n",
    );
    let (c, nachher) = emitted(&src);
    assert!(nachher.is_empty(), "emits without a refusal, got {nachher:?}");
    assert!(c.contains("M[i][j] = v;"), "the store lowers:\n{c}");
    assert!(c.contains("return M[i][j];"), "the read lowers:\n{c}");
}

#[test]
fn nested_const_table_lowers_to_nested_initialiser() {
    let src = unit(
        "const T : [[u32; 2]; 2] = [[1, 2], [3, 4]];\n\
         impl fn lies(i : u32 in 0 ..< 2, j : u32 in 0 ..< 2) -> u32 \
             effects { pure } costs <= 3 ops { return T[i][j]; }\n",
    );
    let (c, nachher) = emitted(&src);
    assert!(nachher.is_empty(), "emits without a refusal, got {nachher:?}");
    assert!(
        c.contains(
            "static const uint32_t T[2][2] __attribute__((unused)) = {{1u, 2u}, {3u, 4u}};"
        ),
        "one multi-dimensional array, values folded:\n{c}"
    );
}

#[test]
fn nested_struct_field_lowers() {
    let src = unit(
        "type Matrix = { m : [[u32; 4]; 3], };\n\
         static mut S : Matrix = Matrix(m: 0);\n\
         impl fn lies(i : u32 in 0 ..< 3, j : u32 in 0 ..< 4) -> u32 \
             effects { reads S } costs <= 3 ops { return S.m[i][j]; }\n",
    );
    let (c, nachher) = emitted(&src);
    assert!(nachher.is_empty(), "emits without a refusal, got {nachher:?}");
    assert!(c.contains("uint32_t m[3][4];"), "the field spells both:\n{c}");
    assert!(c.contains("return S.m[i][j];"), "the read lowers:\n{c}");
}

#[test]
fn nested_nonzero_static_fill_nests_its_braces() {
    // The checker refuses the non-zero fill first (`M140`, the static-value
    // shape rule -- only `= 0` means *every cell* in both languages). The
    // emitter is reached anyway on the parsed tree (`command_emit` runs the
    // back end before it reads the verdict, gift 662's fence story), and
    // there the fill nests its braces exactly, inside the byte budget.
    let src = unit("static mut M : [[u32; 2]; 2] = 7;\n");
    assert_eq!(errors(&src), vec!["M140"]);
    let (tree, mut refusals) = gabbro_syntax::lies("nested_arrays", &src);
    let c = gabbro_check::emit::emittiere(&tree, &mut refusals);
    assert!(
        c.contains("static uint32_t M[2][2] __attribute__((unused)) = {{7, 7}, {7, 7}};"),
        "every cell carries the fill, exactly once:\n{c}"
    );
}

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
         impl fn tausche(i : u32 in 0 ..< 3, j : u32 in 0 ..< 3) \
             effects { reads M, writes M } costs <= 8 ops { M[i] = M[j]; }\n",
    );
    assert_eq!(errors(&src), vec!["N287"], "a row is an array, not a value");
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
        "static mut A : [u32; 4] = 0;\n\
         static mut B : [u32; 4] = 0;\n\
         impl fn kopiere() effects { reads A, writes B } costs <= 4 ops { B = A; }\n",
    );
    assert_eq!(errors(&src), vec!["N287"], "C has none at any depth");
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
