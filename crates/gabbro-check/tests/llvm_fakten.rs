//! **Facts handed to LLVM, each justified by a checker fact.**
//!
//! * `nuw`/`nsw` on plain `+ - *`: M104 refuses every operation that could leave the
//!   operands' width, so such an operation never wraps. The wrapping forms carry no flag.
//! * `inbounds` on fixed-array element addresses: M4/M103 refuses an index that is not
//!   proven below the array length.
//!
//! Every fact kind is counted: the IR ends with `; gabbro-fact KIND N` lines.

use gabbro_check::gatter::Bau;
use gabbro_check::llvm::{ZIEL_AARCH64, ZIEL_X86_64};

fn ir(quelle: &str, ziel: &'static gabbro_check::llvm::Ziel) -> String {
    let (baum, mut absagen) = gabbro_syntax::lies("fakten", quelle);
    gabbro_check::pruefe(&baum, &mut absagen);
    assert_eq!(absagen.fehler_zahl(), 0, "{}", absagen.zeige(quelle));
    gabbro_check::llvm::emittiere_llvm(&baum, &mut absagen, Bau::Auslieferung, ziel)
}

const PROBE: &str = r#"module fakten {
pub static mut A : [u32; 16] = 0;
pub fn g(i : u32 in 0 .. 15, a : u32 in 0 .. 1000, b : u32 in 0 .. 1000) -> u32
    effects { reads A }
    costs <= 8 ops
{
    let x : u32 in 0 .. 1000000 = a * b;
    return A[i];
}
pub fn main() -> u32
    effects { reads A }
    costs <= 20 ops
{
    return g(3, 4, 5);
}
}
"#;

const WRAP: &str = r#"module fakten {
pub fn w(a : u8, b : u8) -> u8
    effects { pure }
    costs <= 4 ops
{
    return a +% b;
}
pub fn main() -> u32
    effects { pure }
    costs <= 4 ops
{
    return 7;
}
}
"#;

#[test]
fn plain_product_and_array_index_carry_their_facts_on_both_targets() {
    for z in [&ZIEL_X86_64, &ZIEL_AARCH64] {
        let t = ir(PROBE, z);
        assert!(t.contains("mul nuw i32"), "{t}");
        assert!(t.contains("getelementptr inbounds [16 x i32]"), "{t}");
        assert!(t.contains("; gabbro-fact nuw 1"), "{t}");
        assert!(t.contains("; gabbro-fact inbounds 1"), "{t}");
    }
}

#[test]
fn wrapping_forms_carry_no_flag() {
    let t = ir(WRAP, &ZIEL_X86_64);
    assert!(t.contains(" add i8"), "{t}");
    assert!(!t.contains(" add nuw") && !t.contains(" add nsw"), "{t}");
    assert!(!t.contains("gabbro-fact nuw"), "{t}");
}
