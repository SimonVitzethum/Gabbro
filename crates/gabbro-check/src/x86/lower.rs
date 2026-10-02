//! **Rust mirror of the typed-source-to-pilot-bytes lowering (wave B/C).**
//!
//! Mirrors `senkAtom`/`senkFrag` (`grammatik/Grammatik/X86/
//! ExpressionLowering.lean`) and `senkAssign`
//! (`grammatik/Grammatik/X86/SourceAssignmentLowering.lean`) over a small
//! Rust input type ([`Fragment`]) standing in for the covered slice of
//! the typed source `Expr`: integer literals, integer variables already
//! bound to a register, and ONE bounded ADD/SUB level over atomic
//! operands, plus a slot store. Every other shape refuses, exactly as
//! the Lean lowering's `none` arms do.
//!
//! ## What this is NOT
//!
//! * **Not a proof.** This is the UNTRUSTED Rust producer; `senkFrag`/
//!   `senkAssign` in Lean are what any generated sequence is checked
//!   against (via the golden vectors in `codec_golden.rs` and by
//!   `senkung_korrekt`/`senkAssign_korrekt` over the Lean model itself).
//! * **No register allocator, no real `Expr`/`Ctx`/`Env` typing.**
//!   [`Fragment`] is a standalone enum, not the typed source AST; the
//!   caller is responsible for actually having literals/variables of
//!   this exact shape and for supplying registers that are free of the
//!   source's own variables (mirrored here as the explicit `aliasing`
//!   check, standing in for the Lean side condition `Frisch`).
//! * **No flags, no overflow reasoning, no memory layout beyond the one
//!   `store64` displacement passed in.**

use super::codec::encode;
use super::typen::{Befehl, Byte, Disp32, Register, Wort};

/// Modular integer-to-word conversion, mirroring `ScalarFloat.lean`'s
/// `intWort`: two's complement modulo `2^64`. Takes `i128` (not `i64`)
/// so values up to `±2^64` -- the golden sweep uses `2^63` and
/// `-2^63` -- are representable before the reduction, matching Lean's
/// arbitrary-precision `Int`.
pub fn int_wort(n: i128) -> Wort {
    const MODULUS: i128 = 1i128 << 64;
    let r = n.rem_euclid(MODULUS);
    // `r` is in `0 .. 2^64` by construction of `rem_euclid` against a
    // positive modulus, so every bit fits in a `u64`.
    r as u64
}

/// One atom: a literal or a variable already bound to a register.
/// Mirrors the `IstAtom`/`senkAtom` cases of `ExpressionLowering.lean`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Atom {
    Lit(i128),
    Var(Register),
}

/// A small lowerable source fragment, standing in for the covered slice
/// of the typed `Expr`. `Mul` and `Nested` exist ONLY to exercise the
/// refusals (`senkFrag_verweigert_mul`, `senkFrag_verweigert_tief`); the
/// pilot never lowers them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fragment {
    Lit(i128),
    Var(Register),
    Add(Atom, Atom),
    Sub(Atom, Atom),
    /// PLANTED REFUSAL shape: multiplication is outside the fragment.
    Mul(Box<Fragment>, Box<Fragment>),
    /// PLANTED REFUSAL shape: a nested add/sub (depth two) is outside
    /// the fragment -- the inner fragment is itself non-atomic.
    Nested(Box<Fragment>, Box<Fragment>),
}

/// Why a lowering was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LowerError {
    /// The shape is outside the covered fragment (`senkAtom`/`senkFrag`
    /// return `none`): multiplication, nested arithmetic, or anything
    /// else not a literal/variable/one bounded add-or-sub over atoms.
    Unsupported,
    /// A `Frisch` violation: the two working registers coincide, or a
    /// source variable lives in one of them. Lean states `Frisch` as an
    /// explicit premise of the correctness theorems rather than a
    /// lowering-time check; this producer refuses it outright instead
    /// of silently emitting code the Lean side would not be proved
    /// correct for.
    RegisterAlias,
}

/// Lower one atom: mirrors `senkAtom`. Literals become one `movImm64`,
/// variables one `movReg64`; there is no other atom shape here, so this
/// function (unlike `senk_frag`) cannot refuse on shape -- only the
/// caller-level `aliasing` check in `senk_frag`/`senk_assign` can refuse.
fn senk_atom(a: Atom, dst: Register) -> Vec<Befehl> {
    match a {
        Atom::Lit(n) => vec![Befehl::MovImm64 {
            dst,
            value: int_wort(n),
        }],
        Atom::Var(src) => vec![Befehl::MovReg64 { dst, src }],
    }
}

/// The `Frisch` side condition, restricted to what this input type can
/// express: the two working registers differ, and the fragment's own
/// variable registers (if any) are disjoint from both. Mirrors
/// `ExpressionLowering.lean`'s `Frisch` definition.
fn aliasing_ok(frag: &Fragment, dst: Register, tmp: Register) -> bool {
    if dst == tmp {
        return false;
    }
    let touches = |a: Atom| -> bool {
        matches!(a, Atom::Var(r) if r == dst || r == tmp)
    };
    match *frag {
        Fragment::Lit(_) => true,
        Fragment::Var(r) => r != dst && r != tmp,
        Fragment::Add(a, b) | Fragment::Sub(a, b) => !touches(a) && !touches(b),
        Fragment::Mul(..) | Fragment::Nested(..) => true,
    }
}

/// Lower one fragment to a canonical pilot instruction list. Mirrors
/// `senkFrag` exactly: literals and variables as single moves, one
/// bounded ADD/SUB over atomic operands, and `LowerError::Unsupported`
/// (Lean's `none`) for every other shape -- multiplication, nesting, or
/// an add/sub whose operand is itself non-atomic. Register aliasing is
/// refused before the shape is even inspected further, since no
/// correctness theorem covers an aliased pair.
pub fn senk_frag(frag: &Fragment, dst: Register, tmp: Register) -> Result<Vec<Befehl>, LowerError> {
    if !aliasing_ok(frag, dst, tmp) {
        return Err(LowerError::RegisterAlias);
    }
    match *frag {
        Fragment::Lit(n) => Ok(vec![Befehl::MovImm64 {
            dst,
            value: int_wort(n),
        }]),
        Fragment::Var(src) => Ok(vec![Befehl::MovReg64 { dst, src }]),
        Fragment::Add(a, b) => {
            let mut pa = senk_atom(a, dst);
            let pb = senk_atom(b, tmp);
            pa.extend(pb);
            pa.push(Befehl::AddReg64 { dst, src: tmp });
            Ok(pa)
        }
        Fragment::Sub(a, b) => {
            let mut pa = senk_atom(a, dst);
            let pb = senk_atom(b, tmp);
            pa.extend(pb);
            pa.push(Befehl::SubReg64 { dst, src: tmp });
            Ok(pa)
        }
        Fragment::Mul(..) | Fragment::Nested(..) => Err(LowerError::Unsupported),
    }
}

/// Lower one admitted assignment: the fragment lowered by [`senk_frag`],
/// followed by one `store64` through `base` at `disp`. Mirrors
/// `senkAssign` (`SourceAssignmentLowering.lean`): `prog ++
/// [store64 base dst disp]` on success, the same refusal otherwise. The
/// base register is also checked against the `Frisch` pair, mirroring
/// `senkAssign_korrekt`'s `hBasis` premise (`baseR ≠ dst ∧ baseR ≠ tmp`).
pub fn senk_assign(
    frag: &Fragment,
    dst: Register,
    tmp: Register,
    base: Register,
    disp: Disp32,
) -> Result<Vec<Befehl>, LowerError> {
    if base == dst || base == tmp {
        return Err(LowerError::RegisterAlias);
    }
    let mut prog = senk_frag(frag, dst, tmp)?;
    prog.push(Befehl::Store64 { base, src: dst, disp });
    Ok(prog)
}

/// Lowered instructions as canonical bytes: `encode` flattened over the
/// generated program. Convenience composition, not a new encoding.
pub fn to_bytes(prog: &[Befehl]) -> Vec<Byte> {
    prog.iter().flat_map(encode).collect()
}

#[cfg(test)]
mod proben {
    use super::*;
    use crate::x86::typen::Register::*;

    #[test]
    fn literal_senkt_auf_einen_immediate_zug() {
        let prog = senk_frag(&Fragment::Lit(42), Rax, Rcx).unwrap();
        assert_eq!(
            prog,
            vec![Befehl::MovImm64 {
                dst: Rax,
                value: int_wort(42)
            }]
        );
    }

    #[test]
    fn negative_literale_wickeln_modular() {
        // intWort(-1) = u64::MAX, matching ScalarFloat.lean's intWort
        // modulo-2^64 reduction of a negative Int.
        let prog = senk_frag(&Fragment::Lit(-1), Rax, Rcx).unwrap();
        assert_eq!(
            prog,
            vec![Befehl::MovImm64 {
                dst: Rax,
                value: u64::MAX
            }]
        );
    }

    #[test]
    fn grosse_literale_an_den_kanten() {
        assert_eq!(int_wort(0), 0);
        assert_eq!(int_wort(-1), u64::MAX);
        assert_eq!(int_wort(1i128 << 63), 0x8000_0000_0000_0000u64);
        assert_eq!(int_wort(-(1i128 << 63)), 0x8000_0000_0000_0000u64);
        assert_eq!(int_wort((1i128 << 64) - 1), u64::MAX);
        assert_eq!(int_wort(1i128 << 64), 0);
    }

    #[test]
    fn variable_senkt_auf_einen_registerzug() {
        let prog = senk_frag(&Fragment::Var(R10), Rax, Rcx).unwrap();
        assert_eq!(prog, vec![Befehl::MovReg64 { dst: Rax, src: R10 }]);
    }

    #[test]
    fn add_ueber_zwei_atome() {
        let prog = senk_frag(&Fragment::Add(Atom::Var(R10), Atom::Lit(12)), Rax, Rcx).unwrap();
        assert_eq!(
            prog,
            vec![
                Befehl::MovReg64 { dst: Rax, src: R10 },
                Befehl::MovImm64 {
                    dst: Rcx,
                    value: int_wort(12)
                },
                Befehl::AddReg64 { dst: Rax, src: Rcx },
            ]
        );
    }

    #[test]
    fn sub_ueber_zwei_atome() {
        let prog = senk_frag(&Fragment::Sub(Atom::Lit(100), Atom::Var(R11)), Rax, Rcx).unwrap();
        assert_eq!(
            prog,
            vec![
                Befehl::MovImm64 {
                    dst: Rax,
                    value: int_wort(100)
                },
                Befehl::MovReg64 { dst: Rcx, src: R11 },
                Befehl::SubReg64 { dst: Rax, src: Rcx },
            ]
        );
    }

    /// PLANTED REFUSAL: multiplication is outside the fragment. Mirrors
    /// `senkFrag_verweigert_mul`.
    #[test]
    fn multiplikation_wird_verweigert() {
        let frag = Fragment::Mul(
            Box::new(Fragment::Lit(2)),
            Box::new(Fragment::Lit(3)),
        );
        assert_eq!(senk_frag(&frag, Rax, Rcx), Err(LowerError::Unsupported));
    }

    /// PLANTED REFUSAL: a nested add (depth two) is outside the
    /// fragment. Mirrors `senkFrag_verweigert_tief`.
    #[test]
    fn tiefe_schachtelung_wird_verweigert() {
        let inner = Fragment::Add(Atom::Lit(1), Atom::Lit(2));
        let frag = Fragment::Nested(Box::new(inner), Box::new(Fragment::Lit(3)));
        assert_eq!(senk_frag(&frag, Rax, Rcx), Err(LowerError::Unsupported));
    }

    /// PLANTED REFUSAL: the two working registers coincide.
    #[test]
    fn gleiche_arbeitsregister_werden_verweigert() {
        assert_eq!(
            senk_frag(&Fragment::Add(Atom::Lit(1), Atom::Lit(2)), Rax, Rax),
            Err(LowerError::RegisterAlias)
        );
    }

    /// PLANTED REFUSAL: a source variable lives in one of the working
    /// registers (the `Frisch` premise, violated).
    #[test]
    fn variable_im_arbeitsregister_wird_verweigert() {
        assert_eq!(
            senk_frag(&Fragment::Add(Atom::Var(Rax), Atom::Lit(2)), Rax, Rcx),
            Err(LowerError::RegisterAlias)
        );
        assert_eq!(
            senk_frag(&Fragment::Add(Atom::Lit(2), Atom::Var(Rcx)), Rax, Rcx),
            Err(LowerError::RegisterAlias)
        );
    }

    /// PLANTED REFUSAL: the slot base register coincides with a working
    /// register (the `hBasis` premise of `senkAssign_korrekt`, violated).
    #[test]
    fn basisregister_im_arbeitspaar_wird_verweigert() {
        assert_eq!(
            senk_assign(
                &Fragment::Lit(1),
                Rax,
                Rcx,
                Rax,
                Disp32::von_bits(0)
            ),
            Err(LowerError::RegisterAlias)
        );
    }

    #[test]
    fn assign_haengt_den_store_an() {
        let prog = senk_assign(
            &Fragment::Add(Atom::Var(R10), Atom::Lit(12)),
            Rax,
            Rcx,
            Rbx,
            Disp32::von_bits(0),
        )
        .unwrap();
        assert_eq!(
            prog,
            vec![
                Befehl::MovReg64 { dst: Rax, src: R10 },
                Befehl::MovImm64 {
                    dst: Rcx,
                    value: int_wort(12)
                },
                Befehl::AddReg64 { dst: Rax, src: Rcx },
                Befehl::Store64 {
                    base: Rbx,
                    src: Rax,
                    disp: Disp32::von_bits(0)
                },
            ]
        );
    }

    /// GOLDEN COMPARISON: the witness program of
    /// `SourceAssignmentLowering.lean`'s `witProg628` (`x + 12` with `x`
    /// bound to `r10`, stored through `rbx` at displacement 0) comes out
    /// byte-identical from this Rust lowering plus `encode`. The Lean
    /// side computes the SAME bytes by `rfl`/`decide` over
    /// `witSenkAssign628`/`witBytes628`.
    #[test]
    fn witness_628_byte_identisch() {
        let prog = senk_assign(
            &Fragment::Add(Atom::Var(R10), Atom::Lit(12)),
            Rax,
            Rcx,
            Rbx,
            Disp32::von_bits(0),
        )
        .unwrap();
        let bytes = to_bytes(&prog);
        let erwartet: Vec<Byte> = [
            Befehl::MovReg64 { dst: Rax, src: R10 },
            Befehl::MovImm64 {
                dst: Rcx,
                value: int_wort(12),
            },
            Befehl::AddReg64 { dst: Rax, src: Rcx },
            Befehl::Store64 {
                base: Rbx,
                src: Rax,
                disp: Disp32::von_bits(0),
            },
        ]
        .iter()
        .flat_map(encode)
        .collect();
        assert_eq!(bytes, erwartet);
        // Pinned against the actual byte values Lean's `witBytes628`
        // computes by `decide`: REX.W mov r10->rax (0x4C 0x89 0xD0),
        // REX.W movImm64 12 into rcx (0x48 0xB9 <le64 12>), REX.W add
        // rax+=rcx (0x48 0x01 0xC8), REX.W store rax through rbx at
        // disp32 0 (0x48 0x89 0x83 <le32 0>, no SIB: regLow(rbx)=3).
        let gepinnt: Vec<Byte> = vec![
            0x4C, 0x89, 0xD0, 0x48, 0xB9, 12, 0, 0, 0, 0, 0, 0, 0, 0x48, 0x01, 0xC8, 0x48, 0x89,
            0x83, 0, 0, 0, 0,
        ];
        assert_eq!(bytes, gepinnt);
    }
}
