//! **The direct-x86 pilot byte codec (wave B/C, Rust mirror).**
//!
//! Untrusted Rust producer mirroring the canonical
//! `grammatik/Grammatik/X86/Codec.lean` exactly, per
//! `dokumente/x86/BYTE-PILOT.md`: one canonical encoding per `Befehl`
//! constructor, and a decoder that parses bytes (never encode-equality)
//! and refuses every non-canonical form the Lean decoder refuses.
//!
//! ## What this is NOT
//!
//! * **Not a proof.** This file is the UNTRUSTED producer; the Lean
//!   `Codec.lean` decoder is what any emitted byte stream is checked
//!   against. Agreement with Lean is tested here with golden vectors
//!   (`codec_golden.rs`), computed by `#eval`-ing the Lean definitions
//!   themselves -- it is evidence, not a machine-checked correspondence.
//! * **No hardware correspondence, no execution, no TSO bridge, no ABI
//!   or whole-image coverage.** Same scope boundary as `Codec.lean`'s
//!   own `CUTS` block.
//! * **Pilot-only.** Exactly the 14 `Befehl` forms of `typen::Befehl`;
//!   every other x86-64 encoding is out of scope and this module makes
//!   no claim about it.

use super::typen::{Bedingung, Befehl, Byte, Decodiert, Disp32, Register, Wort};

/// REX.W prefix with R=`rh` and B=`bh` extension bits (X=0).
/// Mirrors `Codec.lean`'s `rexByte`.
fn rex_byte(rh: u8, bh: u8) -> Byte {
    0x48 + 4 * rh + bh
}

/// High bit of a register's architectural code (the REX R/B extension).
/// Mirrors `Codec.lean`'s `regHigh`.
fn reg_high(r: Register) -> u8 {
    r.code() / 8
}

/// Low three bits of a register's architectural code (ModRM field).
/// Mirrors `Codec.lean`'s `regLow`.
fn reg_low(r: Register) -> u8 {
    r.code() % 8
}

/// ModRM byte with mod=3 (register-direct) over low 3-bit codes.
/// Mirrors `Codec.lean`'s `modrmReg`.
fn modrm_reg(rl: u8, rm: u8) -> Byte {
    0xC0 + 8 * (rl % 8) + (rm % 8)
}

/// ModRM byte with mod=2 (base plus disp32) over low 3-bit codes.
/// Mirrors `Codec.lean`'s `modrmMem`.
fn modrm_mem(rl: u8, rm: u8) -> Byte {
    0x80 + 8 * (rl % 8) + (rm % 8)
}

/// Little-endian bytes of a 32-bit displacement. Mirrors `leBytes32`.
fn le_bytes32(d: u32) -> [Byte; 4] {
    d.to_le_bytes()
}

/// Parse four little-endian bytes, returning the value and bytes consumed.
/// Mirrors `parseLe32`.
fn parse_le32(bytes: &[Byte]) -> Option<(u32, usize)> {
    if bytes.len() < 4 {
        return None;
    }
    Some((
        u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]),
        4,
    ))
}

/// Little-endian bytes of a 64-bit immediate. Mirrors `leBytes64`.
fn le_bytes64(v: Wort) -> [Byte; 8] {
    v.to_le_bytes()
}

/// Parse eight little-endian bytes, returning the value and bytes consumed.
/// Mirrors `parseLe64`.
fn parse_le64(bytes: &[Byte]) -> Option<(Wort, usize)> {
    if bytes.len() < 8 {
        return None;
    }
    Some((
        u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]),
        8,
    ))
}

/// Canonical byte encoding of one pilot instruction (`BYTE-PILOT.md`).
/// Multi-byte immediates and displacements are little endian. Mirrors
/// `Codec.lean`'s `encode`, constructor for constructor and byte for byte.
pub fn encode(b: &Befehl) -> Vec<Byte> {
    match *b {
        Befehl::MovImm64 { dst, value } => {
            let mut out = vec![0x48 + dst.code() / 8, 0xB8 + dst.code() % 8];
            out.extend_from_slice(&le_bytes64(value));
            out
        }
        Befehl::MovReg64 { dst, src } => vec![
            rex_byte(reg_high(src), reg_high(dst)),
            0x89,
            modrm_reg(reg_low(src), reg_low(dst)),
        ],
        Befehl::AddReg64 { dst, src } => vec![
            rex_byte(reg_high(src), reg_high(dst)),
            0x01,
            modrm_reg(reg_low(src), reg_low(dst)),
        ],
        Befehl::SubReg64 { dst, src } => vec![
            rex_byte(reg_high(src), reg_high(dst)),
            0x29,
            modrm_reg(reg_low(src), reg_low(dst)),
        ],
        Befehl::XorReg64 { dst, src } => vec![
            rex_byte(reg_high(src), reg_high(dst)),
            0x31,
            modrm_reg(reg_low(src), reg_low(dst)),
        ],
        Befehl::CmpReg64 { lhs, rhs } => vec![
            rex_byte(reg_high(rhs), reg_high(lhs)),
            0x39,
            modrm_reg(reg_low(rhs), reg_low(lhs)),
        ],
        Befehl::Load64 { dst, base, disp } => {
            let mut out = vec![
                rex_byte(reg_high(dst), reg_high(base)),
                0x8B,
                modrm_mem(reg_low(dst), reg_low(base)),
            ];
            if reg_low(base) == 4 {
                out.push(0x24);
            }
            out.extend_from_slice(&le_bytes32(disp.bits));
            out
        }
        Befehl::Store64 { base, src, disp } => {
            let mut out = vec![
                rex_byte(reg_high(src), reg_high(base)),
                0x89,
                modrm_mem(reg_low(src), reg_low(base)),
            ];
            if reg_low(base) == 4 {
                out.push(0x24);
            }
            out.extend_from_slice(&le_bytes32(disp.bits));
            out
        }
        Befehl::Jump32 { disp } => {
            let mut out = vec![0xE9];
            out.extend_from_slice(&le_bytes32(disp.bits));
            out
        }
        Befehl::JumpIf32 { cond, disp } => {
            let mut out = vec![0x0F, 0x80 + cond.code()];
            out.extend_from_slice(&le_bytes32(disp.bits));
            out
        }
        Befehl::Call32 { disp } => {
            let mut out = vec![0xE8];
            out.extend_from_slice(&le_bytes32(disp.bits));
            out
        }
        Befehl::Push64 { src } => {
            let code = src.code();
            if code < 8 {
                vec![0x50 + code]
            } else {
                vec![0x41, 0x50 + (code - 8)]
            }
        }
        Befehl::Pop64 { dst } => {
            let code = dst.code();
            if code < 8 {
                vec![0x58 + code]
            } else {
                vec![0x41, 0x58 + (code - 8)]
            }
        }
        Befehl::Ret => vec![0xC3],
    }
}

/// Decode one register-direct operation after REX, opcode and ModRM.
/// The first result register always comes from the ModRM r/m side:
/// destination for mov/add/sub/xor, left-hand side for cmp. Mirrors
/// `decodeRegReg`; length is always 3 (REX + opcode + ModRM).
fn decode_reg_reg(op: Byte, r_bit: u8, b_bit: u8, reg: u8, rm: u8) -> Option<Decodiert> {
    let rs = Register::from_code(r_bit * 8 + reg)?;
    let rd = Register::from_code(b_bit * 8 + rm)?;
    let befehl = match op {
        0x89 => Befehl::MovReg64 { dst: rd, src: rs },
        0x01 => Befehl::AddReg64 { dst: rd, src: rs },
        0x29 => Befehl::SubReg64 { dst: rd, src: rs },
        0x31 => Befehl::XorReg64 { dst: rd, src: rs },
        0x39 => Befehl::CmpReg64 { lhs: rd, rhs: rs },
        _ => return None,
    };
    Some(Decodiert::unvalidiert(befehl, 3))
}

/// Decode one base-plus-displacement access after REX, opcode and ModRM.
/// `rest` is the bytes strictly after the ModRM byte. Length 8 with the
/// SIB byte, 7 without; both refused when truncated. Mirrors `decodeMem`.
fn decode_mem(
    is_load: bool,
    r_bit: u8,
    b_bit: u8,
    reg: u8,
    rm: u8,
    rest: &[Byte],
) -> Option<Decodiert> {
    let (&b, tail) = rest.split_first()?;
    if rm == 4 {
        if b != 0x24 {
            return None;
        }
        let (d, _) = parse_le32(tail)?;
        let rr = Register::from_code(r_bit * 8 + reg)?;
        let rb = Register::from_code(b_bit * 8 + rm)?;
        let befehl = if is_load {
            Befehl::Load64 {
                dst: rr,
                base: rb,
                disp: Disp32::von_bits(d),
            }
        } else {
            Befehl::Store64 {
                base: rb,
                src: rr,
                disp: Disp32::von_bits(d),
            }
        };
        Some(Decodiert::unvalidiert(befehl, 8))
    } else {
        let (d, _) = parse_le32(rest)?;
        let rr = Register::from_code(r_bit * 8 + reg)?;
        let rb = Register::from_code(b_bit * 8 + rm)?;
        let befehl = if is_load {
            Befehl::Load64 {
                dst: rr,
                base: rb,
                disp: Disp32::von_bits(d),
            }
        } else {
            Befehl::Store64 {
                base: rb,
                src: rr,
                disp: Disp32::von_bits(d),
            }
        };
        Some(Decodiert::unvalidiert(befehl, 7))
    }
}

/// Dispatch on the ModRM mod field after REX and opcode. Only mod=3
/// (register-direct, five opcodes) and mod=2 (disp32, load/store only)
/// are canonical; every other mode refuses. Mirrors `decodeModrm`.
fn decode_modrm(r_bit: u8, b_bit: u8, op: Byte, rest: &[Byte]) -> Option<Decodiert> {
    let (&m, tail) = rest.split_first()?;
    let reg = (m / 8) % 8;
    let rm = m % 8;
    match m / 64 {
        3 => decode_reg_reg(op, r_bit, b_bit, reg, rm),
        2 => match op {
            0x89 => decode_mem(false, r_bit, b_bit, reg, rm, tail),
            0x8B => decode_mem(true, r_bit, b_bit, reg, rm, tail),
            _ => None,
        },
        _ => None,
    }
}

/// Decode after one canonical REX.W prefix (X=0). Mirrors `decodeRex`.
fn decode_rex(r_bit: u8, b_bit: u8, rest: &[Byte]) -> Option<Decodiert> {
    let (&op, tail) = rest.split_first()?;
    if (0xB8..0xC0).contains(&op) {
        let dst = Register::from_code(b_bit * 8 + (op - 0xB8))?;
        let (v, _) = parse_le64(tail)?;
        return Some(Decodiert::unvalidiert(Befehl::MovImm64 { dst, value: v }, 10));
    }
    match op {
        0x89 => decode_modrm(r_bit, b_bit, 0x89, tail),
        0x01 => decode_modrm(r_bit, b_bit, 0x01, tail),
        0x29 => decode_modrm(r_bit, b_bit, 0x29, tail),
        0x31 => decode_modrm(r_bit, b_bit, 0x31, tail),
        0x39 => decode_modrm(r_bit, b_bit, 0x39, tail),
        0x8B => decode_modrm(r_bit, b_bit, 0x8B, tail),
        _ => None,
    }
}

/// Decode the first canonical instruction, returning it with its consumed
/// length (`Decodiert::laenge`). Only canonical encodings are accepted;
/// anything else is refused with `None`. The remaining bytes are
/// `&bytes[decoded.laenge as usize..]`, exactly as the Lean `decode`'s
/// second return component. Mirrors `Codec.lean`'s `decode`.
pub fn decode(bytes: &[Byte]) -> Option<Decodiert> {
    let (&b0, rest) = bytes.split_first()?;
    match b0 {
        0xC3 => Some(Decodiert::unvalidiert(Befehl::Ret, 1)),
        0xE8 => {
            let (d, _) = parse_le32(rest)?;
            Some(Decodiert::unvalidiert(
                Befehl::Call32 {
                    disp: Disp32::von_bits(d),
                },
                5,
            ))
        }
        0xE9 => {
            let (d, _) = parse_le32(rest)?;
            Some(Decodiert::unvalidiert(
                Befehl::Jump32 {
                    disp: Disp32::von_bits(d),
                },
                5,
            ))
        }
        0x0F => {
            let (&c, rest2) = rest.split_first()?;
            if (0x80..0x90).contains(&c) {
                let cond = Bedingung::from_code(c - 0x80)?;
                let (d, _) = parse_le32(rest2)?;
                Some(Decodiert::unvalidiert(
                    Befehl::JumpIf32 {
                        cond,
                        disp: Disp32::von_bits(d),
                    },
                    6,
                ))
            } else {
                None
            }
        }
        0x41 => {
            let (&v, rest2) = rest.split_first()?;
            if (0x50..0x58).contains(&v) {
                let r = Register::from_code(v - 0x50 + 8)?;
                Some(Decodiert::unvalidiert(Befehl::Push64 { src: r }, 2))
            } else if (0x58..0x60).contains(&v) {
                let r = Register::from_code(v - 0x58 + 8)?;
                Some(Decodiert::unvalidiert(Befehl::Pop64 { dst: r }, 2))
            } else {
                let _ = rest2;
                None
            }
        }
        0x48 => decode_rex(0, 0, rest),
        0x49 => decode_rex(0, 1, rest),
        0x4C => decode_rex(1, 0, rest),
        0x4D => decode_rex(1, 1, rest),
        n if (0x50..0x58).contains(&n) => {
            let r = Register::from_code(n - 0x50)?;
            Some(Decodiert::unvalidiert(Befehl::Push64 { src: r }, 1))
        }
        n if (0x58..0x60).contains(&n) => {
            let r = Register::from_code(n - 0x58)?;
            Some(Decodiert::unvalidiert(Befehl::Pop64 { dst: r }, 1))
        }
        _ => None,
    }
}

#[cfg(test)]
mod proben {
    use super::*;
    use crate::x86::typen::Register::*;

    /// Round trip: encoding then decoding reproduces the instruction and
    /// its exact byte length, over a trailing suffix (mirrors `roundtrip`).
    fn roundtrip_ok(b: Befehl, suffix: &[Byte]) {
        let enc = encode(&b);
        let mut full = enc.clone();
        full.extend_from_slice(suffix);
        let d = decode(&full).expect("decode must accept its own encoding");
        assert_eq!(d.befehl, b, "decoded instruction must match");
        assert_eq!(d.laenge as usize, enc.len(), "consumed length must match");
    }

    #[test]
    fn ret_rundreise() {
        roundtrip_ok(Befehl::Ret, &[]);
        roundtrip_ok(Befehl::Ret, &[0xAA, 0xBB]);
    }

    #[test]
    fn alle_register_movreg64_rundreise() {
        for &dst in Register::ALLE.iter() {
            for &src in Register::ALLE.iter() {
                roundtrip_ok(Befehl::MovReg64 { dst, src }, &[0x90]);
                roundtrip_ok(Befehl::AddReg64 { dst, src }, &[]);
                roundtrip_ok(Befehl::SubReg64 { dst, src }, &[]);
                roundtrip_ok(Befehl::XorReg64 { dst, src }, &[]);
                roundtrip_ok(Befehl::CmpReg64 { lhs: dst, rhs: src }, &[]);
            }
        }
    }

    #[test]
    fn alle_register_movimm64_rundreise() {
        let werte: [Wort; 6] = [
            0,
            1,
            u64::MAX,
            0x7fff_ffff_ffff_ffff,
            0x8000_0000_0000_0000,
            0x0102_0304_0506_0708,
        ];
        for &dst in Register::ALLE.iter() {
            for &v in werte.iter() {
                roundtrip_ok(Befehl::MovImm64 { dst, value: v }, &[]);
            }
        }
    }

    #[test]
    fn alle_bedingungen_jumpif32_rundreise() {
        let disps: [i32; 5] = [0, 1, -1, i32::MAX, i32::MIN];
        for &cond in Bedingung::ALLE.iter() {
            for &dv in disps.iter() {
                roundtrip_ok(
                    Befehl::JumpIf32 {
                        cond,
                        disp: Disp32::von_signed(dv),
                    },
                    &[],
                );
            }
        }
    }

    #[test]
    fn verschiebungs_kanten_jump_call_rundreise() {
        let disps: [i32; 5] = [0, 1, -1, i32::MAX, i32::MIN];
        for &dv in disps.iter() {
            roundtrip_ok(
                Befehl::Jump32 {
                    disp: Disp32::von_signed(dv),
                },
                &[],
            );
            roundtrip_ok(
                Befehl::Call32 {
                    disp: Disp32::von_signed(dv),
                },
                &[],
            );
        }
    }

    #[test]
    fn load_store_alle_basen_rundreise() {
        let disps: [i32; 5] = [0, 1, -1, i32::MAX, i32::MIN];
        for &dst in Register::ALLE.iter() {
            for &base in Register::ALLE.iter() {
                for &dv in disps.iter() {
                    roundtrip_ok(
                        Befehl::Load64 {
                            dst,
                            base,
                            disp: Disp32::von_signed(dv),
                        },
                        &[],
                    );
                    roundtrip_ok(
                        Befehl::Store64 {
                            base,
                            src: dst,
                            disp: Disp32::von_signed(dv),
                        },
                        &[],
                    );
                }
            }
        }
    }

    #[test]
    fn push_pop_alle_register_rundreise() {
        for &r in Register::ALLE.iter() {
            roundtrip_ok(Befehl::Push64 { src: r }, &[]);
            roundtrip_ok(Befehl::Pop64 { dst: r }, &[]);
        }
    }

    // --- Refusals: every one mirrors a `decode_nichts_*`/`pin_*` theorem
    // in `Codec.lean` by exact byte pattern. ---

    #[test]
    fn leere_eingabe_wird_abgewiesen() {
        assert_eq!(decode(&[]), None);
    }

    #[test]
    fn einsamer_rex_wird_abgewiesen() {
        assert_eq!(decode(&[0x48]), None);
    }

    #[test]
    fn sprung_mit_kurzer_verschiebung_wird_abgewiesen() {
        assert_eq!(decode(&[0xE9, 0x01]), None);
    }

    #[test]
    fn einsames_zweibyte_praefix_wird_abgewiesen() {
        assert_eq!(decode(&[0x0F]), None);
    }

    #[test]
    fn einsames_erweiterungs_praefix_wird_abgewiesen() {
        assert_eq!(decode(&[0x41]), None);
    }

    #[test]
    fn unbekannter_opcode_wird_abgewiesen() {
        assert_eq!(decode(&[0xFF]), None);
    }

    #[test]
    fn rex_mit_x_bit_wird_abgewiesen() {
        // REX byte 0x4A has X set; not a canonical prefix (72/73/76/77 only).
        assert_eq!(decode(&[0x4A, 0x89, 0xC0]), None);
    }

    #[test]
    fn registerzug_ohne_rex_wird_abgewiesen() {
        assert_eq!(decode(&[0x89, 0xC0]), None);
    }

    #[test]
    fn modus_null_wird_abgewiesen() {
        assert_eq!(decode(&[0x48, 0x89, 0x00]), None);
    }

    #[test]
    fn registerdirekte_last_wird_abgewiesen() {
        // Loads use mod=2, never mod=3 (register-direct).
        assert_eq!(decode(&[0x48, 0x8B, 0xC0]), None);
    }

    #[test]
    fn falsches_sib_byte_wird_abgewiesen() {
        assert_eq!(
            decode(&[0x48, 0x8B, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]),
            None
        );
    }

    #[test]
    fn sib_mit_kurzer_verschiebung_wird_abgewiesen() {
        assert_eq!(decode(&[0x48, 0x8B, 0x84, 0x24]), None);
    }

    #[test]
    fn kurzsprung_wird_abgewiesen() {
        assert_eq!(decode(&[0xEB, 0x00]), None);
    }

    #[test]
    fn operandengroessen_praefix_wird_abgewiesen() {
        assert_eq!(decode(&[0x66, 0xC3]), None);
    }

    #[test]
    fn zweites_byte_ohne_sprung_wird_abgewiesen() {
        assert_eq!(
            decode(&[0x0F, 0x90, 0x00, 0x00, 0x00, 0x00]),
            None
        );
    }

    // --- Pinned bytes, matching `Codec.lean`'s `pin_*` theorems exactly. ---

    #[test]
    fn pin_movimm64_r8() {
        let enc = encode(&Befehl::MovImm64 {
            dst: R8,
            value: 0x0102030405060708,
        });
        assert_eq!(
            enc,
            vec![0x49, 0xB8, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]
        );
        let d = decode(&enc).unwrap();
        assert_eq!(
            d.befehl,
            Befehl::MovImm64 {
                dst: R8,
                value: 0x0102030405060708
            }
        );
        assert_eq!(d.laenge, 10);
    }

    #[test]
    fn pin_addreg64_erweitert() {
        let enc = encode(&Befehl::AddReg64 { dst: R9, src: R15 });
        assert_eq!(enc, vec![0x4D, 0x01, 0xF9]);
        let d = decode(&enc).unwrap();
        assert_eq!(d.befehl, Befehl::AddReg64 { dst: R9, src: R15 });
        assert_eq!(d.laenge, 3);
    }

    #[test]
    fn pin_load64_rsp() {
        let enc = encode(&Befehl::Load64 {
            dst: Rax,
            base: Rsp,
            disp: Disp32::von_signed(16),
        });
        assert_eq!(
            enc,
            vec![0x48, 0x8B, 0x84, 0x24, 0x10, 0x00, 0x00, 0x00]
        );
        let d = decode(&enc).unwrap();
        assert_eq!(
            d.befehl,
            Befehl::Load64 {
                dst: Rax,
                base: Rsp,
                disp: Disp32::von_signed(16)
            }
        );
        assert_eq!(d.laenge, 8);
    }

    #[test]
    fn pin_store64_r12() {
        let enc = encode(&Befehl::Store64 {
            base: R12,
            src: Rdx,
            disp: Disp32::von_signed(0),
        });
        assert_eq!(
            enc,
            vec![0x49, 0x89, 0x94, 0x24, 0x00, 0x00, 0x00, 0x00]
        );
        let d = decode(&enc).unwrap();
        assert_eq!(
            d.befehl,
            Befehl::Store64 {
                base: R12,
                src: Rdx,
                disp: Disp32::von_signed(0)
            }
        );
        assert_eq!(d.laenge, 8);
    }

    #[test]
    fn pin_load64_rbp() {
        // rbp is a real base and never SIB/RIP-relative.
        let enc = encode(&Befehl::Load64 {
            dst: Rcx,
            base: Rbp,
            disp: Disp32::von_signed(0),
        });
        assert_eq!(enc, vec![0x48, 0x8B, 0x8D, 0x00, 0x00, 0x00, 0x00]);
        let d = decode(&enc).unwrap();
        assert_eq!(
            d.befehl,
            Befehl::Load64 {
                dst: Rcx,
                base: Rbp,
                disp: Disp32::von_signed(0)
            }
        );
        assert_eq!(d.laenge, 7);
    }

    #[test]
    fn pin_store64_r13() {
        let enc = encode(&Befehl::Store64 {
            base: R13,
            src: R8,
            disp: Disp32::von_signed(1),
        });
        assert_eq!(enc, vec![0x4D, 0x89, 0x85, 0x01, 0x00, 0x00, 0x00]);
        let d = decode(&enc).unwrap();
        assert_eq!(
            d.befehl,
            Befehl::Store64 {
                base: R13,
                src: R8,
                disp: Disp32::von_signed(1)
            }
        );
        assert_eq!(d.laenge, 7);
    }

    #[test]
    fn pin_jump32_negativ() {
        let enc = encode(&Befehl::Jump32 {
            disp: Disp32::von_signed(-5),
        });
        assert_eq!(enc, vec![0xE9, 0xFB, 0xFF, 0xFF, 0xFF]);
        let d = decode(&enc).unwrap();
        assert_eq!(
            d.befehl,
            Befehl::Jump32 {
                disp: Disp32::von_signed(-5)
            }
        );
        assert_eq!(d.laenge, 5);
    }

    #[test]
    fn pin_push64_r8() {
        let enc = encode(&Befehl::Push64 { src: R8 });
        assert_eq!(enc, vec![0x41, 0x50]);
        let d = decode(&enc).unwrap();
        assert_eq!(d.befehl, Befehl::Push64 { src: R8 });
        assert_eq!(d.laenge, 2);
    }

    #[test]
    fn pin_pop64_r15() {
        let enc = encode(&Befehl::Pop64 { dst: R15 });
        assert_eq!(enc, vec![0x41, 0x5F]);
        let d = decode(&enc).unwrap();
        assert_eq!(d.befehl, Befehl::Pop64 { dst: R15 });
        assert_eq!(d.laenge, 2);
    }

    #[test]
    fn pin_ret() {
        let enc = encode(&Befehl::Ret);
        assert_eq!(enc, vec![0xC3]);
        let d = decode(&enc).unwrap();
        assert_eq!(d.befehl, Befehl::Ret);
        assert_eq!(d.laenge, 1);
    }

    /// Every canonical encoding is between 1 and 15 bytes. Mirrors
    /// `Codec.lean`'s `encode_len`.
    #[test]
    fn laenge_zwischen_eins_und_fuenfzehn() {
        let disps: [i32; 3] = [0, 1, -1];
        let mut all: Vec<Befehl> = Vec::new();
        for &dst in Register::ALLE.iter() {
            for &src in Register::ALLE.iter() {
                all.push(Befehl::MovReg64 { dst, src });
                all.push(Befehl::AddReg64 { dst, src });
                all.push(Befehl::SubReg64 { dst, src });
                all.push(Befehl::XorReg64 { dst, src });
                all.push(Befehl::CmpReg64 { lhs: dst, rhs: src });
                for &dv in disps.iter() {
                    all.push(Befehl::Load64 {
                        dst,
                        base: src,
                        disp: Disp32::von_signed(dv),
                    });
                    all.push(Befehl::Store64 {
                        base: src,
                        src: dst,
                        disp: Disp32::von_signed(dv),
                    });
                }
            }
            all.push(Befehl::MovImm64 { dst, value: 0 });
            all.push(Befehl::Push64 { src: dst });
            all.push(Befehl::Pop64 { dst });
        }
        all.push(Befehl::Ret);
        for b in all {
            let len = encode(&b).len();
            assert!((1..=15).contains(&len), "{:?} has length {}", b, len);
        }
    }
}
