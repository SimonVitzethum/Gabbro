//! **The direct-x86 pilot vocabulary, as Rust data (wave A, lane 273).**
//!
//! A safe, dependency-free mirror of the canonical
//! `grammatik/Grammatik/X86/Typen.lean` (`Gabbro.Grammatik.X86`): machine
//! words, the 16 registers in architectural encoding order, widths,
//! conditions, flags, sparse byte memory with explicit permissions, machine
//! state, the pilot `Befehl` set and `Decodiert`.
//!
//! ## What this is NOT
//!
//! * **Representation fidelity is UNPROVED.** No machine-checked
//!   Rust-to-Lean correspondence exists yet; the field-by-field mapping to
//!   `Typen.lean` is by inspection only and is owned by a later wave.
//! * **Generic instruction DATA only.** No encoder, no decoder, no
//!   round-trip claim, no instruction semantics, no flag computation, no
//!   permission-checked load/store, no TSO bridge, no source correspondence,
//!   no ABI/image coverage. Length in `Decodiert` is carried data, never a
//!   validated claim (validated decoding owns length).
//! * **Unwired foundation.** Nothing in the checker, the emitter or any CLI
//!   reads this module yet. Existing C behaviour is unchanged.
//! * **Sparse maps are partial.** Lean models memory and permissions as total
//!   functions; `Speicher` here is a finite sparse map. An absent address has
//!   NO byte (reads answer `None`) and is treated as not permitted. That
//!   difference is a coverage gap, not a semantics.
//! * **Displacements are BITS with explicit signed reading.** Every 32-bit
//!   displacement is stored as `u32`; the signed interpretation (`i32`,
//!   sign-extended `i64`) is computed by the named helpers only, never by a
//!   silent cast at a use site.

use std::collections::{BTreeMap, BTreeSet};

/// A machine byte. Canonical `Byte` is `BitVec 8`.
pub type Byte = u8;
/// A 64-bit machine word. Canonical `Wort` is `BitVec 64`.
pub type Wort = u64;
/// A 64-bit address. Canonical `Adresse` is `BitVec 64`.
pub type Adresse = u64;

/// The 16 general registers in architectural encoding order.
///
/// Order is fixed by the canonical `Register` enum and matches the x86-64
/// ModRM/SIB encoding: `rax = 0, rcx = 1, rdx = 2, rbx = 3, rsp = 4,
/// rbp = 5, rsi = 6, rdi = 7, r8 = 8 .. r15 = 15`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Register {
    Rax = 0,
    Rcx = 1,
    Rdx = 2,
    Rbx = 3,
    Rsp = 4,
    Rbp = 5,
    Rsi = 6,
    Rdi = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
}

impl Register {
    /// All registers in encoding order.
    pub const ALLE: [Register; 16] = [
        Register::Rax,
        Register::Rcx,
        Register::Rdx,
        Register::Rbx,
        Register::Rsp,
        Register::Rbp,
        Register::Rsi,
        Register::Rdi,
        Register::R8,
        Register::R9,
        Register::R10,
        Register::R11,
        Register::R12,
        Register::R13,
        Register::R14,
        Register::R15,
    ];

    /// The architectural encoding number (0..16).
    pub fn code(self) -> u8 {
        self as u8
    }

    /// Checked conversion from an encoding number. Refuses anything above 15.
    pub fn from_code(code: u8) -> Option<Register> {
        match code {
            0 => Some(Register::Rax),
            1 => Some(Register::Rcx),
            2 => Some(Register::Rdx),
            3 => Some(Register::Rbx),
            4 => Some(Register::Rsp),
            5 => Some(Register::Rbp),
            6 => Some(Register::Rsi),
            7 => Some(Register::Rdi),
            8 => Some(Register::R8),
            9 => Some(Register::R9),
            10 => Some(Register::R10),
            11 => Some(Register::R11),
            12 => Some(Register::R12),
            13 => Some(Register::R13),
            14 => Some(Register::R14),
            15 => Some(Register::R15),
            _ => None,
        }
    }

    /// The canonical assembly spelling.
    pub fn name(self) -> &'static str {
        match self {
            Register::Rax => "rax",
            Register::Rcx => "rcx",
            Register::Rdx => "rdx",
            Register::Rbx => "rbx",
            Register::Rsp => "rsp",
            Register::Rbp => "rbp",
            Register::Rsi => "rsi",
            Register::Rdi => "rdi",
            Register::R8 => "r8",
            Register::R9 => "r9",
            Register::R10 => "r10",
            Register::R11 => "r11",
            Register::R12 => "r12",
            Register::R13 => "r13",
            Register::R14 => "r14",
            Register::R15 => "r15",
        }
    }
}

/// Operand width. Canonical `Breite` with `bits` 8/16/32/64.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Breite {
    B8,
    B16,
    B32,
    B64,
}

impl Breite {
    /// Width in bits.
    pub fn bits(self) -> u32 {
        match self {
            Breite::B8 => 8,
            Breite::B16 => 16,
            Breite::B32 => 32,
            Breite::B64 => 64,
        }
    }

    /// Width in bytes. Always positive, at most 8 (cf. `breite_bytes`).
    pub fn bytes(self) -> u32 {
        self.bits() / 8
    }

    /// Low-bit mask for the width (`0xff`, `0xffff`, `0xffffffff`, `u64::MAX`).
    pub fn mask(self) -> u64 {
        match self {
            Breite::B8 => 0xff,
            Breite::B16 => 0xffff,
            Breite::B32 => 0xffff_ffff,
            Breite::B64 => u64::MAX,
        }
    }

    /// Truncate a word to this width (low bits kept, modular semantics).
    pub fn truncate(self, wort: u64) -> u64 {
        wort & self.mask()
    }
}

/// Branch conditions in architectural condition-code order.
///
/// Order is fixed by the canonical `Bedingung` enum and matches the Intel
/// condition-code numbers: `o = 0, no = 1, b = 2, ae = 3, e = 4, ne = 5,
/// be = 6, a = 7, s = 8, ns = 9, p = 10, np = 11, l = 12, ge = 13,
/// le = 14, g = 15`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Bedingung {
    O = 0,
    No = 1,
    B = 2,
    Ae = 3,
    E = 4,
    Ne = 5,
    Be = 6,
    A = 7,
    S = 8,
    Ns = 9,
    P = 10,
    Np = 11,
    L = 12,
    Ge = 13,
    Le = 14,
    G = 15,
}

impl Bedingung {
    /// All conditions in code order.
    pub const ALLE: [Bedingung; 16] = [
        Bedingung::O,
        Bedingung::No,
        Bedingung::B,
        Bedingung::Ae,
        Bedingung::E,
        Bedingung::Ne,
        Bedingung::Be,
        Bedingung::A,
        Bedingung::S,
        Bedingung::Ns,
        Bedingung::P,
        Bedingung::Np,
        Bedingung::L,
        Bedingung::Ge,
        Bedingung::Le,
        Bedingung::G,
    ];

    /// The architectural condition number (0..16).
    pub fn code(self) -> u8 {
        self as u8
    }

    /// Checked conversion from a condition number. Refuses anything above 15.
    pub fn from_code(code: u8) -> Option<Bedingung> {
        match code {
            0 => Some(Bedingung::O),
            1 => Some(Bedingung::No),
            2 => Some(Bedingung::B),
            3 => Some(Bedingung::Ae),
            4 => Some(Bedingung::E),
            5 => Some(Bedingung::Ne),
            6 => Some(Bedingung::Be),
            7 => Some(Bedingung::A),
            8 => Some(Bedingung::S),
            9 => Some(Bedingung::Ns),
            10 => Some(Bedingung::P),
            11 => Some(Bedingung::Np),
            12 => Some(Bedingung::L),
            13 => Some(Bedingung::Ge),
            14 => Some(Bedingung::Le),
            15 => Some(Bedingung::G),
            _ => None,
        }
    }
}

/// Machine flags. Canonical `Flags`; `af = None` is UNDEFINED, not false.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Flags {
    pub cf: bool,
    pub pf: bool,
    pub af: Option<bool>,
    pub zf: bool,
    pub sf: bool,
    pub of: bool,
}

impl Flags {
    /// Cleared flags with `af` undefined (the honest initial value).
    pub fn undefiniert_af() -> Flags {
        Flags {
            cf: false,
            pf: false,
            af: None,
            zf: false,
            sf: false,
            of: false,
        }
    }
}

/// A 32-bit displacement as raw BITS.
///
/// Canonical displacements are `BitVec 32` (signed). The bits travel as
/// `u32`; every signed reading goes through `signed`, `extended` or the
/// address helpers below. No silent `as i32` at a use site.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Disp32 {
    pub bits: u32,
}

impl Disp32 {
    /// Carry raw bits, no interpretation.
    pub fn von_bits(bits: u32) -> Disp32 {
        Disp32 { bits }
    }

    /// Wrap a signed value into its 32-bit pattern.
    pub fn von_signed(wert: i32) -> Disp32 {
        Disp32 {
            bits: wert as u32,
        }
    }

    /// The EXPLICIT signed interpretation (two's complement).
    pub fn signed(self) -> i32 {
        self.bits as i32
    }

    /// Sign-extended to 64 bits, as address arithmetic needs it.
    pub fn extended(self) -> i64 {
        self.signed() as i64
    }

    /// Effective address of `base + sign(disp)` with wrapping machine arithmetic.
    pub fn effektive_adresse(self, basis: u64) -> u64 {
        basis.wrapping_add(self.extended() as u64)
    }

    /// Branch/call target: the address AFTER the decoded instruction plus the
    /// sign-extended displacement (canonical relative-flow rule).
    pub fn sprungziel(self, folge_rip: u64) -> u64 {
        folge_rip.wrapping_add(self.extended() as u64)
    }
}

/// Sparse byte memory with explicit per-address permissions.
///
/// Finite counterpart of canonical `Speicher` (total byte contents plus
/// read/write/execute predicates). Absence is explicit: `byte_an` answers
/// `None` off-map, and every permission answers `false` off-set.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Speicher {
    pub bytes: BTreeMap<Adresse, Byte>,
    pub lesbar: BTreeSet<Adresse>,
    pub schreibbar: BTreeSet<Adresse>,
    pub ausfuehrbar: BTreeSet<Adresse>,
}

impl Speicher {
    /// Empty memory: nothing mapped, nothing permitted.
    pub fn leer() -> Speicher {
        Speicher::default()
    }

    /// The byte at an address, or `None` where nothing is mapped.
    pub fn byte_an(&self, adresse: Adresse) -> Option<Byte> {
        self.bytes.get(&adresse).copied()
    }

    /// Record one byte and its permissions.
    pub fn lege_ab(
        &mut self,
        adresse: Adresse,
        byte: Byte,
        lesbar: bool,
        schreibbar: bool,
        ausfuehrbar: bool,
    ) {
        self.bytes.insert(adresse, byte);
        if lesbar {
            self.lesbar.insert(adresse);
        }
        if schreibbar {
            self.schreibbar.insert(adresse);
        }
        if ausfuehrbar {
            self.ausfuehrbar.insert(adresse);
        }
    }

    /// Explicit permission reads. `false` off-set, never assumed.
    pub fn ist_lesbar(&self, adresse: Adresse) -> bool {
        self.lesbar.contains(&adresse)
    }

    /// Explicit permission reads. `false` off-set, never assumed.
    pub fn ist_schreibbar(&self, adresse: Adresse) -> bool {
        self.schreibbar.contains(&adresse)
    }

    /// Explicit permission reads. `false` off-set, never assumed.
    pub fn ist_ausfuehrbar(&self, adresse: Adresse) -> bool {
        self.ausfuehrbar.contains(&adresse)
    }
}

/// Machine state: register file, flags, instruction pointer, memory.
///
/// Counterpart of canonical `Zustand`. The register file is indexed by the
/// architectural `Register::code`; `Flags.af = None` stays undefined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Zustand {
    pub register: [Wort; 16],
    pub flags: Flags,
    pub rip: Adresse,
    pub speicher: Speicher,
}

impl Zustand {
    /// Zeroed registers, undefined `af`, given `rip`, empty memory.
    pub fn anfang(rip: Adresse) -> Zustand {
        Zustand {
            register: [0u64; 16],
            flags: Flags::undefiniert_af(),
            rip,
            speicher: Speicher::leer(),
        }
    }

    /// Read a register by its architectural name.
    pub fn lese(&self, reg: Register) -> Wort {
        self.register[reg.code() as usize]
    }

    /// Write a register by its architectural name.
    pub fn schreibe(&mut self, reg: Register, wert: Wort) {
        self.register[reg.code() as usize] = wert;
    }
}

/// The pilot instruction set. Canonical `Befehl`; displacements are raw
/// `u32` bits with signed reading through `Disp32`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Befehl {
    MovImm64 { dst: Register, value: Wort },
    MovReg64 { dst: Register, src: Register },
    AddReg64 { dst: Register, src: Register },
    SubReg64 { dst: Register, src: Register },
    XorReg64 { dst: Register, src: Register },
    CmpReg64 { lhs: Register, rhs: Register },
    Load64 {
        dst: Register,
        base: Register,
        disp: Disp32,
    },
    Store64 {
        base: Register,
        src: Register,
        disp: Disp32,
    },
    Jump32 { disp: Disp32 },
    JumpIf32 { cond: Bedingung, disp: Disp32 },
    Call32 { disp: Disp32 },
    Push64 { src: Register },
    Pop64 { dst: Register },
    Ret,
}

impl Befehl {
    /// The raw displacement bits carried by this instruction, if any.
    /// Generic data accessor only; control-flow meaning belongs to the
    /// execution lane, decoding validity to the decoder lane.
    pub fn disp_bits(self) -> Option<u32> {
        match self {
            Befehl::Load64 { disp, .. }
            | Befehl::Store64 { disp, .. }
            | Befehl::Jump32 { disp }
            | Befehl::Call32 { disp } => Some(disp.bits),
            Befehl::JumpIf32 { disp, .. } => Some(disp.bits),
            _ => None,
        }
    }
}

/// A decoded instruction: the instruction plus its byte length.
///
/// Carried data only. Length belongs to validated decoding, never to an
/// untrusted emitter annotation; constructing this value validates nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Decodiert {
    pub befehl: Befehl,
    pub laenge: u64,
}

impl Decodiert {
    /// Carry instruction and length without validating either.
    pub fn unvalidiert(befehl: Befehl, laenge: u64) -> Decodiert {
        Decodiert { befehl, laenge }
    }
}

#[cfg(test)]
mod proben {
    use super::*;

    #[test]
    fn register_tragen_die_architekturnummern() {
        // Hardcoded against the x86-64 encoding, not against our own table:
        // a wrong table that round-trips would still fail here.
        let erwartet = [
            (Register::Rax, 0u8),
            (Register::Rcx, 1u8),
            (Register::Rdx, 2u8),
            (Register::Rbx, 3u8),
            (Register::Rsp, 4u8),
            (Register::Rbp, 5u8),
            (Register::Rsi, 6u8),
            (Register::Rdi, 7u8),
            (Register::R8, 8u8),
            (Register::R9, 9u8),
            (Register::R10, 10u8),
            (Register::R11, 11u8),
            (Register::R12, 12u8),
            (Register::R13, 13u8),
            (Register::R14, 14u8),
            (Register::R15, 15u8),
        ];
        for (reg, code) in erwartet {
            assert_eq!(reg.code(), code, "register {}", reg.name());
            assert_eq!(
                Register::from_code(code),
                Some(reg),
                "from_code({code}) must return {}",
                reg.name()
            );
        }
    }

    #[test]
    fn register_weisen_ausserhalb_ab() {
        assert_eq!(Register::from_code(16), None);
        assert_eq!(Register::from_code(17), None);
        assert_eq!(Register::from_code(255), None);
        assert_eq!(Register::from_code(u8::MAX), None);
    }

    #[test]
    fn breiten_sind_bits_und_bytes() {
        // Hardcoded widths: a swapped row must fail, not round-trip.
        assert_eq!((Breite::B8.bits(), Breite::B8.bytes()), (8, 1));
        assert_eq!((Breite::B16.bits(), Breite::B16.bytes()), (16, 2));
        assert_eq!((Breite::B32.bits(), Breite::B32.bytes()), (32, 4));
        assert_eq!((Breite::B64.bits(), Breite::B64.bytes()), (64, 8));
        assert_eq!(Breite::B8.mask(), 0xffu64);
        assert_eq!(Breite::B16.mask(), 0xffffu64);
        assert_eq!(Breite::B32.mask(), 0xffff_ffffu64);
        assert_eq!(Breite::B64.mask(), u64::MAX);
        assert_eq!(Breite::B8.truncate(0x1ff), 0xff);
        assert_eq!(Breite::B32.truncate(0x1_0000_0001), 1);
        assert_eq!(Breite::B64.truncate(u64::MAX), u64::MAX);
    }

    #[test]
    fn bedingung_traegt_die_intel_nummern() {
        // Hardcoded against the Intel condition-code numbers.
        let erwartet = [
            (Bedingung::O, 0u8),
            (Bedingung::No, 1u8),
            (Bedingung::B, 2u8),
            (Bedingung::Ae, 3u8),
            (Bedingung::E, 4u8),
            (Bedingung::Ne, 5u8),
            (Bedingung::Be, 6u8),
            (Bedingung::A, 7u8),
            (Bedingung::S, 8u8),
            (Bedingung::Ns, 9u8),
            (Bedingung::P, 10u8),
            (Bedingung::Np, 11u8),
            (Bedingung::L, 12u8),
            (Bedingung::Ge, 13u8),
            (Bedingung::Le, 14u8),
            (Bedingung::G, 15u8),
        ];
        for (cond, code) in erwartet {
            assert_eq!(cond.code(), code);
            assert_eq!(Bedingung::from_code(code), Some(cond));
        }
    }

    #[test]
    fn bedingung_weist_ausserhalb_ab() {
        assert_eq!(Bedingung::from_code(16), None);
        assert_eq!(Bedingung::from_code(200), None);
        assert_eq!(Bedingung::from_code(255), None);
    }

    #[test]
    fn displacement_kanten_sind_vorzeichenbehaftet() {
        // Signed edges of the 32-bit two's complement range.
        assert_eq!(Disp32::von_bits(0x0000_0000).signed(), 0i32);
        assert_eq!(Disp32::von_bits(0x7fff_ffff).signed(), i32::MAX);
        assert_eq!(Disp32::von_bits(0x8000_0000).signed(), i32::MIN);
        assert_eq!(Disp32::von_bits(0xffff_ffff).signed(), -1i32);
        assert_eq!(Disp32::von_signed(-1).bits, 0xffff_ffff);
        assert_eq!(Disp32::von_signed(i32::MIN).bits, 0x8000_0000);
        assert_eq!(Disp32::von_bits(0xffff_ffff).extended(), -1i64);
        assert_eq!(
            Disp32::von_bits(0x8000_0000).extended(),
            -2_147_483_648i64
        );
    }

    #[test]
    fn relative_ziele_zaehlen_ab_folgeadresse() {
        // Relative flow uses the address AFTER the decoded instruction.
        let folge = 0x1000u64;
        assert_eq!(Disp32::von_bits(0).sprungziel(folge), 0x1000);
        assert_eq!(
            Disp32::von_signed(-2).sprungziel(folge),
            folge.wrapping_sub(2)
        );
        assert_eq!(
            Disp32::von_signed(i32::MIN).sprungziel(folge),
            folge.wrapping_add(0xffff_ffff_8000_0000u64)
        );
        // Base-plus-displacement addressing wraps like the machine.
        assert_eq!(Disp32::von_signed(-8).effektive_adresse(0x1000), 0xff8);
        assert_eq!(
            Disp32::von_bits(0xffff_ffff).effektive_adresse(0),
            u64::MAX
        );
    }

    #[test]
    fn befehlsdaten_tragen_bits_ohne_deutung() {
        let b = Befehl::Load64 {
            dst: Register::Rax,
            base: Register::Rbx,
            disp: Disp32::von_signed(-8),
        };
        assert_eq!(b.disp_bits(), Some(0xffff_fff8));
        let j = Befehl::JumpIf32 {
            cond: Bedingung::E,
            disp: Disp32::von_bits(0x10),
        };
        assert_eq!(j.disp_bits(), Some(0x10));
        assert_eq!(Befehl::Ret.disp_bits(), None);
        assert_eq!(
            Befehl::MovReg64 {
                dst: Register::Rax,
                src: Register::Rcx
            }
            .disp_bits(),
            None
        );
    }

    #[test]
    fn zustand_liest_und_schreibt_nach_nummer() {
        let mut z = Zustand::anfang(0x4000);
        z.schreibe(Register::Rax, 0xaa);
        z.schreibe(Register::R15, 0xbb);
        assert_eq!(z.lese(Register::Rax), 0xaa);
        assert_eq!(z.lese(Register::R15), 0xbb);
        assert_eq!(z.lese(Register::Rcx), 0);
        assert_eq!(z.flags.af, None, "af stays undefined, never false");
        // Sparse memory: absent means unmapped and unpermitted.
        assert_eq!(z.speicher.byte_an(0x4000), None);
        assert!(!z.speicher.ist_lesbar(0x4000));
        z.speicher.lege_ab(0x4000, 0x90, true, false, true);
        assert_eq!(z.speicher.byte_an(0x4000), Some(0x90));
        assert!(z.speicher.ist_lesbar(0x4000));
        assert!(!z.speicher.ist_schreibbar(0x4000));
        assert!(z.speicher.ist_ausfuehrbar(0x4000));
    }
}
