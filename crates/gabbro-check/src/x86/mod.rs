//! **The direct-x86 target vocabulary (wave A, lane 273).**
//!
//! Internal foundation for the direct x86-64 target, mirroring the canonical
//! `grammatik/Grammatik/X86/Typen.lean`. The actual vocabulary lives in
//! [`typen`]; this module only re-exports it and records the boundary.
//!
//! Unwired: no checker pass, no emitter template and no CLI reads this
//! module. No encoder/decoder and no semantics belong here; instruction-level
//! sequential helpers do not establish concurrent atomicity, and per-access
//! TSO correspondence remains a separate obligation (wave contract
//! `dokumente/x86/WELLE-A.md`). Rust-to-Lean representation fidelity is
//! unproved and marked at [`typen`].

pub mod opt;
pub mod typen;
pub mod codec;
#[cfg(test)]
mod codec_golden;
pub mod lower;
pub mod pipeline;

pub use typen::{
    Adresse, Bedingung, Befehl, Breite, Byte, Decodiert, Disp32, Flags, Register, Speicher, Wort,
    Zustand,
};
pub use codec::{decode, encode};
pub use lower::{int_wort, senk_assign, senk_frag, Atom, Fragment, LowerError};
pub use pipeline::{compile_to_image, Image, PipeCfg, Program, Refusal};

#[cfg(test)]
mod proben {
    use super::*;

    #[test]
    fn reexporte_tragen_dieselbe_bedeutung() {
        // The umbrella path and the inner path name one vocabulary.
        let r: Register = typen::Register::Rdi;
        assert_eq!(r.code(), 7u8);
        let c: Bedingung = typen::Bedingung::G;
        assert_eq!(c.code(), 15u8);
        assert_eq!(Breite::B64.bytes(), 8u32);
        let d = Decodiert::unvalidiert(Befehl::Ret, 1);
        assert_eq!(d.laenge, 1u64);
    }
}
