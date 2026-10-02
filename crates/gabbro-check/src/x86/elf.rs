//! **A minimal ELF64 container for the pipeline image (`pipeline::Bild`).**
//!
//! `grammatik/Grammatik/X86/Bild.lean` models an ELF-like image: exact file
//! bytes, sections mapping a file range to a virtual range with read/write/
//! execute permissions and an alignment, an entry vector and a fixed load
//! mode. This file writes that image as a static ELF64 executable file
//! layout -- one `PT_LOAD` program header per `Abschnitt`, in order, the
//! image file bytes behind the headers, `e_entry` the first entry -- and
//! reads it back ([`lies_elf`]), so the container round-trips to the very
//! `Bild` the Lean `imageOk` judged.
//!
//! ## CUTS (exactly what is NOT claimed)
//!
//! * **Not a loader claim.** The Lean image check speaks about
//!   `Bild.geladen`, a BYTE-granular loader. An operating-system loader maps
//!   PAGE-granular segments and needs `p_offset ≡ p_vaddr (mod page)`;
//!   the pilot images (10-byte stubs at a 16-byte stride, a non-executable
//!   stop byte right behind the code) violate both, so under such a loader
//!   the permissions of neighbouring bytes would differ from the checked
//!   image. [`seitentreu`] decides whether a file is page-faithful; no
//!   current pipeline image is, and nothing here pretends otherwise.
//! * No section headers, no symbols, no dynamic linking, no interpreter,
//!   no relocations (the builder never produces any), no OS ABI note.
//!   The OS/ABI byte is `ELFOSABI_NONE`; nothing in the file names an
//!   operating system.
//! * Nothing was executed: the file is never run on this machine.
//! * The extra entry (`eintraege[1]`, the code start behind the entry
//!   sequence) has no ELF field and is not carried; [`lies_elf`] restores
//!   only `e_entry`, so the round trip is exact for the file bytes and
//!   sections and for the FIRST entry.

use super::pipeline::{Abschnitt, Bild};
use super::typen::Byte;

const EHDR: usize = 64;
const PHDR: usize = 56;
const PT_LOAD: u32 = 1;
const PF_X: u32 = 1;
const PF_W: u32 = 2;
const PF_R: u32 = 4;

/// Why an image has no ELF64 form.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ElfFehler {
    /// A field does not fit its 64-bit (or 16-bit count) ELF field.
    ZuGross,
    /// The image lists no entry.
    KeinEintrag,
    /// The alignment is not 0, 1 or a power of two (ELF demands it).
    Ausrichtung,
    /// A section's file range leaves the image file bytes.
    Dateibereich,
}

/// Where the image file bytes start in the ELF file: behind the headers,
/// rounded up to 16.
pub fn daten_start(n_abschnitte: usize) -> usize {
    (EHDR + PHDR * n_abschnitte).div_ceil(16) * 16
}

fn u64_von(x: u128) -> Result<u64, ElfFehler> {
    u64::try_from(x).map_err(|_| ElfFehler::ZuGross)
}

/// Serialise the image as an ELF64 file (little endian, x86-64, `ET_EXEC`).
pub fn schreibe_elf(b: &Bild) -> Result<Vec<Byte>, ElfFehler> {
    let n = b.abschnitte.len();
    let phnum = u16::try_from(n).map_err(|_| ElfFehler::ZuGross)?;
    let start = daten_start(n);
    let eintrag = u64_von(*b.eintraege.first().ok_or(ElfFehler::KeinEintrag)?)?;
    let mut out = Vec::with_capacity(start + b.datei.len());
    // e_ident: magic, ELFCLASS64, ELFDATA2LSB, EV_CURRENT, ELFOSABI_NONE.
    out.extend_from_slice(&[0x7F, b'E', b'L', b'F', 2, 1, 1, 0]);
    out.extend_from_slice(&[0; 8]);
    out.extend_from_slice(&2u16.to_le_bytes()); // e_type ET_EXEC
    out.extend_from_slice(&62u16.to_le_bytes()); // e_machine EM_X86_64
    out.extend_from_slice(&1u32.to_le_bytes()); // e_version
    out.extend_from_slice(&eintrag.to_le_bytes()); // e_entry
    out.extend_from_slice(&(EHDR as u64).to_le_bytes()); // e_phoff
    out.extend_from_slice(&0u64.to_le_bytes()); // e_shoff
    out.extend_from_slice(&0u32.to_le_bytes()); // e_flags
    out.extend_from_slice(&(EHDR as u16).to_le_bytes()); // e_ehsize
    out.extend_from_slice(&(PHDR as u16).to_le_bytes()); // e_phentsize
    out.extend_from_slice(&phnum.to_le_bytes()); // e_phnum
    out.extend_from_slice(&64u16.to_le_bytes()); // e_shentsize
    out.extend_from_slice(&0u16.to_le_bytes()); // e_shnum
    out.extend_from_slice(&0u16.to_le_bytes()); // e_shstrndx
    for s in &b.abschnitte {
        let ende = s
            .datei_off
            .checked_add(s.datei_len)
            .ok_or(ElfFehler::ZuGross)?;
        if ende > b.datei.len() as u128 {
            return Err(ElfFehler::Dateibereich);
        }
        if s.ausr > 1 && !s.ausr.is_power_of_two() {
            return Err(ElfFehler::Ausrichtung);
        }
        let flags = (if s.lesbar { PF_R } else { 0 })
            | (if s.schreibbar { PF_W } else { 0 })
            | (if s.ausfuehrbar { PF_X } else { 0 });
        out.extend_from_slice(&PT_LOAD.to_le_bytes());
        out.extend_from_slice(&flags.to_le_bytes());
        out.extend_from_slice(&u64_von(s.datei_off + start as u128)?.to_le_bytes());
        out.extend_from_slice(&u64_von(s.vaddr)?.to_le_bytes()); // p_vaddr
        out.extend_from_slice(&u64_von(s.vaddr)?.to_le_bytes()); // p_paddr
        out.extend_from_slice(&u64_von(s.datei_len)?.to_le_bytes());
        out.extend_from_slice(&u64_von(s.mem_len)?.to_le_bytes());
        out.extend_from_slice(&u64_von(s.ausr)?.to_le_bytes());
    }
    out.resize(start, 0);
    out.extend_from_slice(&b.datei);
    Ok(out)
}

fn lies_u16(d: &[Byte], o: usize) -> Option<u16> {
    Some(u16::from_le_bytes(d.get(o..o + 2)?.try_into().ok()?))
}
fn lies_u32(d: &[Byte], o: usize) -> Option<u32> {
    Some(u32::from_le_bytes(d.get(o..o + 4)?.try_into().ok()?))
}
fn lies_u64(d: &[Byte], o: usize) -> Option<u64> {
    Some(u64::from_le_bytes(d.get(o..o + 8)?.try_into().ok()?))
}

/// Read a file written by [`schreibe_elf`] back to the image (file bytes,
/// sections, first entry). `None` on anything this writer does not produce.
pub fn lies_elf(d: &[Byte]) -> Option<Bild> {
    if d.get(..8)? != [0x7F, b'E', b'L', b'F', 2, 1, 1, 0] {
        return None;
    }
    if lies_u16(d, 16)? != 2 || lies_u16(d, 18)? != 62 || lies_u64(d, 32)? != EHDR as u64 {
        return None;
    }
    let n = usize::from(lies_u16(d, 56)?);
    if usize::from(lies_u16(d, 54)?) != PHDR {
        return None;
    }
    let start = daten_start(n);
    let datei = d.get(start..)?.to_vec();
    let mut abschnitte = Vec::with_capacity(n);
    for i in 0..n {
        let o = EHDR + PHDR * i;
        if lies_u32(d, o)? != PT_LOAD {
            return None;
        }
        let flags = lies_u32(d, o + 4)?;
        let off = u128::from(lies_u64(d, o + 8)?).checked_sub(start as u128)?;
        abschnitte.push(Abschnitt {
            datei_off: off,
            datei_len: u128::from(lies_u64(d, o + 32)?),
            vaddr: u128::from(lies_u64(d, o + 16)?),
            mem_len: u128::from(lies_u64(d, o + 40)?),
            lesbar: flags & PF_R != 0,
            schreibbar: flags & PF_W != 0,
            ausfuehrbar: flags & PF_X != 0,
            ausr: u128::from(lies_u64(d, o + 48)?),
        });
    }
    Some(Bild {
        datei,
        abschnitte,
        eintraege: vec![u128::from(lies_u64(d, 24)?)],
    })
}

/// Is the file page-faithful for a page-granular loader with page size
/// `seite`: every segment's file offset congruent to its address, and no
/// two segments with different permissions sharing a page? (The checked
/// pipeline images are not; see the CUTS.)
pub fn seitentreu(b: &Bild, seite: u128) -> bool {
    let start = daten_start(b.abschnitte.len()) as u128;
    let kongruent = b
        .abschnitte
        .iter()
        .all(|s| (s.datei_off + start) % seite == s.vaddr % seite);
    let seiten = |s: &Abschnitt| (s.vaddr / seite, (s.vaddr + s.mem_len.max(1) - 1) / seite);
    let rechte = |s: &Abschnitt| (s.lesbar, s.schreibbar, s.ausfuehrbar);
    let getrennt = b.abschnitte.iter().enumerate().all(|(i, a)| {
        b.abschnitte[i + 1..].iter().all(|c| {
            let ((a0, a1), (c0, c1)) = (seiten(a), seiten(c));
            rechte(a) == rechte(c) || a1 < c0 || c1 < a0
        })
    });
    kongruent && getrennt
}

#[cfg(test)]
mod proben {
    use super::super::pipeline::proben::{pi_es, pi_ps, pw_cfg, pw_ctx, pw_decl, pw_src, pw_welt};
    use super::super::pipeline::*;
    use super::*;

    fn bild() -> Bild {
        let c = PipeCfg {
            exit_stride: 16,
            ..pw_cfg()
        };
        let p = Program {
            decl: pw_decl(),
            ctx: pw_ctx(),
            block: pw_src(0),
            certs: None,
            placements: pi_ps(),
            welt: pw_welt(),
            extents: pi_es(),
            profil: Profil::P48,
            abi: None,
        };
        compile_to_image(&p, &c).unwrap().bild
    }

    #[test]
    fn the_container_round_trips() {
        let b = bild();
        let f = schreibe_elf(&b).unwrap();
        assert_eq!(&f[..4], &[0x7F, b'E', b'L', b'F']);
        assert_eq!(f.len(), daten_start(b.abschnitte.len()) + b.datei.len());
        let zurueck = lies_elf(&f).unwrap();
        assert_eq!(zurueck.datei, b.datei);
        assert_eq!(zurueck.abschnitte, b.abschnitte);
        assert_eq!(zurueck.eintraege, vec![b.eintraege[0]]);
    }

    #[test]
    fn the_headers_carry_the_permissions() {
        let b = bild();
        let f = schreibe_elf(&b).unwrap();
        // Code: R+X, stub: R+X, data: R+W.
        assert_eq!(lies_u32(&f, EHDR + 4), Some(PF_R | PF_X));
        assert_eq!(lies_u32(&f, EHDR + PHDR + 4), Some(PF_R | PF_X));
        assert_eq!(lies_u32(&f, EHDR + 2 * PHDR + 4), Some(PF_R | PF_W));
        assert_eq!(lies_u64(&f, 24), Some(4096));
    }

    #[test]
    fn pilot_images_are_not_page_faithful() {
        assert!(!seitentreu(&bild(), 4096));
    }

    #[test]
    fn malformed_images_are_refused() {
        let mut b = bild();
        b.eintraege.clear();
        assert_eq!(schreibe_elf(&b), Err(ElfFehler::KeinEintrag));
        let mut b = bild();
        b.abschnitte[0].ausr = 3;
        assert_eq!(schreibe_elf(&b), Err(ElfFehler::Ausrichtung));
        let mut b = bild();
        b.abschnitte[0].datei_len += 10_000;
        assert_eq!(schreibe_elf(&b), Err(ElfFehler::Dateibereich));
        let mut b = bild();
        b.abschnitte[0].vaddr = 1u128 << 64;
        assert_eq!(schreibe_elf(&b), Err(ElfFehler::ZuGross));
        assert_eq!(lies_elf(&[0; 10]), None);
    }
}
