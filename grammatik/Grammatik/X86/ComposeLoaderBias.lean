/-
  Composition closing: loader-bias closing (lane 855).

  Producer/consumer interface closed here: the producers are the accepted
  `Bild` checked mapping (`wohlgeformt`, `geladen`, `abteilFinden`,
  `ladenByte`, `dateiByte`, `effBias`), the accepted relocation arithmetic
  (`rel32Passt`, `dispSigned`) and site checks (`RelocatedExecution`
  `PatchSite`, `siteStart`, `siteNext`, `patchSiteOk`, `patchSite_ziel`,
  `bildSite_ruf_dekode`, `fenster5`, `relocBytes`), and the accepted
  validator mapping check (`ValidatorSkeleton.transferOk`). Nothing is
  redefined here: no second loader, decoder, executor, ISA model or
  interpreter. The consumer is the layout validator and the image-coverage
  proof, which discharge one file-offset/virtual-address/bias/operand site
  by `ComposeLoaderBias_verbindung` and refuse bad displacements or
  unlisted targets by `loaderBias_disp_aussen` / `loaderBias_loch_verweigert`.
-/
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt
import Grammatik.X86.LoadedExecution
import Grammatik.X86.Relokation
import Grammatik.X86.RelocatedExecution
import Grammatik.X86.ValidatorSkeleton

namespace Gabbro.Grammatik.X86

/-- The one checked loader-bias closing step: the final image mapping AND
    the relocation-operand site check AND the executed-target mapping
    check, re-decided from the carried values. File offsets never become
    virtual addresses directly: the site start is always
    `bias + vaddr + off`. -/
def loaderBiasOk (p : Profil) (bild : Bild) (bias : Nat)
    (site : PatchSite) : Bool :=
  wohlgeformt p bild && patchSiteOk site && transferOk bild bias site.ziel

/-- The closing step implies the checked final-image mapping. -/
theorem loaderBiasOk_wohlgeformt (p : Profil) (bild : Bild) (bias : Nat)
    (site : PatchSite) (h : loaderBiasOk p bild bias site = true) :
    wohlgeformt p bild = true := by
  unfold loaderBiasOk at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

/-- The closing step implies the relocation-operand site check. -/
theorem loaderBiasOk_site (p : Profil) (bild : Bild) (bias : Nat)
    (site : PatchSite) (h : loaderBiasOk p bild bias site = true) :
    patchSiteOk site = true := by
  unfold loaderBiasOk at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

/-- The closing step implies the executed-target mapping check. -/
theorem loaderBiasOk_transfer (p : Profil) (bild : Bild) (bias : Nat)
    (site : PatchSite) (h : loaderBiasOk p bild bias site = true) :
    transferOk bild bias site.ziel = true := by
  unfold loaderBiasOk at h
  exact (Bool.and_eq_true_iff.mp h).2

/-- LOADER-BIAS CONNECTION (generic, arbitrary admitted inputs): from
    the one checked closing step (final-image mapping, operand-site check,
    executed-target mapping) plus the site formation facts (member code
    section, effective bias, section-relative start, displacement bridge,
    next-RIP equation, signed-32 fit, machine-range bounds, stable section
    lookup, file-backed extent, exact file bytes) derive W^X, the aligned
    biased base, the virtual-address formation, the loaded-window decode
    through the checked mapping, and the executed relocation target as a
    machine word and as a Nat. Proved by applying the accepted producer
    lemmas by name; no producer fact is re-proved here. -/
theorem ComposeLoaderBias_verbindung
    (p : Profil) (bild : Bild) (sec : Abschnitt) (bias off : Nat)
    (site : PatchSite) (d : BitVec 32)
    (hok : loaderBiasOk p bild bias site = true)
    (hmem : sec ∈ bild.abschnitte)
    (hbias : bias = effBias bild.modus)
    (hsite_sec : site.bias = bias ∧ site.vaddr = sec.vaddr ∧
      site.off = off ∧ site.art = .ruf)
    (hdisp : dispSigned d = site.disp)
    (hgleich : (site.ziel : Int) = (siteStart site : Int) +
      (relocLen site.art : Int) + site.disp)
    (hfit : rel32Passt site.disp = true)
    (hnext : siteNext site < 2 ^ 64)
    (hziel : site.ziel < 2 ^ 64)
    (hfind : ∀ i : Nat, i < 5 →
      abteilFinden bild.abschnitte bias (bias + sec.vaddr + off + i) =
        some sec)
    (hbacked : ∀ i : Nat, i < 5 → off + i < sec.dateiLen)
    (hb0 : dateiByte bild.datei (sec.dateiOff + off) = natByte 232)
    (hb1 : dateiByte bild.datei (sec.dateiOff + (off + 1)) =
      natByte (d.toNat % 256))
    (hb2 : dateiByte bild.datei (sec.dateiOff + (off + 2)) =
      natByte ((d.toNat / 256) % 256))
    (hb3 : dateiByte bild.datei (sec.dateiOff + (off + 3)) =
      natByte ((d.toNat / 65536) % 256))
    (hb4 : dateiByte bild.datei (sec.dateiOff + (off + 4)) =
      natByte ((d.toNat / 16777216) % 256)) :
    wohlgeformt p bild = true ∧
    patchSiteOk site = true ∧
    transferOk bild bias site.ziel = true ∧
    wxOk sec = true ∧
    (0 < sec.ausr ∧ (bias + sec.vaddr) % sec.ausr = 0) ∧
    siteStart site = bias + sec.vaddr + off ∧
    decode (fenster5 bild bias (bias + sec.vaddr + off)) =
      some (⟨.call32 d, 5⟩, []) ∧
    direktZiel (BitVec.ofNat 64 (bias + sec.vaddr + off)) 5 d =
      BitVec.ofNat 64 site.ziel ∧
    (direktZiel (BitVec.ofNat 64 (bias + sec.vaddr + off)) 5 d).toNat =
      site.ziel := by
  have hwf := loaderBiasOk_wohlgeformt p bild bias site hok
  have hpatch := loaderBiasOk_site p bild bias site hok
  have htrans := loaderBiasOk_transfer p bild bias site hok
  have hwx := wohlgeformt_wx p bild sec hmem hwf
  have hausr := wohlgeformt_ausr p bild sec bias hbias hmem hwf
  have hstart : siteStart site = bias + sec.vaddr + off := by
    unfold siteStart
    rw [hsite_sec.1, hsite_sec.2.1, hsite_sec.2.2.1]
  have hart : site.art = RelocArt.ruf := hsite_sec.2.2.2
  have hdec := bildSite_ruf_dekode bild bias sec off d hfind hbacked
    hb0 hb1 hb2 hb3 hb4
  have hz := patchSite_ziel site d hdisp hgleich hfit hnext hziel
  have hlen : relocLen RelocArt.ruf = 5 := rfl
  have hz1 : direktZiel (BitVec.ofNat 64 (bias + sec.vaddr + off)) 5 d =
      BitVec.ofNat 64 site.ziel := by
    have e1 := hz.1
    rw [hstart, hart, hlen] at e1
    exact e1
  have hz2 : (direktZiel (BitVec.ofNat 64 (bias + sec.vaddr + off)) 5 d).toNat =
      site.ziel := by
    rw [hz1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hziel]
  exact ⟨hwf, hpatch, htrans, hwx, hausr, hstart, hdec, hz1, hz2⟩

/-- REFUSAL (out of range): an out-of-range relocation displacement
    admits no closing step. The operand-site check refuses
    (`patchSiteOk_disp_aussen`), so the conjunction refuses. -/
theorem loaderBias_disp_aussen (p : Profil) (bild : Bild) (bias : Nat)
    (site : PatchSite) (h : rel32Passt site.disp = false) :
    loaderBiasOk p bild bias site = false := by
  have hsite : patchSiteOk site = false := patchSiteOk_disp_aussen site h
  unfold loaderBiasOk
  rw [hsite]
  simp

/-- REFUSAL (unlisted target): a relocation target outside every loaded
    section admits no closing step. The executed-target mapping check
    refuses, so the conjunction refuses. -/
theorem loaderBias_loch_verweigert (p : Profil) (bild : Bild) (bias : Nat)
    (site : PatchSite)
    (hloch : abteilFinden bild.abschnitte bias site.ziel = none) :
    loaderBiasOk p bild bias site = false := by
  have htrans : transferOk bild bias site.ziel = false := by
    unfold transferOk
    rw [hloch]
  unfold loaderBiasOk
  rw [htrans]
  simp

/-! ## Joint witness: a non-degenerate three-section image.

    Code (`call +4091` at 0x1000) plus an executable transfer target
    (0x2000) plus a writable stack section (0x3000): the image analogue of
    a written table. The call executes through `byteschritt` to a real
    stack write on the same image. -/

/-- Witness code section: `call` bytes at 0x1000, never writable. -/
def lbCode : Abschnitt :=
  { dateiOff := 0, dateiLen := 5, vaddr := 0x1000, memLen := 5,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 1 }

/-- Witness target section: eight `ret` bytes at 0x2000, never writable. -/
def lbZielSec : Abschnitt :=
  { dateiOff := 5, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 1 }

/-- Witness stack section: three file bytes plus a BSS tail at 0x3000,
    readable and writable, never executable. -/
def lbStapel : Abschnitt :=
  { dateiOff := 13, dateiLen := 3, vaddr := 0x3000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 1 }

/-- Witness file: `call +4091` (`E8 FB 0F 00 00`), eight `ret` bytes,
    then three zero stack bytes. -/
def lbDatei : List Byte :=
  [natByte 232, natByte 251, natByte 15, natByte 0, natByte 0,
    natByte 195, natByte 195, natByte 195, natByte 195,
    natByte 195, natByte 195, natByte 195, natByte 195,
    natByte 0, natByte 0, natByte 0]

/-- The witness image: code plus listed transfer target plus writable
    stack under a fixed bias, entry inside code. -/
def lbBild : Bild :=
  { datei := lbDatei
    abschnitte := [lbCode, lbZielSec, lbStapel]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- Witness site: bias 0, base 0x1000, `call +4091` to 0x2000. -/
def lbSite : PatchSite := ⟨0, 0x1000, 0, .ruf, 4091, 0x2000⟩

/-- Witness displacement field: 4091 as 32 bits. -/
def lbD : BitVec 32 := BitVec.ofNat 32 4091

/-- ACCEPTANCE: the witness image validates under profile 48. -/
theorem lb_wohlgeformt : wohlgeformt .p48 lbBild = true := by
  decide

/-- The witness site is admitted. -/
theorem lb_patch : patchSiteOk lbSite = true := by
  decide

/-- The witness target is a listed mapping. -/
theorem lb_transfer : transferOk lbBild 0 lbSite.ziel = true := by
  decide

/-- The one checked closing step admits the witness site. -/
theorem lb_ok : loaderBiasOk .p48 lbBild 0 lbSite = true := by
  decide

/-- The code section is a member of the witness image. -/
theorem lb_mem : lbCode ∈ lbBild.abschnitte := by
  decide

/-- The witness bias is the effective bias of the fixed mode. -/
theorem lb_bias : 0 = effBias lbBild.modus := by
  decide

/-- The witness site formation: bias, base, offset and class. -/
theorem lb_site : lbSite.bias = 0 ∧ lbSite.vaddr = lbCode.vaddr ∧
    lbSite.off = 0 ∧ lbSite.art = RelocArt.ruf := by
  decide

/-- Stable section lookup over the five call bytes. -/
theorem lb_find : ∀ i : Nat, i < 5 →
    abteilFinden lbBild.abschnitte 0 (0 + lbCode.vaddr + 0 + i) =
      some lbCode := by
  intro i hi
  have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hi5 with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The five call bytes are file-backed. -/
theorem lb_backed : ∀ i : Nat, i < 5 → 0 + i < lbCode.dateiLen := by
  intro i hi
  have e : lbCode.dateiLen = 5 := rfl
  omega

/-- The five file bytes are exactly the relocated call bytes. -/
theorem lb_b0 : dateiByte lbBild.datei (lbCode.dateiOff + 0) =
    natByte 232 := by
  decide

theorem lb_b1 : dateiByte lbBild.datei (lbCode.dateiOff + (0 + 1)) =
    natByte (lbD.toNat % 256) := by
  decide

theorem lb_b2 : dateiByte lbBild.datei (lbCode.dateiOff + (0 + 2)) =
    natByte ((lbD.toNat / 256) % 256) := by
  decide

theorem lb_b3 : dateiByte lbBild.datei (lbCode.dateiOff + (0 + 3)) =
    natByte ((lbD.toNat / 65536) % 256) := by
  decide

theorem lb_b4 : dateiByte lbBild.datei (lbCode.dateiOff + (0 + 4)) =
    natByte ((lbD.toNat / 16777216) % 256) := by
  decide

/-- The displacement field carries the site displacement. -/
theorem lb_disp : dispSigned lbD = lbSite.disp := by
  decide

/-- The next-RIP equation over the final length. -/
theorem lb_gleich : (lbSite.ziel : Int) = (siteStart lbSite : Int) +
    (relocLen lbSite.art : Int) + lbSite.disp := by
  decide

/-- The witness displacement fits. -/
theorem lb_fit : rel32Passt lbSite.disp = true := by
  decide

/-- The witness next-RIP is in machine range. -/
theorem lb_next : siteNext lbSite < 2 ^ 64 := by
  decide

/-- The witness target is in machine range. -/
theorem lb_ziel : lbSite.ziel < 2 ^ 64 := by
  decide

/-- Witness registers: stack top at 0x3008, everything else zero. -/
def lbReg : Register → Wort := fun q =>
  if q = Register.rsp then BitVec.ofNat 64 0x3008 else BitVec.ofNat 64 0

/-- Witness state: the loaded witness image, instruction at 0x1000. -/
def lbZustand : Zustand :=
  { register := lbReg
    flags := witnessFlags
    rip := BitVec.ofNat 64 0x1000
    speicher := geladen lbBild 0 }

/-- LOADED CALL EXECUTION: one byte step from loaded image memory stores
    the return-address byte at the stack slot (zero before) and lands on
    the listed target. A real reached memory-changing execution over
    `geladen` memory, through `byteschritt` rather than a hand-fed
    `schritt`. -/
theorem lb_call_speichert :
    ausgangByte (BitVec.ofNat 64 0x3000) (byteschritt lbZustand) =
      some (natByte 5) ∧
    lbZustand.speicher.bytes (BitVec.ofNat 64 0x3000) =
      BitVec.ofNat 8 0 ∧
    ausgangRip (byteschritt lbZustand) =
      some (BitVec.ofNat 64 0x2000) := by
  decide

/-- HOLE REFUSAL on the witness image: 0x1800 is in no section. -/
theorem lb_loch : transferOk lbBild 0 0x1800 = false := by
  decide

/-- COMPOSED REFUSAL: an out-of-range displacement admits no closing
    step on the witness image. -/
theorem lb_disp_verweigert :
    loaderBiasOk .p48 lbBild 0 ⟨0, 0x1000, 0, .ruf, 2147483648, 0x2000⟩ =
      false :=
  loaderBias_disp_aussen .p48 lbBild 0 _ (by decide)

/-- JOINT WITNESS for `ComposeLoaderBias_verbindung`: all premises are
    instantiated jointly on the accepted three-section witness image
    (executable code plus listed transfer target plus writable stack: the
    non-degenerate case, the image analogue of a written table), with the
    composed connection, a reached memory-changing run through the closing
    step (return-address byte 5 into the stack slot, zero before, landing
    on the listed target), and planted refusal cases (out-of-range
    displacement at the site and at the composed step, interior target,
    unlisted transfer). -/
theorem ComposeLoaderBias_verbindung_zeuge :
    ∃ (p : Profil) (bild : Bild) (sec : Abschnitt) (bias off : Nat)
      (site : PatchSite) (d : BitVec 32),
      sec ∈ bild.abschnitte ∧
      bias = effBias bild.modus ∧
      (site.bias = bias ∧ site.vaddr = sec.vaddr ∧
        site.off = off ∧ site.art = RelocArt.ruf) ∧
      dispSigned d = site.disp ∧
      ((site.ziel : Int) = (siteStart site : Int) +
        (relocLen site.art : Int) + site.disp) ∧
      rel32Passt site.disp = true ∧
      siteNext site < 2 ^ 64 ∧
      site.ziel < 2 ^ 64 ∧
      (∀ i : Nat, i < 5 →
        abteilFinden bild.abschnitte bias (bias + sec.vaddr + off + i) =
          some sec) ∧
      (∀ i : Nat, i < 5 → off + i < sec.dateiLen) ∧
      dateiByte bild.datei (sec.dateiOff + off) = natByte 232 ∧
      dateiByte bild.datei (sec.dateiOff + (off + 1)) =
        natByte (d.toNat % 256) ∧
      dateiByte bild.datei (sec.dateiOff + (off + 2)) =
        natByte ((d.toNat / 256) % 256) ∧
      dateiByte bild.datei (sec.dateiOff + (off + 3)) =
        natByte ((d.toNat / 65536) % 256) ∧
      dateiByte bild.datei (sec.dateiOff + (off + 4)) =
        natByte ((d.toNat / 16777216) % 256) ∧
      loaderBiasOk p bild bias site = true ∧
      wohlgeformt p bild = true ∧
      patchSiteOk site = true ∧
      transferOk bild bias site.ziel = true ∧
      wxOk sec = true ∧
      (0 < sec.ausr ∧ (bias + sec.vaddr) % sec.ausr = 0) ∧
      siteStart site = bias + sec.vaddr + off ∧
      decode (fenster5 bild bias (bias + sec.vaddr + off)) =
        some (⟨.call32 d, 5⟩, []) ∧
      direktZiel (BitVec.ofNat 64 (bias + sec.vaddr + off)) 5 d =
        BitVec.ofNat 64 site.ziel ∧
      (direktZiel (BitVec.ofNat 64 (bias + sec.vaddr + off)) 5 d).toNat =
        site.ziel ∧
      lbZustand.speicher.bytes (BitVec.ofNat 64 0x3000) =
        BitVec.ofNat 8 0 ∧
      ausgangByte (BitVec.ofNat 64 0x3000) (byteschritt lbZustand) =
        some (natByte 5) ∧
      ausgangRip (byteschritt lbZustand) =
        some (BitVec.ofNat 64 0x2000) ∧
      patchSiteOk ⟨0, 0x1000, 0, .sprung, 2147483648, 0x1000⟩ = false ∧
      patchSiteOk ⟨0, 0x1000, 0, .sprung, -3, 0x1002⟩ = false ∧
      transferOk lbBild 0 0x1800 = false ∧
      loaderBiasOk .p48 lbBild 0 ⟨0, 0x1000, 0, .ruf, 2147483648, 0x2000⟩ =
        false := by
  have hconn := ComposeLoaderBias_verbindung .p48 lbBild lbCode 0 0 lbSite lbD
    lb_ok lb_mem lb_bias lb_site lb_disp lb_gleich lb_fit lb_next lb_ziel
    lb_find lb_backed lb_b0 lb_b1 lb_b2 lb_b3 lb_b4
  obtain ⟨hwf, hpatch, htrans, hwx, hausr, hstart, hdec, hz1, hz2⟩ := hconn
  exact ⟨.p48, lbBild, lbCode, 0, 0, lbSite, lbD,
    lb_mem, lb_bias, lb_site, lb_disp, lb_gleich, lb_fit, lb_next, lb_ziel,
    lb_find, lb_backed, lb_b0, lb_b1, lb_b2, lb_b3, lb_b4,
    lb_ok, hwf, hpatch, htrans, hwx, hausr, hstart, hdec, hz1, hz2,
    lb_call_speichert.2.1, lb_call_speichert.1, lb_call_speichert.2.2,
    aussen_verweigert, innen_verweigert, lb_loch, lb_disp_verweigert⟩

/- CUTS:
    Proved here, by composing the accepted producer modules (no producer
    fact re-proved, no second loader/decoder/executor/ISA): the one
    checked closing step `loaderBiasOk` (final-image mapping AND
    operand-site check AND executed-target mapping) with its three
    projections, the generic loader-bias connection for arbitrary
    admitted inputs (`ComposeLoaderBias_verbindung`: mapping, W^X,
    aligned biased base, virtual-address formation, loaded-window decode,
    executed word/Nat target), the out-of-range-displacement refusal, the
    unlisted-target refusal, and one joint non-degenerate witness
    (`ComposeLoaderBias_verbindung_zeuge`) on a three-section image
    (code plus listed target plus writable stack) with a reached
    memory-changing run (return-address byte into the stack slot, zero
    before, landing on the listed target) and planted refusals.
    NOT proved here, and not claimed:
    - No source correspondence: nothing here claims the image bytes are
      the emitted form of any source program, or that duties, contracts,
      costs, locks or call logs refine anything. Source claims stay OPEN.
    - No hardware correspondence: fetch runs over the model `Speicher`
      function, not silicon; caches, TLBs, store buffers, faults beyond
      the decoded refusal, interrupts and timing are OPEN.
    - No whole-binary theorem: no multi-step control-flow validation, no
      entry legality beyond containment, no patched-site re-decoding
      beyond the one call site (owner: rel32 lane 561 via `patchSiteOk`),
      no ABI, cost or concurrency claim; the TSO/GX bridge stays with
      its owner (lanes 567/573-574).
    - No data-field/abs64/rel8 site classes: only code-operand call
      sites close here (`siteArtOk` refuses `datenFeld`; abs64/rel8 have
      no `RelocArt` case, owner: extension codec lanes).
    - No termination claim: `verweigert` is the absence of a successful
      transition, never normal program termination.
-/

#print axioms loaderBiasOk_wohlgeformt
#print axioms loaderBiasOk_site
#print axioms loaderBiasOk_transfer
#print axioms ComposeLoaderBias_verbindung
#print axioms loaderBias_disp_aussen
#print axioms loaderBias_loch_verweigert
#print axioms ComposeLoaderBias_verbindung_zeuge

end Gabbro.Grammatik.X86
