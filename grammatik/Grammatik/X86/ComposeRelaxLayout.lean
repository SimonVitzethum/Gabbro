/-
  File:      Grammatik/X86/ComposeRelaxLayout.lean
  Subject:   Composition closing: bounded branch relaxation to final-byte revalidation.

  Lane 845: closes one bounded relaxation round to final-byte revalidation.
  Every narrowed branch is re-decoded through the reused canonical decoder
  (`relocBytes_decode` over `relocBytes`), and `layoutOk` is re-decided after
  each round (`relaxNarrow_ok`). The producer/consumer interface closed here:

  producers (reused by name, never re-proved, no second decoder/loader/
  executor/ISA/IR): `BranchLayout` (`zweigOk`, `zweigLaenge`, `dispSigned`,
  `zweigOk_kurz`, length stability), `TableLayout` (`layoutOk`, `layoutFuer`,
  `zeugenU`, `ueberlapp_verweigert`), `RelocatedExecution` (`PatchSite`,
  `siteStart`/`siteNext`, `patchSiteOk` + acceptance/refusals, `relocLen`,
  `relocBefehl`, `relocBytes` + `relocBytes_decode`, `patchSite_ziel`,
  `patchSite_ruf_schritt`), `ValidatorSkeleton` vocabulary (`valX86`
  mapping+coverage stay the consumer, not re-decided here).

  consumer: the layout validator (`zweigOk` + `layoutOk` re-decision) and the
  whole-image coverage proof (`DecodingCoverage`/`valX86` closing theorem),
  which discharge one call site by `ComposeRelaxLayout_verbindung`.

  A conjunction of checks is not execution: the closing theorem ends in a
  reached `byteschritt` call step over actual loaded bytes (a real `write64`
  return-address store with read-back) plus a planted refusal beside it.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.BranchLayout
import Grammatik.X86.TableLayout
import Grammatik.X86.Relokation
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt
import Grammatik.X86.RelocatedExecution

namespace Gabbro.Grammatik.X86

/-- One relaxation-round site: the checked wide certificate, the carried
    computed layout, the site class and the displacement field. -/
structure RelaxStelle where
  bedingt : Bool
  beleg : ZweigBeleg
  layout : List TabLayout
  art : RelocArt
  feld : BitVec 32
  deriving DecidableEq, Repr

/-- Class/condition agreement: unconditional sites are jumps or calls,
    conditional sites carry their condition. -/
def relaxArtOk : Bool → RelocArt → Bool
  | false, .sprung => true
  | false, .ruf => true
  | true, .bedingt _ => true
  | _, _ => false

/-- The site as a checked relocation site at zero bias: the certificate
    start is the section base, the offset is zero. -/
def patchAusRelax (r : RelaxStelle) : PatchSite :=
  { bias := 0, vaddr := r.beleg.start, off := 0, art := r.art,
    disp := r.beleg.disp, ziel := r.beleg.ziel }

/-- The round check: the wide certificate AND the recomputed layout AND
    the class agreement, each re-decided from carried data. -/
def relaxStelleOk (r : RelaxStelle) : Bool :=
  zweigOk r.bedingt r.beleg && layoutOk r.layout && relaxArtOk r.bedingt r.art

/-- The check implies the wide certificate. -/
theorem relaxStelleOk_beleg (r : RelaxStelle)
    (h : relaxStelleOk r = true) :
    zweigOk r.bedingt r.beleg = true := by
  unfold relaxStelleOk at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1

/-- The check implies the re-decided layout. -/
theorem relaxStelleOk_layout (r : RelaxStelle)
    (h : relaxStelleOk r = true) :
    layoutOk r.layout = true := by
  unfold relaxStelleOk at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

/-- The check implies the class agreement. -/
theorem relaxStelleOk_art (r : RelaxStelle)
    (h : relaxStelleOk r = true) :
    relaxArtOk r.bedingt r.art = true := by
  unfold relaxStelleOk at h
  exact (Bool.and_eq_true_iff.mp h).2

/-- The round over a site list: every site re-decided. -/
def relaxRundeOk (rs : List RelaxStelle) : Bool :=
  rs.all relaxStelleOk

/-- The empty round is accepted. -/
theorem relaxRunde_nil : relaxRundeOk [] = true := by
  rfl

/-- An accepted round admits every member site. -/
theorem relaxRunde_glied (r : RelaxStelle) (rs : List RelaxStelle)
    (hmem : r ∈ rs) (h : relaxRundeOk rs = true) :
    relaxStelleOk r = true := by
  unfold relaxRundeOk at h
  exact (List.all_eq_true.mp h) r hmem

/-- One narrowing step: normalize any selected form to the wide fallback.
    Length-stable by the reused `zweig_len_stabil_*`: no start ever moves. -/
def relaxNarrow (r : RelaxStelle) : RelaxStelle :=
  { r with beleg := { r.beleg with form := .weit } }

/-- Narrowing never moves the site start. -/
theorem relaxNarrow_start (r : RelaxStelle) :
    siteStart (patchAusRelax (relaxNarrow r)) =
      siteStart (patchAusRelax r) := by
  rfl

/-- Narrowing never changes the final bytes. -/
theorem relaxNarrow_bytes (r : RelaxStelle) :
    relocBytes (relaxNarrow r).art (relaxNarrow r).feld =
      relocBytes r.art r.feld := by
  rfl

/-- RE-DECODE: every narrowed branch re-decodes through the one canonical
    decoder at its carried length; the suffix passes through untouched.
    Direct reuse of `relocBytes_decode`, never a second decoder. -/
theorem relaxStelle_dekode (r : RelaxStelle) (suffix : List Byte) :
    decode (relocBytes r.art r.feld ++ suffix) =
      some (⟨relocBefehl r.art r.feld, (relocBytes r.art r.feld).length⟩,
        suffix) := by
  exact relocBytes_decode r.art r.feld suffix

/-- Narrowing preserves the round check: an accepted site stays accepted,
    so `layoutOk` is re-decided green after each round. The `zweigOk`
    premise is used through the short-form exclusion. -/
theorem relaxNarrow_ok (r : RelaxStelle)
    (h : relaxStelleOk r = true) :
    relaxStelleOk (relaxNarrow r) = true := by
  have hzweig := relaxStelleOk_beleg r h
  have hform : r.beleg.form = .weit := by
    cases hf : r.beleg.form with
    | weit => rfl
    | kurz =>
      have hz := zweigOk_kurz r.bedingt r.beleg hf
      rw [hz] at hzweig
      exact (Bool.false_ne_true hzweig).elim
  have heq : relaxNarrow r = r := by
    unfold relaxNarrow
    cases hbeleg : r.beleg with
    | mk start len form disp ziel =>
      rw [hbeleg] at hform
      rw [← hform, ← hbeleg]
  rw [heq]
  exact h

/-- COMPOSITION CLOSING (call sites): an accepted round site revalidates
    end to end. From the re-decided round check plus the carried
    field/equation/fit/bound/exterior linkage and the actual loaded window
    with its real stack write, the narrowed branch re-decodes, the layout
    is re-decided, the executed target is the intended mapped target, the
    carried length agrees with the certificate, and the reached byte step
    stores the return address with read-back. Every premise is used:
    `hok` through the three projections, `hfeld` through the target
    equation, `hgleich`/`hfit`/`hnext`/`hziel` through site admission and
    the target equation, `haussen` through site admission, `hart` through
    the call step, `hbed` through the length agreement, and the
    window/execute/rip/write/read-permission premises through the step
    and its read-back. -/
theorem ComposeRelaxLayout_verbindung (r : RelaxStelle)
    (hok : relaxStelleOk r = true)
    (hfeld : dispSigned r.feld = r.beleg.disp)
    (hgleich : (r.beleg.ziel : Int) = ((siteStart (patchAusRelax r)) : Int) +
      (relocLen r.art : Int) + r.beleg.disp)
    (hfit : rel32Passt r.beleg.disp = true)
    (hnext : siteNext (patchAusRelax r) < 2 ^ 64)
    (hziel : r.beleg.ziel < 2 ^ 64)
    (haussen : r.beleg.ziel ≤ siteStart (patchAusRelax r) ∨
      siteNext (patchAusRelax r) ≤ r.beleg.ziel)
    (hart : r.art = .ruf)
    (hbed : r.bedingt = false)
    (z : Zustand) (suffix : List Byte) (m : Speicher)
    (hwin : geholt z = relocBytes .ruf r.feld ++ suffix)
    (hexe : ausfuehrbarN z.speicher z.rip
      (relocBytes .ruf r.feld).length = true)
    (hrip : z.rip = BitVec.ofNat 64 (siteStart (patchAusRelax r)))
    (hwr : write64 z.speicher (z.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach z.rip (encode (.call32 r.feld)).length) = some m)
    (hles : lesbar8 z.speicher
      (z.register Register.rsp - BitVec.ofNat 64 8) = true) :
    zweigOk r.bedingt r.beleg = true ∧
    layoutOk r.layout = true ∧
    relaxArtOk r.bedingt r.art = true ∧
    patchSiteOk (patchAusRelax r) = true ∧
    (relocBytes .ruf r.feld).length = zweigLaenge r.bedingt .weit ∧
    decode (relocBytes .ruf r.feld ++ suffix) =
      some (⟨relocBefehl .ruf r.feld, (relocBytes .ruf r.feld).length⟩,
        suffix) ∧
    direktZiel (BitVec.ofNat 64 (siteStart (patchAusRelax r)))
        (relocLen .ruf) r.feld = BitVec.ofNat 64 r.beleg.ziel ∧
    byteschritt z = .weiter (schrittCall z Register.rsp m
        (z.register Register.rsp - BitVec.ofNat 64 8)
        (BitVec.ofNat 64 r.beleg.ziel)) ∧
    read64 m (z.register Register.rsp - BitVec.ofNat 64 8) =
      some (ripNach z.rip (encode (.call32 r.feld)).length) := by
  have hzweig := relaxStelleOk_beleg r hok
  have hlayout := relaxStelleOk_layout r hok
  have hartok := relaxStelleOk_art r hok
  have hsite := patchSiteOk_akzeptiert (patchAusRelax r) hgleich hfit
    hnext hziel haussen
  have hlen : (relocBytes .ruf r.feld).length =
      zweigLaenge r.bedingt .weit := by
    rw [hbed, relocBytes_len]
    rfl
  have hdec := relocBytes_decode .ruf r.feld suffix
  have harts : (patchAusRelax r).art = .ruf := hart
  have hziel' := (patchSite_ziel (patchAusRelax r) r.feld hfeld hgleich
    hfit hnext hziel).1
  rw [harts] at hziel'
  have hstep := patchSite_ruf_schritt (patchAusRelax r) r.feld m hfeld
    hgleich hfit hnext hziel harts z suffix hwin hexe hrip hwr
  have hread := read64_nach_write64 _ _ _ _ hwr hles
  exact ⟨hzweig, hlayout, hartok, hsite, hlen, hdec, hziel', hstep, hread⟩

/-- PLANTED REFUSAL (short selection): a short certificate is refused by
    the round check, through the reused `zweigOk_kurz`. -/
theorem relaxStelleOk_kurz (r : RelaxStelle)
    (hform : r.beleg.form = .kurz) :
    relaxStelleOk r = false := by
  have hz := zweigOk_kurz r.bedingt r.beleg hform
  unfold relaxStelleOk
  rw [hz]
  simp

/-- PLANTED REFUSAL (out of range): an out-of-range displacement admits
    no site, through the reused `patchSiteOk_disp_aussen`. -/
theorem relaxPatch_aussen (r : RelaxStelle)
    (h : rel32Passt r.beleg.disp = false) :
    patchSiteOk (patchAusRelax r) = false := by
  exact patchSiteOk_disp_aussen (patchAusRelax r) h

/-- PLANTED REFUSAL (interior target): a target strictly inside the
    site's own bytes admits no site, through `patchSiteOk_innen`. -/
theorem relaxPatch_innen (r : RelaxStelle)
    (h1 : siteStart (patchAusRelax r) < r.beleg.ziel)
    (h2 : r.beleg.ziel < siteNext (patchAusRelax r)) :
    patchSiteOk (patchAusRelax r) = false := by
  exact patchSiteOk_innen (patchAusRelax r) h1 h2

/-- PLANTED REFUSAL (overlap): the overlapping extents are refused by
    the round check, through the reused `ueberlapp_verweigert`. -/
theorem relaxStelleOk_ueberlapp (r : RelaxStelle)
    (hlay : r.layout = [{ tab := 0, basis := 4096, len := 16, ausr := 8 },
      { tab := 1, basis := 4104, len := 16, ausr := 8 }]) :
    relaxStelleOk r = false := by
  unfold relaxStelleOk
  rw [hlay, ueberlapp_verweigert]
  simp

/-- Witness site: the accepted call at 0x1000 (`call +16` to 0x1015)
    over the recomputed nondegenerate table layout. -/
def relaxZeuge : RelaxStelle :=
  ⟨false, ⟨0x1000, 5, .weit, 16, 0x1015⟩, layoutFuer zeugenU 4096 8, .ruf,
    BitVec.ofNat 32 16⟩

/-- JOINT WITNESS for `ComposeRelaxLayout_verbindung`: every premise
    instantiated jointly on concrete values (the accepted call site, the
    loaded call image with its real stack write, the nondegenerate writer
    unit), with the re-decoded bytes, the reached memory-changing byte
    step, the read-back, the observably changed byte and a planted
    out-of-range refusal beside them. -/
theorem ComposeRelaxLayout_verbindung_zeuge :
    ∃ (m : Speicher),
      relaxStelleOk relaxZeuge = true ∧
      layoutOk (layoutFuer zeugenU 4096 8) = true ∧
      slotAufz zeugenU ≠ [] ∧
      (zeugenU.fns.get ⟨0, by decide⟩).schreibt = ["konto"] ∧
      patchSiteOk (patchAusRelax relaxZeuge) = true ∧
      decode (relocBytes .ruf (BitVec.ofNat 32 16) ++ []) =
        some (⟨relocBefehl .ruf (BitVec.ofNat 32 16),
          (relocBytes .ruf (BitVec.ofNat 32 16)).length⟩, []) ∧
      byteschritt zustandRuf =
        .weiter (schrittCall zustandRuf Register.rsp m
          (zustandRuf.register Register.rsp - BitVec.ofNat 64 8)
          (BitVec.ofNat 64 0x1015)) ∧
      read64 m (BitVec.ofNat 64 0x1FF8) =
        some (BitVec.ofNat 64 0x1005) ∧
      m.bytes (BitVec.ofNat 64 0x1FF8) ≠
        zustandRuf.speicher.bytes (BitVec.ofNat 64 0x1FF8) ∧
      patchSiteOk ⟨0, 0x1000, 0, .sprung, 2147483648, 0x1000⟩ =
        false := by
  have hok : relaxStelleOk relaxZeuge = true := by decide
  have hfeld : dispSigned (BitVec.ofNat 32 16) =
      relaxZeuge.beleg.disp := by decide
  have hgleich : (relaxZeuge.beleg.ziel : Int) =
      ((siteStart (patchAusRelax relaxZeuge)) : Int) +
        (relocLen relaxZeuge.art : Int) + relaxZeuge.beleg.disp := by
    decide
  have hfit : rel32Passt relaxZeuge.beleg.disp = true := by decide
  have hnext : siteNext (patchAusRelax relaxZeuge) < 2 ^ 64 := by decide
  have hziel : relaxZeuge.beleg.ziel < 2 ^ 64 := by decide
  have haussen : relaxZeuge.beleg.ziel ≤ siteStart (patchAusRelax relaxZeuge) ∨
      siteNext (patchAusRelax relaxZeuge) ≤ relaxZeuge.beleg.ziel := by
    decide
  have hwin : geholt zustandRuf =
      relocBytes .ruf (BitVec.ofNat 32 16) ++ [] := by decide
  have hexe : ausfuehrbarN zustandRuf.speicher zustandRuf.rip
      (relocBytes .ruf (BitVec.ofNat 32 16)).length = true := by decide
  have hrip : zustandRuf.rip =
      BitVec.ofNat 64 (siteStart (patchAusRelax relaxZeuge)) := by decide
  have eadr : zustandRuf.register Register.rsp - BitVec.ofNat 64 8 =
      BitVec.ofNat 64 0x1FF8 := by decide
  have enach : ripNach zustandRuf.rip
      (encode (.call32 (BitVec.ofNat 32 16))).length =
      BitVec.ofNat 64 0x1005 := by decide
  have hschr : schreibbar8 zustandRuf.speicher
      (BitVec.ofNat 64 0x1FF8) = true := by decide
  have hwr : write64 zustandRuf.speicher
      (zustandRuf.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach zustandRuf.rip
        (encode (.call32 (BitVec.ofNat 32 16))).length) =
      some { zustandRuf.speicher with bytes := writeBytes zustandRuf.speicher (BitVec.ofNat 64 0x1FF8) (BitVec.ofNat 64 0x1005) } := by
    rw [eadr, enach]
    unfold write64
    rw [if_pos hschr]
  have hles : lesbar8 zustandRuf.speicher
      (zustandRuf.register Register.rsp - BitVec.ofNat 64 8) = true := by
    rw [eadr]
    decide
  obtain ⟨hzweig, hlayout, hartok, hsite, hlen, hdec, htarget, hstep,
      hread⟩ :=
    ComposeRelaxLayout_verbindung relaxZeuge hok hfeld hgleich hfit hnext
      hziel haussen rfl rfl zustandRuf [] _ hwin hexe hrip hwr hles
  simp only [relaxZeuge] at hread
  rw [eadr, enach] at hread
  have hhit := writeBytesN_hit zustandRuf.speicher (BitVec.ofNat 64 0x1FF8)
    (BitVec.ofNat 64 0x1005) 8 0 (by decide) (by decide)
  have hnull := addrOff_null (BitVec.ofNat 64 0x1FF8)
  rw [hnull] at hhit
  have hhit2 : writeBytes zustandRuf.speicher (BitVec.ofNat 64 0x1FF8)
      (BitVec.ofNat 64 0x1005) (BitVec.ofNat 64 0x1FF8) =
      wortByte (BitVec.ofNat 64 0x1005) 0 := hhit
  have hinit : zustandRuf.speicher.bytes (BitVec.ofNat 64 0x1FF8) =
      BitVec.ofNat 8 0 := by decide
  have hdiff : writeBytes zustandRuf.speicher (BitVec.ofNat 64 0x1FF8)
        (BitVec.ofNat 64 0x1005) (BitVec.ofNat 64 0x1FF8) ≠
        zustandRuf.speicher.bytes (BitVec.ofNat 64 0x1FF8) := by
    rw [hhit2, hinit]
    decide
  exact ⟨_, hok, zeugenLayout_ok, zeugenSlot_ne, zeugenU_schreibt, hsite,
    hdec, hstep, hread, hdiff, aussen_verweigert⟩

/- CUTS:
    Proved here, over the ACTUAL accepted vocabulary (nothing re-proved,
    no second decoder/loader/executor/ISA/IR created):
    - the round interface (`RelaxStelle`, `relaxArtOk`, `patchAusRelax`,
      `relaxStelleOk` with its three projections, the list round
      `relaxRundeOk` with empty/member facts);
    - narrowing (`relaxNarrow` with start/byte stability and
      `relaxNarrow_ok`: an accepted site stays accepted, so `layoutOk`
      is re-decided green after each round; the short form is excluded
      through the reused `zweigOk_kurz`);
    - re-decode (`relaxStelle_dekode`: every narrowed branch re-decodes
      through the one canonical decoder at its carried length);
    - `ComposeRelaxLayout_verbindung` (call sites): the accepted round
      site revalidates end to end -- certificate, layout, class
      agreement, site admission, carried-length agreement, decode, the
      executed target equation, the reached `byteschritt` call step over
      actual loaded bytes with its real return-address store, and the
      read-back;
    - four planted refusals (short selection, out-of-range displacement,
      interior target, overlapping extents), each through its accepted
      producer refusal;
    - the joint witness `ComposeRelaxLayout_verbindung_zeuge` (concrete
      call +16 to 0x1015 on the loaded call image with a zero-to-0x1005
      stack store that reads back, over the nondegenerate writer unit,
      beside the planted out-of-range refusal).
    NOT proved here, and not claimed:
    - No short-branch acceptance: a `.kurz` certificate is refused by
      the round check; short-byte selection stays with its owner
      (`Rel8Reach`); this round always carries the wide fallback.
    - No whole-image theorem: one site at its final layout per round
      step; multi-site convergence, fall-through coverage and the full
      `DecodingCoverage`/`valX86` closing theorem stay with the
      consumer (`ValidatorSkeleton`).
    - No source correspondence, no TSO/GX bridge, no concurrency, no
      cost/time transfer, no ABI/loader/entry acceptance and no
      hardware correspondence: validation runs on final bytes only.
    - No conditional-branch or data-field sites: the closing theorem
      covers call sites (the memory-changing execution); jumps,
      taken/not-taken conditionals and abs64/data sites stay with
      `RelocatedExecution` (`patchSite_sprung_schritt`,
      `patchSite_bedingt_*_schritt`, `siteArtOk`).
-/

#print axioms relaxStelleOk_beleg
#print axioms relaxStelleOk_layout
#print axioms relaxStelleOk_art
#print axioms relaxRunde_nil
#print axioms relaxRunde_glied
#print axioms relaxNarrow_start
#print axioms relaxNarrow_bytes
#print axioms relaxStelle_dekode
#print axioms relaxNarrow_ok
#print axioms ComposeRelaxLayout_verbindung
#print axioms relaxStelleOk_kurz
#print axioms relaxPatch_aussen
#print axioms relaxPatch_innen
#print axioms relaxStelleOk_ueberlapp
#print axioms ComposeRelaxLayout_verbindung_zeuge

end Gabbro.Grammatik.X86
