/-
  File:      Grammatik/X86/PipelineProfilesReloc.lean
  Subject:   Checked OS profiles with multi-step control flow and
              relocation re-decoding (follow-up of lane 1173).

  Reused, not duplicated (no second loader, decoder, executor, ISA,
  IR or source interpreter):
    - profiles: `PipelineProfiles.profilOk`/`profilOk_teile`,
      `pipeline_profil_verbindung`, `profilOk_folgen`,
      `profilOk_stuetz_schritt`/`_verweigert`, `profil_verweigert_*`,
      `profil_gehostet_ok`/`profil_frei_ok`;
    - single patch: `PipelineLinkMulti.multiPatch`,
      `multiPatch_rel32_gleich`, `linkPatch_bereich`/`_stelle`/
      `_rahmen`/`_laenge`, `opsDisjunktB`;
    - re-decode: `PipelineLink.verknuepft_rel32_schliesst` (jump),
      `PipelineLinkMulti.multi_ruf_schliesst` (call);
    - multi-step run: `Pipeline.lauf_zu_laufBytes`, `laufBytes_add`;
    - run vocabulary: `Bild.schreibLese_zeuge`,
      `TableLayout.zeugenU_schreibt`,
      `RelocatedExecution.ruf_schritt_zeuge`.
  No OS behaviour beyond the named binding assumptions; environment
  services stay user logic; only hardware behaviour is assumed.
-/
import Grammatik.X86.PipelineProfiles
import Grammatik.X86.PipelineLinkMulti

namespace Gabbro.Grammatik.X86.PipelineProfilesReloc

open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineProfiles

/-- The checked relocation admission of one OS profile: the profile
    admission AND one applied rel32 operand at the relocated
    call/jump site. Unsupported shapes are REFUSED, never guessed. -/
def relocOk (w : ZielProfil) (bild : Bild) (bias : Nat)
    (z : EintrittZustand) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (h : NolibcHaken) (code rueck : Nat)
    (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte) : Bool :=
  profilOk w bild bias z tor moves es h code rueck &&
  decide (multiPatch img (istart + 1) (.rel32 disp) = some out)

/-! ## 1. Admission split and patch frame.

    The profile half and the applied-operand half. The frame legs
    reuse the two-unit link facts through the rel32 equality
    (`multiPatch_rel32_gleich`); only names change, no rule is
    re-proved. -/

/-- ADMISSION SPLIT: an admitted relocation meets the profile half
    and the applied-operand half. -/
theorem relocOk_teile (w : ZielProfil) (bild : Bild) (bias : Nat)
    (z : EintrittZustand) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (h : NolibcHaken) (code rueck : Nat)
    (img : List Byte) (istart : Nat) (disp : Int) (out : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true) :
    profilOk w bild bias z tor moves es h code rueck = true ∧
    multiPatch img (istart + 1) (.rel32 disp) = some out := by
  unfold relocOk at hadm
  simp only [Bool.and_eq_true] at hadm
  exact ⟨hadm.1, of_decide_eq_true hadm.2⟩

/-- Admission implies the profile admission. -/
theorem relocOk_profil (w : ZielProfil) (bild : Bild) (bias : Nat)
    (z : EintrittZustand) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (h : NolibcHaken) (code rueck : Nat)
    (img : List Byte) (istart : Nat) (disp : Int) (out : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true) :
    profilOk w bild bias z tor moves es h code rueck = true :=
  (relocOk_teile w bild bias z tor moves es h code rueck img
    istart disp out hadm).1

/-- Admission implies the applied operand. -/
theorem relocOk_patch (w : ZielProfil) (bild : Bild) (bias : Nat)
    (z : EintrittZustand) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (h : NolibcHaken) (code rueck : Nat)
    (img : List Byte) (istart : Nat) (disp : Int) (out : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true) :
    multiPatch img (istart + 1) (.rel32 disp) = some out :=
  (relocOk_teile w bild bias z tor moves es h code rueck img
    istart disp out hadm).2

/-- The applied operand as the two-unit link patch (reuse, not a
    second rule). -/
theorem relocOk_patch_link (w : ZielProfil) (bild : Bild) (bias : Nat)
    (z : EintrittZustand) (tor : TorDekl) (moves : List Befehl)
    (es : List TabLayout) (h : NolibcHaken) (code rueck : Nat)
    (img : List Byte) (istart : Nat) (disp : Int) (out : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true) :
    linkPatch img (istart + 1) (.rel32 disp) = some out := by
  rw [← multiPatch_rel32_gleich]
  exact relocOk_patch w bild bias z tor moves es h code rueck img
    istart disp out hadm

/-- The relocated site lies inside the image. -/
theorem relocOk_patch_bereich (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true) :
    istart + 1 + (feldBytes (.rel32 disp)).length ≤ img.length :=
  linkPatch_bereich img (istart + 1) (.rel32 disp) out
    (relocOk_patch_link w bild bias z tor moves es h code rueck img
      istart disp out hadm)

/-- The relocated site holds exactly the displacement bytes. -/
theorem relocOk_patch_stelle (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true)
    (k : Nat) (hk : k < 4) :
    out[istart + 1 + k]? = (rel32Bytes disp)[k]? := by
  have hlink := relocOk_patch_link w bild bias z tor moves es h
    code rueck img istart disp out hadm
  have hk' : k < (feldBytes (.rel32 disp)).length := by
    simp only [feldBytes, rel32Bytes_laenge]
    exact hk
  have hsite := linkPatch_stelle img (istart + 1) (.rel32 disp) out
    hlink k hk'
  simpa only [feldBytes] using hsite

/-- FRAME: no relocation changes a byte outside its operand. -/
theorem relocOk_patch_rahmen (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true)
    (i : Nat)
    (haussen : ∀ k, k < (feldBytes (.rel32 disp)).length →
      i ≠ istart + 1 + k) :
    out[i]? = img[i]? :=
  linkPatch_rahmen img (istart + 1) (.rel32 disp) out
    (relocOk_patch_link w bild bias z tor moves es h code rueck img
      istart disp out hadm) i haussen

/-- The applied operand keeps the image length. -/
theorem relocOk_patch_laenge (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true) :
    out.length = img.length :=
  linkPatch_laenge img (istart + 1) (.rel32 disp) out
    (relocOk_patch_link w bild bias z tor moves es h code rueck img
      istart disp out hadm)

/-! ## 2. The relocation closings: profile plus re-decoded call/jump.

    For a hosted and a freestanding profile alike: the generic
    profile closing over arbitrary admitted inputs, and the patched
    site re-decoded to the patched displacement with the fit, the
    coverage and the exact window. The jump leg reuses the two-unit
    link closing, the call leg the multi-unit one; decoder
    determinism is never re-proved here. -/

/-- **RELOCATION CLOSING, unconditional jump.** The profile
    admission carries the accepted joint entry admission, both
    hooks, the unchanged status handoff, the executable RIP through
    the CHECKED loaded mapping, the entry stack window and every
    support half; the patched jump re-decodes to the patched
    displacement. Every premise is load-bearing. -/
theorem relocOk_sprung_verbindung (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte) (d : BitVec 32) (rest : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true)
    (himg : img[istart]? = some (natByte 233))
    (hdec : decode (out.drop istart) =
      some ((⟨.jump32 d, 5⟩, rest))) :
    (eintrittZulassung .p48 bild bias (profilEintritt w) z [tor] = true ∧
      hakenOk h = true ∧ rueck = code ∧
      (geladen bild bias).ausfuehrbar z.zustand.rip = true ∧
      lesbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      schreibbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      valX86 .p48 bild = true ∧ torOkB tor = true ∧
      valLayout es = true ∧
      bindungErstelltB tor moves = true ∧
      stubEndsTrapB (moves.flatMap encode ++ trapBytes) = true ∧
      mxcsrGueltig z.mxcsr = true) ∧
    dispSigned d = disp ∧
    5 + rest.length = (out.drop istart).length ∧
    rel32Passt disp = true ∧
    out[istart]? = some (natByte 233) ∧
    (∀ k, k < 4 → out[istart + 1 + k]? = (rel32Bytes disp)[k]?) ∧
    decktAb ⟨.jump32 d, 5⟩ ∧
    decode ((out.drop istart).take 5 ++ rest) =
      some ((⟨.jump32 d, 5⟩, rest)) := by
  have hprof := relocOk_profil w bild bias z tor moves es h code rueck
    img istart disp out hadm
  have hpr : patchRel32 img (istart + 1) disp = some out :=
    relocOk_patch_link w bild bias z tor moves es h code rueck img
      istart disp out hadm
  obtain ⟨hdisp, hlen, hfit, hop, hsite, hdeckt, hregion⟩ :=
    verknuepft_rel32_schliesst img istart disp out d rest himg hpr
      hdec
  exact ⟨pipeline_profil_verbindung w bild bias z tor moves es h code
    rueck hprof, hdisp, hlen, hfit, hop, hsite, hdeckt, hregion⟩

/-- **RELOCATION CLOSING, direct call.** The same profile closing;
    the patched call re-decodes to the patched displacement through
    the multi-unit leg. -/
theorem relocOk_ruf_verbindung (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte) (d : BitVec 32) (rest : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true)
    (himg : img[istart]? = some (natByte 232))
    (hdec : decode (out.drop istart) =
      some ((⟨.call32 d, 5⟩, rest))) :
    (eintrittZulassung .p48 bild bias (profilEintritt w) z [tor] = true ∧
      hakenOk h = true ∧ rueck = code ∧
      (geladen bild bias).ausfuehrbar z.zustand.rip = true ∧
      lesbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      schreibbar8 z.zustand.speicher
        (eintrittRsp z - BitVec.ofNat 64 8) = true ∧
      valX86 .p48 bild = true ∧ torOkB tor = true ∧
      valLayout es = true ∧
      bindungErstelltB tor moves = true ∧
      stubEndsTrapB (moves.flatMap encode ++ trapBytes) = true ∧
      mxcsrGueltig z.mxcsr = true) ∧
    dispSigned d = disp ∧
    5 + rest.length = (out.drop istart).length ∧
    rel32Passt disp = true ∧
    out[istart]? = some (natByte 232) ∧
    (∀ k, k < 4 → out[istart + 1 + k]? = (rel32Bytes disp)[k]?) ∧
    decktAb ⟨.call32 d, 5⟩ ∧
    decode ((out.drop istart).take 5 ++ rest) =
      some ((⟨.call32 d, 5⟩, rest)) := by
  have hprof := relocOk_profil w bild bias z tor moves es h code rueck
    img istart disp out hadm
  have hpr : patchRel32 img (istart + 1) disp = some out :=
    relocOk_patch_link w bild bias z tor moves es h code rueck img
      istart disp out hadm
  obtain ⟨hdisp, hlen, hfit, hop, hsite, hdeckt, hregion⟩ :=
    multi_ruf_schliesst img istart disp out d rest himg hpr hdec
  exact ⟨pipeline_profil_verbindung w bild bias z tor moves es h code
    rueck hprof, hdisp, hlen, hfit, hop, hsite, hdeckt, hregion⟩

/-! ## 3. Multi-step control flow: entry sequence plus lowered program.

    The entry sequence (profile ABI copies) runs first and the
    lowered straight-line program runs after it; byte runs compose.
    Nothing here re-proves the fetch bridge: the lowered run is the
    accepted `lauf_zu_laufBytes`, the composition the accepted
    `laufBytes_add`. -/

/-- A concrete multi-step straight-line program: two immediate
    moves and an add (three byte steps through fetched memory). -/
def relocProg : List Befehl :=
  [.movImm64 .rax (intWort 1), .movImm64 .rbx (intWort 2),
    .addReg64 .rax .rbx]

/-- The concrete program is straight-line code. -/
theorem relocProg_gerade : relocProg.all gerade = true := by
  decide

/-- MULTI-STEP RUN: a straight-line canonical run whose bytes sit at
    the instruction pointer of a W^X code region is the same run
    when every instruction is FETCHED from actual memory and
    decoded. -/
theorem relocOk_mehrschritt (P : List Befehl) (pre post flat : List Byte)
    (cs : Adresse) (s s' : Zustand)
    (hg : P.all gerade = true)
    (hl : lauf (P.map kanon) s = some s')
    (hc : CodeAt s.speicher cs flat)
    (hf : flat = pre ++ encodeAll P ++ post)
    (hrip : s.rip = addrOff cs pre.length) :
    laufBytes P.length s = .weiter s' ∧
      s'.rip = addrOff cs (pre.length + (encodeAll P).length) ∧
      CodeAt s'.speicher cs flat ∧
      s'.speicher.lesbar = s.speicher.lesbar ∧
      s'.speicher.schreibbar = s.speicher.schreibbar :=
  lauf_zu_laufBytes cs flat P pre post s s' hg hl hc hf hrip

/-- ENTRY PLUS PROGRAM: the fetched entry sequence run and the
    fetched lowered-program run compose to one fetched run from the
    entry. -/
theorem relocOk_eintritt_plus_programm (n1 n2 : Nat)
    (s0 s1 s' : Zustand)
    (h1 : laufBytes n1 s0 = .weiter s1)
    (h2 : laufBytes n2 s1 = .weiter s') :
    laufBytes (n1 + n2) s0 = .weiter s' := by
  have h := laufBytes_add n1 n2 s0 s1 h1
  rw [h]
  exact h2

/-! ## 4. Support coverage: every reachable support byte is covered
    or refused.

    Through the closing step over loaded image memory a successful
    fetch runs the existing `schritt`, and no fetch means no
    transition: unvalidated reachable bytes refuse, and nothing
    outside the validated image is ever fetched. The admission
    premise is load-bearing through the validated-image conjunct. -/

/-- COVERED: a successful fetch runs the existing step, and the
    image is validated. -/
theorem relocOk_stuetz_abdeckung (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true)
    (s : Zustand) (d : Decodiert) (rest : List Byte) (s' : Zustand)
    (hf : fetchDekodiert { s with speicher := geladen bild bias } =
      some (d, rest))
    (hs : schritt d { s with speicher := geladen bild bias } =
      some s') :
    stuetzSchritt bild bias s = .weiter s' ∧
      valX86 .p48 bild = true := by
  have hprof := relocOk_profil w bild bias z tor moves es h code
    rueck img istart disp out hadm
  exact ⟨profilOk_stuetz_schritt bild bias s d rest s' hf hs,
    (profilOk_folgen w bild bias z tor moves es h code rueck
      hprof).2.2.2.1⟩

/-- REFUSED: no fetch means no transition, and the image is still
    validated (the refusal is the missing byte, never the image). -/
theorem relocOk_stuetz_verweigert (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte)
    (hadm : relocOk w bild bias z tor moves es h code rueck img
      istart disp out = true)
    (s : Zustand)
    (hf : fetchDekodiert { s with speicher := geladen bild bias } =
      none) :
    stuetzSchritt bild bias s = .verweigert ∧
      valX86 .p48 bild = true := by
  have hprof := relocOk_profil w bild bias z tor moves es h code
    rueck img istart disp out hadm
  exact ⟨profilOk_stuetz_verweigert bild bias s hf,
    (profilOk_folgen w bild bias z tor moves es h code rueck
      hprof).2.2.2.1⟩

/-! ## 5. Refusals: every missing leg refuses the relocation.

    Unsupported shapes are REFUSED, never guessed. The profile legs
    reuse the accepted profile refusals; the patch legs refuse a
    missing operand; the probes below plant each one. -/

/-- REFUSAL: without an applied operand no relocation is admitted. -/
theorem reloc_verweigert_ohne_patch (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte)
    (hpatch : multiPatch img (istart + 1) (.rel32 disp) ≠ some out) :
    relocOk w bild bias z tor moves es h code rueck img istart disp
      out = false := by
  unfold relocOk
  have hdec : decide (multiPatch img (istart + 1) (.rel32 disp) =
      some out) = false :=
    eq_false_of_ne_true (fun ht => hpatch (of_decide_eq_true ht))
  rw [hdec]
  simp

/-- REFUSAL: without the `anfang` handoff no relocation is admitted. -/
theorem reloc_verweigert_ohne_anfang (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte) (hanf : h.anfang = false) :
    relocOk w bild bias z tor moves es h code rueck img istart disp
      out = false := by
  unfold relocOk
  rw [profil_verweigert_ohne_anfang w bild bias z tor moves es h code
    rueck hanf]
  simp

/-- REFUSAL: a handed status that differs from the returned one
    admits no relocation. -/
theorem reloc_verweigert_status (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte) (hmis : rueck ≠ code) :
    relocOk w bild bias z tor moves es h code rueck img istart disp
      out = false := by
  unfold relocOk
  rw [profil_verweigert_status w bild bias z tor moves es h code rueck
    hmis]
  simp

/-- REFUSAL: support bytes outside a validated image admit no
    relocation, whatever the patch side says. -/
theorem reloc_verweigert_ohne_bild (w : ZielProfil) (bild : Bild)
    (bias : Nat) (z : EintrittZustand) (tor : TorDekl)
    (moves : List Befehl) (es : List TabLayout) (h : NolibcHaken)
    (code rueck : Nat) (img : List Byte) (istart : Nat) (disp : Int)
    (out : List Byte) (hbild : valX86 .p48 bild = false) :
    relocOk w bild bias z tor moves es h code rueck img istart disp
      out = false := by
  unfold relocOk
  rw [profil_verweigert_ohne_bild w bild bias z tor moves es h code
    rueck hbild]
  simp

/-- POISON PROBE, overrun: a four-byte operand one byte before the
    end of a three-byte image patches nothing. -/
theorem reloc_probe_ueberlauf :
    multiPatch [natByte 233, natByte 0, natByte 0] 1 (.rel32 16) =
      none := by
  decide

/-- POISON PROBE, range: an out-of-range displacement patches
    nothing. -/
theorem reloc_probe_aussen :
    multiPatch zeugenVerknuepft 1 (.rel32 2147483648) = none := by
  decide

/-- POISON PROBE, overlap: overlapping operand sites are not
    decided disjoint, so no multi-operand closing runs over them. -/
theorem reloc_probe_ueberlapp :
    opsDisjunktB [(0, .rel32 16), (1, .rel32 16)] = false := by
  decide

/-- POISON PROBE, missing handoff: without `anfang` the hosted
    relocation on the minimal image is refused. -/
theorem reloc_probe_ohne_anfang :
    relocOk .gehostet valZeuge 0 zeugenEintrittAusf schreibTor
      zeugenMoves (layoutFuer zeugenU 4096 8)
      { anfang := false, ende := true } 0 0 zeugenVerknuepft 0 16
      zeugenGepatcht = false :=
  reloc_verweigert_ohne_anfang _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl

/-- POISON PROBE, missing operand: the overrunning patch admits no
    hosted relocation. -/
theorem reloc_probe_ohne_patch :
    relocOk .gehostet valZeuge 0 zeugenEintrittAusf schreibTor
      zeugenMoves (layoutFuer zeugenU 4096 8) zeugenHaken 0 0
      [natByte 233, natByte 0, natByte 0] 0 16 zeugenGepatcht =
      false := by
  apply reloc_verweigert_ohne_patch
  rw [reloc_probe_ueberlauf]
  simp

/-- POISON PROBE, status: a handed status that differs from the
    returned one admits no freestanding relocation. -/
theorem reloc_probe_status :
    relocOk .frei valZeuge 0 zeugenEintrittAusf schreibTor zeugenMoves
      (layoutFuer zeugenU 4096 8) zeugenHaken 0 1 zeugenVerknuepft 0
      16 zeugenGepatcht = false :=
  reloc_verweigert_status _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide)

end Gabbro.Grammatik.X86.PipelineProfilesReloc
