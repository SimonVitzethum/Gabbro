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

end Gabbro.Grammatik.X86.PipelineProfilesReloc
