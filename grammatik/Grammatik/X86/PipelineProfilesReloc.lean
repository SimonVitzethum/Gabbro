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

end Gabbro.Grammatik.X86.PipelineProfilesReloc
