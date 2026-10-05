/-
  File:      Grammatik/X86/PipelineProfiles.lean
  Subject:   Checked hosted/freestanding profiles for the direct pipeline:
              ABI, image layout, entry sequence, support-code bytes and
              bindings for a hosted profile and a freestanding profile.

  Reused, not duplicated:
    - entry hooks: `ComposeEntryHooks.eintrittHakenZulassung`,
      `hakenZulassung_*`, `zeugenHaken`, `haken_zeuge_*`;
    - support bytes: `ComposeSupportBytes.stuetzOk`/`stuetzSchritt`,
      `stuetzOk_teile`, `stuetzSchritt_weiter`/`_verweigert_*`,
      `stuetz_verweigert_*`, `schreibLese_zeuge`;
    - profile selection: `ComposeProfileSelect.composeInstr`,
      `compose_zero`, `compose_bytes_revalidated`;
    - entry sequence: `PipelineEntry.prolog`/`prologPaare`/`prologOk`/
      `prologOk_teile`/`zuege_lauf`/`sysvParameter`;
    - image/loader: `ValidatorSkeleton.valX86`/`valZeuge`/`valWx`,
      `GateStub.schreibTor`/`torAusClobber`/`zeugenMoves`,
      `TableLayout.layoutFuer`/`zeugenU`/`zeugenLayout_ok`,
      `EntryExecution.eintrittZulassung`/`zeugenEintrittAusf`,
      `EntryState.profilEintritt` is new here (OS profile, not CPU `Profil`).
  No second loader, decoder, executor, IR or source interpreter. No
  implicit Linux/POSIX/libc/ELF: environment services stay user logic;
  only hardware behaviour is assumed.
-/
import Grammatik.X86.PipelineEntry
import Grammatik.X86.ComposeEntryHooks
import Grammatik.X86.ComposeSupportBytes
import Grammatik.X86.ComposeProfileSelect
import Grammatik.X86.TableLayout

namespace Gabbro.Grammatik.X86.PipelineProfiles

open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.PipelineEntry

/-- The two checked OS profiles: hosted (`main` under a C runtime) and
    freestanding (`nolibc` entry with the `os_anfang`/`os_ende` hooks). -/
inductive ZielProfil where
  | gehostet
  | frei
  deriving DecidableEq, Repr

/-- The entry kind each OS profile runs through (IMAGE-ABI section 5). -/
def profilEintritt : ZielProfil → EintrittArt
  | .gehostet => .hostedMain
  | .frei => .nolibcMain

/-- The integer parameter ABI of each OS profile: the System V AMD64
    order, stated per profile so a future target varies it as data. -/
def profilAbi : ZielProfil → List Register
  | .gehostet => sysvParameter
  | .frei => sysvParameter

/- CUTS (skeleton): profile vocabulary only; admission, refusals,
   entry-sequence execution and witnesses follow. -/

#print axioms profilEintritt
#print axioms profilAbi

end Gabbro.Grammatik.X86.PipelineProfiles
