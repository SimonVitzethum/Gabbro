/-
  File:      Grammatik/X86/ComposeVaCheck.lean
  Subject:   Composition closing: virtual-address closing.

  Lane 856: ONE checked closing step over already-accepted producers.
  Producers (reused by name, never re-proved): `AddressEncoding.adrEff`
  (with the pilot bridge `adrEff_basisForm`), `kanonisch48` and
  `fussZugelassen`; `AddressedHardwareExecution.adrPruefe` (with
  `adrPruefe_gleich_fuss` and the order lemmas), `adrLade`/`adrSpeichere`
  (with `adrLade_erfolg`, `adrSpeichere_erfolg`,
  `adrLade_basisForm_pilot`); `HardwareFaults.istKanonisch` and `adrKlasse`
  (with `adrKlasse_kanonisch_kein_fehler`); `ExceptionPriorityHardware`
  `SeitenInfo`/`seitenKlasse` (with both resolution lemmas).
  Consumer: the actual execution/footprint sites (`schritt`,
  `byteschritt`, `zugriff`), which discharge one data-access site by
  `ComposeVaCheck_verbindung` and refuse the planted cases. No second
  address model, decoder, executor or paging structure is invented here:
  mapped status is the caller-stated `SeitenInfo` present bit, never
  inferred from refusal.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.AddressEncoding
import Grammatik.X86.HardwareFaults
import Grammatik.X86.AddressedHardwareExecution
import Grammatik.X86.ExceptionPriorityHardware

namespace Gabbro.Grammatik.X86

/-- Canonical-form agreement: the accepted `kanonisch48` check and the
    accepted `istKanonisch` fault gate decide the same predicate. -/
theorem kanonisch48_istKanonisch (a : Adresse) :
    kanonisch48 a = istKanonisch a := rfl

/-- The one ordered closing classifier over a computed address: the
    accepted `adrPruefe` order (canonical, no-wrap, permission) mapped to
    architectural classes. Noncanonical addresses fault as #SS/#GP by the
    accepted `adrKlasse`; permission failures resolve to #GP/#PF from the
    caller-stated page state by `seitenKlasse`; the wrap edge and success
    carry no fault (validator refusal, never hardware). -/
def vaKlasse (pg : SeitenInfo) (m : Speicher) (a : Adresse)
    (schreiben stapel : Bool) : Option ArchFehler :=
  match adrPruefe m a schreiben with
  | some .unkanonisch => adrKlasse a stapel
  | some .keinLesen => some (seitenKlasse pg a)
  | some .keinSchreiben => some (seitenKlasse pg a)
  | some .umbruch => none
  | none => none

end Gabbro.Grammatik.X86
