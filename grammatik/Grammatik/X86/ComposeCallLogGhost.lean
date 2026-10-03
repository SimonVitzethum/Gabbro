/-
  File:      Grammatik/X86/ComposeCallLogGhost.lean
  Subject:   COMPOSITION CLOSING: inlining/selection with ghost call/return events.

  Producer legs (accepted, reused by name, never re-proved):
  * `AufrufOpt`: ghost pair (`geistPaar`: entry/return with ACTUAL `rho`/`v`/`s0`/`s1`,
    both the value and the `grund` reason channel) and its order preservation
    (`geistRekon_folge`, `geistRekon_folge_grund`) over the real source call log.
  * `InstructionSelection` (`Anweisungswahl`): the selector verdict `wahlOk`
    (a clobbering `xor` under live flags is refused).

  Interface closed here: an eliminated/inlined call site carries NO physical log
  event, so the site is legal only with the ghost pair re-emitted AND the order
  leg (`FolgeLog`) preserved. The checked Bool `senkeOk` encodes exactly the two
  armed side conditions of `geistRekon_folge`/`_grund`; `schlussOk` conjoins the
  ghost-order leg with the selector verdict. `ComposeCallLogGhost_verbindung`
  derives the ordered spliced log from the check; order loss refuses
  (`ComposeCallLogGhost_verweigert_*`, plus decided instances).
-/
import Grammatik.RufMaschineG
import Grammatik.Folge
import Grammatik.Semantik
import Grammatik.ZielOrtEinfadenZeuge
import Grammatik.FolgeBeweis
import Grammatik.FolgeZeuge
import Grammatik.X86.AufrufOpt
import Grammatik.X86.InstructionSelection

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik
open Anweisungswahl

variable {D : Deklaration}

/-- Checked ghost-order leg of one eliminated call site: exactly the two armed
    side conditions of `geistRekon_folge` (value channel) and
    `geistRekon_folge_grund` (reason channel) as a `Bool`. -/
def senkeOk (Φ : Folge D) (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D)
    (a : GeistAntwort D g) (rest : List (RufEreignisF D)) : Bool :=
  match a with
  | .ok v s1 =>
    (match rest with
      | [] => true
      | _ :: _ =>
        (!Pflichtig Φ (RufEreignisF.eintritt g rho s0)) || Armiert Φ rest) &&
    ((!Pflichtig Φ (RufEreignisF.rueck g rho v s0 s1)) ||
      Armiert Φ (RufEreignisF.eintritt g rho s0 :: rest))
  | .grund r s1 =>
    (match rest with
      | [] => true
      | _ :: _ =>
        (!Pflichtig Φ (RufEreignisF.eintritt g rho s0)) || Armiert Φ rest) &&
    ((!Pflichtig Φ (RufEreignisF.grund g rho r s0 s1)) ||
      Armiert Φ (RufEreignisF.eintritt g rho s0 :: rest))

/- CUTS (skeleton):
  - `schlussOk`, `ComposeCallLogGhost_verbindung` (+ `_zeuge`), refusals: open.
-/

end Gabbro.Grammatik.X86
