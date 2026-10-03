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

/-! ## 1. The composed closing check: ghost order meets selector verdict. -/

/-- The composed closing check of one inlining/selection site: the ghost-order
    leg for the eliminated call AND the selector verdict for the chosen
    bytes. Either leg refuses the site. -/
def schlussOk (Φ : Folge D) (g : D.Fn) (rho : Env D (D.params g)) (s0 : World D)
    (a : GeistAntwort D g) (rest : List (RufEreignisF D))
    (wahl : List Befehl) (flagsLive : Bool) : Bool :=
  senkeOk Φ g rho s0 a rest && wahlOk flagsLive wahl

/-- VALUE CHANNEL: `senkeOk = true` discharges exactly the two side conditions
    of `geistRekon_folge`, with the actual argument environment, result value
    and entry/return worlds. -/
theorem senkeOk_ordnung_wert (Φ : Folge D) (g : D.Fn)
    (rho : Env D (D.params g)) (s0 s1 : World D) (v : ErgVal D (D.erg g))
    (rest : List (RufEreignisF D))
    (h : senkeOk Φ g rho s0 (.ok v s1) rest = true) :
    (rest ≠ [] →
      Pflichtig Φ (RufEreignisF.eintritt g rho s0) = true →
      Armiert Φ rest = true) ∧
    (Pflichtig Φ (RufEreignisF.rueck g rho v s0 s1) = true →
      Armiert Φ (RufEreignisF.eintritt g rho s0 :: rest) = true) := by
  simp only [senkeOk] at h
  have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  refine ⟨?_, ?_⟩
  · intro hne hp
    cases rest with
    | nil => exact absurd rfl hne
    | cons _ _ => simpa [hp] using h1
  · intro hp
    cases hpfl : Pflichtig Φ (RufEreignisF.rueck g rho v s0 s1) with
    | true => simpa [hpfl] using h2
    | false => simp [hp] at hpfl

/-- REASON CHANNEL: `senkeOk = true` discharges exactly the two side
    conditions of `geistRekon_folge_grund`. -/
theorem senkeOk_ordnung_grund (Φ : Folge D) (g : D.Fn)
    (rho : Env D (D.params g)) (s0 s1 : World D) (r : Fin (D.gruende g))
    (rest : List (RufEreignisF D))
    (h : senkeOk Φ g rho s0 (.grund r s1) rest = true) :
    (rest ≠ [] →
      Pflichtig Φ (RufEreignisF.eintritt g rho s0) = true →
      Armiert Φ rest = true) ∧
    (Pflichtig Φ (RufEreignisF.grund g rho r s0 s1) = true →
      Armiert Φ (RufEreignisF.eintritt g rho s0 :: rest) = true) := by
  simp only [senkeOk] at h
  have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  refine ⟨?_, ?_⟩
  · intro hne hp
    cases rest with
    | nil => exact absurd rfl hne
    | cons _ _ => simpa [hp] using h1
  · intro hp
    cases hpfl : Pflichtig Φ (RufEreignisF.grund g rho r s0 s1) with
    | true => simpa [hpfl] using h2
    | false => simp [hp] at hpfl

/-! ## 2. The composition: the checked site keeps the order leg. -/

/-- COMPOSITION CLOSING: an eliminated call site whose checked ghost-order leg
    passes splices exactly the ghost pair (actual arguments, actual answer on
    either channel, entry/return worlds) back into the physical log, and the
    order leg holds over the spliced log. -/
theorem ComposeCallLogGhost_verbindung (Φ : Folge D) (g : D.Fn)
    (rho : Env D (D.params g)) (s0 : World D) (a : GeistAntwort D g)
    (rest : List (RufEreignisF D))
    (hrest : FolgeLog Φ rest)
    (hok : senkeOk Φ g rho s0 a rest = true) :
    FolgeLog Φ (geistPaar g rho s0 a ++ rest) := by
  cases a with
  | ok v s1 =>
    have ⟨o1, o2⟩ := senkeOk_ordnung_wert Φ g rho s0 s1 v rest hok
    have h := geistRekon_folge Φ g rho s0 s1 v rest o1 hrest (fun _ => o2)
    simpa [geistPaar] using h
  | grund r s1 =>
    have ⟨o1, o2⟩ := senkeOk_ordnung_grund Φ g rho s0 s1 r rest hok
    have h := geistRekon_folge_grund Φ g rho s0 s1 r rest o1 hrest (fun _ => o2)
    simpa [geistPaar] using h

/-! ## 3. Refusals: order loss and an illegal selection refuse the site. -/

/-- SELECTION REFUSAL: the clobbering `xor` under live flags refuses the
    composed site for every ghost state -- the selector verdict is load-bearing
    in `schlussOk`, not decorative. -/
theorem ComposeCallLogGhost_verweigert_wahl (Φ : Folge D) (g : D.Fn)
    (rho : Env D (D.params g)) (s0 : World D) (a : GeistAntwort D g)
    (rest : List (RufEreignisF D)) (dst : Register) :
    schlussOk Φ g rho s0 a rest [.xorReg64 dst dst] true = false := by
  simp [schlussOk, wahlOk_verweigert_xor_le]

/-- ORDER REFUSAL: a failed ghost-order leg refuses the composed site for
    every selector choice -- order loss is never outvoted by the bytes. -/
theorem ComposeCallLogGhost_verweigert_senke (Φ : Folge D) (g : D.Fn)
    (rho : Env D (D.params g)) (s0 : World D) (a : GeistAntwort D g)
    (rest : List (RufEreignisF D)) (wahl : List Befehl) (flagsLive : Bool)
    (h : senkeOk Φ g rho s0 a rest = false) :
    schlussOk Φ g rho s0 a rest wahl flagsLive = false := by
  simp [schlussOk, h]

/-! ## 4. Decided instances: the good splice passes, order loss refuses. -/

/-- DECIDED ORDER LOSS: the ghost entry of `pruefe` behind a physical log whose
    newest event is the bare start entry (no return of `setze` behind it) fails
    the checked leg -- `decide`, no premise. -/
theorem ComposeCallLogGhost_ordnung_verloren :
    senkeOk Φ50 ePruefe .nil (eSp.welt [])
      (.ok () (eSp.welt []))
      [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])] = false := by
  decide

/-- DECIDED GOOD SPLICE: the ghost pair of `pruefe` over a physical log whose
    newest event is the return of `setze` passes the checked leg. -/
theorem ComposeCallLogGhost_splice_gut :
    senkeOk Φ50 ePruefe .nil (eSp.welt [])
      (.ok () (eSp.welt []))
      [RufEreignisF.rueck eSetze .nil () (eSp.welt []) (eSp.welt [])] = true := by
  decide

/-- DECIDED COMPOSED CHECK: the good ghost splice together with the
    flag-preserving zeroing choice passes the composed site check. -/
theorem ComposeCallLogGhost_schluss_gut :
    schlussOk Φ50 ePruefe .nil (eSp.welt [])
      (.ok () (eSp.welt []))
      [RufEreignisF.rueck eSetze .nil () (eSp.welt []) (eSp.welt [])]
      [.movImm64 .rax 0] true = true := by
  decide

/-- DECIDED COMPOSED REFUSAL: the same good ghost splice with the clobbering
    `xor` under live flags fails the composed site check. -/
theorem ComposeCallLogGhost_schluss_verweigert :
    schlussOk Φ50 ePruefe .nil (eSp.welt [])
      (.ok () (eSp.welt []))
      [RufEreignisF.rueck eSetze .nil () (eSp.welt []) (eSp.welt [])]
      [.xorReg64 .rax .rax] true = false := by
  decide

/- CUTS (skeleton):
  - `ComposeCallLogGhost_verbindung_zeuge`: open.
-/

end Gabbro.Grammatik.X86
