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

/-! ## 5. Joint witness on a non-degenerate source program. -/

/-- JOINT WITNESS: on the reached five-step run of the table-writing fixture
    program (call `setze`, its write `0 -> 5`, its return, call `pruefe`, its
    return) the thread log holds exactly the ghost pair of `pruefe` over the
    return of `setze` with the actual values; the checked leg passes there and
    the order leg holds there by the composition theorem. -/
theorem ComposeCallLogGhost_verbindung_zeuge :
    ∃ M : RufMaschineG eD,
      RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M ∧
      (eSp.slots () 0 ()).n = 0 ∧
      (eD.signatur eSetze).schreibt () = true ∧
      ∃ (rhoP : Env eD (eD.params ePruefe)) (wP bP : World eD)
        (vP : ErgVal eD (eD.erg ePruefe))
        (rhoS : Env eD (eD.params eSetze)) (vS : ErgVal eD (eD.erg eSetze))
        (aS bS : World eD) (rest : List (RufEreignisF eD)),
        (M.faeden 0).log =
          geistPaar ePruefe rhoP wP (.ok vP bP) ++
          (RufEreignisF.rueck eSetze rhoS vS aS bS :: rest) ∧
        (wP.slots () 0 ()).n = 5 ∧
        senkeOk Φ50 ePruefe rhoP wP (.ok vP bP)
          (RufEreignisF.rueck eSetze rhoS vS aS bS :: rest) = true ∧
        FolgeLog Φ50 (M.faeden 0).log := by
  have h00 : (RufStartG eP eSp eInit).faeden 0 = ⟨[], ⟨eHaupt, .nil, eSp.welt [],
      ⟨false, [], [], .nil, .ende eRumpfHaupt⟩⟩, [],
      [RufEreignisF.eintritt eHaupt .nil (eSp.welt [])]⟩ := rfl
  have hoff0 : offen ((RufStartG eP eSp eInit).faeden 0).spur = [] := rfl
  obtain ⟨M1, s1, hZ1⟩ := w_rufEnde (P := eP) (O := eO) (passes := 0) h00 eSetze .nil eHpSetze rfl
    (.cons (.call ePruefe .nil eHpPruefe rfl) (.ret .keine List.Perm.nil)) .nil rfl (ehg0 hoff0).heldIn
  have hoff1 : offen (M1.faeden 0).spur = [] := by
    rw [hZ1.spur, (Erw.lese _ _ _).offen]; exact hoff0
  obtain ⟨M2, s2, hZ2⟩ := w_blatt (P := eP) (O := eO) (passes := 0) hZ1.1
    _ _ _ rfl rfl (ehg0 (eoff_z hZ1 hoff1)).heldIn _ _ (execStmt_assignSlot _ _ _ _ _ _ _ _ _ _ _)
    ((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _))
  have hoff2 : offen (M2.faeden 0).spur = [] := by
    rw [hZ2.spur]
    exact (((Erw.lese _ _ _).trans (Erw.schreibSlot _ _ _ _ _ _)).offen).trans hoff1
  obtain ⟨M3, s3, hG3⟩ := w_rueckP (P := eP) (O := eO) (passes := 0) hZ2.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (ehg0 (eoff_z hZ2 hoff2)).heldIn
  have hoff3 : offen (M3.faeden 0).spur = [] := by
    rw [hG3.1]
    exact ((Erw.lese _ _ _).offen).trans hoff2
  obtain ⟨M4, s4, hZ4⟩ := w_rufEnde (P := eP) (O := eO) (passes := 0) hG3.1 ePruefe .nil eHpPruefe
    rfl (.ret .keine List.Perm.nil) .nil rfl (ehg0 (eoff_g hG3 hoff3)).heldIn
  have hoff4 : offen (M4.faeden 0).spur = [] := by
    rw [hZ4.spur, (Erw.lese _ _ _).offen]; exact hoff3
  obtain ⟨M5, s5, hG5⟩ := w_rueckP (P := eP) (O := eO) (passes := 0) hZ4.1 _ _ rfl
    (PopArt.wie rfl) _ _ _ rfl (ehg0 (eoff_z hZ4 hoff4)).heldIn
  have hr5 : RufErreichbarG eP eO 0 (RufStartG eP eSp eInit) M5 :=
    .schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ (.schritt _ _ _ .start s1)
      s2) s3) s4) s5
  have hlog5 : ∃ (rhoP : Env eD (eD.params ePruefe)) (wP bP : World eD)
      (vP : ErgVal eD (eD.erg ePruefe))
      (rhoS : Env eD (eD.params eSetze)) (vS : ErgVal eD (eD.erg eSetze))
      (aS bS : World eD) (rest : List (RufEreignisF eD)),
      (M5.faeden 0).log = RufEreignisF.rueck ePruefe rhoP vP wP bP ::
        RufEreignisF.eintritt ePruefe rhoP wP ::
        RufEreignisF.rueck eSetze rhoS vS aS bS :: rest := by
    rw [hG5.1]
    exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  obtain ⟨rhoP, wP, bP, vP, rhoS, vS, aS, bS, rest, hl5⟩ := hlog5
  have hm5 : RufEreignisF.eintritt ePruefe rhoP wP ∈ (M5.faeden 0).log := by
    rw [hl5]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hreq5 := ((eP_zertifiziert M5 hr5).1 0 _ hm5).1 _ _ _ rfl
  have hfol : FolgeLog Φ50 (M5.faeden 0).log :=
    (folgeG_erreichbar eSp eInit hr5 Φ50 eP_folge50 0).1
  rw [hl5] at hfol
  have hrest : FolgeLog Φ50 (RufEreignisF.rueck eSetze rhoS vS aS bS :: rest) :=
    hfol.2.2
  have e1 : Pflichtig Φ50 (RufEreignisF.eintritt ePruefe rhoP wP) = true := rfl
  have e2 : Armiert Φ50 (RufEreignisF.rueck eSetze rhoS vS aS bS :: rest) = true := rfl
  have e3 : Pflichtig Φ50 (RufEreignisF.rueck ePruefe rhoP vP wP bP) = false := rfl
  have hok : senkeOk Φ50 ePruefe rhoP wP (.ok vP bP)
      (RufEreignisF.rueck eSetze rhoS vS aS bS :: rest) = true := by
    simp [senkeOk, e1, e2, e3]
  refine ⟨M5, hr5, rfl, rfl, rhoP, wP, bP, vP, rhoS, vS, aS, bS, rest, ?_, ?_, hok, ?_⟩
  · rw [hl5]; rfl
  · exact of_decide_eq_true hreq5
  · rw [hl5]
    exact ComposeCallLogGhost_verbindung Φ50 ePruefe rhoP wP (.ok vP bP) _ hrest hok

/- CUTS:
  - No executable source-body inline rewrite: as in `AufrufOpt`, there is no
    function splicing a callee body at a call site, hence no proved body-splice
    simulation. What is closed here is the CHECKED site step: the ghost pair
    (`geistPaar`, actual values, both channels) re-emitted at the eliminated
    site preserves `FolgeLog` exactly under the recomputed `senkeOk` legs.
  - No target-byte execution of the ghost: ghost events are source call-log
    data (`RufEreignisF`), not emitted bytes; the byte side enters only through
    the selector verdict (`wahlOk`) in `schlussOk`. The lowering of ghost
    emission to the shared representation (QUELLBRUECKE, phase B) is the next
    dependency (owning lane: the bridge wave, not lane 833).
  - No concrete `grund`-channel decided instance: `eD.gruende` is `0` for every
    fixture function, so `Fin (eD.gruende _)` is empty; the reason channel is
    covered generically (`senkeOk_ordnung_grund`, the `grund` case of the
    composition) but has no closed fixture inhabitant.
  - Return-duty extraction stays where `AufrufOpt` left it: only the entry half
    is derived; the composition carries the actual answer values but does not
    discharge `ensures`.
  - Indirect calls, bounds/depth, budget timing, concurrency transfer: untouched,
    as in the producer legs.
-/

#print axioms senkeOk_ordnung_wert
#print axioms senkeOk_ordnung_grund
#print axioms ComposeCallLogGhost_verbindung
#print axioms ComposeCallLogGhost_verbindung_zeuge
#print axioms ComposeCallLogGhost_verweigert_wahl
#print axioms ComposeCallLogGhost_verweigert_senke
#print axioms ComposeCallLogGhost_ordnung_verloren
#print axioms ComposeCallLogGhost_splice_gut
#print axioms ComposeCallLogGhost_schluss_gut
#print axioms ComposeCallLogGhost_schluss_verweigert

end Gabbro.Grammatik.X86
