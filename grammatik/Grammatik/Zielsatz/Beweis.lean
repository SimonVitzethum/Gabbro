/-
  File:      Grammatik/Zielsatz/Beweis.lean -- PLAN-ZIELSATZ.md step 4:
             `GabbroZiel` (Spec.lean) PROVED: `gabbro_ziel`.

  THE CHAIN. From the premises of `GabbroZiel` on `P`:
  * (a) `C.akzeptiert … = true` -- `C.korrekt` -> `AkzeptiertSpec P S fs ws`
    -> `akzeptiertSpec_mitRuhe` -> `AkzeptiertSpec P.mitRuhe S.mitRuhe
    (fsRuhe fs) (wsRuhe ws)` (Zielsatz/Ruhe.lean);
  * (b) `NutzerPflicht P S Q` -> `nutzerPflicht_mitRuhe` -> the obligation on
    `P.mitRuhe` with `S.mitRuhe` and `axEnsRuhe Q` (Zielsatz/RuheNutzer.lean);
  * (c) `HardwareAnnahmen O Q` -> `hardware_mitRuhe` -> on `O.mitRuhe`;
  * (d) `StartZulaessig P.mitRuhe …` as given.
  `ziel_aus` then derives every leg of `Ziel` on ANY program meeting
  `AkzeptiertSpec`, `NutzerPflicht`, `HardwareAnnahmen`, `StartZulaessig`
  (generic in the declaration), and is instantiated with `P.mitRuhe`.

  PER LEG (`ziel_aus`):
  * `speicherSicher` (`SpurInv`)       -- `spurInv_erreichbar` (`GutO`);
  * `rennfrei` (`RennfreiBis`)         -- `rennfreiBis_of` (AkzeptiertSpec + StartZulaessig + `GutO`);
  * `vertrag`, `sperrInv`, `keinLogikHalt`, `invRueck`, `startEnde`, `keinStartGrund`
                                       -- `ziel_ort_mehrfaden_ende` with the computed call
                                          graphs `kVon` (`Akzeptiert_ok`), `SperrInvOk` =
                                          `sperrOrte` + `SperrInvLokal`, `StartOhneGrund`
                                          from `wurzel_of`;
  * `invGrund` (`InvAmGrundG`)         -- `ziel_ort_mehrfaden_invGrund`;
  * `keineVerklemmung`                 -- `keine_verklemmungG` (`StufenM`, starts without
                                          signature locks, `ls` complete);
  * `fortschritt` (`FortschrittG`)     -- `fortschrittG_aus` (the `keinLogikHalt` leg,
                                          a lock-free hence duplicate-free start trace);
  * `zeit` (`ZeitAb`)                  -- `frame_schritte_beschraenkt`, per frame: `ZeitAb`
                                          carries its own `rufTief` admission, so no
                                          program-wide premise is needed.

  THE FORMER GAP, CLOSED (2026-09-14): the event `e0`. The replay behind
  `ziel_ort_mehrfaden_ende` and `ziel_ort_mehrfaden_invGrund` keyed every
  recorded call and axiom answer at a FRESH trace position, one event past
  the key world, so the recorded handler is a function (`FunkV`). A
  declaration with no table, no global and no lock has no event: every
  world is one point (`welt_eq`) and a key is only (callee, parameters). The
  replay now keeps such records functional by JUSTIFICATION instead
  (`Begruendet`, SperreBeweis.lean §0b): a recorded answer is what the
  callee's body ends in against every handler repeating the callee's own
  justified record, and two justified answers with one key are equal
  (`begruendet_eindeutig`, by induction on the justification). That is the
  determinism of machine G such a declaration needs, obtained from the
  replay itself, without a lemma over the 70 rules and without touching the
  rules or `Spec.lean`. With an event nothing changed (the fresh piece is
  `frischSpur`, an event's `neutral` trace piece). `e0` is gone from every
  theorem of the chain.
-/
import Grammatik.Zielsatz.RuheNutzer
import Grammatik.Zielsatz.Ruhe
import Grammatik.ZielOrtStart
import Grammatik.ZielOrtInvGrund
import Grammatik.Fortschritt

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Every leg, for any program meeting the four premise groups -/

section Aus

variable [DecidableEq D.Fn]

/-- **The legs of `Ziel` from the premise groups** (generic in the
    declaration; no event needed). -/
theorem ziel_aus (P : Programm D) (S : SperrInv D) (Q : AxEns D) (fs : Aufzaehlung D.Fn)
    (ls : Aufzaehlung D.Lock) (ws : List D.Fn)
    (hA : AkzeptiertSpec P S fs.1 ws) (hN : NutzerPflicht P S Q) (O : Orakel D)
    (hH : HardwareAnnahmen O Q) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hZ : StartZulaessig P S fs.1 ws sp init)
    (M : RufMaschineG D) (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    Ziel P S O passes (RufStartG P sp init) M := by
  obtain ⟨hFrag, hAbg, hW, hFuss, hSO, hStart, hSstart, hex, hSt, hLeer, -⟩ :=
    Akzeptiert_ok fs.2 hA hZ
  have hS : SperrInvOk S := ⟨hSO, hN.2.1⟩
  have hGrund : StartOhneGrund init := fun t => (wurzel_of hA hZ t).2
  have main := ziel_ort_mehrfaden_ende P O Q S fs.1 sp init (kVon P fs.1 init) hH.1 hH.2.1
    hH.2.2 hN.2.2 hS fs.2 hFrag hAbg hW hFuss (fun pa f => (hN.1 pa f).1) hStart hSstart hex
    (fun pa f => (hN.1 pa f).2.1) hGrund passes M hr
  have hIG := ziel_ort_mehrfaden_invGrund P O Q S fs.1 sp init (kVon P fs.1 init) hH.1 hH.2.1
    hH.2.2 hN.2.2 hS fs.2 hFrag hAbg hW hFuss (fun pa f => (hN.1 pa f).1) hStart hSstart hex
    (fun pa f => (hN.1 pa f).2.2) passes M hr
  exact {
    speicherSicher := spurInv_erreichbar hH.1 sp init hr
    rennfrei := rennfreiBis_of fs.2 hA hZ hH.1 passes M
    vertrag := main.1.1.1
    sperrInv := main.1.1.2.1
    invRueck := main.1.2
    invGrund := hIG
    startEnde := main.2.1
    keinStartGrund := main.2.2
    keinLogikHalt := main.1.1.2.2.1
    keineVerklemmung := fun hWt => keine_verklemmungG hH.1 hSt sp init hLeer ls.1 ls.2 hr hWt
    fortschritt := fortschrittG_aus hH.1 hSt sp init (startSpur_nodup_leer init hLeer) hr
      main.1.1.2.2.1
    zeit := fun f g n _ _ _ hadm hE _ run hA' =>
      frame_schritte_beschraenkt P O passes f g n hadm hE run hA' }

end Aus

/-! ## 2. The goal -/

/-- **GABBRO_ZIEL, PROVED.** For every checker `C`, every declaration and
    program accepted by it, the user's logic, the named hardware
    assumptions and every admissible start of `P` with the runtime's idle
    root: every leg of `Ziel` on every reachable machine. -/
theorem gabbro_ziel : GabbroZiel := by
  intro C D _ P S Q fs ls cs ws hC hN O hH passes sp init hZ M hr
  have hA := akzeptiertSpec_mitRuhe P fs.2 (C.korrekt P S fs ls cs ws hC)
  exact ziel_aus P.mitRuhe S.mitRuhe (axEnsRuhe Q) ⟨fsRuhe fs.1, fsRuhe_voll fs.2⟩ ls (wsRuhe ws)
    hA (nutzerPflicht_mitRuhe hN) O.mitRuhe (hardware_mitRuhe hH) passes sp init hZ M hr

#print axioms Gabbro.Grammatik.Zielsatz.ziel_aus
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel

end Gabbro.Grammatik.Zielsatz
