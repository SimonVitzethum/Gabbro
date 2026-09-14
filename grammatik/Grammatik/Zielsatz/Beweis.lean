/-
  File:      Grammatik/Zielsatz/Beweis.lean -- PLAN-ZIELSATZ.md step 4:
             `GabbroZiel` (Spec.lean) assembled from the flagship theorems.

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

  THE ONE GAP: the event `e0`. The replay behind `ziel_ort_mehrfaden_ende`
  and `ziel_ort_mehrfaden_invGrund` (`popS_kopf`, `rahmenWelt`,
  ZielOrtRahmenSem.lean) needs an inhabitant `e0 : Ereignis D` to give every
  recorded call answer a fresh trace position, so the recorded handler is a
  function (`FunkV`, `KurzV`). `Ereignis D.mitRuhe` is inhabited exactly when
  `D` declares a table, a global or a lock (`ereignis_iff`); the idle root
  adds a FUNCTION, and events name carriers and locks only. For a
  declaration with none of the three the world is a single point
  (`World D` has no memory and an always-empty trace), every key of the
  record collapses to (callee, parameters), and the replay would need that
  two returns of one callee with equal parameters return equal values -- a
  determinism lemma for machine G that the tree does not have (the CUT
  "Declarations without any table, global and lock" of ZielOrtBeweis.lean).

  WHAT IS PROVED, therefore:
  * `gabbro_ziel_ereignis` : `GabbroZielEreignis` -- `GabbroZiel` for every
    declaration that declares a table, a global or a lock (`Nonempty
    (Ereignis D)`, not a premise of `GabbroZiel` itself).
  * `gabbro_ziel_teil` : for EVERY declaration (no event), the legs that do
    not go through the replay: `speicherSicher`, `rennfrei`,
    `keinStartGrund`, `keineVerklemmung`, `zeit`.
  * `gabbro_ziel_leer` : for a declaration WITHOUT table, global and lock,
    additionally `sperrInv`, `invRueck`, `invGrund` (vacuous there).
  * Open for such a declaration: `vertrag`, `startEnde`, `keinLogikHalt`,
    `fortschritt` (which uses `keinLogikHalt`).
  `gabbro_ziel : GabbroZiel` is NOT proved.
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
    declaration; `e0` for the replay). -/
theorem ziel_aus (P : Programm D) (S : SperrInv D) (Q : AxEns D) (fs : Aufzaehlung D.Fn)
    (ls : Aufzaehlung D.Lock) (ws : List D.Fn) (e0 : Ereignis D)
    (hA : AkzeptiertSpec P S fs.1 ws) (hN : NutzerPflicht P S Q) (O : Orakel D)
    (hH : HardwareAnnahmen O Q) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hZ : StartZulaessig P S fs.1 ws sp init)
    (M : RufMaschineG D) (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    Ziel P S O passes (RufStartG P sp init) M := by
  obtain ⟨hFrag, hAbg, hW, hFuss, hSO, hStart, hSstart, hex, hSt, hLeer, -⟩ :=
    Akzeptiert_ok fs.2 hA hZ
  have hS : SperrInvOk S := ⟨hSO, hN.2.1⟩
  have hGrund : StartOhneGrund init := fun t => (wurzel_of hA hZ t).2
  have main := ziel_ort_mehrfaden_ende P O Q S fs.1 sp init e0 (kVon P fs.1 init) hH.1 hH.2.1
    hH.2.2 hN.2.2 hS fs.2 hFrag hAbg hW hFuss (fun pa f => (hN.1 pa f).1) hStart hSstart hex
    (fun pa f => (hN.1 pa f).2.1) hGrund passes M hr
  have hIG := ziel_ort_mehrfaden_invGrund P O Q S fs.1 sp init e0 (kVon P fs.1 init) hH.1 hH.2.1
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

/-- The legs that do not go through the replay, for any program meeting the
    premise groups -- no event needed. -/
theorem ziel_teil_aus (P : Programm D) (S : SperrInv D) (Q : AxEns D) (fs : Aufzaehlung D.Fn)
    (ls : Aufzaehlung D.Lock) (ws : List D.Fn)
    (hA : AkzeptiertSpec P S fs.1 ws) (O : Orakel D)
    (hH : HardwareAnnahmen O Q) (passes : Nat) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hZ : StartZulaessig P S fs.1 ws sp init)
    (M : RufMaschineG D) (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    SpurInv M ∧ RennfreiBis P O passes (RufStartG P sp init) M ∧ KeinStartGrundG M ∧
      ((∀ t, ¬ FertigG M t → WartetG M t) → ∀ t, FertigG M t) ∧ ZeitAb P O passes M := by
  obtain ⟨-, -, -, -, -, -, -, -, hSt, hLeer, -⟩ := Akzeptiert_ok fs.2 hA hZ
  exact ⟨spurInv_erreichbar hH.1 sp init hr, rennfreiBis_of fs.2 hA hZ hH.1 passes M,
    keinStartGrundG (fun t => (wurzel_of hA hZ t).2) hr,
    fun hWt => keine_verklemmungG hH.1 hSt sp init hLeer ls.1 ls.2 hr hWt,
    fun f g n _ _ _ hadm hE _ run hA' => frame_schritte_beschraenkt P O passes f g n hadm hE run hA'⟩

end Aus

/-! ## 2. The event, on `D.mitRuhe` -/

/-- **`D.mitRuhe` has an event exactly when `D` declares a table, a global
    or a lock.** The idle root adds a function, and no event names one. -/
theorem ereignis_iff : Nonempty (Ereignis D.mitRuhe) ↔
    Nonempty D.Tab ∨ Nonempty D.Glob ∨ Nonempty D.Lock := by
  constructor
  · rintro ⟨e⟩
    cases e with
    | zugriff t _ _ _ => exact Or.inl ⟨t⟩
    | gzugriff g _ _ _ => exact Or.inr (Or.inl ⟨g⟩)
    | nimmt L _ => exact Or.inr (Or.inr ⟨L⟩)
    | gibt L => exact Or.inr (Or.inr ⟨L⟩)
  · rintro (h | h | h)
    · obtain ⟨t⟩ := h
      exact ⟨.zugriff (D := D.mitRuhe) t false [] []⟩
    · obtain ⟨g⟩ := h
      exact ⟨.gzugriff (D := D.mitRuhe) g false [] []⟩
    · obtain ⟨L⟩ := h
      exact ⟨.gibt (D := D.mitRuhe) L⟩

/-! ## 3. The goal, for declarations with an event -/

/-- **`GabbroZiel` for every declaration that declares a table, a global or
    a lock** -- the statement of `Spec.lean` with the one extra hypothesis
    `Nonempty (Ereignis D)` right after the checker's Bool. -/
def GabbroZielEreignis : Prop :=
  ∀ (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (P : Programm D) (S : SperrInv D)
    (Q : AxEns D) (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock)
    (cs : Aufzaehlung (D.Tab ⊕ D.Glob)) (ws : List D.Fn),
    C.akzeptiert P S fs.1 ls.1 cs.1 ws = true →
    Nonempty (Ereignis D) →
    NutzerPflicht P S Q →
    ∀ O : Orakel D, HardwareAnnahmen O Q →
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      StartZulaessig P.mitRuhe S.mitRuhe (fsRuhe fs.1) (wsRuhe ws) sp init →
      ∀ M : RufMaschineG D.mitRuhe,
        RufErreichbarG P.mitRuhe O.mitRuhe passes (RufStartG P.mitRuhe sp init) M →
          Ziel P.mitRuhe S.mitRuhe O.mitRuhe passes (RufStartG P.mitRuhe sp init) M

/-- **THE GOAL, for every declaration with a table, a global or a lock.** -/
theorem gabbro_ziel_ereignis : GabbroZielEreignis := by
  intro C D _ P S Q fs ls cs ws hC ⟨e0⟩ hN O hH passes sp init hZ M hr
  have hA := akzeptiertSpec_mitRuhe P fs.2 (C.korrekt P S fs ls cs ws hC)
  exact ziel_aus P.mitRuhe S.mitRuhe (axEnsRuhe Q) ⟨fsRuhe fs.1, fsRuhe_voll fs.2⟩ ls (wsRuhe ws)
    (evR e0) hA (nutzerPflicht_mitRuhe hN) O.mitRuhe (hardware_mitRuhe hH) passes sp init hZ M hr

/-! ## 4. Every declaration: the legs without the replay -/

/-- **The legs of `GabbroZiel` that hold for EVERY declaration** (no event):
    memory safety, race freedom, no start frame at a reason return, no
    deadlock, time. -/
theorem gabbro_ziel_teil (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (P : Programm D)
    (S : SperrInv D) (Q : AxEns D) (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock)
    (cs : Aufzaehlung (D.Tab ⊕ D.Glob)) (ws : List D.Fn)
    (hC : C.akzeptiert P S fs.1 ls.1 cs.1 ws = true) (_hN : NutzerPflicht P S Q)
    (O : Orakel D) (hH : HardwareAnnahmen O Q) (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hZ : StartZulaessig P.mitRuhe S.mitRuhe (fsRuhe fs.1) (wsRuhe ws) sp init)
    (M : RufMaschineG D.mitRuhe)
    (hr : RufErreichbarG P.mitRuhe O.mitRuhe passes (RufStartG P.mitRuhe sp init) M) :
    SpurInv M ∧ RennfreiBis P.mitRuhe O.mitRuhe passes (RufStartG P.mitRuhe sp init) M ∧
      KeinStartGrundG M ∧ ((∀ t, ¬ FertigG M t → WartetG M t) → ∀ t, FertigG M t) ∧
      ZeitAb P.mitRuhe O.mitRuhe passes M :=
  ziel_teil_aus P.mitRuhe S.mitRuhe (axEnsRuhe Q) ⟨fsRuhe fs.1, fsRuhe_voll fs.2⟩ ls (wsRuhe ws)
    (akzeptiertSpec_mitRuhe P fs.2 (C.korrekt P S fs ls cs ws hC)) O.mitRuhe (hardware_mitRuhe hH)
    passes sp init hZ M hr

/-- **Without a table, a global and a lock** the lock-invariant and the
    table-invariant legs hold outright: there is no lock, and no invariant
    is owed (its carriers are tables, and there are none). -/
theorem gabbro_ziel_leer (P : Programm D) (S : SperrInv D) (hT : D.Tab → False)
    (hL : D.Lock → False) (M : RufMaschineG D.mitRuhe) :
    SperrInvG S.mitRuhe M ∧ InvAmOrtG P.mitRuhe M ∧ InvAmGrundG P.mitRuhe M := by
  have hs : ∀ (g : D.mitRuhe.Fn) (i : D.Inv), schuldet g i = false := by
    intro g i
    unfold schuldet
    cases h : D.traeger i with
    | nil => rfl
    | cons t _ => exact (hT t).elim
  refine ⟨fun L _ => (hL L).elim, fun _ _ _ g _ _ _ _ _ i _ hsi => ?_,
    fun _ _ _ g _ _ _ _ _ i _ hsi => ?_⟩
  · rw [hs g i] at hsi; cases hsi
  · rw [hs g i] at hsi; cases hsi

#print axioms Gabbro.Grammatik.Zielsatz.ziel_aus
#print axioms Gabbro.Grammatik.Zielsatz.ziel_teil_aus
#print axioms Gabbro.Grammatik.Zielsatz.ereignis_iff
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_ereignis
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_teil
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_leer

end Gabbro.Grammatik.Zielsatz
