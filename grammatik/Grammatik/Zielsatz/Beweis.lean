/-
  File:      Grammatik/Zielsatz/Beweis.lean -- PLAN-ZIELSATZ.md step 4:
             `GabbroZiel` (Spec.lean) PROVED: `gabbro_ziel`.

  THE CHAIN. From the premises of `GabbroZiel` on the program `E` (code
  `E.P`, lock invariants `E.S`, axiom ensures `E.Q`, declared starts
  `E.starts`, initial memory `E.sp0`; since 2026-09-15):
  * (a) `C.akzeptiert E … = true` -- `C.korrekt` -> `AkzeptiertSpec E.P E.S
    fs E.ws` -> `akzeptiertSpec_mitRuhe` -> `AkzeptiertSpec P.mitRuhe
    S.mitRuhe (fsRuhe fs) (wsRuhe ws)` (Zielsatz/Ruhe.lean);
  * (b) `NutzerPflicht E` = `LogikPflicht E.P E.S E.Q` (-> `logikPflicht_mitRuhe`
    -> the obligation on `P.mitRuhe` with `S.mitRuhe` and `axEnsRuhe Q`,
    Zielsatz/RuheNutzer.lean) and `StartPflicht E`;
  * (c) `HardwareAnnahmen O E.Q` -> `hardware_mitRuhe` -> on `O.mitRuhe`;
  * (d) `Laufzeit E sp init`, with `StartPflicht E` -> `startZulaessig_aus`
    -> `StartZulaessig P.mitRuhe S.mitRuhe (fsRuhe fs) (wsRuhe ws) sp init`.
  `ziel_aus` then derives every leg of `Ziel` on ANY program meeting
  `AkzeptiertSpec`, `LogikPflicht`, `HardwareAnnahmen`, `StartZulaessig`
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
  * `keinZyklus` (`KeinWarteZyklus`)   -- `kein_warteZyklusG` (the same rank invariant;
                                          2026-09-15, verdict F2);
  * `fortschritt` (`FortschrittG`)     -- `fortschrittG_aus` (`AkzeptiertSpec.antworten`: a
                                          head at an empty answer type is an axiom `-> never`,
                                          since W1; the `keinLogikHalt` leg,
                                          a lock-free hence duplicate-free start trace,
                                          and `bereichG_mehrfaden`: every float range
                                          check passes, since the body obligation excludes
                                          `logik bereich` -- verdict F1);
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

/-! ## 0. No wait cycle (verdict F2) -/

section Zyklus

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **NO WAIT CYCLE FROM LOCK RANKS.** On every reachable machine there are no threads
    `t₀, …, tₙ₊₁ = t₀` with each `tᵢ` at `locks Lᵢ` while `tᵢ₊₁` holds `Lᵢ` -- whatever the
    other threads do. Along such a chain the ranks rise strictly (`sperre_rang`: every lock a
    thread holds ranks below the lock it stands at), and the last link closes it:
    `rang L₀ ≤ rang Lₙ < rang L₀`. -/
theorem kein_warteZyklusG (hO : GutO O) (hSt : StufenM P) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hLeer : ∀ t, D.haelt (init t).1 = [])
    {M : RufMaschineG D} (hr : RufErreichbarG P O passes (RufStartG P sp init) M) :
    KeinWarteZyklus M := by
  have hI := fun t => rangInvG_erreichbar hO hSt sp init (startSpur_nodup_leer init hLeer) hr t
  intro n ts Ls hW he
  have hlt : ∀ i, i < n → D.rang (Ls i) < D.rang (Ls (i + 1)) := fun i hi =>
    (sperre_rang (hI (ts (i + 1))) (hW (i + 1) hi).1).2 (Ls i) (hW i (Nat.le_of_lt hi)).2
  have hle : ∀ i, i ≤ n → D.rang (Ls 0) ≤ D.rang (Ls i) := by
    intro i
    induction i with
    | zero => intro _; exact Int.le_refl _
    | succ i ih =>
        intro hi
        have h1 := hlt i hi
        have h2 := ih (Nat.le_of_succ_le hi)
        omega
  have h1 := (hW n (Nat.le_refl n)).2
  rw [he] at h1
  have hlast := (sperre_rang (hI (ts 0)) (hW 0 (Nat.zero_le n)).1).2 (Ls n) h1
  have := hle n (Nat.le_refl n)
  omega

end Zyklus

/-! ## 1. Every leg, for any program meeting the four premise groups -/

section Aus

variable [DecidableEq D.Fn]

/-- **The legs of `Ziel` from the premise groups** (generic in the
    declaration; no event needed). -/
theorem ziel_aus (P : Programm D) (S : SperrInv D) (Q : AxEns D) (fs : Aufzaehlung D.Fn)
    (ls : Aufzaehlung D.Lock) (ws : List D.Fn)
    (hA : AkzeptiertSpec P S fs.1 ws) (hN : LogikPflicht P S Q) (O : Orakel D)
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
    keinZyklus := kein_warteZyklusG hH.1 hSt sp init hLeer hr
    fortschritt := fortschrittG_aus hH.1 hSt sp init (startSpur_nodup_leer init hLeer) hr
      main.1.1.2.2.1
      (bereichG_mehrfaden P O passes Q S fs.1 sp init (kVon P fs.1 init) hH.1 hH.2.1 hH.2.2
        hN.2.2 hS fs.2 hFrag hAbg hW hFuss (fun f => (hN.1 passes f).1) hStart hSstart hex M hr)
      hA.antworten
    zeit := fun f g n _ _ _ hadm hE _ run hA' =>
      frame_schritte_beschraenkt P O passes f g n hadm hE run hA' }

end Aus

/-! ## 2. The start, from (b) and (d) -/

section Start

variable [DecidableEq D.Fn]

/-- **The start the proof works with, derived** (2026-09-15): the runtime's
    start (d) and the user's start obligation (b) give an admissible start
    of `P.mitRuhe`. Before, `StartZulaessig` was itself the premise, and its
    `req`/`sperren` belonged to no premise group (verdict P1). -/
theorem startZulaessig_aus (E : Einheit D) (fs : List D.Fn) (hN : StartPflicht E)
    {sp : Speicher D.mitRuhe}
    {init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)}
    (hL : Laufzeit E sp init) :
    StartZulaessig E.P.mitRuhe E.S.mitRuhe (fsRuhe fs) (wsRuhe E.ws) sp init where
  wurzel t := by
    rcases hL.start t with h | ⟨a, ha, h⟩
    · rw [h]
      exact Or.inr (ruhig_mitRuhe E.P)
    · rw [h]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem ha))
  einmal t u htu he := by
    rcases hL.einmal t u htu he with h | ⟨w, hw, hm⟩
    · rw [h]
      exact Or.inl (ruhig_mitRuhe E.P)
    · rw [hw]
      exact Or.inr (hm.map some)
  req t := by
    show ReqAmEintritt E.P.mitRuhe (init t).1 (sp.welt []) (init t).2
    rcases hL.start t with h | ⟨a, ha, h⟩
    · rw [h]
      rfl
    · rw [h, hL.lader]
      exact (req_mitRuhe_iff E.P a.1 (E.sp0.welt []) a.2).mpr (hN.req a ha)
  sperren L := by
    show E.S.inv L (speicherZ sp) = true
    rw [hL.lader, speicherZ_speicherR]
    exact hN.sperren L

end Start

/-! ## 3. The goal -/

/-- **GABBRO_ZIEL, PROVED.** For every checker `C`, every declaration and
    program `E` accepted by it, the user's logic (bodies AND start), the
    named hardware assumptions and the runtime's start of `E` (A4, with the
    idle root): every leg of `Ziel` on every reachable machine. -/
theorem gabbro_ziel : GabbroZiel := by
  intro C D _ E fs ls cs hC hN O hH passes sp init hL M hr
  have hA := akzeptiertSpec_mitRuhe E.P fs.2 (C.korrekt E fs ls cs hC)
  exact ziel_aus E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q) ⟨fsRuhe fs.1, fsRuhe_voll fs.2⟩ ls
    (wsRuhe E.ws) hA (logikPflicht_mitRuhe hN.logik) O.mitRuhe (hardware_mitRuhe hH) passes sp
    init (startZulaessig_aus E fs.1 hN.start hL) M hr

#print axioms Gabbro.Grammatik.Zielsatz.kein_warteZyklusG
#print axioms Gabbro.Grammatik.Zielsatz.ziel_aus
#print axioms Gabbro.Grammatik.Zielsatz.startZulaessig_aus
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel

end Gabbro.Grammatik.Zielsatz
