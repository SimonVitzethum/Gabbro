/-
  File:      Grammatik/Zielsatz/AtomarZiel.lean
  Subject:   THE GOAL WITH SHARED ATOMICS IN THE SHAPE OF `GabbroZiel`: checker, (b) with the
             rely, hardware assumptions, the runtime's start with the idle root, every machine W
             reaches (Opus lane O25b, 2026-09-26). Standalone: `Spec.lean` is unchanged.

  * `PrueferX` -- a checker whose soundness target is `AkzeptiertSpecX`; `akzeptiertX_pruefer`
    is the concrete one (`AkzeptiertX`).
  * `akzeptiertSpecX_mitRuhe` -- the checker's facts transfer to `P.mitRuhe` (the idle root is in
    no footprint, and a user function keeps its footprint, contracts, graph and guards).
  * `geteiltA_mitRuhe_rueck` -- a shared atomic of `P.mitRuhe` is one of `P`, so the user's
    obligation with the rely on `P` is the one on `P.mitRuhe` (`logikPflichtA_mitRuhe`).
  * **`gabbro_ziel_atomar`** -- for every checker `C : PrueferX`, every unit it accepts, the
    user's logic with the rely (`NutzerPflichtA`), the named hardware assumptions and the
    runtime's start (`Laufzeit`): every machine W reaches, for every order assignment, satisfies
    `ZielAtomar` -- every leg of `Ziel` in its form with shared atomics.
  * `gabbro_ziel_atomar_vor` -- the EMBEDDING: the premises of `gabbro_ziel` (a `Pruefer`,
    `NutzerPflicht`) give the premises here, so every unit the goal covers today is covered.

  WHAT IS NOT HERE: the thread machine (`ZielF`: spawn and join legs over GX), the linked
  statement (`GabbroZielVerbund`), and the Rust checker's alignment with `AkzeptiertX`.
-/
import Grammatik.Zielsatz.AtomarAkzeptiert
import Grammatik.Zielsatz.AtomarRuheNutzer
import Grammatik.Zielsatz.Beweis

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

section Transfer

variable [DecidableEq D.Fn] (P : Programm D) {S : SperrInv D} {fs ws : List D.Fn}

/-- Thread-locality on `P.mitRuhe` is thread-locality on `P`. -/
theorem getrennt_mitRuhe_rueck (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ w, AbgK P fs (reachB P fs w)) {c : D.Tab ⊕ D.Glob}
    (h : Getrennt P.mitRuhe (fsRuhe fs) (wsRuhe ws) c) : Getrennt P fs ws c := by
  intro w₁ hw₁ w₂ hw₂ hne f g hf hc hg
  have := h (some w₁) (mem_wsRuhe.mpr ⟨w₁, hw₁, rfl⟩) (some w₂) (mem_wsRuhe.mpr ⟨w₂, hw₂, rfl⟩)
    (by
      rcases hne with hne | hne
      · exact Or.inl fun e => hne (Option.some.inj e)
      · exact Or.inr ((mehrfach_map_inj (fun a b e => Option.some.inj e)).mpr hne))
    (some f) (some g) (by rw [reachB_mitRuhe P hvoll hAbg]; exact hf)
    (by rw [fussOrteG_mitRuhe]; exact hc) (by rw [reachB_mitRuhe P hvoll hAbg]; exact hg)
  rw [traegerSchreibt_mitRuhe] at this
  exact this

/-- **A shared atomic of `P.mitRuhe` is a shared atomic of `P`.** -/
theorem geteiltA_mitRuhe_rueck (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ w, AbgK P fs (reachB P fs w)) {c : D.Tab ⊕ D.Glob}
    (h : GeteiltA P.mitRuhe (wsRuhe ws) c) : GeteiltA P ws c := by
  obtain ⟨⟨g, e, ha⟩, hB, hR⟩ := h
  refine ⟨⟨g, e, ha⟩, fun L hL => hB L ((bewacht_mitRuhe (D := D) c L).mpr hL), fun hR' => hR ?_⟩
  refine (getrenntR_iff (fsRuhe_voll hvoll) (abg_mitRuhe P hvoll hAbg) c).mpr
    (getrennt_mitRuhe P hvoll hAbg ((getrenntR_iff hvoll hAbg c).mp hR'))

omit [DecidableEq D.Fn] in
/-- `VertragsFrei` transfers to `P.mitRuhe` (the root has `requires true`, `ensures true` and
    owes nothing). -/
theorem vertragsFrei_mitRuhe {c : D.Tab ⊕ D.Glob} (h : VertragsFrei P c) :
    VertragsFrei P.mitRuhe c
  | none => ⟨List.not_mem_nil, List.not_mem_nil, by rw [invOrteP_mitRuhe_ruhe]; exact List.not_mem_nil⟩
  | some f => ⟨by rw [requires_mitRuhe_orte]; exact (h f).1,
      by rw [ensures_mitRuhe_orte]; exact (h f).2.1,
      by rw [invOrteP_mitRuhe]; exact (h f).2.2⟩

/-- **The footprint property with the admitted shared atomics transfers to `P.mitRuhe`.** -/
theorem fussSX_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    (h : ∀ f, FussSX P S (lokW P fs ws) (GeteiltV P ws) f) :
    ∀ f', FussSX P.mitRuhe S.mitRuhe (lokW P.mitRuhe (fsRuhe fs) (wsRuhe ws))
      (GeteiltV P.mitRuhe (wsRuhe ws)) f'
  | none => ⟨fun c hc => by rw [fussOrte_mitRuhe_ruhe] at hc; exact absurd hc List.not_mem_nil,
      fun c hc => absurd hc List.not_mem_nil⟩
  | some f => by
      obtain ⟨h1, h2⟩ := h f
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · rw [fussOrte_mitRuhe] at hc
        rcases h1 c hc with h3 | ⟨L, hL, hcL⟩ | ⟨⟨⟨g, e, ha⟩, hB, hR⟩, hV⟩
        · left
          simp only [Bool.or_eq_true] at h3 ⊢
          rw [sigB_mitRuhe]
          exact h3.imp id (lokW_mitRuhe P hvoll hAbg)
        · exact Or.inr (Or.inl ⟨L, (bewacht_mitRuhe (D := D) c L).mpr hL, hcL⟩)
        · cases hl : lokW P.mitRuhe (fsRuhe fs) (wsRuhe ws) c
          · refine Or.inr (Or.inr ⟨⟨⟨g, e, ha⟩, fun L hL => hB L ((bewacht_mitRuhe (D := D) c L).mp hL),
              fun hR' => ?_⟩, vertragsFrei_mitRuhe P hV⟩)
            have hg := (getrenntR_iff (fsRuhe_voll hvoll) (abg_mitRuhe P hvoll hAbg) c).mp hR'
            unfold lokW at hl
            rw [@decide_eq_true _ (Classical.propDecidable _) hg] at hl
            cases hl
          · left
            simp
      · have hc' : c ∈ (P.rumpf f).regs.flatMap D.rtraeger := by
          have e := rumpf_mitRuhe_regs P f
          exact e ▸ hc
        have h3 := h2 c hc'
        simp only [Bool.or_eq_true] at h3 ⊢
        rw [sigB_mitRuhe]
        exact h3.imp id (lokW_mitRuhe P hvoll hAbg)

/-- **Transfer of the checker's facts with the rely to `P.mitRuhe`.** -/
theorem akzeptiertSpecX_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertSpecX P S fs ws) :
    AkzeptiertSpecX P.mitRuhe S.mitRuhe (fsRuhe fs) (wsRuhe ws) where
  frag := frag_mitRuhe P hA.frag
  abg := abg_mitRuhe P hvoll hA.abg
  fuss := fussSX_mitRuhe P hvoll hA.abg hA.fuss
  stufen := stufen_mitRuhe P hA.stufen
  sperrOrte := fun L c hc => (bewacht_mitRuhe (D := D) c L).mpr (hA.sperrOrte L c hc)
  wurzeln := fun w' hw' => by
    obtain ⟨w, hw, rfl⟩ := mem_wsRuhe.mp hw'
    exact hA.wurzeln w hw
  einzeln := einzelnPool_mitRuhe P hvoll hA.abg hA.einzeln
  renn := fun c hB hAt => schreibGetrennt_mitRuhe P hvoll hA.abg
    (hA.renn c (fun L hL => hB L ((bewacht_mitRuhe (D := D) c L).mpr hL)) hAt)
  antworten
    | none, _, hx => absurd hx List.not_mem_nil
    | some f, x, hx => (stelleOk_mitRuhe (D := D) x).mpr
        (hA.antworten f x (by rw [← rumpf_mitRuhe_ants P f]; exact hx))

end Transfer

/-- **A checker for the rely**: its soundness target is `AkzeptiertSpecX`. -/
structure PrueferX where
  akzeptiert : ∀ {D : Deklaration} [DecidableEq D.Fn],
    Einheit D → List D.Fn → List D.Lock → List (D.Tab ⊕ D.Glob) → Bool
  korrekt : ∀ {D : Deklaration} [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    akzeptiert E fs.1 ls.1 cs.1 = true → AkzeptiertSpecX E.P E.S fs.1 E.ws

/-- **The concrete checker with the rely**: its Bool is `AkzeptiertX`. -/
def akzeptiertX_pruefer : PrueferX where
  akzeptiert := fun E fs ls cs => AkzeptiertX E.P E.S fs ls cs E.ws
  korrekt := fun _ fs ls cs h => akzeptiertSpecX_of fs.2 ls.2 cs.2 h

/-- **Every checker of the goal is a checker for the rely** (`akzeptiertSpecX_of_spec`). -/
def Pruefer.alsX (C : Pruefer) : PrueferX where
  akzeptiert := C.akzeptiert
  korrekt := fun E fs ls cs h => akzeptiertSpecX_of_spec (C.korrekt E fs ls cs h)

/-- **THE GOAL WITH SHARED ATOMICS.** For every checker `C` for the rely, every declaration and
    unit `E` it accepts, the user's logic with the rely (bodies against every answer a shared
    atomic read may give, AND the start), the named hardware assumptions and the runtime's
    start of `E` (A4, with the idle root): for every order assignment of the atomics, every
    machine W reaches -- views, messages, racing atomics -- satisfies every leg of `ZielAtomar`
    over the admitted shared atomics of `P.mitRuhe`. -/
theorem gabbro_ziel_atomar (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflichtA E)
    (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat)
    (ord : D.mitRuhe.Glob → Ordnung) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Laufzeit E sp init) :
    ∀ W : RufMaschineW D.mitRuhe,
      RufErreichbarW E.P.mitRuhe O.mitRuhe passes ord (RufStartW (RufStartG E.P.mitRuhe sp init)) W →
      ZielAtomar E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes ord (GeteiltV E.P.mitRuhe (wsRuhe E.ws))
        (RufStartG E.P.mitRuhe sp init) W := by
  have hA := C.korrekt E fs ls cs hC
  have hN' : LogikPflichtA E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q)
      (GeteiltA E.P.mitRuhe (wsRuhe E.ws)) := by
    have h := logikPflichtA_mitRuhe hN.logik
    exact ⟨fun passes f => ⟨koerperGutSA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA.abg hc)
        (h.1 passes f).1,
      invGutSA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA.abg hc) (h.1 passes f).2.1,
      invGutGrundA_mono (fun c hc => geteiltA_mitRuhe_rueck E.P fs.2 hA.abg hc) (h.1 passes f).2.2⟩,
      h.2⟩
  exact ziel_atomar_spec E.P.mitRuhe E.S.mitRuhe (axEnsRuhe E.Q) (fsRuhe_voll fs.2) ls.2
    (wsRuhe E.ws) (akzeptiertSpecX_mitRuhe E.P fs.2 hA) hN' O.mitRuhe (hardware_mitRuhe hH) passes
    ord sp init (startZulaessig_aus E fs.1 hN.start hL)

/-- **THE EMBEDDING: every unit `gabbro_ziel` covers is covered here**, with the premises of
    `gabbro_ziel` -- a goal checker, the user obligation WITHOUT the rely (on such a unit the two
    obligations are equivalent, `logikPflichtA_iff_akzeptiert`). -/
theorem gabbro_ziel_atomar_vor (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflicht E)
    (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat)
    (ord : D.mitRuhe.Glob → Ordnung) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Laufzeit E sp init) :
    ∀ W : RufMaschineW D.mitRuhe,
      RufErreichbarW E.P.mitRuhe O.mitRuhe passes ord (RufStartW (RufStartG E.P.mitRuhe sp init)) W →
      ZielAtomar E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes ord (GeteiltV E.P.mitRuhe (wsRuhe E.ws))
        (RufStartG E.P.mitRuhe sp init) W :=
  gabbro_ziel_atomar C.alsX D E fs ls cs hC
    (nutzerPflichtA_of_akzeptiert fs.2 (C.korrekt E fs ls cs hC) hN) O hH passes ord sp init hL

#print axioms Gabbro.Grammatik.Zielsatz.akzeptiertSpecX_mitRuhe
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_atomar
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_atomar_vor

end Gabbro.Grammatik.Zielsatz
