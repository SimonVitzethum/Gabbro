module

public import Grammatik.Zielsatz.Atomar.AtomarZiel
public import Grammatik.Speichermodell.Maschine.GXMaschine
public import Grammatik.Zielsatz.Faeden.Verbund
public import Grammatik.Logik.Fortschritt.Hungerfrei
public import Grammatik.Bausteine.Arena.Ownership.Ruhe.Start
public import Grammatik.Zielsatz.Atomar.BeweisAtomar.Teil1
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz
open Gabbro.Grammatik Speichermodell
variable {D : Deklaration}

/-- **The goal on every run of machine GX** (every thread live, nothing spawned): the reading
    of `GabbroZiel` over plain GX runs, as `gabbro_ziel_g` is the reading of the statement of
    before over G runs. -/
theorem gabbro_ziel_gx (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (E : Einheit D)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflichtA E)
    (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Laufzeit E sp init) (M : RufMaschineG D.mitRuhe)
    (hr : RufErreichbarGX E.P.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (RufStartG E.P.mitRuhe sp init) M) :
    ZielX E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (GeteiltV (D := D) E.P E.ws)
      (RufStartG E.P.mitRuhe sp init) M :=
  (gabbro_ziel C D E fs ls cs hC hN O hH passes sp init hL (fun _ => true)
    (FadenMaschine.alleLebend M) (fadenErreichbarX_von_GX hr)).g

/-- **On a declaration without an `atomic` global, (b) with the rely is (b)**: no read of a
    shared atomic exists. -/
theorem nutzerPflichtA_ohne_atomar {D : Deklaration} [DecidableEq D.Fn] {E : Einheit D}
    (hat : ∀ g : D.Glob, D.atomar g = false) (h : NutzerPflicht E) : NutzerPflichtA E :=
  ⟨logikPflichtA_of_frei (fun f c _ hc => by
      obtain ⟨g, _, hg⟩ := hc.1
      rw [hat g] at hg
      cases hg) h.logik, h.start⟩

/-! ## 5. The embedding: the statement of before follows -/

section Einbettung

variable {P : Programm D} {S : SperrInv D} {O : Orakel D} {passes : Nat}
  {Tg : D.Tab ⊕ D.Glob → Prop}

/-- **With no shared atomic, `ZielX` is `Ziel`.** -/
theorem ziel_of_X (hT : ∀ c, ¬ Tg c) {M0 M : RufMaschineG D}
    (h : ZielX P S O passes Tg M0 M) : Ziel P S O passes M0 M where
  speicherSicher := h.speicherSicher
  rennfrei := rennfreiBis_of_GA h.rennfrei
  schwach := fun ord W W' u hr hWg hs => by
    obtain ⟨σ, M'', wahl, neu, hs'⟩ := hs
    exact gx_leer_g hT (h.schwach ord W W' u σ M'' wahl neu hr hWg hs').1
  vertrag := h.vertrag
  sperrInv := h.sperrInv
  invRueck := h.invRueck
  invGrund := h.invGrund
  invRuhe := h.invRuhe
  invSicht := h.invSicht
  sperrWechsel := fun u M' L hs => h.sperrWechsel u M' L (gx_aus_g hs)
  sperrSicht := fun u M' hs => h.sperrSicht u M' (gx_aus_g hs)
  startEnde := h.startEnde
  keinStartGrund := h.keinStartGrund
  keinLogikHalt := h.keinLogikHalt
  keineVerklemmung := h.keineVerklemmung
  keinZyklus := h.keinZyklus
  keinKernHalt := kernHaltE_of_EA h.keinKernHalt
  fortschritt := h.fortschritt
  zeit := fun f g n rho s0 k hadm hE M2 run hA => by
    have h1 := h.zeit f g n rho s0 k hadm hE M2 (SegLauf.alsX (Tg := Tg) run)
      (aktivVor_alsX f k run hA)
    rw [segZaehle_alsX] at h1
    exact h1
  folge := h.folge

/-- **With no shared atomic, `ZielFX` is `ZielF`.** -/
theorem zielF_of_X (hT : ∀ c, ¬ Tg c) {M0 : RufMaschineG D} {K : FadenMaschine D}
    {B : List (ArenaOwnership.Body.ArenaIface D)} (h : ZielFX P S O passes Tg M0 B K) : ZielF P S O passes M0 K where
  g := ziel_of_X hT h.g
  schlafendUnberuehrt := h.schlafendUnberuehrt
  schlafendFrei := h.schlafendFrei
  joinFrei := h.joinFrei
  keineVerklemmung := h.keineVerklemmung
  keinZyklus := h.keinZyklus
  fortschritt := fortschrittF_aus h.g.fortschritt
  spawnSicht := fun K' t hs => h.spawnSicht K' t (fadenSchrittX_of hs)

variable [DecidableEq D.Fn]

/-- **A unit the checker of before accepts has no shared atomic at all**: every footprint
    carrier is signature-guarded, lock-protected or thread-local (`FussS`), so no carrier is read
    by one start while another writes it without a guard. -/
theorem geteiltA_leer {fs ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {A : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpec P S fs ws A) (c : D.Tab ⊕ D.Glob) : ¬ GeteiltA P ws c := by
  rintro ⟨_, hB, hR⟩
  apply hR
  intro w₁ hw₁ w₂ hw₂ hne f g hf hcf hg
  have lokal : (sigB f c || lokW P fs ws c) = true → TraegerSchreibt g c = false := by
    intro h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨L, hL, _⟩ := sigB_ok h
      exact absurd hL (hB L)
    · have hG : Getrennt P fs ws c := @of_decide_eq_true _ (Classical.propDecidable _) h
      exact (getrenntR_iff hvoll hA.abg c).mpr hG w₁ hw₁ w₂ hw₂ hne f g hf hcf hg
  rcases List.mem_append.mp hcf with hc | hc
  · rcases (hA.fuss f).1 c hc with h | ⟨L, hL, _⟩
    · exact lokal h
    · exact absurd hL (hB L)
  · exact lokal ((hA.fuss f).2 c hc)

theorem geteiltV_leer {fs ws : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {A : List (Kernzelle.AccumulatorDecl D)}
    (hA : AkzeptiertSpec P S fs ws A) (c : D.Tab ⊕ D.Glob) : ¬ GeteiltV P ws c :=
  fun h => geteiltA_leer hvoll hA c h.1

end Einbettung

/-- **THE STATEMENT OF BEFORE, DERIVED.** Every checker of before is a checker for the rely
    (`Pruefer.alsX`), on every unit it accepts (b) and (b) with the rely coincide
    (`nutzerPflichtA_of_akzeptiert`), every thread-machine run over G is one over GX
    (`fadenErreichbarX_of`), and such a unit has no admitted shared atomic (`geteiltV_leer`), so
    `ZielFX` there is `ZielF` (`zielF_of_X`). Since 2026-10-24 for every unit of before: one
    without an arena (`hB`); `Pruefer.alsX` adds the ownership acceptance, which such a unit passes.
    Since 2026-11-02 (C15) for every unit without an accumulator (`hA`); `Pruefer.alsX` adds the
    accumulator admission and neutral initialization, which such a unit passes vacuously.
    On a unit WITH an arena the statement of before is `gabbro_ziel_sc` (proved directly). -/
theorem gabbro_ziel_sc_aus (h : GabbroZiel) (C : Pruefer) (D : Deklaration) [DecidableEq D.Fn]
    (E : Einheit D) (hB : E.arenen = []) (hA : E.akku = []) (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock)
    (cs : Aufzaehlung (D.Tab ⊕ D.Glob)) (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerPflicht E)
    (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)) (hL : Laufzeit E sp init)
    (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe)
    (hK : FadenErreichbar E.P.mitRuhe O.mitRuhe passes (FadenStart E.P.mitRuhe sp init lebt0) K) :
    ZielF E.P.mitRuhe E.S.mitRuhe O.mitRuhe passes (RufStartG E.P.mitRuhe sp init) K := by
  have hA0 := C.korrekt E fs ls cs hC
  have hZ := h C.alsX D E fs ls cs (C.alsX_akzeptiert hB hA hC) (nutzerPflichtA_of_akzeptiert fs.2 hA0 hN) O hH passes sp
    init hL lebt0 K (fadenErreichbarX_of hK)
  refine zielF_of_X ?_ hZ
  exact fun c => geteiltV_leer fs.2 hA0 c

/-! ## 6. Linked units -/

section Verbund

variable [DecidableEq D.Fn] {E₁ E₂ : Einheit D} {e : D.Fn → Bool}

/-- **The linked unit is accepted by the checker of before**, from two units each accepted WITH
    the rely: the link check's `lok` makes every carrier a function relies on without a lock
    thread-local over the composed hulls -- shared atomics included -- so the linked footprints
    need no rely. The per-body components are each unit's own. -/
theorem akzeptiertSpec_verbindeX {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {B₁ B₂ : List (ArenaOwnership.Body.ArenaIface D)}
    {A₁ A₂ : List (Kernzelle.AccumulatorDecl D)}
    (hA₁ : AkzeptiertSpecX E₁.P E₁.S fs E₁.ws B₁ A₁)
    (hA₂ : AkzeptiertSpecX E₂.P E₂.S fs E₂.ws B₂ A₂)
    (hV : Verbindbar E₁ E₂) (hS : SchnittstelleSpec fs e E₁ E₂) :
    AkzeptiertSpec (verbinde e E₁ E₂).P (verbinde e E₁ E₂).S fs (verbinde e E₁ E₂).ws [] := by
  have hH := huelle_of_reach (e := e) (E₁ := E₁) (E₂ := E₂) hvoll hS.keinRueckruf
  have hfrag : ∀ f, ((teilP e E₁ E₂ f).rumpf f).gOk
      (kandB (teilP e E₁ E₂ f) fs (fussOrteG (teilP e E₁ E₂ f) f)) (fun _ => true) = true := by
    intro f
    unfold teilP
    cases e f
    · exact List.all_eq_true.mp hA₂.frag f (hvoll f)
    · exact List.all_eq_true.mp hA₁.frag f (hvoll f)
  have hGetrennt : ∀ c, LokBedarf e E₁ E₂ c →
      Getrennt (verbinde e E₁ E₂).P fs (verbinde e E₁ E₂).ws c := by
    intro c hc w₁ hw₁ w₂ hw₂ hne f g hf hcf hg
    refine hS.lok c hc w₁ hw₁ w₂ hw₂ hne f g (hH w₁ f hf) ?_ (hH w₂ g hg)
    rw [← fussOrteG_teil hV]
    exact hcf
  refine ⟨?_, abg_verbinde hvoll hA₁.abg hA₂.abg hS.blatt₁ hS.blatt₂, ?_, ?_, hA₁.sperrOrte,
    ?_, ?_, ?_, ?_, ?_, Kernzelle.accumulatorAdmission_leer _ _, hA₁.reset⟩
  · refine List.all_eq_true.mpr fun f _ => ?_
    show ((verbindeP e E₁ E₂).rumpf f).gOk
      (kandB (verbindeP e E₁ E₂) fs (fussOrteG (verbindeP e E₁ E₂) f)) (fun _ => true) = true
    rw [verbindeP_rumpf, kandB_teil hV fs f, fussOrteG_teil hV]
    exact hfrag f
  · intro f
    have hlok : ∀ c, LokBedarf e E₁ E₂ c → lokW (verbinde e E₁ E₂).P fs (verbinde e E₁ E₂).ws c = true :=
      fun c hc => @decide_eq_true _ (Classical.propDecidable _) (hGetrennt c hc)
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have hc' : c ∈ fussOrte (teilP e E₁ E₂ f) f := by
        rw [← fussOrte_teil hV]
        exact hc
      by_cases hs : sigB f c = true
      · exact Or.inl (by rw [hs, Bool.true_or])
      · by_cases hg : ∃ L, Bewacht c L ∧ c ∈ E₁.S.orte L
        · exact Or.inr hg
        · refine Or.inl ?_
          rw [hlok c ⟨f, Or.inl ⟨hc', by simpa using hs, hg⟩⟩, Bool.or_true]
    · have hc' : c ∈ ((teilP e E₁ E₂ f).rumpf f).regs.flatMap D.rtraeger := by
        rw [← verbindeP_rumpf]
        exact hc
      by_cases hs : sigB f c = true
      · rw [hs, Bool.true_or]
      · rw [hlok c ⟨f, Or.inr ⟨hc', by simpa using hs⟩⟩, Bool.or_true]
  · intro f
    show Grammatik.mE (bodenM f) ((verbindeP e E₁ E₂).rumpf f) = true
    rw [verbindeP_rumpf]
    unfold teilP
    cases e f
    · exact hA₂.stufen f
    · exact hA₁.stufen f
  · intro w hw
    rcases mem_ws_verbinde hw with h | h
    · exact hA₁.wurzeln w h
    · exact hA₂.wurzeln w h
  · intro w hw
    obtain ⟨h1, h2, h3⟩ := hS.einzeln w hw
    exact ⟨h1, h2, fun f hf c hc => h3 f (hH w f hf) c hc⟩
  · intro c hB hAt w₁ hw₁ w₂ hw₂ hne g hg hgc h hh
    have := hS.renn c hB hAt w₁ hw₁ w₂ hw₂ hne g (hH w₁ g hg) hgc h (hH w₂ h hh)
    have e' : fussOrteG (verbinde e E₁ E₂).P h = fussOrteG (teilP e E₁ E₂ h) h := fussOrteG_teil hV h
    rw [e']
    exact this
  · intro f x hx
    change x ∈ ((verbindeP e E₁ E₂).rumpf f).ants at hx
    rw [verbindeP_rumpf] at hx
    unfold teilP at hx
    cases hf : e f
    · rw [hf] at hx
      exact hA₂.antworten f x hx
    · rw [hf] at hx
      exact hA₁.antworten f x hx
  · intro w hw h hh
    show Grammatik.mE (NurMaskiert D) ((verbindeP e E₁ E₂).rumpf h) = true
    rw [verbindeP_rumpf]
    exact hS.masken w hw h (hH w h hh)

/-- The rely duty of a unit implies its duty of before. -/
theorem nutzerTeil_of_A {eigen : D.Fn → Bool} {E : Einheit D} (h : NutzerTeilA eigen E) :
    NutzerTeil eigen E :=
  ⟨⟨fun pa f hf => ⟨koerperGutS_of_A (h.logik.1 pa f hf).1, invGutS_of_A (h.logik.1 pa f hf).2.1,
    invGutGrund_of_A (h.logik.1 pa f hf).2.2⟩, h.logik.2.1, h.logik.2.2⟩, h.start⟩

/-- On a unit the checker of before accepts, its duty of before is its rely duty. -/
theorem nutzerTeilA_of {eigen : D.Fn → Bool} {E : Einheit D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertSpec E.P E.S fs E.ws E.akku) (h : NutzerTeil eigen E) :
    NutzerTeilA eigen E :=
  ⟨⟨fun pa f hf => ⟨koerperGutSA_of_frei (akzeptiert_liest_nicht_geteilt hvoll hA f)
      (h.logik.1 pa f hf).1,
    invGutSA_of_frei (akzeptiert_liest_nicht_geteilt hvoll hA f) (h.logik.1 pa f hf).2.1,
    invGutGrundA_of_frei (akzeptiert_liest_nicht_geteilt hvoll hA f) (h.logik.1 pa f hf).2.2⟩,
    h.logik.2.1, h.logik.2.2⟩, h.start⟩

end Verbund

/-- **LINKING WITH THE ATOMIC RELY, PROVED.** -/
theorem gabbro_ziel_verbund : GabbroZielVerbund := by
  intro C D _ E₁ E₂ e fs ls cs h₁ h₂ hV hS hN₁ hN₂ hQ O hH passes sp init hL lebt0 K hK
  have hA := akzeptiertSpec_verbindeX fs.2 (C.korrekt E₁ fs ls cs h₁).1 (C.korrekt E₂ fs ls cs h₂).1
    hV hS
  -- the linked unit without its arenas: the linked statement claims no ownership
  let E : Einheit D := { verbinde e E₁ E₂ with arenen := [] }
  have hB : akzeptiertX_pruefer.akzeptiert E fs.1 ls.1 cs.1 = true :=
    (Bool.and_eq_true _ _).mpr
      ⟨(Bool.and_eq_true _ _).mpr
        ⟨akzeptiertX_of_akzeptiert ((akzeptiert_iff fs.2 ls.2 cs.2 []).mpr hA), besitzB_leer rfl⟩,
      Kernzelle.akkuStartB_leer E⟩
  have hN : NutzerPflichtA (verbinde e E₁ E₂) := nutzerPflichtA_of_akzeptiert fs.2 hA
    (nutzerPflicht_verbinde hV hQ (nutzerTeil_of_A hN₁) (nutzerTeil_of_A hN₂))
  exact gabbro_ziel akzeptiertX_pruefer D E fs ls cs hB ⟨hN.logik, ⟨hN.start.sperren, hN.start.req⟩⟩
    O hH passes sp init ⟨hL.lader, hL.start, hL.einmal⟩ lebt0 K hK

/-- **THE LINKED STATEMENT OF BEFORE, DERIVED**, for two units of before (no arena, `hB₁`, `hB₂`). -/
theorem gabbro_ziel_verbund_sc_aus (h : GabbroZielVerbund) (C : Pruefer) (D : Deklaration)
    [DecidableEq D.Fn] (E₁ E₂ : Einheit D) (hB₁ : E₁.arenen = []) (hB₂ : E₂.arenen = [])
    (hA₁ : E₁.akku = []) (hA₂ : E₂.akku = []) (e : D.Fn → Bool)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (h₁ : C.akzeptiert E₁ fs.1 ls.1 cs.1 = true) (h₂ : C.akzeptiert E₂ fs.1 ls.1 cs.1 = true)
    (hV : Verbindbar E₁ E₂) (hS : SchnittstelleSpec fs.1 e E₁ E₂) (hN₁ : NutzerTeil e E₁)
    (hN₂ : NutzerTeil (fun f => !e f) E₂) (hQ : E₂.Q = E₁.Q) (O : Orakel D) (hH : HardwareAnnahmen O E₁.Q)
    (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f))
    (hL : Laufzeit (verbinde e E₁ E₂) sp init) (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe)
    (hK : FadenErreichbar (verbinde e E₁ E₂).P.mitRuhe O.mitRuhe passes
      (FadenStart (verbinde e E₁ E₂).P.mitRuhe sp init lebt0) K) :
    ZielF (verbinde e E₁ E₂).P.mitRuhe (verbinde e E₁ E₂).S.mitRuhe O.mitRuhe passes
      (RufStartG (verbinde e E₁ E₂).P.mitRuhe sp init) K := by
  have hA₁ := C.korrekt E₁ fs ls cs h₁
  have hA₂ := C.korrekt E₂ fs ls cs h₂
  have hZ := h C.alsX D E₁ E₂ e fs ls cs (C.alsX_akzeptiert hB₁ hA₁ h₁) (C.alsX_akzeptiert hB₂ hA₂ h₂) hV hS (nutzerTeilA_of fs.2 hA₁ hN₁)
    (nutzerTeilA_of fs.2 hA₂ hN₂) hQ O hH passes sp init hL lebt0 K (fadenErreichbarX_of hK)
  refine zielF_of_X ?_ hZ
  exact fun c => geteiltV_leer fs.2 (akzeptiertSpec_verbinde fs.2 hA₁ hA₂ hV hS) c

#print axioms Gabbro.Grammatik.Zielsatz.zielX_aus
#print axioms Gabbro.Grammatik.Zielsatz.zielFX_aus
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_sc_aus
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_gx
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_verbund
#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel_verbund_sc_aus

end Gabbro.Grammatik.Zielsatz
