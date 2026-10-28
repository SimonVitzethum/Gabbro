import Grammatik.Zielsatz.Projekte.Zeuge
import Grammatik.Speichermodell.Atomar.AtomarGleich

/-!
  File:      Grammatik/Zielsatz/Projekte/Verbund.lean
  Subject:   **Separate compilation of any number of units, every leg** (BUILD-SYSTEM 7.7).

  A program linked from units each CHECKED ALONE: every unit is accepted by the checker on its own
  (its verdict is reused, by content, in every program that links it), and one LINK CHECK decides
  what only the whole program can decide (`BindeSpec`). Then every leg of the goal holds for the
  linked program, with nothing restricted:

  * any number of units (`Projekt`), each owning functions (`eigen`) and locks (`sperren`);
  * callbacks and calls in every direction (the link check reads the composed call graph);
  * shared atomics across units (the footprint rule over the composed roots admits them; each unit
    proved its bodies against the open-world rely);
  * ownership across units: arenas of every unit, every body against every arena;
  * differing assumptions (the program assumes the conjunction, `qAlle`) and differing initial
    memories (`Passend`: each unit initializes its own carriers);
  * one lock order over the composed program (the floors of the link declaration).

  What each unit decides alone (`einheit_teil`): the fragment, the lock floors, the answer sites,
  the ownership check of its bodies against its own arenas, its roots and its arenas' words -- all
  per body or per declaration. What the link decides (`BindeSpec`): closed call graphs, footprints
  with thread-locality and shared atomics, pool safety, write separation and the interrupt masks
  over the composed graph, the ownership check of a body against an arena of another unit, and the
  ownership start. `akzeptiertSpecX_komponiere` puts them together; `gabbro_ziel_verbund_n` is
  `gabbro_ziel` on the linked unit.
-/

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

/-- The ownership check of ONE body against one arena (`Checked` is this at every function). -/
def CheckedAt (P : Programm D) (A : FreiForm D) (I : ArenaOwnership.Body.Interfaces A) (f : D.Fn) :
    Prop :=
  ArenaOwnership.Body.OE A I (V := vertragVon D f) (I f).output ArenaOwnership.Body.noLoop
    (ArenaOwnership.Source.Flow.parameterContext (I f).parameters) (P.rumpf f)

theorem checked_iff (P : Programm D) (A : FreiForm D) (I : ArenaOwnership.Body.Interfaces A) :
    ArenaOwnership.Body.Checked P A I ↔ ∀ f, CheckedAt P A I f := Iff.rfl

/-- The unit whose body of `f` the linked program runs: the first owner. -/
def besitzerVon (ps : List (Projekt D)) (f : D.Fn) : Option (Projekt D) := ps.find? fun p => p.eigen f

/-- **THE LINK CHECK** over the linked unit `K = komponiere B ps`: what depends on more than one
    body or on the composed roots. -/
structure BindeSpec [DecidableEq D.Fn] (fs : List D.Fn) (B : Einheit D) (ps : List (Projekt D)) : Prop where
  abg : ∀ w, AbgK (komponiere B ps).P fs (reachB (komponiere B ps).P fs w)
  fuss : ∀ f, FussSX (komponiere B ps).P (komponiere B ps).S
    (lokW (komponiere B ps).P fs (komponiere B ps).ws)
    (GeteiltV (komponiere B ps).P (komponiere B ps).ws) f
  einzeln : EinzelnPool (komponiere B ps).P fs (komponiere B ps).ws
  renn : ∀ c, (∀ L, ¬ Bewacht c L) → ¬ AtomarAusgenommen c →
    SchreibGetrennt (komponiere B ps).P fs (komponiere B ps).ws c
  masken : MaskenDisziplin (komponiere B ps).P fs
  -- a body against an arena its own unit does not declare
  besitzFremd : ∀ a ∈ (komponiere B ps).arenen, ∀ f,
    (∀ p, besitzerVon ps f = some p → a ∉ p.E.arenen) → CheckedAt (komponiere B ps).P a.A a.I f
  besitzStart : BesitzStart (komponiere B ps)

/-! ## Each unit's own verdict -/

section Teil

variable {B : Einheit D} {ps : List (Projekt D)}

theorem besitzer_mem {f : D.Fn} {p : Projekt D} (h : besitzerVon ps f = some p) :
    p ∈ ps ∧ p.eigen f = true ∧ koerperVon B.P ps f = p.E.P.rumpf f := by
  unfold besitzerVon at h
  refine ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h, ?_⟩
  unfold koerperVon
  rw [h]

theorem besitzer_da (hD : Deckend ps) (f : D.Fn) : ∃ p, besitzerVon ps f = some p := by
  unfold besitzerVon
  cases h : ps.find? (fun p => p.eigen f) with
  | none =>
      obtain ⟨p, hp, he⟩ := hD f
      exact absurd he (by simpa using List.find?_eq_none.mp h p hp)
  | some p => exact ⟨p, rfl⟩

theorem komponiere_rumpf {f : D.Fn} {p : Projekt D} (h : besitzerVon ps f = some p) :
    (komponiere B ps).P.rumpf f = p.E.P.rumpf f := (besitzer_mem h).2.2

/-- Under the owner's program and the linked one, the footprint of `f` is the same. -/
theorem fussOrteG_besitzer (hV : ∀ p ∈ ps, Passend B p) {f : D.Fn} {p : Projekt D}
    (h : besitzerVon ps f = some p) : fussOrteG (komponiere B ps).P f = fussOrteG p.E.P f := by
  rw [passend_P (hV p (besitzer_mem (B := B) h).1)]
  exact fussOrteG_mitRumpf2 B.P _ _ f (besitzer_mem (B := B) h).2.2

theorem kandB_besitzer (hV : ∀ p ∈ ps, Passend B p) {p : Projekt D} (hp : p ∈ ps) (fs : List D.Fn) :
    kandB (komponiere B ps).P fs = kandB p.E.P fs := by
  rw [passend_P (hV p hp)]
  rfl

theorem mem_ws_komponiere {w : D.Fn} (h : w ∈ (komponiere B ps).ws) : ∃ p ∈ ps, w ∈ p.E.ws := by
  simp only [Einheit.ws, komponiere, List.mem_map, List.mem_append, List.mem_flatMap] at h
  obtain ⟨a, ha, rfl⟩ := h
  rcases ha with (⟨p, hp, ha⟩ | ⟨p, hp, ha⟩) | ⟨p, hp, ha⟩
  · exact ⟨p, hp, List.mem_map.mpr ⟨a, by simp only [List.append_assoc, List.mem_append, ha, or_self, true_or], rfl⟩⟩
  · exact ⟨p, hp, List.mem_map.mpr ⟨a, by simp only [List.append_assoc, List.mem_append, ha, or_self, or_true], rfl⟩⟩
  · exact ⟨p, hp, List.mem_map.mpr ⟨a, by simp only [List.append_assoc, List.mem_append, ha, or_self, or_true], rfl⟩⟩

theorem mem_arenen_komponiere {a : ArenaOwnership.Body.ArenaIface D} (h : a ∈ (komponiere B ps).arenen) :
    ∃ p ∈ ps, a ∈ p.E.arenen := by
  simpa [komponiere] using h

end Teil

/-! ## The linked unit is accepted -/

/-- **Each unit checked alone and the link check give the whole program's acceptance.** -/
theorem akzeptiertSpecX_komponiere [DecidableEq D.Fn] {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    {B : Einheit D} {ps : List (Projekt D)} (hne : ps ≠ []) (hD : Deckend ps)
    (hV : ∀ p ∈ ps, Passend B p)
    (hA : ∀ p ∈ ps, AkzeptiertSpecX p.E.P p.E.S fs p.E.ws p.E.arenen) (hL : BindeSpec fs B ps) :
    AkzeptiertSpecX (komponiere B ps).P (komponiere B ps).S fs (komponiere B ps).ws
      (komponiere B ps).arenen := by
  obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil ps hne
  refine ⟨?_, hL.abg, hL.fuss, ?_, ?_, ?_, hL.einzeln, hL.renn, ?_, hL.masken, ?_, ?_⟩
  · refine List.all_eq_true.mpr fun f _ => ?_
    obtain ⟨p, hb⟩ := besitzer_da hD f
    have hp := (besitzer_mem (B := B) hb).1
    rw [komponiere_rumpf hb, kandB_besitzer hV hp fs, fussOrteG_besitzer hV hb]
    exact List.all_eq_true.mp (hA p hp).frag f (hvoll f)
  · intro f
    obtain ⟨p, hb⟩ := besitzer_da hD f
    show Grammatik.mE (bodenM f) ((komponiere B ps).P.rumpf f) = true
    rw [komponiere_rumpf hb]
    exact (hA p (besitzer_mem (B := B) hb).1).stufen f
  · intro L c hc
    have : (komponiere B ps).S = p0.E.S := (hV p0 hp0).sperrInv
    rw [this] at hc
    exact (hA p0 hp0).sperrOrte L c hc
  · intro w hw
    obtain ⟨p, hp, hw'⟩ := mem_ws_komponiere hw
    exact (hA p hp).wurzeln w hw'
  · intro f x hx
    obtain ⟨p, hb⟩ := besitzer_da hD f
    rw [komponiere_rumpf hb] at hx
    exact (hA p (besitzer_mem (B := B) hb).1).antworten f x hx
  · intro a ha f
    obtain ⟨p, hb⟩ := besitzer_da hD f
    by_cases hap : a ∈ p.E.arenen
    · show CheckedAt _ a.A a.I f
      unfold CheckedAt
      rw [komponiere_rumpf hb]
      exact (hA p (besitzer_mem (B := B) hb).1).besitz a hap f
    · exact hL.besitzFremd a ha f (fun q hq => by rw [hb] at hq; cases hq; exact hap)
  · intro a ha
    obtain ⟨p, hp, ha'⟩ := mem_arenen_komponiere ha
    exact (hA p hp).worte a ha'

/-! ## The link check, decided -/

/-- **The link check as a Bool**, over the composed program: the whole-program components of the
    checker (closed graphs, footprints with shared atomics, pool safety, write separation, masks),
    every body against every arena, and the ownership start. (Each body against the arenas of its
    own unit is checked again: membership of an arena cannot be decided, a re-check can.) -/
noncomputable def bindeB [DecidableEq D.Fn] (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob)) (B : Einheit D)
    (ps : List (Projekt D)) : Bool :=
  abgAlleB (komponiere B ps).P fs && fussWXB (komponiere B ps).P (komponiere B ps).S fs (komponiere B ps).ws &&
    einzelnPoolB (komponiere B ps).P fs cs (komponiere B ps).ws &&
    rennB (komponiere B ps).P fs cs (komponiere B ps).ws && maskenB (komponiere B ps).P fs &&
    besitzB (komponiere B ps) fs

/-- **The decided link check is sound.** -/
theorem bindeB_sound [DecidableEq D.Fn] {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) {B : Einheit D} {ps : List (Projekt D)}
    (h : bindeB fs cs B ps = true) : BindeSpec fs B ps := by
  unfold bindeB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hAbg := (abgAlleB_iff hvoll).mp h1
  obtain ⟨hb, -, hs⟩ := besitzB_sound hvoll h6
  exact ⟨hAbg, fussWXB_ok hvoll hAbg h2, (einzelnPoolB_iff hvoll hcs).mp h3, (rennB_iff hvoll hcs).mp h4,
    (maskenB_iff hvoll).mp h5, fun a ha f _ => (checked_iff _ _ _).mp (hb a ha) f, hs⟩

/-- **The checker that decides the specification**: accepts exactly what `AkzeptiertSpecX` and the
    ownership start establish (the strongest checker the statement admits). -/
noncomputable def specPruefer : PrueferX where
  akzeptiert := fun E fs _ _ =>
    @decide (AkzeptiertSpecX E.P E.S fs E.ws E.arenen ∧ BesitzStart E) (Classical.propDecidable _)
  korrekt := fun _ _ _ _ h => @of_decide_eq_true _ (Classical.propDecidable _) h

/-- **GABBRO_ZIEL FOR SEPARATELY CHECKED UNITS, ANY NUMBER, EVERY LEG.** -/
def GabbroZielVerbundN : Prop :=
  ∀ (C : PrueferX) (D : Deklaration) [DecidableEq D.Fn] (B : Einheit D) (ps : List (Projekt D))
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob)),
    (∀ p ∈ ps, C.akzeptiert p.E fs.1 ls.1 cs.1 = true) →      -- (a) each unit, ALONE
    (∀ p ∈ ps, Passend B p) → ps ≠ [] → Deckend ps → DeckendS ps → -- one link declaration
    BindeSpec fs.1 B ps →                                       -- (a) the link check
    (∀ p ∈ ps, NutzerTeilO p) →                                 -- (b) each unit's user, once
    ∀ O : Orakel D, HardwareAnnahmen O (komponiere B ps).Q →    -- (c) all units' assumptions
    ∀ (passes : Nat) (sp : Speicher D.mitRuhe)
      (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)),
      Laufzeit (komponiere B ps) sp init →                      -- (d) the linked program
      ∀ (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe),
        FadenErreichbarX (komponiere B ps).P.mitRuhe O.mitRuhe passes
          (GeteiltV (D := D) (komponiere B ps).P (komponiere B ps).ws)
          (FadenStart (komponiere B ps).P.mitRuhe sp init lebt0) K →
          ZielFX (komponiere B ps).P.mitRuhe (komponiere B ps).S.mitRuhe O.mitRuhe passes
            (GeteiltV (D := D) (komponiere B ps).P (komponiere B ps).ws)
            (RufStartG (komponiere B ps).P.mitRuhe sp init)
            ((komponiere B ps).arenen.map (·.mitRuhe)) K

/-- **PROVED.** -/
theorem gabbro_ziel_verbund_n : GabbroZielVerbundN := by
  intro C D _ B ps fs ls cs hC hV hne hD hDS hL hN O hH passes sp init hLz lebt0 K hK
  have hA : ∀ p ∈ ps, AkzeptiertSpecX p.E.P p.E.S fs.1 p.E.ws p.E.arenen :=
    fun p hp => (C.korrekt p.E fs ls cs (hC p hp)).1
  have hK' : specPruefer.akzeptiert (komponiere B ps) fs.1 ls.1 cs.1 = true :=
    @decide_eq_true _ (Classical.propDecidable _)
      ⟨akzeptiertSpecX_komponiere fs.2 hne hD hV hA hL, hL.besitzStart⟩
  exact gabbro_ziel specPruefer D (komponiere B ps) fs ls cs hK'
    (nutzerPflichtA_komponiere hV hne hD hDS hN) O hH passes sp init hLz lebt0 K hK

/-! ## A library proved against a smaller rely -/

/-- **A project proved against its own (closed-world) rely `T₁`** owes a new proof only for the bodies
    that read an unguarded atomic outside `T₁`; every other body keeps its proof in every program.
    The checker decides `LiestNicht` per body; this is what makes the re-check automatic. -/
theorem nutzerTeilO_wachs {p : Projekt D} {T₁ : D.Tab ⊕ D.Glob → Prop}
    (hL : ∀ (passes : Nat) (f : D.Fn), p.eigen f = true →
      KoerperGutSA p.E.P passes p.E.Q p.E.S T₁ f ∧ InvGutSA p.E.P passes p.E.Q p.E.S T₁ f ∧
        InvGutGrundA p.E.P passes p.E.Q p.E.S T₁ f)
    (hNeu : ∀ (passes : Nat) (f : D.Fn), p.eigen f = true →
      (∀ c ∈ endblockOrteP p.E.P (p.E.P.rumpf f), ¬ (OffenA c ∧ ¬ T₁ c)) ∨
        (KoerperGutSA p.E.P passes p.E.Q p.E.S OffenA f ∧ InvGutSA p.E.P passes p.E.Q p.E.S OffenA f ∧
          InvGutGrundA p.E.P passes p.E.Q p.E.S OffenA f))
    (hSL : SperrInvLokal p.E.S) (hQL : AxEnsLokal p.E.Q) (hstart : StartTeil p) : NutzerTeilO p :=
  ⟨⟨fun passes f hf => by
      rcases hNeu passes f hf with hl | hneu
      · obtain ⟨k, i, g⟩ := hL passes f hf
        exact ⟨koerperGutSA_wachs k hl, invGutSA_wachs i hl, invGutGrundA_wachs g hl⟩
      · exact hneu, hSL, hQL⟩, hstart⟩

/-! ## The witness, for every accepted unit and every boundary -/

theorem lokW_ohne_wurzeln [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn) (c : D.Tab ⊕ D.Glob) : lokW P fs [] c = true :=
  @decide_eq_true _ (Classical.propDecidable _) fun _ h => nomatch h

/-- **A unit without roots and arenas is accepted alone** whenever the unit it is cut from is: what
    depends on roots holds vacuously, the rest is per body. -/
theorem ohne_wurzeln_akzeptiert [DecidableEq D.Fn] {E : Einheit D} {fs : List D.Fn}
    (hA : AkzeptiertSpecX E.P E.S fs E.ws E.arenen) :
    specPruefer.akzeptiert { E with starts := [], gestartet := [], arenen := [] } fs [] [] = true := by
  have hws : ({ E with starts := [], gestartet := [], arenen := [] } : Einheit D).ws = [] := rfl
  refine @decide_eq_true _ (Classical.propDecidable _) ⟨⟨hA.frag, hA.abg, (fun f => ?_), hA.stufen,
    hA.sperrOrte, (fun w h => by rw [hws] at h; cases h), (fun _ h => ?_),
    (fun _ _ _ w h => by rw [hws] at h; cases h), hA.antworten,
    hA.masken, (fun _ h => by cases h), (fun _ h => by cases h)⟩,
    ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩⟩
  · show FussSX E.P E.S (lokW E.P fs []) _ f
    refine ⟨fun c _ => Or.inl (by rw [lokW_ohne_wurzeln, Bool.or_true]), fun c _ => by
      rw [lokW_ohne_wurzeln, Bool.or_true]⟩
  · rw [hws] at h
    exact absurd h (by simp only [Mehrfach, List.sublist_nil, reduceCtorEq, not_false_eq_true])

/-- **The witness of `gabbro_ziel_verbund_n`**: every unit the checker of the specification accepts,
    cut at any boundary into two units checked ALONE -- the first the unit, the second its other
    functions without roots -- passes the link check, and every leg of the goal holds for the
    linked program. -/
theorem verbund_zeuge [DecidableEq D.Fn] (E : Einheit D) (eigen : D.Fn → Bool)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hA : AkzeptiertSpecX E.P E.S fs.1 E.ws E.arenen) (hBS : BesitzStart E)
    (hN : NutzerTeilO ⟨fun _ => true, fun _ => true, E⟩)
    (O : Orakel D) (hH : HardwareAnnahmen O E.Q) (passes : Nat) (sp : Speicher D.mitRuhe)
    (init : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f)) (hL : Laufzeit E sp init)
    (lebt0 : Faden → Bool) (K : FadenMaschine D.mitRuhe)
    (hK : FadenErreichbarX (komponiere E (schnitt E eigen)).P.mitRuhe O.mitRuhe passes
      (GeteiltV (D := D) (komponiere E (schnitt E eigen)).P (komponiere E (schnitt E eigen)).ws)
      (FadenStart (komponiere E (schnitt E eigen)).P.mitRuhe sp init lebt0) K) :
    ZielFX (komponiere E (schnitt E eigen)).P.mitRuhe (komponiere E (schnitt E eigen)).S.mitRuhe
      O.mitRuhe passes
      (GeteiltV (D := D) (komponiere E (schnitt E eigen)).P (komponiere E (schnitt E eigen)).ws)
      (RufStartG (komponiere E (schnitt E eigen)).P.mitRuhe sp init)
      ((komponiere E (schnitt E eigen)).arenen.map (·.mitRuhe)) K := by
  have hkomp := schnitt_komponiere E eigen
  have hC : ∀ p ∈ schnitt E eigen, specPruefer.akzeptiert p.E fs.1 ls.1 cs.1 = true := by
    intro p hp
    simp only [schnitt, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact @decide_eq_true _ (Classical.propDecidable _) ⟨hA, hBS⟩
    · exact ohne_wurzeln_akzeptiert hA
  have hL' : BindeSpec fs.1 E (schnitt E eigen) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hkomp]
    · exact hA.abg
    · exact hA.fuss
    · exact hA.einzeln
    · exact hA.renn
    · exact hA.masken
    · exact fun a ha f _ => (checked_iff _ _ _).mp (hA.besitz a ha) f
    · exact hBS
  exact gabbro_ziel_verbund_n specPruefer D E (schnitt E eigen) fs ls cs hC (schnitt_passend E eigen)
    (by simp only [schnitt, ne_eq, reduceCtorEq, not_false_eq_true]) (schnitt_deckend E eigen) (schnitt_deckendS E eigen) hL' (schnitt_nutzer hN) O
    (by rw [hkomp]; exact hH) passes sp init (by rw [hkomp]; exact hL) lebt0 K hK

#print axioms gabbro_ziel_verbund_n
#print axioms verbund_zeuge
#print axioms nutzerTeilO_wachs

end Gabbro.Grammatik.Zielsatz
