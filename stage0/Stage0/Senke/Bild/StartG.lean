/-
  File:      stage0/Stage0/Senke/Bild/StartG.lean
  Subject:   The start of machine G that a one-thread image realises (image theorem, piece T2), and the checker's
             facts without the atomic rely.
             * `bildInit thr f ρ r ρr`: thread `thr` starts `f` with `ρ`; every other thread starts `r` with `ρr`.
               `randG_start`: at the start machine `RufStartG P sp init`, thread `thr` stands at the first boundary of
               the body of `f` (`RandG`, residue `.ende (P.rumpf f)`, world `sp.welt []`, no other thread holding a
               lock), when neither `f` nor the other threads' starts hold a lock by signature.
             * `startZulaessig_bild`: `StartZulaessig` for `bildInit` from the user's start duty, when `f` is a judged
               start and `r` is idle (`Ruhig`) with its `requires` true. Over `P` (not `P.mitRuhe`) the idle `r` is
               needed: `Faden` is `Nat`, so some start function runs on two threads, and `einmal` admits that only for
               an idle or twice-declared start (`Mehrfach`), which `main` is not. `ruhigB` decides `Ruhig` over
               complete member lists (`ruhigB_ok`).
             * `akzeptiertSpec_of_X`: the checker's facts with the atomic rely (`AkzeptiertSpecX`) give those without
               it (`AkzeptiertSpec`) on a unit with no admitted shared atomic (`GeteiltV` empty); `keinGeteiltV`
               derives that side condition from a declaration without `atomic` globals.
-/
module
public import Stage0.Senke.Bild.Korrespondenz
public import Grammatik.Zielsatz.Kern.Beweis
public import Grammatik.Zielsatz.Atomar.AtomarPflicht
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Stage0.Senke

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## The start machine -/

/-- Thread `t` of the start machine whose start `init t` is `⟨g, rho⟩`. -/
theorem rufStartG_faeden_von (P : Programm D) (sp : Speicher D)
    {init : Faden → Σ f : D.Fn, Env D (D.params f)} {t : Faden} {g : D.Fn} {rho : Env D (D.params g)}
    (h : init t = ⟨g, rho⟩) :
    (RufStartG P sp init).faeden t =
      ⟨[], ⟨g, rho, sp.welt [],
        ⟨false, D.params g, Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩,
       startSpur g, [RufEreignisF.eintritt g rho (sp.welt [])]⟩ := by
  unfold RufStartG
  dsimp only
  rw [h] <;> rfl

/-- The trace a thread starts with: its start function's signature locks. -/
theorem rufStartG_spur (P : Programm D) (sp : Speicher D) (init : Faden → Σ f : D.Fn, Env D (D.params f))
    (t : Faden) : ((RufStartG P sp init).faeden t).spur = startSpur (init t).1 := by
  cases hx : init t with
  | mk g rho => rw [rufStartG_faeden_von P sp hx] <;> rfl

/-- A start function without signature locks starts with the empty trace. -/
theorem startSpur_leer {f : D.Fn} (hf : D.haelt f = []) : startSpur f = [] := by
  simp only [startSpur, hf, nimmtAlle]

/-- **Machine G at the image's first body boundary**: thread `thr` of the start machine runs the root frame of `f`
    with the residue `.ende (P.rumpf f)`, the entry environment and the start world `sp.welt []`; its holdings tie
    the body's entry resources; no other thread holds a lock. -/
theorem randG_start (P : Programm D) (sp : Speicher D) {init : Faden → Σ g : D.Fn, Env D (D.params g)}
    {thr : Faden} {f : D.Fn} {rho : Env D (D.params f)} (Agl : D.Lock → Prop) (hinit : init thr = ⟨f, rho⟩)
    (hf : D.haelt f = []) (hfrei : ∀ t, t ≠ thr → D.haelt (init t).1 = []) :
    RandG thr [] f rho (sp.welt []) Agl (P.rumpf f) (RufStartG P sp init) (sp.welt []) rho := by
  refine ⟨⟨[RufEreignisF.eintritt f rho (sp.welt [])], ?_, rfl⟩, ⟨fun L hL => ?_, fun L hL => ?_⟩, ?_⟩
  · rw [rufStartG_faeden_von P sp hinit, startSpur_leer hf] <;> rfl
  · have h' := (held_anfang (D.signatur f) L).mp hL
    rw [show (D.signatur f).haelt = [] from hf] at h'
    exact (List.not_mem_nil h').elim
  · change L ∈ ([] : List D.Lock) at hL
    exact (List.not_mem_nil hL).elim
  · intro L _ t ht hL
    rw [rufStartG_spur, offen_startSpur, hfrei t ht] at hL
    exact List.not_mem_nil hL

/-! ## The start the image realises -/

/-- Thread `thr` starts `f` with `ρ`, every other thread the idle start `r` with `ρr`. -/
def bildInit (thr : Faden) (f : D.Fn) (ρ : Env D (D.params f)) (r : D.Fn) (ρr : Env D (D.params r)) :
    Faden → Σ g : D.Fn, Env D (D.params g) :=
  fun t => if t = thr then ⟨f, ρ⟩ else ⟨r, ρr⟩

theorem bildInit_gleich {thr t : Faden} {f : D.Fn} {ρ : Env D (D.params f)} {r : D.Fn}
    {ρr : Env D (D.params r)} (h : t = thr) : bildInit thr f ρ r ρr t = ⟨f, ρ⟩ := by
  subst h
  exact if_pos rfl

theorem bildInit_sonst {thr t : Faden} {f : D.Fn} {ρ : Env D (D.params f)} {r : D.Fn}
    {ρr : Env D (D.params r)} (h : t ≠ thr) : bildInit thr f ρ r ρr t = ⟨r, ρr⟩ :=
  if_neg h

section Zulaessig

variable [DecidableEq D.Fn]

/-- Every thread but `thr` holds no lock at the start, when the idle start holds none. -/
theorem bildInit_frei {thr : Faden} {f : D.Fn} {ρ : Env D (D.params f)} {r : D.Fn}
    {ρr : Env D (D.params r)} (hr : D.haelt r = []) :
    ∀ t, t ≠ thr → D.haelt (bildInit thr f ρ r ρr t).1 = [] := by
  intro t ht
  rw [bildInit_sonst ht]
  exact hr

/-- A decision of `Ruhig` over member lists of the functions and the carriers. -/
def ruhigB (P : Programm D) (fs : List D.Fn) (cs : List (D.Tab ⊕ D.Glob)) (w : D.Fn) : Bool :=
  (D.haelt w).isEmpty && (D.gruende w == 0) &&
    fs.all (fun f => !reachB P fs w f || ((fussOrteG P f).isEmpty && cs.all (fun c => !TraegerSchreibt f c)))

/-- Over complete member lists `ruhigB` is sound for `Ruhig`. -/
theorem ruhigB_ok {P : Programm D} {fs : List D.Fn} {cs : List (D.Tab ⊕ D.Glob)} {w : D.Fn}
    (hfs : ∀ g, g ∈ fs) (hcs : ∀ c, c ∈ cs) (h : ruhigB P fs cs w = true) : Ruhig P fs w := by
  simp only [ruhigB, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨List.isEmpty_iff.mp h1, beq_iff_eq.mp h2, fun f hf => ?_⟩
  have h4 := List.all_eq_true.mp h3 f (hfs f)
  simp only [hf, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h4
  refine ⟨List.isEmpty_iff.mp h4.1, fun c => ?_⟩
  have h5 := List.all_eq_true.mp h4.2 c (hcs c)
  simpa using h5

/-- **The admissible start of the image** (`StartZulaessig` for `bildInit`): `f` is a judged start, `r` is idle,
    both `requires` hold at the start world, and every lock invariant holds at the start memory. -/
theorem startZulaessig_bild {P : Programm D} {S : SperrInv D} {fs ws : List D.Fn} {sp : Speicher D}
    {thr : Faden} {f : D.Fn} {ρ : Env D (D.params f)} {r : D.Fn} {ρr : Env D (D.params r)}
    (hf : f ∈ ws) (hr : Ruhig P fs r) (hreq : ReqAmEintritt P f (sp.welt []) ρ)
    (hreqr : ReqAmEintritt P r (sp.welt []) ρr) (hS : ∀ L, S.inv L sp = true) :
    StartZulaessig P S fs ws sp (bildInit thr f ρ r ρr) where
  wurzel t := by
    by_cases h : t = thr
    · rw [bildInit_gleich h]
      exact Or.inl hf
    · rw [bildInit_sonst h]
      exact Or.inr hr
  einmal t u htu he := by
    by_cases h : t = thr
    · have hu : u ≠ thr := fun e => htu (h.trans e.symm)
      rw [bildInit_gleich h, bildInit_sonst hu] at he
      have he' : f = r := he
      rw [bildInit_gleich h]
      show Ruhig P fs f ∨ Mehrfach ws f
      rw [he']
      exact Or.inl hr
    · rw [bildInit_sonst h]
      exact Or.inl hr
  req t := by
    by_cases h : t = thr
    · rw [bildInit_gleich h]
      exact hreq
    · rw [bildInit_sonst h]
      exact hreqr
  sperren := hS

end Zulaessig

/-! ## The checker's facts without the rely -/

/-- No `atomic` global, no admitted shared atomic. -/
theorem keinGeteiltV [DecidableEq D.Fn] {P : Programm D} {ws : List D.Fn} (h : ∀ g, D.atomar g = false)
    (c : D.Tab ⊕ D.Glob) :
    ¬ GeteiltV P ws c := by
  rintro ⟨⟨⟨g, _, hg⟩, _, _⟩, _⟩
  rw [h g] at hg
  exact Bool.false_ne_true hg

/-- **(a) with the rely gives (a) without it, on a unit with no admitted shared atomic**: every field of
    `AkzeptiertSpecX` but the footprint rule is a field of `AkzeptiertSpec`, and the footprint rule's extra disjunct
    (`GeteiltV c`) is empty. -/
theorem akzeptiertSpec_of_X [DecidableEq D.Fn] {P : Programm D} {S : SperrInv D} {fs ws : List D.Fn}
    {B : List (ArenaOwnership.Body.ArenaIface D)} {A : List (Kernzelle.AccumulatorDecl D)}
    (h : AkzeptiertSpecX P S fs ws B A) (hT : ∀ c, ¬ GeteiltV P ws c) : AkzeptiertSpec P S fs ws A where
  frag := h.frag
  abg := h.abg
  fuss f := by
    refine ⟨fun c hc => ?_, (h.fuss f).2⟩
    rcases (h.fuss f).1 c hc with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exact (hT c h3).elim
  stufen := h.stufen
  sperrOrte := h.sperrOrte
  wurzeln := h.wurzeln
  einzeln := h.einzeln
  renn := h.renn
  antworten := h.antworten
  masken := h.masken
  schnittstellen := h.schnittstellen
  reset := h.reset
  bibliothek := h.bibliothek
  akku := h.akku
  pruef := h.pruef

end Gabbro.Stage0.Senke.BildLauf
