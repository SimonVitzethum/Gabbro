/-
  File:      Grammatik/Zielsatz/Ruhe.lean
  Subject:   The checker's facts and the admissible starts on `P.mitRuhe`
             (the program with the runtime's idle root, MitRuhe.lean).

  * `akzeptiertSpec_mitRuhe`: every field of `AkzeptiertSpec` for `P` gives
    the same field for `P.mitRuhe` (functions `fsRuhe fs`, starts
    `wsRuhe ws`, lock invariants `S.mitRuhe`).
  * `akzeptiert_mitRuhe`: the checker's Bool on `P.mitRuhe` follows from the
    Bool on `P`.
  * `ruhig_mitRuhe`: the root `none` is an idle start of `P.mitRuhe`.
  * `startZulaessig_mitRuhe`: "declared starts on their threads, the idle
    root on every other thread" is an admissible start of `P.mitRuhe`, given
    the starts' `requires` and the lock invariants at the start memory;
    `startZulaessig_ruhe`: the idle root on EVERY thread is admissible as
    soon as some memory meets the lock invariants.
-/
import Grammatik.Zielsatz.Akzeptiert
import Grammatik.MitRuheStatisch

namespace Gabbro.Grammatik

open Zielsatz

variable {D : Deklaration}

theorem decide_succ_eq (a b : Nat) : decide (a + 1 = b + 1) = decide (a = b) :=
  decide_eq_decide.mpr ⟨Nat.succ.inj, fun e => e ▸ rfl⟩

theorem bewacht_mitRuhe (c : D.Tab ⊕ D.Glob) (L : D.Lock) :
    @Bewacht D.mitRuhe c L ↔ @Bewacht D c L := by
  cases c <;> exact Iff.rfl

theorem waechter_mitRuhe (l : List (D.Lock ⊕ (D.Marke × Nat))) :
    waechter (D := D.mitRuhe) l = waechter (D := D) l := by
  induction l with
  | nil => rfl
  | cons w l ih => rcases w with L | m <;> simp only [waechter, ih]

theorem waechterVon_mitRuhe (c : D.Tab ⊕ D.Glob) :
    waechterVon (D := D.mitRuhe) c = waechterVon (D := D) c := by
  rcases c with t | g
  · exact waechter_mitRuhe (D := D) (D.braucht t)
  · exact waechter_mitRuhe (D := D) (D.gbraucht g)

theorem sigB_mitRuhe (f : D.Fn) (c : D.Tab ⊕ D.Glob) : sigB (D := D.mitRuhe) (some f) c = sigB f c := by
  unfold sigB
  rw [waechterVon_mitRuhe]
  rfl

theorem traegerSchreibt_mitRuhe (f : D.Fn) (c : D.Tab ⊕ D.Glob) :
    TraegerSchreibt (D := D.mitRuhe) (some f) c = TraegerSchreibt f c := by
  cases c <;> rfl

theorem atomar_mitRuhe (c : D.Tab ⊕ D.Glob) :
    AtomarAusgenommen (D := D.mitRuhe) c ↔ AtomarAusgenommen (D := D) c := Iff.rfl

theorem paarung_mitRuhe (c : D.Tab ⊕ D.Glob) :
    PaarungAusgenommen (D := D.mitRuhe) c ↔ PaarungAusgenommen (D := D) c := Iff.rfl

theorem mem_wsRuhe {ws : List D.Fn} {w' : D.mitRuhe.Fn} :
    w' ∈ wsRuhe ws ↔ ∃ w ∈ ws, w' = some w := by
  unfold wsRuhe
  constructor
  · intro h
    obtain ⟨w, hw, e⟩ := List.mem_map.mp h
    exact ⟨w, hw, e.symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact List.mem_map_of_mem hw

section Transfer

variable [DecidableEq D.Fn] (P : Programm D) {S : SperrInv D} {fs ws : List D.Fn}

theorem reach_mitRuhe_cases (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {w : D.Fn} {g' : D.mitRuhe.Fn} (h : reachB P.mitRuhe (fsRuhe fs) (some w) g' = true) :
    ∃ g, g' = some g ∧ reachB P fs w g = true := by
  cases g' with
  | none => rw [reachB_mitRuhe_nicht_ruhe P hAbg] at h; cases h
  | some g => exact ⟨g, rfl, by rw [← reachB_mitRuhe P hvoll hAbg]; exact h⟩

theorem reach_mitRuhe_ruhe_cases {g' : D.mitRuhe.Fn}
    (h : reachB P.mitRuhe (fsRuhe fs) none g' = true) : g' = none := by
  cases g' with
  | none => rfl
  | some g => rw [reachB_mitRuhe_ruhe P g] at h; cases h

theorem getrennt_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {c : D.Tab ⊕ D.Glob} (h : Getrennt P fs ws c) :
    Getrennt P.mitRuhe (fsRuhe fs) (wsRuhe ws) c := by
  intro w₁' hw₁' w₂' hw₂' hne f' g' hf' hc hg'
  obtain ⟨w₁, hw₁, rfl⟩ := mem_wsRuhe.mp hw₁'
  obtain ⟨w₂, hw₂, rfl⟩ := mem_wsRuhe.mp hw₂'
  obtain ⟨f, rfl, hf⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
  obtain ⟨g, rfl, hg⟩ := reach_mitRuhe_cases P hvoll hAbg hg'
  rw [fussOrteG_mitRuhe] at hc
  rw [traegerSchreibt_mitRuhe]
  exact h w₁ hw₁ w₂ hw₂ (fun e => hne (e ▸ rfl)) f g hf hc hg

theorem schreibGetrennt_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs)
    (hAbg : ∀ w, AbgK P fs (reachB P fs w)) {c : D.Tab ⊕ D.Glob}
    (h : SchreibGetrennt P fs ws c) : SchreibGetrennt P.mitRuhe (fsRuhe fs) (wsRuhe ws) c := by
  intro w₁' hw₁' w₂' hw₂' hne g' hg' hgw h' hh'
  obtain ⟨w₁, hw₁, rfl⟩ := mem_wsRuhe.mp hw₁'
  obtain ⟨w₂, hw₂, rfl⟩ := mem_wsRuhe.mp hw₂'
  obtain ⟨g, rfl, hg⟩ := reach_mitRuhe_cases P hvoll hAbg hg'
  obtain ⟨k, rfl, hk⟩ := reach_mitRuhe_cases P hvoll hAbg hh'
  rw [fussOrteG_mitRuhe, traegerSchreibt_mitRuhe]
  rw [traegerSchreibt_mitRuhe] at hgw
  exact h w₁ hw₁ w₂ hw₂ (fun e => hne (e ▸ rfl)) g hg hgw k hk

theorem lokW_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    {c : D.Tab ⊕ D.Glob} (h : lokW P fs ws c = true) :
    lokW P.mitRuhe (fsRuhe fs) (wsRuhe ws) c = true := by
  unfold lokW at h ⊢
  exact @decide_eq_true _ (Classical.propDecidable _)
    (getrennt_mitRuhe P hvoll hAbg (@of_decide_eq_true _ (Classical.propDecidable _) h))

omit [DecidableEq D.Fn] in
theorem kandB_mitRuhe (L : List (D.Tab ⊕ D.Glob)) :
    kZ (kandB P.mitRuhe (fsRuhe fs) L) = kandB P fs L := by
  funext n
  show kandB P.mitRuhe (fsRuhe fs) L (n + 1) = kandB P fs L n
  unfold kandB
  rw [all_fsRuhe]
  have h0 : decide ((D.mitRuhe).sig none = n + 1) = false :=
    decide_eq_false (fun e => Nat.succ_ne_zero n e.symm)
  rw [h0, Bool.not_false, Bool.true_or, Bool.true_and]
  congr 1
  funext g
  show (!decide (D.sig g + 1 = n + 1) ||
    ((P.mitRuhe.requires (some g)).orte ++ (P.mitRuhe.ensures (some g)).orte).all _) = _
  rw [decide_succ_eq, requires_mitRuhe_orte, ensures_mitRuhe_orte] <;> rfl

omit [DecidableEq D.Fn] in
theorem frag_mitRuhe (h : programmImFragmentG P fs = true) :
    programmImFragmentG P.mitRuhe (fsRuhe fs) = true := by
  unfold programmImFragmentG
  rw [all_fsRuhe]
  refine Bool.and_eq_true_iff.mpr ⟨rfl, List.all_eq_true.mpr fun f hf => ?_⟩
  refine (rumpf_mitRuhe_gOk P _ _ f).trans ?_
  rw [kandB_mitRuhe, fussOrteG_mitRuhe]
  exact (List.all_eq_true.mp h) f hf

theorem abg_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w)) :
    ∀ w', AbgK P.mitRuhe (fsRuhe fs) (reachB P.mitRuhe (fsRuhe fs) w') := by
  intro w' f' hf'
  cases w' with
  | none =>
      rw [reach_mitRuhe_ruhe_cases P hf']
      rfl
  | some w =>
      obtain ⟨f, rfl, hf⟩ := reach_mitRuhe_cases P hvoll hAbg hf'
      rw [rumpf_mitRuhe_mE]
      have e : mZ (rufM (fsRuhe fs) (reachB P.mitRuhe (fsRuhe fs) (some w))) =
          rufM fs (reachB P fs w) := by
        apply merkmal_ext
        · funext h
          exact reachB_mitRuhe P hvoll hAbg w h
        · funext n
          show (fsRuhe fs).all (fun g' => !(decide ((D.mitRuhe).sig g' = n + 1)) ||
            reachB P.mitRuhe (fsRuhe fs) (some w) g') = _
          rw [all_fsRuhe]
          have h0 : decide ((D.mitRuhe).sig none = n + 1) = false :=
            decide_eq_false (fun e => Nat.succ_ne_zero n e.symm)
          rw [h0, Bool.not_false, Bool.true_or, Bool.true_and]
          congr 1
          funext g
          show (!decide (D.sig g + 1 = n + 1) || reachB P.mitRuhe (fsRuhe fs) (some w) (some g)) = _
          rw [decide_succ_eq, reachB_mitRuhe P hvoll hAbg] <;> rfl
        · rfl
      rw [e]
      exact hAbg w f hf

theorem fussS_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    (h : ∀ f, FussS P S (lokW P fs ws) f) :
    ∀ f', FussS P.mitRuhe S.mitRuhe (lokW P.mitRuhe (fsRuhe fs) (wsRuhe ws)) f'
  | none => ⟨fun c hc => by rw [fussOrte_mitRuhe_ruhe] at hc; exact absurd hc List.not_mem_nil,
      fun c hc => absurd hc List.not_mem_nil⟩
  | some f => by
      obtain ⟨h1, h2⟩ := h f
      refine ⟨fun c hc => ?_, fun c hc => ?_⟩
      · rw [fussOrte_mitRuhe] at hc
        rcases h1 c hc with h3 | ⟨L, hL, hcL⟩
        · left
          simp only [Bool.or_eq_true] at h3 ⊢
          rw [sigB_mitRuhe]
          exact h3.imp id (lokW_mitRuhe P hvoll hAbg)
        · exact Or.inr ⟨L, (bewacht_mitRuhe (D := D) c L).mpr hL, hcL⟩
      · have hc' : c ∈ (P.rumpf f).regs.flatMap D.rtraeger := by
          have e := rumpf_mitRuhe_regs P f
          exact e ▸ hc
        have h3 := h2 c hc'
        simp only [Bool.or_eq_true] at h3 ⊢
        rw [sigB_mitRuhe]
        exact h3.imp id (lokW_mitRuhe P hvoll hAbg)

omit [DecidableEq D.Fn] in
theorem stufen_mitRuhe (h : StufenM P) : StufenM P.mitRuhe
  | none => rfl
  | some f => by
      show mE (bodenM (some f)) (P.mitRuhe.rumpf (some f)) = true
      rw [rumpf_mitRuhe_mE]
      exact h f

/-- **Transfer of the checker's facts to `P.mitRuhe`.** -/
theorem akzeptiertSpec_mitRuhe (hvoll : ∀ g : D.Fn, g ∈ fs) (hA : AkzeptiertSpec P S fs ws) :
    AkzeptiertSpec P.mitRuhe S.mitRuhe (fsRuhe fs) (wsRuhe ws) where
  frag := frag_mitRuhe P hA.frag
  abg := abg_mitRuhe P hvoll hA.abg
  fuss := fussS_mitRuhe P hvoll hA.abg hA.fuss
  stufen := stufen_mitRuhe P hA.stufen
  sperrOrte := fun L c hc => (bewacht_mitRuhe (D := D) c L).mpr (hA.sperrOrte L c hc)
  wurzeln := fun w' hw' => by
    obtain ⟨w, hw, rfl⟩ := mem_wsRuhe.mp hw'
    exact hA.wurzeln w hw
  renn := fun c hB hAt hP => schreibGetrennt_mitRuhe P hvoll hA.abg
    (hA.renn c (fun L hL => hB L ((bewacht_mitRuhe (D := D) c L).mpr hL)) hAt hP)

/-- **The checker's Bool on `P.mitRuhe` follows from the Bool on `P`**
    (the member lists of locks and carriers are the same). -/
theorem akzeptiert_mitRuhe {ls : List D.Lock} {cs : List (D.Tab ⊕ D.Glob)}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hls : ∀ L : D.Lock, L ∈ ls)
    (hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs) (h : Akzeptiert P S fs ls cs ws = true) :
    Akzeptiert P.mitRuhe S.mitRuhe (fsRuhe fs) ls cs (wsRuhe ws) = true :=
  (akzeptiert_iff (fsRuhe_voll hvoll) hls hcs).mpr
    (akzeptiertSpec_mitRuhe P hvoll (akzeptiertSpec_of hvoll hls hcs h))

/-- **The root is an idle start of `P.mitRuhe`.** -/
theorem ruhig_mitRuhe : Ruhig P.mitRuhe (fsRuhe fs) none :=
  ⟨rfl, rfl, fun f' hf => by
    rw [reach_mitRuhe_ruhe_cases P hf]
    exact ⟨fussOrteG_mitRuhe_ruhe P, fun c => by cases c <;> rfl⟩⟩

end Transfer

/-! ## The admissible starts of `P.mitRuhe` -/

/-- **The runtime's start**: thread `t < aktiv.length` runs the declared
    start `aktiv[t]`, every other thread the idle root. -/
def initRuhe (aktiv : List (Σ w : D.Fn, Env D (D.params w))) :
    Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f) :=
  fun t => match aktiv[t]? with
    | some ⟨w, ρ⟩ => ⟨some w, envR ρ⟩
    | none => ⟨none, .nil⟩

section Start

variable [DecidableEq D.Fn] (P : Programm D) {S : SperrInv D} {fs ws : List D.Fn}

/-- **"Declared starts on their threads, the idle root everywhere else" is
    admissible on `P.mitRuhe`**: each declared start at most once, its
    `requires` at the start memory, every lock invariant at the start
    memory. -/
theorem startZulaessig_mitRuhe (aktiv : List (Σ w : D.Fn, Env D (D.params w)))
    (sp : Speicher D.mitRuhe) (hws : ∀ a ∈ aktiv, a.1 ∈ ws) (hnd : (aktiv.map (·.1)).Nodup)
    (hreq : ∀ a ∈ aktiv, ReqAmEintritt P.mitRuhe (some a.1) (sp.welt []) (envR a.2))
    (hS : ∀ L, S.inv L (speicherZ sp) = true) :
    StartZulaessig P.mitRuhe S.mitRuhe (fsRuhe fs) (wsRuhe ws) sp (initRuhe aktiv) where
  wurzel t := by
    unfold initRuhe
    cases h : aktiv[t]? with
    | none => exact Or.inr (ruhig_mitRuhe P)
    | some a => exact Or.inl (List.mem_map_of_mem (hws a (List.mem_of_getElem? h)))
  einmal t u htu he := by
    revert he
    unfold initRuhe
    cases ht : aktiv[t]? with
    | none => intro _; exact ruhig_mitRuhe P
    | some a =>
        cases hu : aktiv[u]? with
        | none => intro he; cases he
        | some b =>
            intro he
            exfalso
            have hab : a.1 = b.1 := Option.some.inj he
            have ht' : (aktiv.map (·.1))[t]? = some a.1 := by rw [List.getElem?_map, ht]; rfl
            have hu' : (aktiv.map (·.1))[u]? = some b.1 := by rw [List.getElem?_map, hu]; rfl
            rw [hab] at ht'
            have hlt : t < (aktiv.map (·.1)).length := (List.getElem?_eq_some_iff.mp ht').1
            exact htu ((List.getElem?_inj hlt hnd).mp (ht'.trans hu'.symm))
  req t := by
    show ReqAmEintritt P.mitRuhe (initRuhe aktiv t).1 (sp.welt []) (initRuhe aktiv t).2
    unfold initRuhe
    cases h : aktiv[t]? with
    | none => rfl
    | some a => exact hreq a (List.mem_of_getElem? h)
  sperren := hS

/-- The idle root on every thread. -/
def ruheInit (D : Deklaration) : Faden → Σ f : D.mitRuhe.Fn, Env D.mitRuhe (D.mitRuhe.params f) :=
  fun _ => ⟨none, .nil⟩

/-- **The idle root on every thread is admissible on `P.mitRuhe`** as soon
    as the memory meets the lock invariants -- whatever `P` declares. -/
theorem startZulaessig_ruhe (sp : Speicher D.mitRuhe) (hS : ∀ L, S.inv L (speicherZ sp) = true) :
    StartZulaessig P.mitRuhe S.mitRuhe (fsRuhe fs) ws' sp (ruheInit D) where
  wurzel _ := Or.inr (ruhig_mitRuhe P)
  einmal _ _ _ _ := ruhig_mitRuhe P
  req _ := rfl
  sperren := hS

end Start

#print axioms Gabbro.Grammatik.akzeptiertSpec_mitRuhe
#print axioms Gabbro.Grammatik.akzeptiert_mitRuhe
#print axioms Gabbro.Grammatik.ruhig_mitRuhe
#print axioms Gabbro.Grammatik.startZulaessig_mitRuhe
#print axioms Gabbro.Grammatik.startZulaessig_ruhe

end Gabbro.Grammatik
