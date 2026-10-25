import Grammatik.Zielsatz.Projekte.Ziel

/-!
  File:      Grammatik/Zielsatz/Projekte/Zeuge.lean
  Subject:   The witness of `gabbro_ziel_projekte` for every unit and every boundary.

  Every unit can be cut into two projects at any boundary (`schnitt`): the first owns the functions
  `eigen` names, with the unit's starts, run-time roots and arenas; the second owns the rest. The
  two link declarations agree, cover every function, and compose back into the unit
  (`schnitt_komponiere`). So every call, held lock, guarded table, invariant, shared atomic and
  arena of the unit that crosses `eigen` crosses a project boundary, and `gabbro_ziel_projekte`
  gives every leg of the goal for the linked program from each project's own part
  (`projekte_zeuge`). Nothing here names a particular program.
-/

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik Speichermodell

variable {D : Deklaration}

/-- **A unit cut into two projects** at the boundary `eigen`. -/
def schnitt (E : Einheit D) (eigen : D.Fn → Bool) : List (Projekt D) :=
  [⟨eigen, fun _ => true, E⟩,
    ⟨fun f => !eigen f, fun _ => false, { E with starts := [], gestartet := [], arenen := [] }⟩]

theorem gleichAuf_refl (S : List (D.Tab ⊕ D.Glob)) (σ : World D) : GleichAuf S σ σ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem schnitt_passend (E : Einheit D) (eigen : D.Fn → Bool) :
    ∀ p ∈ schnitt E eigen, Passend E p := by
  intro p hp
  simp only [schnitt, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => gleichAuf_refl _ _, fun _ _ => gleichAuf_refl _ _⟩

theorem schnitt_deckendS (E : Einheit D) (eigen : D.Fn → Bool) : DeckendS (schnitt E eigen) :=
  fun _ => ⟨_, List.mem_cons_self, rfl⟩

theorem schnitt_deckend (E : Einheit D) (eigen : D.Fn → Bool) : Deckend (schnitt E eigen) := by
  intro f
  cases h : eigen f
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp [h]⟩
  · exact ⟨_, List.mem_cons_self, h⟩

/-- **The two projects compose back into the unit.** -/
theorem schnitt_komponiere (E : Einheit D) (eigen : D.Fn → Bool) :
    komponiere E (schnitt E eigen) = E := by
  have hP : koerperVon E.P (schnitt E eigen) = E.P.rumpf := by
    funext f
    unfold koerperVon
    cases h : eigen f <;> simp [schnitt, h]
  have hQ : qAlle (schnitt E eigen) = E.Q := by
    funext a σ v
    simp [qAlle, schnitt]
  unfold komponiere komponiereP
  rw [hP, hQ]
  cases E
  simp [mitRumpf, schnitt]

/-- Each part owes what the whole unit owes. -/
theorem schnitt_nutzer {E : Einheit D} {eigen : D.Fn → Bool}
    (hN : NutzerTeilO ⟨fun _ => true, fun _ => true, E⟩) :
    ∀ p ∈ schnitt E eigen, NutzerTeilO p := by
  intro p hp
  simp only [schnitt, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨fun passes f _ => hN.logik.1 passes f rfl, hN.logik.2⟩, ⟨hN.start.sperren, hN.start.req⟩⟩
  · refine ⟨⟨fun passes f _ => hN.logik.1 passes f rfl, hN.logik.2⟩, ⟨(fun _ h => by cases h), ?_⟩⟩
    intro a ha
    simp at ha

/-- **The witness**: for every checker for the rely, every unit it accepts, every boundary through
    it, the unit's own logic against the open-world rely, its hardware assumptions and its runtime,
    every leg of `ZielFX` holds on every reachable thread machine of the program linked from the two
    projects. -/
theorem projekte_zeuge (C : PrueferX) [DecidableEq D.Fn] (E : Einheit D) (eigen : D.Fn → Bool)
    (fs : Aufzaehlung D.Fn) (ls : Aufzaehlung D.Lock) (cs : Aufzaehlung (D.Tab ⊕ D.Glob))
    (hC : C.akzeptiert E fs.1 ls.1 cs.1 = true) (hN : NutzerTeilO ⟨fun _ => true, fun _ => true, E⟩)
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
      ((komponiere E (schnitt E eigen)).arenen.map (·.mitRuhe)) K :=
  gabbro_ziel_projekte C D E (schnitt E eigen) fs ls cs (schnitt_passend E eigen) (by simp [schnitt])
    (schnitt_deckend E eigen) (schnitt_deckendS E eigen) (by rw [schnitt_komponiere]; exact hC) (schnitt_nutzer hN) O
    (by rw [schnitt_komponiere]; exact hH) passes sp init (by rw [schnitt_komponiere]; exact hL)
    lebt0 K hK

/-- **The boundary is crossed wherever the unit crosses `eigen`**: the linked program is the unit's,
    one project owns `f`, the other `g`. -/
theorem schnitt_grenze (E : Einheit D) (eigen : D.Fn → Bool) {f g : D.Fn} (hf : eigen f = true)
    (hg : eigen g = false) :
    (komponiere E (schnitt E eigen)).P = E.P ∧
      ∃ p ∈ schnitt E eigen, ∃ q ∈ schnitt E eigen, p ≠ q ∧ p.eigen f = true ∧ q.eigen g = true := by
  refine ⟨by rw [schnitt_komponiere], _, List.mem_cons_self, _,
    List.mem_cons_of_mem _ List.mem_cons_self, ?_, hf, by simp [hg]⟩
  intro h
  have := congrArg (fun p : Projekt D => p.eigen g) h
  simp [hg] at this

#print axioms projekte_zeuge
#print axioms schnitt_grenze

end Gabbro.Grammatik.Zielsatz
