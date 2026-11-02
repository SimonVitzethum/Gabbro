module

public import Grammatik.Kern.Semantik.Semantik.Transition

public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

private theorem invariantReads_memory (P : Programm D) (is : List D.Inv) (state : World D) :
    let after := is.foldl (fun s i => s.lese (invSicht D i) (P.invariante i).orte) state
    after.slots = state.slots ∧ after.globs = state.globs := by
  induction is generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons i is ih => exact ih (state.lese (invSicht D i) (P.invariante i).orte)

/-- Successful ordinary calls passed their actual requires and returned from
    their actual body. The ensures/invariant read epilogue changes no memory. -/
theorem transition_call_inversion (P : Programm D) (O : Orakel D) (passes fuel : Nat)
    (f : D.Fn) (entry : World D) (env : Env D (D.params f))
    (post : World D) (value : ErgVal D (D.erg f))
    (success : rufAt P O passes (fuel + 1) f entry env = .ok post value) :
    let checked := entry.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte
    wahr? (eval checked (P.requires f) checked env) = true ∧
    ∃ bodyWorld bodyValue,
      execEnd O passes (rufAt P O passes fuel) (P.rumpf f) checked env =
        .zurueck bodyWorld bodyValue ∧
      post.slots = bodyWorld.slots ∧ post.globs = bodyWorld.globs := by
  dsimp only
  let checked := entry.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte
  simp only [rufAt] at success
  split at success
  · cases success
  · rename_i pre
    have preTrue : wahr? (eval checked (P.requires f) checked env) = true := by
      simpa only [Bool.not_eq_false] using pre
    refine ⟨preTrue, ?_⟩
    split at success
    · rename_i bodyWorld bodyValue bodyRun
      split at success
      · cases success
      · split at success
        · cases success
        · cases success
          exact ⟨bodyWorld, bodyValue, bodyRun,
            (invariantReads_memory P (D.invs.filter (schuldet f))
              (bodyWorld.lese (vertragVon D f).ende (P.ensures f).orte)).1,
            (invariantReads_memory P (D.invs.filter (schuldet f))
              (bodyWorld.lese (vertragVon D f).ende (P.ensures f).orte)).2⟩
    · cases success
    · rename_i impossible _ _ _; exact absurd impossible (by decide)
    · rename_i impossible _ _ _; exact absurd impossible (by decide)
    · cases success
    · cases success

private theorem transitionReturn_world {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)}
    (void : V.erg = none) (resources : Λ.Perm V.ende)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (state : World D) (env : Env D Γ) :
    ∃ value, execEnd O passes R (transitionReturn V void resources) state env =
      .zurueck state value := by
  cases V
  cases void
  exact ⟨(), rfl⟩

/-- Every successful call of a certified expansion satisfies its full ordered
    entry-snapshot memory relation and ordinary frame. This includes all
    targets and the original clause, rather than only a graph edge. The
    epilogue's ordinary reads remain present in the actual call trace. -/
theorem TransitionExpansion.call_correct {P : Programm D} {f : D.Fn}
    (expansion : TransitionExpansion P f) (O : Orakel D) (passes fuel : Nat)
    (entry : World D) (env : Env D (D.params f))
    (post : World D) (value : ErgVal D (D.erg f))
    (success : rufAt P O passes (fuel + 1) f entry env = .ok post value) :
    let checked := entry.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte
    let written := transitionWorld expansion.writes checked env checked
    ((∀ write ∈ expansion.writes,
      wahr? (eval checked write.sourceEq checked env) = true) ∧
      wahr? (eval checked expansion.clause checked env) = true) ∧
    post.slots = written.slots ∧ post.globs = written.globs ∧
    Rahmen (D.schreibt f) (D.gschreibt f) entry post := by
  dsimp only
  obtain ⟨pre, bodyWorld, bodyValue, bodyRun, slots, globs⟩ :=
    transition_call_inversion P O passes fuel f entry env post value success
  let checked := entry.lese (Signatur.anfang D (D.signatur f)) (P.requires f).orte
  have preRelation := (transitionRequires_iff expansion.writes expansion.clause
    checked checked env).mp (by rw [← expansion.requires_exact]; exact pre)
  rw [expansion.body_correct O passes (rufAt P O passes fuel) checked checked env] at bodyRun
  obtain ⟨returnValue, returnRun⟩ := transitionReturn_world expansion.result_none
    (by rw [expansion.resources]; exact List.Perm.refl _)
    O passes (rufAt P O passes fuel) (transitionWorld expansion.writes checked env checked) env
  rw [returnRun] at bodyRun
  cases bodyRun
  refine ⟨preRelation, slots, globs, ?_⟩
  have preFrame : Rahmen (D.schreibt f) (D.gschreibt f) entry checked := rahmen_gleich rfl rfl
  have postFrame : Rahmen (D.schreibt f) (D.gschreibt f)
      (transitionWorld expansion.writes checked env checked) post := rahmen_gleich slots globs
  exact (preFrame.trans (transitionWorld_frame expansion.writes expansion.rights checked checked env)).trans
    postFrame

end Gabbro.Grammatik
