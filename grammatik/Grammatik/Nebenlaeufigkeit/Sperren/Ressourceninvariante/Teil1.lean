/-
  File:      Grammatik/Nebenlaeufigkeit/Sperren/Ressourceninvariante.lean (formerly `CSLInvariante.lean`)
  Subject:   THE CSL RESOURCE INVARIANT -- THE MAIN THEOREM (lane 81).

  While lock L is free everywhere, the L-guarded table's invariant holds.
  Lane 54 proved the leaf lemma for non-oracle leaves
  (`blatt_slots_t_gleich` in `RessourcenBlatt.lean`) and cut the main theorem
  because `Stmt.axiomCall` could write guarded tables without the lock.
  Lane 74 repaired that: `axiomCall` carries `hd`/`hgd`, and
  `FremdSperre.lean` proves `axiomCall_haelt_waechter`. This file extends
  the leaf argument to `axiomCall` (oracle frame + `hd` + `HeldGenau`)
  and runs the induction over `PCReach`.
-/
module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ressourceninvariante.Teil1a

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Nebenlaeufigkeit.Sperren.RessourcenBlatt.Teil3
public import Grammatik.Korpus.Referenz.ReferenzB

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 3. The main theorem: the CSL resource invariant -/

/-- **The CSL resource invariant.** While lock `L` is free everywhere, the
    invariant `inv` over the `L`-guarded table `t` holds at every reachable
    machine. The induction invariant is the conclusion itself.

    - `start`: the start memory carries `inv` (`hStart`).
    - `take L'`: memory is unchanged; every thread but the taker keeps its
      trace, and the taker's trace only gains -- so `L`-freedom pushes back
      and the induction hypothesis applies.
    - `rel L'`: memory is unchanged. Either the pre-machine is already
      `L`-free (induction hypothesis), or some thread holds `L`: a thread
      other than the releaser keeps its trace (contradiction with
      post-freedom), so the releaser itself held `L` -- and `hRelease`
      concludes `inv` at the post-machine directly.
    - `leaf`: if the stepping thread holds `L`, held locks are preserved
      (`blatt_brav`, so `offen` is unchanged) -- contradiction with
      post-freedom. Otherwise the thread does not hold `L`: `L`-freedom
      pushes back, the induction hypothesis gives `inv` at the pre-memory,
      and `blatt_erhaelt_slots` plus locality (`hLokal`) move it to the
      post-memory.

    Every premise is used: `hO` (leaf preservation and the oracle frame),
    `hGuard` (leaf preservation), `hLokal` (leaf transfer), `hStart`
    (`start`), `hRelease` (release of `L` by its holder). -/
theorem csl_ressourceninvariante
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D)
    (t : D.Tab) (L : D.Lock) (inv : Speicher D → Prop)
    (hGuard : Sum.inl L ∈ D.braucht t)
    (hLokal : ∀ s s' : Speicher D, (∀ k f, s.slots t k f = s'.slots t k f) → (inv s ↔ inv s'))
    (hStart : inv sp)
    (hRelease : ∀ M pc f M' pc', PCReach P O passes prog (GenStart sp) M pc →
        PCSchritt P O passes prog M pc f M' pc' →
        L ∈ offen (M.spuren f) → L ∉ offen (M'.spuren f) → inv M'.speicher) :
    ∀ M pc, PCReach P O passes prog (GenStart sp) M pc →
      (∀ g, L ∉ offen (M.spuren g)) → inv M.speicher := by
  intro M pc hreach
  induction hreach with
  | start =>
      -- The start machine runs on `sp`; the freeness hypothesis is not
      -- needed for this branch (it is used in every `step` branch).
      intro _
      exact hStart
  | step M M' pc pc' f hreachM hs ih =>
      intro hfree'
      cases hs with
      | leaf V l Γ Λ Λ' s ρ hleaf hΛ σ' _ hstep _ _ _ _ _ _ _ _ =>
          show inv σ'.speicher
          have hbrav := blatt_brav O passes hO M f V l Γ Λ Λ' s ρ hleaf hΛ σ' hstep
          -- OPEN (C11): `hopenf` below is the pre-C11 lock equality, false
          -- for a scoped return (it unwinds scopes). The `hLf` case needs
          -- the release-aware argument (a scope release of `L` must meet
          -- `hRelease` like an explicit `rel`); `hbrav` is kept for the
          -- push-back direction (`BravRet.mem`). Lead decision pending.
          have hopenf : offen σ'.spur = offen (M.spuren f) := by
            have e1 : σ'.haelt = offen σ'.spur := rfl
            have e2 : (M.weltVon f).haelt = offen (M.spuren f) := rfl
            rw [← e1, ← e2]
            exact hbrav.1
          by_cases hLf : L ∈ offen (M.spuren f)
          ·
            have hcon : L ∈ offen σ'.spur := hopenf ▸ hLf
            have hff : L ∉ offen σ'.spur := by
              have h := hfree' f
              simp only [genUpdate_self] at h
              exact h
            exact absurd hcon hff
          ·
            have hfreeM : ∀ g, L ∉ offen (M.spuren g) := by
              intro g
              by_cases heq : g = f
              ·
                subst g
                exact hLf
              ·
                have h := hfree' g
                simp only [genUpdate_noteq _ _ _ heq] at h
                exact h
            have hmem := ih hfreeM
            have hslots : ∀ (k : Int) (fld : D.Feld t),
                M.speicher.slots t k fld = σ'.speicher.slots t k fld := by
              intro k fld
              show M.speicher.slots t k fld = σ'.slots t k fld
              exact (blatt_erhaelt_slots O passes hO M f s ρ hleaf σ' hstep t L
                hGuard hΛ.heldIn hLf k fld).symm
            exact ((hLokal M.speicher σ'.speicher hslots).mp hmem)
      | take L' _ _ _ _ =>
          show inv M.speicher
          apply ih
          intro g
          by_cases heq : g = f
          · subst g
            have h := hfree' f
            simp only [genUpdate_self] at h
            have h2 : L ∉ L' :: offen (M.spuren f) := h
            intro hm
            exact h2 (List.mem_cons.mpr (Or.inr hm))
          · have h := hfree' g
            simp only [genUpdate_noteq _ _ _ heq] at h
            exact h
      | rel L' hhaelt hpc =>
          by_cases hfreeM : ∀ g, L ∉ offen (M.spuren g)
          · show inv M.speicher
            exact ih hfreeM
          · have hex : ∃ g, L ∈ offen (M.spuren g) :=
              Classical.byContradiction fun hcon =>
                hfreeM (fun g hm => hcon ⟨g, hm⟩)
            obtain ⟨g0, hg0'⟩ := hex
            by_cases heq : g0 = f
            · subst g0
              exact hRelease M pc f _ _ hreachM
                (PCSchritt.rel M pc f L' hhaelt hpc) hg0' (hfree' f)
            · have h := hfree' g0
              simp only [genUpdate_noteq _ _ _ heq] at h
              exact absurd hg0' h

/-! ## 4. Witness on the reference fixture (rule 13) -/

/-- The reference thread program has no release atoms: thread 1 takes the
    lock then fires the writing leaf, every other thread rests. -/
theorem refB_prog_kein_rel (f : Faden) (n : Nat) (L' : refD.Lock) :
    (refB_prog f)[n]? ≠ some (PCAtom.rel L') := by
  intro hcon
  by_cases hf : f = 1
  ·
    subst hf
    have e : refB_prog 1 =
        [PCAtom.take (), PCAtom.leaf [Res.held (D := refD) ()] [Sum.inl (())]] := rfl
    rw [e] at hcon
    cases n with
    | zero => simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, getElem?_pos,
  List.getElem_cons_zero, Option.some.injEq, reduceCtorEq] at hcon
    | succ n =>
        cases n with
        | zero => simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq, reduceCtorEq] at hcon
        | succ n => simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.not_lt, Nat.le_add_left,
  getElem?_neg, reduceCtorEq] at hcon
  ·
    have e : refB_prog f = [] := by
      simp only [refB_prog]
    rw [e] at hcon
    simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg, reduceCtorEq] at hcon

/-- The witness guard: `konto` is guarded by its lock. -/
theorem refInv81_guard : Sum.inl () ∈ refD.braucht () :=
  List.mem_singleton.mpr rfl

end Gabbro.Grammatik
