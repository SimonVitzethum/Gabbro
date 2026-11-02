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
     - `leaf`: if the stepping thread holds `L`, the leaf moved it from held
       to free -- a release like an explicit `rel`, so `hRelease` concludes
       `inv` at the post-machine (this covers scoped returns, which unwind
       scopes: every released lock carries exactly the invariant duty of a
       normal release, no weaker statement). Otherwise the thread does not
       hold `L`: `L`-freeness pushes back, the induction hypothesis gives
       `inv` at the pre-memory, and `blatt_erhaelt_slots` plus locality
       (`hLokal`) move it to the post-memory.

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
      have hs' := hs
      cases hs with
      | leaf V l Γ Λ Λ' s ρ hleaf hΛ σ' _ hstep _ _ _ _ _ _ _ _ =>
          show inv σ'.speicher
          -- A leaf that moves `L` from held to free is a release like an
          -- explicit `rel`: it meets `hRelease` (C11, lead 2026-11-02: every
          -- lock a scoped return releases carries exactly the invariant duty
          -- of a normal release, no weaker statement). Otherwise freeness
          -- pushes back and locality moves the induction hypothesis over.
          by_cases hLf : L ∈ offen (M.spuren f)
          · exact hRelease M pc f _ _ hreachM hs' hLf (hfree' f)
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

/-- On the reference run, a counter `1` on thread 1 means only the take
    fired: memory is still the start memory. A `rel` never fires
    (`refB_prog_kein_rel`); a `leaf` fires only at counter `1`, whose
    atom is the writing leaf, so no leaf lands at counter `≤ 1` either.
    `take` keeps memory. -/
theorem pc1_speicher_le (M : GenMaschine refD) (pc : PCStand)
    (hreach : PCReach refP refO 0 refB_prog (GenStart refSp0) M pc)
    (hle : pc 1 ≤ 1) : M.speicher = refSp0 := by
  induction hreach with
  | start => intro _; rfl
  | step M M' pc pc' f hreachM hs ih =>
      intro hle'
      cases hs with
      | leaf V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkein Λa cs hpc hΛa hmark hcar =>
          by_cases hf : f = 1
          · subst hf
            have hpre : pc 1 = 0 := by
              rw [pcAdvance_self pc 1] at hle'
              omega
            have eprog : refB_prog 1 =
                [PCAtom.take (), PCAtom.leaf [Res.held (D := refD) ()] [Sum.inl (())]] := rfl
            rw [eprog, hpre, List.getElem?_cons_zero] at hpc
            simp only [Option.some.injEq, reduceCtorEq] at hpc
          · have e : refB_prog f = [] := by
              simp only [refB_prog]
            rw [e] at hpc
            simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true,
              getElem?_neg, reduceCtorEq] at hpc
      | take L' hself _ _ _ =>
          show M.speicher = refSp0
          have hpre : pc 1 ≤ 1 := by
            by_cases hf : f = 1
            · subst hf
              rw [pcAdvance_self pc 1] at hle'
              omega
            · rw [pcAdvance_noteq pc f 1 (Ne.symm hf)] at hle'
              exact hle'
          exact ih hpre
      | rel L' _ hpc =>
          exact False.elim (refB_prog_kein_rel f (pc f) L' hpc)

end Gabbro.Grammatik
