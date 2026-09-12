/-
  File:      Grammatik/CSLInvariante.lean
  Subject:   THE CSL RESOURCE INVARIANT -- THE MAIN THEOREM (lane 81).

  While lock L is free everywhere, the L-guarded table's invariant holds.
  Lane 54 proved the leaf lemma for non-oracle leaves
  (`blatt_slots_t_gleich` in CSLInvarianteC.lean) and cut the main theorem
  because `Stmt.axiomCall` could write guarded tables without the lock.
  Lane 74 repaired that: `axiomCall` carries `hd`/`hgd`, and
  `FremdSperre.lean` proves `axiomCall_haelt_waechter`. This file extends
  the leaf argument to `axiomCall` (oracle frame + `hd` + `HeldGenau`)
  and runs the induction over `PCReach`.
-/
import Grammatik.Maschine
import Grammatik.CSLInvarianteC
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Witness invariant on the reference fixture: the two slots of `konto`
    agree. True at the start (both `0`), local to `konto` slots, and not
    trivially true for every memory (see `badSp81`). -/
def refInv81 (σ : Speicher refD) : Prop :=
  σ.slots () 0 () = σ.slots () 1 ()

/-! ## 2. Leaf extension: a firing leaf of a thread not holding L,
    including `axiomCall`, preserves the slots of the L-guarded carrier -/

/-- A firing leaf step of a thread that does not hold `L` leaves every slot
    of the `L`-guarded carrier `t` unchanged -- now including `axiomCall`.

    Direct writes carry their guard (`hL`) on the constructor, so a
    same-carrier write contradicts `hfrei` through `HeldGenau`; a
    foreign-carrier write goes through the store frame (imported from
    `CSLInvarianteC`). `axiomCall` answers with the oracle world: a slot
    difference forces `D.aschreibt a t = true` through the oracle frame
    (`hO`, frame clause only), and `hd` turns that into the guard. Every
    other leaf never touches table slots.

    Every premise is used: `hleaf` eliminates the eleven compounds, `hstep`
    fires in every branch, `hGuard`/`hΛ`/`hfrei` close the same-carrier and
    oracle cases, `hO` gives the oracle frame. -/
theorem blatt_erhaelt_slots
    (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (t : D.Tab) (L : D.Lock)
    (hGuard : Sum.inl L ∈ D.braucht t)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (hfrei : L ∉ offen (M.spuren f)) :
    ∀ (k : Int) (fld : D.Feld t), σ'.slots t k fld = (M.weltVon f).slots t k fld := by
  have hheld : Res.held L ∈ Λ → L ∈ offen (M.spuren f) := fun h => (hΛ L).mp h
  cases s with
  | assignSlot u fld i e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      by_cases htu : u = t
      · subst htu
        have hmem : Res.held L ∈ Λ := by
          have hdarf := hL _ hGuard
          simpa [Res.von] using hdarf
        exact False.elim (hfrei (hheld hmem))
      · intro k fld'
        have hslot : (((M.weltVon f).lese Λ (i.orte ++ e.orte)).schreibSlot u Λ
            (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) i
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ).n fld
            (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ)).slots t k fld' =
            ((M.weltVon f).lese Λ (i.orte ++ e.orte)).slots t k fld' :=
          storeSlot_fremd_traeger _ (Ne.symm htu) _ _ _ _ _
        have hgoal : (((M.weltVon f).lese Λ (i.orte ++ e.orte)).schreibSlot u Λ
            (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) i
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ).n fld
            (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ)).slots t k fld' =
            (M.weltVon f).slots t k fld' := by
          rw [hslot]
          exact lese_slots_gleich _ _ _ _ _ _
        exact hgoal
  | assignDurch p u ht fld i e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      by_cases htu : u = t
      · subst htu
        have hmem : Res.held L ∈ Λ := by
          have hdarf := hL _ hGuard
          simpa [Res.von] using hdarf
        exact False.elim (hfrei (hheld hmem))
      · intro k fld'
        have hslot : (((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot u Λ
            (eval ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) i
              ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n fld
            (eval ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)).slots t k fld' =
            ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)).slots t k fld' :=
          storeSlot_fremd_traeger _ (Ne.symm htu) _ _ _ _ _
        have hgoal : (((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)).schreibSlot u Λ
            (eval ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) i
              ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) ρ).n fld
            (eval ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (p.orte ++ i.orte ++ e.orte)) ρ)).slots t k fld' =
            (M.weltVon f).slots t k fld' := by
          rw [hslot]
          exact lese_slots_gleich _ _ _ _ _ _
        exact hgoal
  | assignGlob g e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      have hgoal : (((M.weltVon f).lese Λ e.orte).schreibGlob g Λ
          (eval ((M.weltVon f).lese Λ e.orte) e
            ((M.weltVon f).lese Λ e.orte) ρ)).slots t k fld' =
          (M.weltVon f).slots t k fld' := by
        have h1 : (((M.weltVon f).lese Λ e.orte).schreibGlob g Λ
            (eval ((M.weltVon f).lese Λ e.orte) e
              ((M.weltVon f).lese Λ e.orte) ρ)).slots t k fld' =
            ((M.weltVon f).lese Λ e.orte).slots t k fld' := by
          have hsg := storeGlob_slots_gleich ((M.weltVon f).lese Λ e.orte) g
            (eval ((M.weltVon f).lese Λ e.orte) e
              ((M.weltVon f).lese Λ e.orte) ρ) t k fld'
          exact hsg
        rw [h1]
        exact lese_slots_gleich _ _ _ _ _ _
      exact hgoal
  | schreibBytes u fld hf n i hlo hhi e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      by_cases htu : u = t
      · subst htu
        have hmem : Res.held L ∈ Λ := by
          have hdarf := hL _ hGuard
          simpa [Res.von] using hdarf
        exact False.elim (hfrei (hheld hmem))
      · intro k fld'
        have hgoal : σ'.slots t k fld' = (M.weltVon f).slots t k fld' := by
          rw [← hstep]
          have hslot := schreibBytes_fremd_traeger
            ((M.weltVon f).lese Λ (i.orte ++ e.orte)) (Ne.symm htu) fld hf Λ
            (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) i
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ).n
            (zahlZuBytes n (eval ((M.weltVon f).lese Λ (i.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (i.orte ++ e.orte)) ρ).n) k fld'
          rw [hslot]
          exact lese_slots_gleich _ _ _ _ _ _
        exact hgoal
  | assignVar x e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      have hgoal : ((M.weltVon f).lese Λ e.orte).slots t k fld' =
          (M.weltVon f).slots t k fld' :=
        lese_slots_gleich _ _ _ _ _ _
      exact hgoal
  | uebergang u fld hτ i von nach hn he hw hL =>
      simp only [execStmt] at hstep
      split at hstep
      · simp only [Ausgang.welt, Option.some.injEq] at hstep
        subst hstep
        by_cases htu : u = t
        · subst htu
          have hmem : Res.held L ∈ Λ := by
            have hdarf := hL _ hGuard
            simpa [Res.von] using hdarf
          exact False.elim (hfrei (hheld hmem))
        · intro k fld'
          have hslot : (((M.weltVon f).lese Λ (.inl u :: i.orte)).schreibSlot u Λ
              (eval ((M.weltVon f).lese Λ (.inl u :: i.orte)) i
                ((M.weltVon f).lese Λ (.inl u :: i.orte)) ρ).n fld
              (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))).slots t k fld' =
              ((M.weltVon f).lese Λ (.inl u :: i.orte)).slots t k fld' :=
            storeSlot_fremd_traeger _ (Ne.symm htu) _ _ _ _ _
          have hgoal : (((M.weltVon f).lese Λ (.inl u :: i.orte)).schreibSlot u Λ
              (eval ((M.weltVon f).lese Λ (.inl u :: i.orte)) i
                ((M.weltVon f).lese Λ (.inl u :: i.orte)) ρ).n fld
              (hτ ▸ (⟨nach, hn.1, hn.2⟩ : Zahl _ _))).slots t k fld' =
              (M.weltVon f).slots t k fld' := by
            rw [hslot]
            exact lese_slots_gleich _ _ _ _ _ _
          exact hgoal
      · simp [Ausgang.welt] at hstep
  | ite c tb eb => simp [Stmt.istBlatt] at hleaf
  | onOption o pb ab => simp [Stmt.istBlatt] at hleaf
  | onTag v arms => simp [Stmt.istBlatt] at hleaf
  | onGrund r arms => simp [Stmt.istBlatt] at hleaf
  | call fn args hp hr => simp [Stmt.istBlatt] at hleaf
  | callInd p args hp hr => simp [Stmt.istBlatt] at hleaf
  | locks Lk hr body => simp [Stmt.istBlatt] at hleaf
  | breaking ii body => simp [Stmt.istBlatt] at hleaf
  | traverse u inv body => simp [Stmt.istBlatt] at hleaf
  | retry n bis body ueber => simp [Stmt.istBlatt] at hleaf
  | forever a inv body => simp [Stmt.istBlatt] at hleaf
  | axiomCall a args _ _ _ hd _ =>
      simp only [execStmt] at hstep
      split at hstep
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at hstep
        subst hstep
        have hfst : (O.wirkt a ((M.weltVon f).lese Λ args.orte)
            (evalArgs ((M.weltVon f).lese Λ args.orte) args
              ((M.weltVon f).lese Λ args.orte) ρ)).1 = σ1 := by
          have h1 := congrArg Prod.fst ha
          simp only [axiomAntwort] at h1
          exact h1
        have hframe := (hO a ((M.weltVon f).lese Λ args.orte)
          (evalArgs ((M.weltVon f).lese Λ args.orte) args
            ((M.weltVon f).lese Λ args.orte) ρ)).1
        intro k fld
        cases heq : D.aschreibt a t with
        | true =>
            have hmem : Res.held L ∈ Λ := by
              have hdarf := hd t heq
              simpa [Res.von] using hdarf _ hGuard
            exact False.elim (hfrei (hheld hmem))
        | false =>
            have e1 : σ1.slots t k fld =
                ((M.weltVon f).lese Λ args.orte).slots t k fld := by
              rw [← hfst]
              exact hframe.1 t heq k fld
            exact e1
      · simp [Ausgang.welt] at hstep
  | regSchreib r hk e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      exact lese_slots_gleich _ _ _ _ _ _
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl
  | publish g e payload hp hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      have hgoal : (((M.weltVon f).lese Λ e.orte).schreibGlob g Λ
          (eval ((M.weltVon f).lese Λ e.orte) e
            ((M.weltVon f).lese Λ e.orte) ρ)).slots t k fld' =
          (M.weltVon f).slots t k fld' := by
        show (((M.weltVon f).lese Λ e.orte).storeGlob g
          (eval ((M.weltVon f).lese Λ e.orte) e
            ((M.weltVon f).lese Λ e.orte) ρ)).slots t k fld' = _
        exact lese_slots_gleich ((M.weltVon f).lese Λ e.orte) Λ e.orte t k fld'
      exact hgoal
  | advances m a hh hs =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl
  | retires m st hh a =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl
  | ret e hΛe =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      exact lese_slots_gleich _ _ _ _ _ _
  | retGrund r hΛe =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl
  | leave hh =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl
  | next hh =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rfl

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
          have hbrav := blatt_brav O passes hO M f V l Γ Λ Λ' s ρ hΛ σ' hstep
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
                hGuard hΛ hLf k fld).symm
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

/-! ## CUTS
  - Green: `refInv81` (definition), `blatt_erhaelt_slots` (leaf extension
    including `axiomCall`), `csl_ressourceninvariante` (the main theorem).
  - Open: the witness `csl_ressourceninvariante_zeuge` on the reference
    fixture (rule 13).
-/

#print axioms Gabbro.Grammatik.refInv81
#print axioms Gabbro.Grammatik.blatt_erhaelt_slots
#print axioms Gabbro.Grammatik.csl_ressourceninvariante

end Gabbro.Grammatik
