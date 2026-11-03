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

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Nebenlaeufigkeit.Sperren.RessourcenBlatt.Teil3
public import Grammatik.Korpus.Referenz.ReferenzB

@[expose] public section



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
    `RessourcenBlatt`). `axiomCall` answers with the oracle world: a slot
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
    (hΛ : HeldIn Λ (offen (M.spuren f)))
    (hfrei : L ∉ offen (M.spuren f)) :
    ∀ (k : Int) (fld : D.Feld t), σ'.slots t k fld = (M.weltVon f).slots t k fld := by
  have hheld : Res.held L ∈ Λ → L ∈ offen (M.spuren f) := fun h => hΛ L h
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
  | assignThru p u ht fld i e hw hL =>
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
  | assignSlotRef r u ht ho fld e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      by_cases htu : u = t
      · subst htu
        have hmem : Res.held L ∈ Λ := by
          have hdarf := hL _ hGuard
          simpa [Res.von] using hdarf
        exact False.elim (hfrei (hheld hmem))
      · intro k fld'
        have hslot : (((M.weltVon f).lese Λ (r.orte ++ e.orte)).schreibSlot u Λ
            ((eval ((M.weltVon f).lese Λ (r.orte ++ e.orte)) r
              ((M.weltVon f).lese Λ (r.orte ++ e.orte)) ρ).zelle : Int) fld
            (eval ((M.weltVon f).lese Λ (r.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (r.orte ++ e.orte)) ρ)).slots t k fld' =
            ((M.weltVon f).lese Λ (r.orte ++ e.orte)).slots t k fld' :=
          storeSlot_fremd_traeger _ (Ne.symm htu) _ _ _ _ _
        have hgoal : (((M.weltVon f).lese Λ (r.orte ++ e.orte)).schreibSlot u Λ
            ((eval ((M.weltVon f).lese Λ (r.orte ++ e.orte)) r
              ((M.weltVon f).lese Λ (r.orte ++ e.orte)) ρ).zelle : Int) fld
            (eval ((M.weltVon f).lese Λ (r.orte ++ e.orte)) e
              ((M.weltVon f).lese Λ (r.orte ++ e.orte)) ρ)).slots t k fld' =
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
  | putBytes u fld hf n i hlo hhi e hw hL =>
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
  | shift u fld hτ i von nach hn he hw hL =>
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
      · simp only [Ausgang.welt, reduceCtorEq] at hstep
  | ite c tb eb => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onOption o pb ab => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onTag v arms => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | onWhy r arms => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | call fn args hp hr => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | callInd p args hp hr => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | callIndElse p args he hp hr err => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | locks Lk hr body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | breaking ii body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | consumeTraverse => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | axiomCallElse => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | traverse u inv body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | retry n bis body ueber => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | forever a inv body => simp only [Stmt.istBlatt, Bool.false_eq_true] at hleaf
  | axiomCall a args _ _ _ hd _ =>
      simp only [execStmt] at hstep
      split at hstep
      · rename_i σ1 v ha
        simp only [Ausgang.welt, Option.some.injEq] at hstep
        subst hstep
        have hfst : (O.wirkt a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
            (evalArgs ((M.weltVon f).lese Λ args.orte) args
              ((M.weltVon f).lese Λ args.orte) ρ)).1 = σ1 := by
          have h1 := congrArg Prod.fst ha
          simp only [axiomAntwort] at h1
          exact h1
        have hframe := (hO a (((M.weltVon f).lese Λ args.orte).fragt (.inl a))
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
      · simp only [Ausgang.welt, reduceCtorEq] at hstep
  | regWrite r hk e =>
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
  | retScoped =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rw [(World.gibt_foldl_speicher _ _).1]
      exact lese_slots_gleich _ _ _ _ _ _
  | retWhyScoped =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      rw [(World.gibt_foldl_speicher _ _).1]
  | ret e hΛe =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      intro k fld'
      exact lese_slots_gleich _ _ _ _ _ _
  | retWhy r hΛe =>
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

end Gabbro.Grammatik
