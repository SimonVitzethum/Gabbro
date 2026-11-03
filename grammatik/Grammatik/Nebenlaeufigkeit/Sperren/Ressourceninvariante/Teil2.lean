module

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Nebenlaeufigkeit.Sperren.RessourcenBlatt.Teil3
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Nebenlaeufigkeit.Sperren.Ressourceninvariante.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- The witness invariant is local: it reads only `konto` slots. -/
theorem refInv81_lokal (s s' : Speicher refD)
    (h : ∀ k f, s.slots () k f = s'.slots () k f) :
    refInv81 s ↔ refInv81 s' := by
  constructor
  ·
    intro hs
    show s'.slots () 0 () = s'.slots () 1 ()
    rw [← h 0 (), ← h 1 (), hs]
  ·
    intro hs
    show s.slots () 0 () = s.slots () 1 ()
    rw [h 0 (), h 1 (), hs]

/-- The witness invariant holds at the start: both slots read `0`. -/
theorem refInv81_start : refInv81 refSp0 := by rfl

/-- The witness release premise: on `refB_prog` a step that moves the lock
    from held to free meets the invariant. `take` only gains it (against its
    own `hself`); `rel` atoms never occur (`refB_prog_kein_rel`); a `leaf`
    either preserves the held lock (every non-scoped leaf keeps its frame,
    so the lock stays and the freeness hypothesis contradicts it) or it is a
    scoped return (which only reads and releases: memory is unchanged, and at
    counter `1` that memory is still the start memory, where the invariant
    holds by `refInv81_start`). The reachability hypothesis is load-bearing
    here: it fixes the memory at the only counter where a leaf can fire. -/
theorem refInv81_release (M : GenMaschine refD) (pc : PCStand) (f : Faden)
    (M' : GenMaschine refD) (pc' : PCStand)
    (hreach : PCReach refP refO 0 refB_prog (GenStart refSp0) M pc)
    (hs : PCSchritt refP refO 0 refB_prog M pc f M' pc')
    (hlt1 : () ∈ offen (M.spuren f)) (hlt2 : () ∉ offen (M'.spuren f)) :
    refInv81 M'.speicher := by
  cases hs with
  | leaf V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkein Λa cs hpc hΛa hmark hcar =>
      by_cases hf : f = 1
      · subst hf
        have eprog : refB_prog 1 =
            [PCAtom.take (), PCAtom.leaf [Res.held (D := refD) ()] [Sum.inl (())]] := rfl
        have hpc1 : pc 1 = 1 := by
          rw [eprog] at hpc
          cases h2 : pc 1 with
          | zero =>
              simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
                Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero,
                Option.some.injEq, reduceCtorEq] at hpc
          | succ n =>
              cases n with
              | zero => omega
              | succ m =>
                  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
                    Nat.not_lt, Nat.le_add_left, getElem?_neg, reduceCtorEq] at hpc
        have hle : pc 1 ≤ 1 := by omega
        have hMem : M.speicher = refSp0 := pc1_speicher_le M pc hreach hle
        cases s with
        | retScoped e R =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hgoal : refInv81 M'.speicher := by
              show refInv81 σ'.speicher
              rw [← hstep]
              unfold refInv81
              have hg := World.gibt_foldl_speicher ((M.weltVon f).lese Λ e.orte) R.scopes
              have e0 : (R.scopes.foldl World.gibt ((M.weltVon f).lese Λ e.orte)).slots () 0 () =
                  M.speicher.slots () 0 () := by
                rw [hg.1]
                rfl
              have e1 : (R.scopes.foldl World.gibt ((M.weltVon f).lese Λ e.orte)).slots () 1 () =
                  M.speicher.slots () 1 () := by
                rw [hg.1]
                rfl
              rw [e0, e1, hMem]
              rfl
            exact hgoal
        | retWhyScoped r R =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hgoal : refInv81 M'.speicher := by
              show refInv81 σ'.speicher
              rw [← hstep]
              unfold refInv81
              have hg := World.gibt_foldl_speicher (M.weltVon f) R.scopes
              have e0 : (R.scopes.foldl World.gibt (M.weltVon f)).slots () 0 () =
                  M.speicher.slots () 0 () := by
                rw [hg.1]
                rfl
              have e1 : (R.scopes.foldl World.gibt (M.weltVon f)).slots () 1 () =
                  M.speicher.slots () 1 () := by
                rw [hg.1]
                rfl
              rw [e0, e1, hMem]
              rfl
            exact hgoal
        | assignSlot t f i e hw hL =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) (M.weltVon f) Λ _
              (orte_append i.orte_darf e.orte_darf) hΛ.heldIn
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hΛ.heldIn))
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | assignThru p t ht f i e hw hL =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) (M.weltVon f) Λ _
              (orte_append (orte_append p.orte_darf i.orte_darf) e.orte_darf) hΛ.heldIn
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hΛ.heldIn))
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | assignThruOwn p t ht f i e m s ho he hg hw hL =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) (M.weltVon f) Λ _
              (orte_append (orte_append p.orte_darf i.orte_darf) e.orte_darf) hΛ.heldIn
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hΛ.heldIn))
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | assignSlotRef r t ht ho f e hw hL =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) (M.weltVon f) Λ _
              (orte_append r.orte_darf e.orte_darf) hΛ.heldIn
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hΛ.heldIn))
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | assignGlob g e hw hL =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) (M.weltVon f) Λ _
              e.orte_darf hΛ.heldIn
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldIn hΛ.heldIn))
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | putBytes t f hf n i hlo hhi e hw hL =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) (M.weltVon f) Λ _
              (orte_append i.orte_darf e.orte_darf) hΛ.heldIn
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact hl.trans (gut_schreibBytes _ t f hf Λ hw hL _ _ (hl.heldIn hΛ.heldIn))
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | assignVar x e =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact gut_lese (M.weltVon f) Λ _ e.orte_darf hΛ.heldIn
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | shift t f hτ i von nach hn he hw hL =>
            simp only [execStmt] at hstep
            split at hstep
            · simp only [Ausgang.welt, Option.some.injEq] at hstep
              have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) (M.weltVon f) Λ _
                (orte_cons (orte_tab hL) i.orte_darf) hΛ.heldIn
              have hG : Gut _ _ (M.weltVon f) σ' := by
                rw [← hstep]
                exact hl.trans (gut_schreibSlot _ t Λ _ f _ hw hL (hl.heldIn hΛ.heldIn))
              have hpost : () ∈ σ'.haelt := by
                have h1 : () ∈ (M.weltVon f).haelt := hlt1
                rw [← hG.haelt] at h1
                exact h1
              have hff : () ∉ σ'.haelt := by
                have h := hlt2
                simp only [genUpdate_self] at h
                exact h
              exact False.elim (hff hpost)
            · simp only [Ausgang.welt, reduceCtorEq] at hstep
        | axiomCall a args he hw hg hd hgd =>
            simp only [execStmt] at hstep
            have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) (M.weltVon f) Λ _
              args.orte_darf hΛ.heldIn
            split at hstep
            · rename_i σ1 v ha
              simp only [Ausgang.welt, Option.some.injEq] at hstep
              have hG : Gut _ _ (M.weltVon f) σ' := by
                rw [← hstep]
                have hax := axiomAntwort_gut refO refO_gut a
                  ((M.weltVon f).lese Λ args.orte)
                  (evalArgs ((M.weltVon f).lese Λ args.orte) args
                    ((M.weltVon f).lese Λ args.orte) ρ) hd hgd (hl.heldIn hΛ.heldIn)
                rw [ha] at hax
                exact hl.trans (Gut.weiter hw hg hax)
              have hpost : () ∈ σ'.haelt := by
                have h1 : () ∈ (M.weltVon f).haelt := hlt1
                rw [← hG.haelt] at h1
                exact h1
              have hff : () ∉ σ'.haelt := by
                have h := hlt2
                simp only [genUpdate_self] at h
                exact h
              exact False.elim (hff hpost)
            · simp only [Ausgang.welt, reduceCtorEq] at hstep
        | regWrite r hk e =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact gut_lese (M.weltVon f) Λ _ e.orte_darf hΛ.heldIn
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | transition =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact gut_fragt _ _
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | publish g e payload hp hw hL =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hl := gut_lese (W := V.schreibt) (G := V.gschreibt) (M.weltVon f) Λ _
              e.orte_darf hΛ.heldIn
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact hl.trans (gut_schreibGlob _ g Λ _ hw hL (hl.heldIn hΛ.heldIn))
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | advances =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact Gut.refl _ _ _
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | retires =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact Gut.refl _ _ _
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | ret e _ =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact gut_lese (M.weltVon f) Λ _ e.orte_darf hΛ.heldIn
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | retWhy _ _ =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact Gut.refl _ _ _
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | leave _ =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact Gut.refl _ _ _
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
        | next _ =>
            simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
            have hG : Gut _ _ (M.weltVon f) σ' := by
              rw [← hstep]
              exact Gut.refl _ _ _
            have hpost : () ∈ σ'.haelt := by
              have h1 : () ∈ (M.weltVon f).haelt := hlt1
              rw [← hG.haelt] at h1
              exact h1
            have hff : () ∉ σ'.haelt := by
              have h := hlt2
              simp only [genUpdate_self] at h
              exact h
            exact False.elim (hff hpost)
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
      · have e : refB_prog f = [] := by
          simp only [refB_prog]
        rw [e] at hpc
        simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg,
          reduceCtorEq] at hpc
  | take L' hself _ _ _ =>
      have eL' : L' = () := by cases L'; rfl
      rw [eL'] at hself
      exact absurd hlt1 hself
  | rel L' _ hpc =>
      exact False.elim (refB_prog_kein_rel f (pc f) L' hpc)

/-- A memory where the witness invariant fails: slot `0` reads `100`,
    slot `1` reads `0`. The invariant is not trivially true. -/
def badSp81 : Speicher refD :=
  ⟨fun _ k _ => if k = 0 then (⟨100, by decide, by decide⟩ : Wert refD (.int 0 100))
      else (⟨0, by decide, by decide⟩ : Wert refD (.int 0 100)),
   fun g => nomatch g⟩

/-- The witness invariant is not trivially true: it fails at `badSp81`. -/
theorem badSp81_neg : ¬ refInv81 badSp81 := by
  intro h
  have h0 : badSp81.slots () 0 () =
      (⟨100, by decide, by decide⟩ : Wert refD (refD.typ () ())) := rfl
  have h1 : badSp81.slots () 1 () =
      (⟨0, by decide, by decide⟩ : Wert refD (refD.typ () ())) := rfl
  unfold refInv81 at h
  rw [h0, h1] at h
  have hn := congrArg Zahl.n h
  simp only [Int.reduceEq] at hn

/-! ## 5. Inhabitation (rule 13): all premises hold jointly -/

/-- **Inhabitation.** All premises of `csl_ressourceninvariante` hold jointly
    on the reference fixture (`refP`/`refO`/`refB_prog`/`refSp0`, table
    `konto`, its lock, invariant "the two slots agree"), the theorem's own
    conclusion is exhibited at those values, the invariant is not trivially
    true (`badSp81`), some function writes the table (`refEin`), and a
    reached run moves memory (`refB_pc_erreicht`/`refB_pc_schreibt`:
    `take` then the writing leaf, slot `0 -> 100`). -/
theorem csl_ressourceninvariante_zeuge :
    GutO refO
    ∧ Sum.inl () ∈ refD.braucht ()
    ∧ (∀ s s' : Speicher refD,
        (∀ k f, s.slots () k f = s'.slots () k f) → (refInv81 s ↔ refInv81 s'))
    ∧ refInv81 refSp0
    ∧ (∀ M pc f M' pc', PCReach refP refO 0 refB_prog (GenStart refSp0) M pc →
        PCSchritt refP refO 0 refB_prog M pc f M' pc' →
        () ∈ offen (M.spuren f) → () ∉ offen (M'.spuren f) → refInv81 M'.speicher)
    ∧ (∀ M pc, PCReach refP refO 0 refB_prog (GenStart refSp0) M pc →
        (∀ g, () ∉ offen (M.spuren g)) → refInv81 M.speicher)
    ∧ (∃ σ : Speicher refD, ¬ refInv81 σ)
    ∧ (vertragVon refD refEin).schreibt () = true
    ∧ ∃ (M : GenMaschine refD) (pc : PCStand),
        PCReach refP refO 0 refB_prog (GenStart refSp0) M pc ∧
        M.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  exact ⟨refO_gut, refInv81_guard, refInv81_lokal, refInv81_start,
    refInv81_release,
    csl_ressourceninvariante refP refO 0 refO_gut refB_prog refSp0
      () () refInv81 refInv81_guard refInv81_lokal refInv81_start refInv81_release,
    ⟨badSp81, badSp81_neg⟩, refEin_schreibt (),
    refPC2, refB_pc2, refB_pc_erreicht, refB_pc_schreibt⟩

/-! ## CUTS
  - Green (standard axioms only): `refInv81`, `blatt_erhaelt_slots` (leaf
    extension including `axiomCall`), `csl_ressourceninvariante` (the main
    theorem), and the rule-13 witness `csl_ressourceninvariante_zeuge` with
    its helpers (`refB_prog_kein_rel`, `refInv81_guard`, `refInv81_lokal`,
    `refInv81_start`, `pc1_speicher_le`, `refInv81_release`, `badSp81`,
    `badSp81_neg`).
  - No cut here (C11, lead 2026-11-02): the `hreach` hypothesis of
    `refInv81_release` is load-bearing -- it fixes the memory at the only
    counter where a leaf can fire (`pc1_speicher_le`), covering scoped
    releases with exactly the invariant duty of a normal release.
-/

#print axioms Gabbro.Grammatik.refInv81
#print axioms Gabbro.Grammatik.blatt_erhaelt_slots
#print axioms Gabbro.Grammatik.pc1_speicher_le
#print axioms Gabbro.Grammatik.refInv81_release
#print axioms Gabbro.Grammatik.csl_ressourceninvariante
#print axioms Gabbro.Grammatik.csl_ressourceninvariante_zeuge

end Gabbro.Grammatik
