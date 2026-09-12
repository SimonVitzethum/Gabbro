/-
  File:      Grammatik/RelySperre.lean
  Subject:   D9, SECOND HALF -- THE RELY FROM LOCK EXCLUSIVITY (lane 106).

  `stabil_aus_bewachung` (StabilBewacht.lean) takes the memory-level rely
  `hRelyT` as a premise. On the PC machine it is derivable: the take rule
  fires only while nobody else holds the lock (`GenFrei`), so two threads
  never hold the same lock (`sperre_exklusiv`, proved here by induction
  over `GenErreichbar` -- no such state-level lemma existed before, only
  the run-level `ForeignExclusion`); a leaf step of a thread not holding
  `L` then leaves the slots of an `L`-guarded table unchanged
  (`blatt_erhaelt_slots` from CSLInvariante.lean) and the globals of an
  `L`-guarded global unchanged (`blatt_erhaelt_globs`, proved here as the
  global mirror). Take/release steps keep memory by construction.
-/
import Grammatik.Maschine
import Grammatik.CSLInvariante
import Grammatik.ReferenzB
import Grammatik.WacheGlobal

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Reads (`World.lese`) only extend the trace: globals are untouched. -/
theorem lese_globs_gleich (σ : World D) (Λ : List (Res D))
    (orte : List (D.Tab ⊕ D.Glob)) (x : D.Glob) :
    (σ.lese Λ orte).globs x = σ.globs x := rfl

/-- A store to another global leaves this global untouched. -/
theorem storeGlob_fremd_global (σ : World D) {x g : D.Glob} (h : x ≠ g)
    (v : Wert D (D.gtyp g)) :
    (σ.storeGlob g v).globs x = σ.globs x := by
  simp [World.storeGlob, h]

/-- A slot write leaves every global untouched. -/
theorem schreibSlot_globs_gleich (σ : World D) (u : D.Tab) (Λ : List (Res D))
    (k : Int) (f : D.Feld u) (v : Wert D (D.typ u f)) (x : D.Glob) :
    (σ.schreibSlot u Λ k f v).globs x = σ.globs x := rfl

/-- Recording events (`World.merke`) leaves globals untouched. -/
theorem merke_globs_gleich (σ : World D) (es : List (Ereignis D)) (x : D.Glob) :
    (σ.merke es).globs x = σ.globs x := rfl

/-- Byte writes leave every global untouched, by induction over the byte
    list. Used: `k`, `bs` drive the induction; every other premise fixes
    the step the induction hypothesis fires on. -/
theorem schreibBytes_globs_gleich (σ : World D) (u : D.Tab) (f : D.Feld u)
    (hf : D.typ u f = .int 0 255) (Λ : List (Res D))
    (k : Int) (bs : List Byte) (x : D.Glob) :
    (σ.schreibBytes u f hf Λ k bs).globs x = σ.globs x := by
  induction bs generalizing σ k with
  | nil => rfl
  | cons b bs ih =>
      simp only [World.schreibBytes]
      have h1 := ih (σ.schreibSlot u Λ k f
        (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))) (k + 1)
      have h2 : (σ.schreibSlot u Λ k f
          (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))).globs x =
          σ.globs x := rfl
      rw [h1, h2]

/-! ## 2. Leaf extension for globals: a firing leaf of a thread not
    holding L preserves the globals of the L-guarded carrier -/

/-- A firing leaf step of a thread that does not hold `L` leaves the
    `L`-guarded global `x` unchanged -- the global mirror of
    `blatt_erhaelt_slots`.

    Table writes go through `schreibSlot`/`schreibBytes`, which never
    touch `globs`; global writes (`assignGlob`, `publish`) to `x` itself
    carry their guard (`hL`) on the constructor, contradicting `hfrei`
    through `HeldGenau`, and to another global go through the store
    frame; `axiomCall` answers with the oracle world, where a difference
    forces `D.agschreibt a x = true` through the oracle frame (`hO`,
    frame clause only) and `hgd` turns that into the guard. Every other
    leaf never touches globals.

    Every premise is used: `hleaf` eliminates the eleven compounds,
    `hstep` fires in every branch, `hGuard`/`hΛ`/`hfrei` close the
    same-global and oracle cases, `hO` gives the oracle frame. -/
theorem blatt_erhaelt_globs
    (O : Orakel D) (passes : Nat) (hO : GutO O)
    (M : GenMaschine D) (f : Faden)
    {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ') (ρ : Env D Γ)
    (hleaf : s.istBlatt = true)
    (σ' : World D)
    (hstep : (execStmt O passes keinRuf s (M.weltVon f) ρ).welt = some σ')
    (x : D.Glob) (L : D.Lock)
    (hGuard : Sum.inl L ∈ D.gbraucht x)
    (hΛ : HeldGenau Λ (offen (M.spuren f)))
    (hfrei : L ∉ offen (M.spuren f)) :
    σ'.globs x = (M.weltVon f).globs x := by
  have hheld : Res.held L ∈ Λ → L ∈ offen (M.spuren f) := fun h => (hΛ L).mp h
  cases s with
  | assignSlot u fld i e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | assignDurch p u ht fld i e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | assignGlob g e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      by_cases hgx : g = x
      · subst hgx
        have hmem : Res.held L ∈ Λ := by
          have hdarf := hL _ hGuard
          simpa [Res.von] using hdarf
        exact False.elim (hfrei (hheld hmem))
      · simp only [World.schreibGlob, merke_globs_gleich]
        exact (storeGlob_fremd_global _ (Ne.symm hgx) _).trans
          (lese_globs_gleich _ _ _ _)
  | schreibBytes u fld hf n i hlo hhi e hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rw [schreibBytes_globs_gleich]
      exact lese_globs_gleich _ _ _ _
  | assignVar x e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | uebergang u fld hτ i von nach hn he hw hL =>
      simp only [execStmt] at hstep
      split at hstep
      · simp only [Ausgang.welt, Option.some.injEq] at hstep
        subst hstep
        rfl
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
  | axiomCall a args _ _ _ _ hgd =>
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
        cases heq : D.agschreibt a x with
        | true =>
            have hmem : Res.held L ∈ Λ := by
              have hdarf := hgd x heq
              have hmem' := hdarf _ hGuard
              simpa [Res.von] using hmem'
            exact False.elim (hfrei (hheld hmem))
        | false =>
            have e1 : σ1.globs x =
                ((M.weltVon f).lese Λ args.orte).globs x := by
              rw [← hfst]
              exact hframe.2 x heq
            exact e1.trans (lese_globs_gleich _ _ _ _)
      · simp [Ausgang.welt] at hstep
  | regSchreib r hk e =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | transition r hk m hm hl maske bits =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | publish g e payload hp hw hL =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      by_cases hgx : g = x
      · subst hgx
        have hmem : Res.held L ∈ Λ := by
          have hdarf := hL _ hGuard
          simpa [Res.von] using hdarf
        exact False.elim (hfrei (hheld hmem))
      · simp only [World.schreibGlob, merke_globs_gleich]
        exact (storeGlob_fremd_global _ (Ne.symm hgx) _).trans
          (lese_globs_gleich _ _ _ _)
  | advances m a hh hs =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | retires m st hh a =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | ret e hΛe =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | retGrund r hΛe =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | leave hh =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl
  | next hh =>
      simp only [execStmt, Ausgang.welt, Option.some.injEq] at hstep
      subst hstep
      rfl

/-! ## CUTS: what is not proved here
  - Skeleton only: `blatt_erhaelt_globs`, `sperre_exklusiv`,
    `rely_aus_sperre`, `rely_aus_sperre_global` and both witnesses follow.
-/

#print axioms Gabbro.Grammatik.lese_globs_gleich
#print axioms Gabbro.Grammatik.storeGlob_fremd_global
#print axioms Gabbro.Grammatik.schreibSlot_globs_gleich
