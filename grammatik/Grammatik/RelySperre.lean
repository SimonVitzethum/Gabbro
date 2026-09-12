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

/-! ## 3. Lock exclusivity: two threads never hold the same lock -/

/-- **Lock exclusivity over reachable machines.** If `f` holds `L` at a
    machine reachable from a start machine, no other thread holds `L`
    there. No such state-level lemma existed: `gen_ausschluss` /
    `pc_ausschluss` (Maschine.lean) state `ForeignExclusion` over the
    run (who takes a lock takes it while nobody else holds it *at that
    position*); this lifts the scheduler rule to held-state
    disjointness by induction over `GenErreichbar`:
    - `blatt` keeps every held set (`blatt_brav`), so disjointness
      pushes through;
    - `nimmt L'` fires only while nobody else holds `L'` (`hfrei`):
      the new `L'`-holding is either the fresh take (excluded
      elsewhere by `hfrei`) or an old holding (exclusive by the
      induction hypothesis);
    - `gibt` only shrinks a held set.
    Every premise is used: `hO` feeds `blatt_brav` in the leaf case,
    `h` drives the induction. -/
theorem sperre_exklusiv (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (sp : Speicher D) (M : GenMaschine D)
    (h : GenErreichbar P O passes (GenStart sp) M)
    (f g : Faden) (hfg : f ≠ g) (L : D.Lock)
    (hLf : L ∈ offen (M.spuren f)) : L ∉ offen (M.spuren g) := by
  revert f g hfg L hLf
  induction h with
  | start =>
      intro f g hfg L hLf
      have e : (GenStart sp).spuren f = [] := rfl
      rw [e] at hLf
      simp [offen] at hLf
  | schritt M M' f0 _ hs ih =>
      intro f g hfg L hLf
      cases hs with
      | blatt V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn =>
          have hbrav := blatt_brav O passes hO M f0 V l Γ Λ Λ' s ρ hΛ σ' hstep
          have hopen : offen σ'.spur = offen (M.spuren f0) := by
            have e1 : σ'.haelt = offen σ'.spur := rfl
            have e2 : (M.weltVon f0).haelt = offen (M.spuren f0) := rfl
            rw [← e1, ← e2]
            exact hbrav.1
          by_cases hf0 : f = f0
          · subst hf0
            have hLf' : L ∈ offen (genUpdate M.spuren f σ'.spur f) := hLf
            rw [genUpdate_self, hopen] at hLf'
            have hgoal : L ∉ offen (genUpdate M.spuren f σ'.spur g) := by
              rw [genUpdate_noteq _ _ _ (Ne.symm hfg)]
              exact ih f g hfg L hLf'
            exact hgoal
          · have hLf' : L ∈ offen (genUpdate M.spuren f0 σ'.spur f) := hLf
            rw [genUpdate_noteq _ _ _ hf0] at hLf'
            by_cases hg0 : g = f0
            · subst hg0
              have hgoal : L ∉ offen (genUpdate M.spuren g σ'.spur g) := by
                rw [genUpdate_self, hopen]
                intro hcon
                exact (ih g f (Ne.symm hf0) L hcon) hLf'
              exact hgoal
            · have hgoal : L ∉ offen (genUpdate M.spuren f0 σ'.spur g) := by
                rw [genUpdate_noteq _ _ _ hg0]
                exact ih f g hfg L hLf'
              exact hgoal
      | nimmt L' hself hrang hfrei =>
          by_cases hf0 : f = f0
          · subst hf0
            have hLf' : L ∈ offen (genUpdate M.spuren f
                (Ereignis.nimmt L' (offen (M.spuren f)) :: M.spuren f) f) := hLf
            rw [genUpdate_self] at hLf'
            simp only [offen, List.mem_cons] at hLf'
            rcases hLf' with rfl | hLf'
            · have hgoal : L ∉ offen (genUpdate M.spuren f
                  (Ereignis.nimmt L (offen (M.spuren f)) :: M.spuren f) g) := by
                rw [genUpdate_noteq _ _ _ (Ne.symm hfg)]
                exact hfrei g (Ne.symm hfg)
              exact hgoal
            · have hgoal : L ∉ offen (genUpdate M.spuren f
                  (Ereignis.nimmt L' (offen (M.spuren f)) :: M.spuren f) g) := by
                rw [genUpdate_noteq _ _ _ (Ne.symm hfg)]
                exact ih f g hfg L hLf'
              exact hgoal
          · have hLf' : L ∈ offen (genUpdate M.spuren f0
                (Ereignis.nimmt L' (offen (M.spuren f0)) :: M.spuren f0) f) := hLf
            rw [genUpdate_noteq _ _ _ hf0] at hLf'
            by_cases hg0 : g = f0
            · subst hg0
              have hgoal : L ∉ offen (genUpdate M.spuren g
                  (Ereignis.nimmt L' (offen (M.spuren g)) :: M.spuren g) g) := by
                rw [genUpdate_self]
                simp only [offen, List.mem_cons]
                intro hcon
                rcases hcon with rfl | hcon
                · exact (hfrei f hf0) hLf'
                · exact (ih g f (Ne.symm hf0) L hcon) hLf'
              exact hgoal
            · have hgoal : L ∉ offen (genUpdate M.spuren f0
                  (Ereignis.nimmt L' (offen (M.spuren f0)) :: M.spuren f0) g) := by
                rw [genUpdate_noteq _ _ _ hg0]
                exact ih f g hfg L hLf'
              exact hgoal
      | gibt L' hhaelt =>
          by_cases hf0 : f = f0
          · subst hf0
            have hLf' : L ∈ offen (genUpdate M.spuren f
                (Ereignis.gibt L' :: M.spuren f) f) := hLf
            rw [genUpdate_self] at hLf'
            simp only [offen] at hLf'
            have hLf'' : L ∈ offen (M.spuren f) :=
              List.mem_of_mem_erase hLf'
            have hgoal : L ∉ offen (genUpdate M.spuren f
                (Ereignis.gibt L' :: M.spuren f) g) := by
              rw [genUpdate_noteq _ _ _ (Ne.symm hfg)]
              exact ih f g hfg L hLf''
            exact hgoal
          · have hLf' : L ∈ offen (genUpdate M.spuren f0
                (Ereignis.gibt L' :: M.spuren f0) f) := hLf
            rw [genUpdate_noteq _ _ _ hf0] at hLf'
            by_cases hg0 : g = f0
            · subst hg0
              have hgoal : L ∉ offen (genUpdate M.spuren g
                  (Ereignis.gibt L' :: M.spuren g) g) := by
                rw [genUpdate_self]
                simp only [offen]
                intro hcon
                exact (ih g f (Ne.symm hf0) L
                  (List.mem_of_mem_erase hcon)) hLf'
              exact hgoal
            · have hgoal : L ∉ offen (genUpdate M.spuren f0
                  (Ereignis.gibt L' :: M.spuren f0) g) := by
                rw [genUpdate_noteq _ _ _ hg0]
                exact ih f g hfg L hLf'
              exact hgoal

/-! ## 4. The rely from lock exclusivity -/

/-- **The table rely from lock exclusivity.** While `f` holds a lock `L`
    guarding table `t`, a step of another thread `g` keeps every slot of
    `t`: `f` holding `L` excludes `g` from holding it
    (`sperre_exklusiv` over the reachability inside `hR`), and a leaf
    step of a thread not holding `L` preserves the guarded slots
    (`blatt_erhaelt_slots`); take/release steps keep memory by
    construction. This discharges the memory-level `hRelyT` premise of
    `stabil_aus_bewachung` on the PC machine.

    Every premise is used: `hO` (leaf preservation and the oracle
    frame inside it, exclusivity), `hR` (exclusivity), `hfg`/`hL`
    (exclusivity), `hS` (the step case), `hGuard` (leaf preservation). -/
theorem rely_aus_sperre (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (hR : PCReach P O passes prog (GenStart sp) M pc)
    (f g : Faden) (hfg : g ≠ f) (L : D.Lock) (hL : L ∈ offen (M.spuren f))
    (M' : GenMaschine D) (pc' : PCStand) (hS : PCSchritt P O passes prog M pc g M' pc')
    (t : D.Tab) (hGuard : Sum.inl L ∈ D.braucht t) :
    ∀ k fld, M'.speicher.slots t k fld = M.speicher.slots t k fld := by
  have hG : GenErreichbar P O passes (GenStart sp) M :=
    pcReach_gen P O passes prog _ M pc hR
  have hfrei : L ∉ offen (M.spuren g) :=
    sperre_exklusiv P O passes hO sp M hG f g (Ne.symm hfg) L hL
  cases hS with
  | leaf V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn Λa cs hpc hΛa hmark hcar =>
      intro k fld
      show σ'.speicher.slots t k fld = M.speicher.slots t k fld
      exact blatt_erhaelt_slots O passes hO M g s ρ hleaf σ' hstep t L
        hGuard hΛ hfrei k fld
  | take L hself hrang hfrei' hpc =>
      intro k fld
      rfl
  | rel L hhaelt hpc =>
      intro k fld
      rfl

/-- **The global rely from lock exclusivity.** While `f` holds a lock
    `L` guarding global `x`, a step of another thread `g` keeps `x`:
    same argument as `rely_aus_sperre` through the global leaf lemma
    `blatt_erhaelt_globs`. This discharges the memory-level `hRelyG`
    premise of `stabil_aus_bewachung` on the PC machine.

    Every premise is used: `hO`, `hR`, `hfg`/`hL` (exclusivity), `hS`
    (the step case), `hGuard` (leaf preservation). -/
theorem rely_aus_sperre_global (P : Programm D) (O : Orakel D) (passes : Nat) (hO : GutO O)
    (prog : PCProg D) (sp : Speicher D) (M : GenMaschine D) (pc : PCStand)
    (hR : PCReach P O passes prog (GenStart sp) M pc)
    (f g : Faden) (hfg : g ≠ f) (L : D.Lock) (hL : L ∈ offen (M.spuren f))
    (M' : GenMaschine D) (pc' : PCStand) (hS : PCSchritt P O passes prog M pc g M' pc')
    (x : D.Glob) (hGuard : Sum.inl L ∈ D.gbraucht x) :
    M'.speicher.globs x = M.speicher.globs x := by
  have hG : GenErreichbar P O passes (GenStart sp) M :=
    pcReach_gen P O passes prog _ M pc hR
  have hfrei : L ∉ offen (M.spuren g) :=
    sperre_exklusiv P O passes hO sp M hG f g (Ne.symm hfg) L hL
  cases hS with
  | leaf V l Γ Λ Λ' s ρ hleaf hΛ σ' neu hstep hneu hkn Λa cs hpc hΛa hmark hcar =>
      show σ'.speicher.globs x = M.speicher.globs x
      exact blatt_erhaelt_globs O passes hO M g s ρ hleaf σ' hstep x L
        hGuard hΛ hfrei
  | take L hself hrang hfrei' hpc =>
      rfl
  | rel L hhaelt hpc =>
      rfl

#print axioms Gabbro.Grammatik.lese_globs_gleich
#print axioms Gabbro.Grammatik.storeGlob_fremd_global
#print axioms Gabbro.Grammatik.schreibSlot_globs_gleich
