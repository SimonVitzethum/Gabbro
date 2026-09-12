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

/-! ## 5. Witness on the reference fixture: table rely -/

/-- Thread program for the table witness: thread 1 takes the lock and
    fires the writing leaf (as in `refB_prog`); thread 0 rests on an
    empty-holdings leaf atom so it can step with a local assignment. -/
def witProg : PCProg refD
  | 1 => [.take (), .leaf [Res.held (D := refD) ()] [Sum.inl (())]]
  | _ => [.leaf ([] : List (Res refD)) []]

/-- Step 1 (witness): thread 1 takes the lock from the start machine. -/
theorem wit_take :
    PCSchritt refP refO 0 witProg (GenStart refSp0) (fun _ => 0) 1
      refPC1pre refB_pc1 := by
  have hself : (() : refD.Lock) ∉ offen ((GenStart refSp0).spuren 1) := by
    intro hmem
    have e : ((GenStart refSp0).spuren 1) = [] := rfl
    have hnil : offen ((GenStart refSp0).spuren 1) = [] := by rw [e]; rfl
    have h2 : (()) ∈ ([] : List refD.Lock) := hnil ▸ hmem
    exact (List.mem_nil_iff _).mp h2 |>.elim
  have hrang : ∀ K ∈ offen ((GenStart refSp0).spuren 1),
      refD.rang K < refD.rang (()) := by
    intro K hK
    have e : ((GenStart refSp0).spuren 1) = [] := rfl
    have hnil : offen ([] : List (Ereignis refD)) = [] := rfl
    rw [e, hnil, List.mem_nil_iff] at hK
    exact absurd hK (by decide)
  have hfrei : GenFrei (GenStart refSp0) 1 (()) := by
    intro g hne hmem
    have e : ((GenStart refSp0).spuren g) = [] := rfl
    have hnil : offen ((GenStart refSp0).spuren g) = [] := by rw [e]; rfl
    have h2 : (()) ∈ ([] : List refD.Lock) := hnil ▸ hmem
    exact (List.mem_nil_iff _).mp h2 |>.elim
  have hpc : (witProg 1)[(fun _ => 0) 1]? =
      some (PCAtom.take (D := refD) ()) := rfl
  exact PCSchritt.take (GenStart refSp0) (fun _ => 0) 1 ()
    hself hrang hfrei hpc

/-- Step 2 (witness): thread 1 fires the writing leaf at position 1. -/
theorem wit_leaf :
    PCSchritt refP refO 0 witProg refPC1pre refB_pc1 1 refPC2 refB_pc2 := by
  have hpc : (witProg 1)[refB_pc1 1]? =
      some (PCAtom.leaf [Res.held (D := refD) ()] [Sum.inl (())]) := rfl
  have hneu : (((refPC1pre.weltVon 1).lese [Res.held (D := refD) ()]
      (refIdxEin.orte ++ refHundert.orte)).schreibSlot ()
      [Res.held (D := refD) ()] refK0 () refV100).spur =
      [Ereignis.zugriff () true [Res.held (D := refD) ()]
        (refPC1pre.weltVon 1).haelt] ++ refPC1pre.spuren 1 := rfl
  have hkn : ∀ (L : refD.Lock) (h : List refD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.zugriff () true
        [Res.held (D := refD) ()] (refPC1pre.weltVon 1).haelt] := by
    intro L h hm
    simp at hm
  have hmark : ∀ e ∈ [Ereignis.zugriff () true [Res.held (D := refD) ()]
      (refPC1pre.weltVon 1).haelt], ∀ (m : refD.Marke) (st : Nat),
      Res.marke m st ∈ e.lambda →
        m ∈ PCAtom.marks (PCAtom.leaf [Res.held (D := refD) ()]
          [Sum.inl (())]) := by
    intro e hm m st hlam
    simp at hm
    subst hm
    simp [Ereignis.lambda] at hlam
  have hcar : ∀ e ∈ [Ereignis.zugriff () true [Res.held (D := refD) ()]
      (refPC1pre.weltVon 1).haelt], ∀ o, e.traeger = some o →
        o ∈ PCAtom.carriers (PCAtom.leaf [Res.held (D := refD) ()]
          [Sum.inl (())]) := by
    intro e hm o ho
    simp at hm
    subst hm
    simp [Ereignis.traeger] at ho
    subst ho
    have hc : PCAtom.carriers (D := refD)
        (PCAtom.leaf [Res.held (D := refD) ()] [Sum.inl (())]) =
        [Sum.inl (())] := rfl
    rw [hc]
    exact List.mem_singleton.mpr rfl
  exact PCSchritt.leaf refPC1pre refB_pc1 1
    (vertragVon refD refEin) false [.int 0 10]
    [Res.held (D := refD) ()] [Res.held (D := refD) ()]
    refWriteStAt refRho7 rfl refPC1haelt _ _ refPCwrite hneu hkn
    [Res.held (D := refD) ()] [Sum.inl (())] hpc rfl hmark hcar

/-- The witness reachability: lock, then the writing leaf. -/
theorem wit_reach :
    PCReach refP refO 0 witProg (GenStart refSp0) refPC2 refB_pc2 := by
  have h1 : PCReach refP refO 0 witProg (GenStart refSp0) refPC1pre
      refB_pc1 :=
    PCReach.step _ _ _ _ _ PCReach.start wit_take
  exact PCReach.step _ _ _ _ _ h1 wit_leaf

/-- The thread-0 step statement: a local assignment, touching no
    memory and recording no events. -/
def witStmt0 : Stmt refD (vertragVon refD refEin) false [.bool] [] [] :=
  .assignVar (τ := .bool) Var.hier
    (.falsch : Expr refD [.bool] [] .bool)

/-- Its environment: the local starts `false`. -/
def witRho0 : Env refD [.bool] := .cons false .nil

/-- The outcome world of the thread-0 step: the read world. -/
def witW0' : World refD :=
  (refPC2.weltVon 0).lese ([] : List (Res refD))
    ([] : List (refD.Tab ⊕ refD.Glob))

/-- The machine after the thread-0 step. -/
def witM' : GenMaschine refD :=
  ⟨witW0'.speicher, genUpdate refPC2.spuren 0 witW0'.spur,
    refPC2.lauf ++ genEigen 0 [], refPC2.start,
    refPC2.welten ++ [witW0'], refPC2.tiefe + 1⟩

/-- Step 3 (witness): thread 0 fires the local assignment. -/
theorem wit_step0 :
    PCSchritt refP refO 0 witProg refPC2 refB_pc2 0 witM'
      (pcAdvance refB_pc2 0) := by
  have hΛ : HeldGenau ([] : List (Res refD)) (offen (refPC2.spuren 0)) := by
    have e : refPC2.spuren 0 = [] := rfl
    rw [e]
    intro L
    simp [offen]
  have hstep : (execStmt (D := refD) (V := vertragVon refD refEin) refO 0
      keinRuf witStmt0 (refPC2.weltVon 0) witRho0).welt = some witW0' := rfl
  have hneu : witW0'.spur = [] ++ refPC2.spuren 0 := rfl
  have hkn : ∀ (L : refD.Lock) (h : List refD.Lock),
      Ereignis.nimmt L h ∉ ([] : List (Ereignis refD)) := by
    intro L h hm
    simp at hm
  have hpc : (witProg 0)[refB_pc2 0]? =
      some (PCAtom.leaf (D := refD) [] []) := rfl
  refine PCSchritt.leaf refPC2 refB_pc2 0 (V := vertragVon refD refEin)
    (l := false) (Γ := [.bool]) (Λ := []) (Λ' := []) (s := witStmt0)
    (ρ := witRho0) (σ' := witW0') (neu := []) (Λa := []) (cs := [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · exact hΛ
  · exact hstep
  · exact hneu
  · exact hkn
  · exact hpc
  · rfl
  · intro e he m st hm
    simp at he
  · intro e he o ho
    simp at he

/-- Thread 1 holds the lock after the writing leaf. -/
theorem wit_haelt1 : (() : refD.Lock) ∈ offen (refPC2.spuren 1) := by
  have e : offen (refPC2.spuren 1) = [()] := rfl
  rw [e]
  exact List.mem_singleton.mpr rfl

/-- The lock guards the table. -/
theorem wit_guard : Sum.inl (() : refD.Lock) ∈ refD.braucht () :=
  List.mem_singleton.mpr rfl

/-- **Inhabitation for `rely_aus_sperre`.** All premises hold jointly on
    the reference fixture: the PC run reaches `refPC2` (lock, then the
    writing leaf) with thread 1 holding the lock of `konto`, and a step
    of thread 0 (a local assignment) keeps every slot. Non-degenerate:
    `einzahlen` writes `konto` and the run moves slot `0` from `0` to
    `100`. -/
theorem rely_aus_sperre_zeuge :
    (∀ (k : Int) (fld : refD.Feld ()),
      witM'.speicher.slots () k fld = refPC2.speicher.slots () k fld) ∧
    refPC2.speicher.slots () 0 () ≠ refSp0.slots () 0 () ∧
    (vertragVon refD refEin).schreibt () = true := by
  refine ⟨?_, refB_pc_schreibt, refEin_schreibt _⟩
  intro k fld
  exact rely_aus_sperre refP refO 0 refO_gut witProg refSp0 refPC2 refB_pc2
    wit_reach 1 0 (by decide) () wit_haelt1 witM' _ wit_step0 () wit_guard
    k fld

/-! ## 6. Witness on a global fixture: global rely -/

/-- Start memory for the global witness: slots `0`, global `0`. -/
def gSp0 : Speicher gD :=
  ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun _ => ⟨0, by decide, by decide⟩⟩

/-- The witness oracle: no axioms, no registers, always visible. -/
def gO : Orakel gD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun _ _ => true

/-- The oracle is good: every conjunct closes on its empty axiom domain. -/
theorem gO_gut : GutO gO := by
  intro a σ ρ
  exact nomatch a

/-- Thread program for the global witness: thread 1 takes the lock and
    fires the global-writing leaf; thread 0 rests on an empty-holdings
    leaf atom. -/
def gProg : PCProg gD
  | 1 => [.take (), .leaf [Res.held (D := gD) ()] [Sum.inr (())]]
  | _ => [.leaf ([] : List (Res gD)) []]

/-- The single-function program: trivial contracts, a returning body. -/
def gPr : Programm gD where
  invariante := fun i => nomatch i
  requires
    | () => .wahr
  ensures
    | () => .wahr
  rumpf
    | () => .ret (Γ := []) (Λ := [Res.held (D := gD) ()])
        .keine (List.Perm.refl _)

/-- The written value `5` in range. -/
def gWriteE : Expr gD [] [Res.held (D := gD) ()] (.int 0 10) :=
  .weiter (by decide) (by decide) (.lit 5)

/-- The global write holds its guard statically. -/
theorem gDarfHeld : gdarf gD () [Res.held (D := gD) ()] := by
  intro w hw
  have hmem : w ∈ ([Sum.inl ()] : List (gD.Lock ⊕ (gD.Marke × Nat))) := hw
  have e : w = Sum.inl () := List.mem_singleton.mp hmem
  subst e
  exact List.mem_singleton.mpr rfl

/-- The thread-1 write statement: global `()` gets `5`. -/
def gWriteSt : Stmt gD (Vertrag.vonSig gD (gD.signatur ())) false []
    [Res.held (D := gD) ()] [Res.held (D := gD) ()] :=
  .assignGlob () gWriteE rfl gDarfHeld

/-- Counter after the lock step on thread 1. -/
def gPc1 : PCStand := pcAdvance (fun _ => 0) 1

/-- The machine after thread 1 takes the lock. -/
def gM1 : GenMaschine gD :=
  ⟨gSp0,
    genUpdate (GenStart gSp0).spuren 1 [Ereignis.nimmt (D := gD) () []],
    (GenStart gSp0).lauf ++ genEigen 1 [Ereignis.nimmt (D := gD) () []],
    (GenStart gSp0).start,
    (GenStart gSp0).welten ++ [gSp0.welt [Ereignis.nimmt (D := gD) () []]],
    (GenStart gSp0).tiefe + 1⟩

/-- Step 1 (global witness): thread 1 takes the lock. -/
theorem gTake :
    PCSchritt gPr gO 0 gProg (GenStart gSp0) (fun _ => 0) 1 gM1 gPc1 := by
  have hself : (() : gD.Lock) ∉ offen ((GenStart gSp0).spuren 1) := by
    intro hmem
    have e : ((GenStart gSp0).spuren 1) = [] := rfl
    have hnil : offen ((GenStart gSp0).spuren 1) = [] := by rw [e]; rfl
    have h2 : (()) ∈ ([] : List gD.Lock) := hnil ▸ hmem
    exact (List.mem_nil_iff _).mp h2 |>.elim
  have hrang : ∀ K ∈ offen ((GenStart gSp0).spuren 1),
      gD.rang K < gD.rang (()) := by
    intro K hK
    have e : ((GenStart gSp0).spuren 1) = [] := rfl
    have hnil : offen ([] : List (Ereignis gD)) = [] := rfl
    rw [e, hnil, List.mem_nil_iff] at hK
    exact absurd hK (by decide)
  have hfrei : GenFrei (GenStart gSp0) 1 (()) := by
    intro g hne hmem
    have e : ((GenStart gSp0).spuren g) = [] := rfl
    have hnil : offen ((GenStart gSp0).spuren g) = [] := by rw [e]; rfl
    have h2 : (()) ∈ ([] : List gD.Lock) := hnil ▸ hmem
    exact (List.mem_nil_iff _).mp h2 |>.elim
  have hpc : (gProg 1)[(fun _ => 0) 1]? =
      some (PCAtom.take (D := gD) ()) := rfl
  exact PCSchritt.take (GenStart gSp0) (fun _ => 0) 1 ()
    hself hrang hfrei hpc

/-- The outcome world of the global write. -/
def gW1w : World gD :=
  (((gM1.weltVon 1).lese [Res.held (D := gD) ()] (gWriteE.orte)).schreibGlob ()
    [Res.held (D := gD) ()]
    (eval ((gM1.weltVon 1).lese [Res.held (D := gD) ()] (gWriteE.orte))
      gWriteE
      ((gM1.weltVon 1).lese [Res.held (D := gD) ()] (gWriteE.orte))
      Env.nil))

/-- Thread 1 holds the lock after taking it. -/
theorem gM1haelt :
    HeldGenau [Res.held (D := gD) ()]
      (offen (gM1.spuren 1)) := by
  have e : offen (gM1.spuren 1) = [()] := rfl
  have h : HeldGenau [Res.held (D := gD) ()] [()] := by
    intro L
    constructor
    · intro hL
      have he : Res.held (D := gD) L = Res.held (D := gD) () :=
        (List.mem_singleton.mp hL)
      have eL : L = () := by cases he; rfl
      have hmem : L ∈ ([()] : List gD.Lock) :=
        eL ▸ List.mem_singleton.mpr rfl
      exact hmem
    · intro hL
      have he : L = () := (List.mem_singleton.mp hL)
      have hmem : Res.held (D := gD) L ∈
          ([Res.held (D := gD) ()] : List (Res gD)) :=
        he ▸ List.mem_singleton.mpr rfl
      exact hmem
  rw [e]
  exact h

/-- Counter after the leaf step on thread 1. -/
def gPc2 : PCStand := pcAdvance gPc1 1

/-- The machine after thread 1 writes the global. -/
def gM2 : GenMaschine gD :=
  ⟨gW1w.speicher, genUpdate gM1.spuren 1 gW1w.spur,
    gM1.lauf ++ genEigen 1
      [Ereignis.gzugriff () true [Res.held (D := gD) ()]
        (gM1.weltVon 1).haelt],
    gM1.start, gM1.welten ++ [gW1w], gM1.tiefe + 1⟩

/-- Step 2 (global witness): thread 1 fires the global-writing leaf. -/
theorem gLeaf :
    PCSchritt gPr gO 0 gProg gM1 gPc1 1 gM2 gPc2 := by
  have hpc : (gProg 1)[gPc1 1]? =
      some (PCAtom.leaf [Res.held (D := gD) ()] [Sum.inr (())]) := rfl
  have hstep : (execStmt (D := gD) (V := Vertrag.vonSig gD (gD.signatur ()))
      gO 0 keinRuf gWriteSt (gM1.weltVon 1) Env.nil).welt = some gW1w := rfl
  have hneu : gW1w.spur =
      [Ereignis.gzugriff () true [Res.held (D := gD) ()]
        (gM1.weltVon 1).haelt] ++ gM1.spuren 1 := rfl
  have hkn : ∀ (L : gD.Lock) (h : List gD.Lock),
      Ereignis.nimmt L h ∉ [Ereignis.gzugriff () true
        [Res.held (D := gD) ()] (gM1.weltVon 1).haelt] := by
    intro L h hm
    simp at hm
  have hmark : ∀ e ∈ [Ereignis.gzugriff () true [Res.held (D := gD) ()]
      (gM1.weltVon 1).haelt], ∀ (m : gD.Marke) (st : Nat),
      Res.marke m st ∈ e.lambda →
        m ∈ PCAtom.marks (PCAtom.leaf [Res.held (D := gD) ()]
          [Sum.inr (())]) := by
    intro e hm m st hlam
    simp at hm
    subst hm
    simp [Ereignis.lambda] at hlam
  have hcar : ∀ e ∈ [Ereignis.gzugriff () true [Res.held (D := gD) ()]
      (gM1.weltVon 1).haelt], ∀ o, e.traeger = some o →
        o ∈ PCAtom.carriers (PCAtom.leaf [Res.held (D := gD) ()]
          [Sum.inr (())]) := by
    intro e hm o ho
    simp at hm
    subst hm
    simp [Ereignis.traeger] at ho
    subst ho
    have hc : PCAtom.carriers (D := gD)
        (PCAtom.leaf [Res.held (D := gD) ()] [Sum.inr (())]) =
        [Sum.inr (())] := rfl
    rw [hc]
    exact List.mem_singleton.mpr rfl
  exact PCSchritt.leaf gM1 gPc1 1 (Vertrag.vonSig gD (gD.signatur ()))
    false [] [Res.held (D := gD) ()] [Res.held (D := gD) ()]
    gWriteSt Env.nil rfl gM1haelt _ _ hstep hneu hkn
    [Res.held (D := gD) ()] [Sum.inr (())] hpc rfl hmark hcar

/-- The global-witness reachability: lock, then the global write. -/
theorem gReach :
    PCReach gPr gO 0 gProg (GenStart gSp0) gM2 gPc2 := by
  have h1 : PCReach gPr gO 0 gProg (GenStart gSp0) gM1 gPc1 :=
    PCReach.step _ _ _ _ _ PCReach.start gTake
  exact PCReach.step _ _ _ _ _ h1 gLeaf

/-- The thread-0 step statement: a local assignment, touching no memory. -/
def gStmt0 : Stmt gD (Vertrag.vonSig gD (gD.signatur ())) false [.bool]
    [] [] :=
  .assignVar (τ := .bool) Var.hier
    (.falsch : Expr gD [.bool] [] .bool)

/-- Its environment: the local starts `false`. -/
def gRho0 : Env gD [.bool] := .cons false .nil

/-- The outcome world of the thread-0 step: the read world. -/
def gW0' : World gD :=
  (gM2.weltVon 0).lese ([] : List (Res gD))
    ([] : List (gD.Tab ⊕ gD.Glob))

/-- The machine after the thread-0 step. -/
def gM3 : GenMaschine gD :=
  ⟨gW0'.speicher, genUpdate gM2.spuren 0 gW0'.spur,
    gM2.lauf ++ genEigen 0 [], gM2.start,
    gM2.welten ++ [gW0'], gM2.tiefe + 1⟩

/-- Step 3 (global witness): thread 0 fires the local assignment. -/
theorem gStep0 :
    PCSchritt gPr gO 0 gProg gM2 gPc2 0 gM3
      (pcAdvance gPc2 0) := by
  have hΛ : HeldGenau ([] : List (Res gD)) (offen (gM2.spuren 0)) := by
    have e : gM2.spuren 0 = [] := rfl
    rw [e]
    intro L
    simp [offen]
  have hstep : (execStmt (D := gD)
      (V := Vertrag.vonSig gD (gD.signatur ())) gO 0
      keinRuf gStmt0 (gM2.weltVon 0) gRho0).welt = some gW0' := rfl
  have hneu : gW0'.spur = [] ++ gM2.spuren 0 := rfl
  have hkn : ∀ (L : gD.Lock) (h : List gD.Lock),
      Ereignis.nimmt L h ∉ ([] : List (Ereignis gD)) := by
    intro L h hm
    simp at hm
  have hpc : (gProg 0)[gPc2 0]? =
      some (PCAtom.leaf (D := gD) [] []) := rfl
  refine PCSchritt.leaf gM2 gPc2 0 (Vertrag.vonSig gD (gD.signatur ()))
    (l := false) (Γ := [.bool]) (Λ := []) (Λ' := []) (s := gStmt0)
    (ρ := gRho0) (σ' := gW0') (neu := []) (Λa := []) (cs := [])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · exact hΛ
  · exact hstep
  · exact hneu
  · exact hkn
  · exact hpc
  · rfl
  · intro e he m st hm
    simp at he
  · intro e he o ho
    simp at he

/-- Thread 1 holds the lock after the global write. -/
theorem gHaelt1 : (() : gD.Lock) ∈ offen (gM2.spuren 1) := by
  have e : offen (gM2.spuren 1) = [()] := rfl
  rw [e]
  exact List.mem_singleton.mpr rfl

/-- The write moved the global: it reads `5` now. -/
theorem gW1w_glob5 : (gM2.speicher.globs ()).n = 5 := rfl

/-- The start global reads `0`. -/
theorem gSp0_glob0 : (gSp0.globs ()).n = 0 := rfl

/-- Memory really moved: the global went from `0` to `5`. -/
theorem gMoved : gM2.speicher.globs () ≠ gSp0.globs () := by
  intro hcon
  have hn : (gM2.speicher.globs ()).n = (gSp0.globs ()).n :=
    congrArg Zahl.n hcon
  rw [gW1w_glob5, gSp0_glob0] at hn
  exact absurd hn (by decide)

/-- **Inhabitation for `rely_aus_sperre_global`.** All premises hold
    jointly on `gD`: the PC run reaches `gM2` (lock, then the global
    write) with thread 1 holding the lock guarding the global, and a
    step of thread 0 (a local assignment) keeps the global.
    Non-degenerate: some function writes a table (`gTabWrite`) and the
    run moves the global from `0` to `5`. -/
theorem rely_aus_sperre_global_zeuge :
    (gM3.speicher.globs () = gM2.speicher.globs ()) ∧
    (gM2.speicher.globs () ≠ gSp0.globs ()) ∧
    (∃ f t, gD.schreibt f t = true) := by
  refine ⟨?_, gMoved, gTabWrite⟩
  exact rely_aus_sperre_global gPr gO 0 gO_gut gProg gSp0 gM2 gPc2
    gReach 1 0 (by decide) () gHaelt1 gM3 _ gStep0 () gGuardInst

/-! ## CUTS: what is not proved here
  - `sperre_exklusiv` lifts the take-time scheduler rule (`GenFrei`)
    to held-state disjointness; it does not relate held state to the
    run-level `ForeignExclusion` beyond sharing the `nimmt` rule.
  - `blatt_erhaelt_globs` covers `axiomCall` through the oracle frame
    plus `hgd`; the trace half of `GutO` is not needed and not used.
  - Both witnesses use hand-built thread programs (`witProg`,
    `gProg`) rather than extracted ones (`Extraktion.progAus`): the
    rely holds for every `PCProg`, so no extraction adequacy is owed.
  - The global witness program `gPr` carries trivial contracts; no
    contract discharge is claimed.
-/

#print axioms Gabbro.Grammatik.lese_globs_gleich
#print axioms Gabbro.Grammatik.storeGlob_fremd_global
#print axioms Gabbro.Grammatik.schreibSlot_globs_gleich
#print axioms Gabbro.Grammatik.merke_globs_gleich
#print axioms Gabbro.Grammatik.schreibBytes_globs_gleich
#print axioms Gabbro.Grammatik.blatt_erhaelt_globs
#print axioms Gabbro.Grammatik.sperre_exklusiv
#print axioms Gabbro.Grammatik.rely_aus_sperre
#print axioms Gabbro.Grammatik.rely_aus_sperre_zeuge
#print axioms Gabbro.Grammatik.rely_aus_sperre_global
#print axioms Gabbro.Grammatik.rely_aus_sperre_global_zeuge
