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
  (`blatt_erhaelt_slots` from `Ressourceninvariante.lean`) and the globals of an
  `L`-guarded global unchanged (`blatt_erhaelt_globs`, proved here as the
  global mirror). Take/release steps keep memory by construction.
-/
module

public import Grammatik.Nebenlaeufigkeit.Sperren.RelySperre.Teil1a

public import Grammatik.Kern.Semantik.Maschine
public import Grammatik.Nebenlaeufigkeit.Sperren.Ressourceninvariante.Teil2
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Nebenlaeufigkeit.Allgemein.WacheGlobal

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
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
      simp only [offen, List.not_mem_nil] at hLf
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
        hGuard hΛ.heldIn hfrei k fld
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
        hGuard hΛ.heldIn hfrei
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

end Gabbro.Grammatik
