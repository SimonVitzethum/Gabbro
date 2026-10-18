import Grammatik.Code.Model.Weak

/-
  File:      Grammatik/Code/Conc/Thread.lean
  Subject:   TRACK L, PHASE L3 -- THE THREAD MACHINE OVER `Code`: several threads, ONE shared memory, an
             interleaving step.

  Machine G's threads are all there from the start (`RufStartG`: every thread is a declared start), so the IR machine
  needs no `spawn` and no `join`: a thread is a running frame with its stack of callers, or a finished run with its
  answer. One memory is shared (the cells of tables, globals and locks, and the `alloc` blocks every thread's locals
  live in: a block is allocated once and never freed, so the locals of two threads are different blocks, see
  `Refine/Frame`'s `Own`). A step is the step relation of `Model/Step.lean` of ONE thread against the shared memory,
  under an interface `S` for atomic loads: `Sees.shared` (`Conc/Shared.lean`) is machine GX's, `Sees.sc` the exact one.
  No views and no history are carried: GX over-approximates the weak memory's answers by "any value at a shared
  atomic" and `step_mono` (`Model/Weak.lean`) carries a refinement against that interface down to a more precise one.

  `treach_solo`: a run of ONE thread (a `Reach` of its configuration) is a run of the machine in which only that thread
  moves, and every other thread is where it was (`upd_other`: `upd` changes the memory and thread `u` only).
-/

namespace Gabbro.Code

variable [Conf]

/-- One thread: running a frame with its callers, or finished with its answer. -/
inductive Th where
  | run (f : Frame) (ks : List Frame)
  | done (v : Option Val)

/-- The machine: the shared memory and the thread table. -/
structure TM where
  m : Mem
  th : Nat → Th

/-- The configuration of thread `u` against the shared memory. -/
def TM.cfg (T : TM) (u : Nat) : Cfg :=
  match T.th u with
  | .run f ks => .run T.m f ks
  | .done v => .fin T.m v

/-- Thread `u` takes the configuration `c` (its memory is the shared one now). -/
def TM.upd (T : TM) (u : Nat) : Cfg → TM
  | .run m f ks => ⟨m, fun v => if v = u then .run f ks else T.th v⟩
  | .fin m x => ⟨m, fun v => if v = u then .done x else T.th v⟩

theorem cfg_upd (T : TM) (u : Nat) (c : Cfg) : (T.upd u c).cfg u = c := by
  cases c <;> simp [TM.upd, TM.cfg]

theorem upd_other (T : TM) {u v : Nat} (c : Cfg) (h : v ≠ u) : (T.upd u c).th v = T.th v := by
  cases c <;> simp [TM.upd, h]

theorem upd_upd (T : TM) (u : Nat) (c c' : Cfg) : (T.upd u c).upd u c' = T.upd u c' := by
  cases c <;> cases c' <;> simp [TM.upd] <;> funext v <;> split <;> rfl

theorem upd_cfg (T : TM) (u : Nat) : T.upd u (T.cfg u) = T := by
  obtain ⟨m, th⟩ := T
  simp only [TM.cfg]
  cases h : th u with
  | run f ks =>
      simp only [TM.upd]
      congr 1
      funext v
      split
      · rename_i e; rw [e]; exact h.symm
      · rfl
  | done x =>
      simp only [TM.upd]
      congr 1
      funext v
      split
      · rename_i e; rw [e]; exact h.symm
      · rfl

/-- **One machine step**: thread `u` takes one step of `Code` against the shared memory. -/
def TStep (M : Modl) (S : Sees) (T : TM) (u : Nat) (T' : TM) : Prop :=
  ∃ c', Step M S (T.cfg u) c' ∧ T' = T.upd u c'

/-- Reachability of the machine (any thread may move at each step). -/
inductive TReach (M : Modl) (S : Sees) : TM → TM → Prop where
  | refl (T : TM) : TReach M S T T
  | step (T T' T'' : TM) (u : Nat) : TStep M S T u T' → TReach M S T' T'' → TReach M S T T''

theorem TReach.trans {M : Modl} {S : Sees} {a b c : TM} (h1 : TReach M S a b) (h2 : TReach M S b c) :
    TReach M S a c := by
  induction h1 with
  | refl => exact h2
  | step x y z u hs _ ih => exact .step x y c u hs (ih h2)

/-- **A run of one thread is a run of the machine** in which only that thread moves. -/
theorem treach_solo {M : Modl} {S : Sees} {u : Nat} {c c' : Cfg} (h : Reach M S c c') :
    ∀ T : TM, T.cfg u = c → TReach M S T (T.upd u c') := by
  induction h with
  | refl c =>
      intro T hT
      rw [← hT, upd_cfg]
      exact .refl T
  | step x y z hs _ ih =>
      intro T hT
      have h1 : TStep M S T u (T.upd u y) := ⟨y, by rw [hT]; exact hs, rfl⟩
      have h2 := ih (T.upd u y) (cfg_upd T u y)
      rw [upd_upd] at h2
      exact .step T _ _ u h1 h2

end Gabbro.Code
