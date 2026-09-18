/-
  File:      Grammatik/CloneHandoff.lean
  Subject:   THE CHECKED CLONE HANDOFF, MODEL SIDE (lane O-1, K-1).

  K-1 measured the gap: a `syscall` gate can declare the raw clone call,
  but "the child starts on the handed stack and must never return into the
  caller's frame" had no checked shape. The Rust half is the `stack` clause
  plus the `child` statement (`clone.rs`, N446-N450); this file is the model
  half, standalone over the existing types (`Syntax.lean` is not touched --
  no new statement constructor, no new machine rule):

  * `CloneAbi` -- a `SysAbi` plus the handed-stack register (`stack`),
    with well-formedness `CloneAbi.good` and its decision procedure;
  * `ChildNoReturn` -- a child thread's log holds no return of its entry
    (the G reading of "never returns into the caller's frame": G is
    address-free, so the handed STACK has no counterpart here -- that half
    is the stub's business and the runtime's assumption);
  * `CloneHandoff` -- every thread a start machine places at a gate entry
    never logs its entry's return;
  * `CloneAssume` -- the (d2) runtime duty: the handoff on every reached run;
  * `CloneStart` -- the (d) population duty: a thread starting at a gate
    entry is no declared start (entries and starts are distinct populations,
    so `einmal` and the worker fan-out never govern one thread twice).

  SKELETON (§1): the shape and the decider. Run laws and witnesses follow
  one definition at a time.
-/
import Grammatik.Syscall
import Grammatik.RufMaschineG

namespace Gabbro.Grammatik

/-! ## 1. The handoff shape: `CloneAbi` -/

/-- `CloneAbi`: a `SysAbi` plus the handed-stack register named by the
    `stack` clause. The number, the map and the table stay in the user
    declaration (beispiele/155); only the SHAPE travels here. -/
structure CloneAbi where
  /-- The gate's machine side (number, input map, output register, clobbers). -/
  abi : SysAbi
  /-- The handed-stack register: the `stack` clause names it AS a stack. -/
  stack : SysReg
  deriving DecidableEq, Repr

/-- Well-formedness: the base map is well-formed, the handed register is
    bound in `regs in`, and it is neither the answer register nor scratch.
    The Rust side decides the same four (`N446` in `clone.rs`). -/
def CloneAbi.good (a : CloneAbi) : Prop :=
  a.abi.gut ∧ a.stack ∈ a.abi.ein.map Prod.fst ∧ a.stack ≠ a.abi.aus ∧
    a.stack ∉ a.abi.clobber

/-- Decision procedure for `CloneAbi.good`. -/
def cloneAbiGoodB (a : CloneAbi) : Bool :=
  sysAbiGutB a.abi && decide (a.stack ∈ a.abi.ein.map Prod.fst) &&
    decide (a.stack ≠ a.abi.aus) && !decide (a.stack ∈ a.abi.clobber)

/-- Soundness: a positive decision means well-formedness. -/
theorem cloneAbiGoodB_sound (a : CloneAbi) (h : cloneAbiGoodB a = true) :
    a.good := by
  unfold cloneAbiGoodB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hGut, hBound⟩, hOut⟩, hClob⟩ := h
  exact ⟨sysAbiGutB_sound a.abi hGut, of_decide_eq_true hBound,
    of_decide_eq_true hOut, by simpa using hClob⟩

/-! ## 2. The handoff legs at declaration level -/

instance : Decidable (CloneAbi.good a) :=
  inferInstanceAs (Decidable
    (a.abi.gut ∧ a.stack ∈ a.abi.ein.map Prod.fst ∧ a.stack ≠ a.abi.aus ∧
      a.stack ∉ a.abi.clobber))

/-- The handed register is bound: first projection of `good`. -/
theorem cloneStack_bound (a : CloneAbi) (h : a.good) :
    a.stack ∈ a.abi.ein.map Prod.fst := h.2.1

/-- The handed register is not the answer register: second projection. -/
theorem cloneStack_notOut (a : CloneAbi) (h : a.good) : a.stack ≠ a.abi.aus :=
  h.2.2.1

/-- The handed register is no scratch register: third projection. -/
theorem cloneStack_notClobber (a : CloneAbi) (h : a.good) :
    a.stack ∉ a.abi.clobber := h.2.2.2

/-! ## 3. Witnesses: one good gate, one bad gate -/

/-- The witness map: two parameters in `rdi`/`rsi`, answers in `rax`,
    clobbers `rcx`/`r11`. -/
def cloneWitnessAbi : SysAbi :=
  { nummer := 1000
    ein := [(.rdi, 0), (.rsi, 1)]
    aus := .rax
    clobber := [.rcx, .r11] }

/-- The witness gate: the map above, handing `rsi`. `1000` is NOT an OS
    number -- the shape is gate-agnostic (beispiele/155 carries a user
    number of its own); any number instantiates it, and this one is chosen
    to be no dispatched call the tree knows. -/
def cloneWitness : CloneAbi :=
  { abi := cloneWitnessAbi
    stack := .rsi }

/-- The witness is well-formed, by computation. -/
theorem cloneWitness_good : cloneWitness.good := by decide

/-- The decider agrees, by computation. -/
theorem cloneWitness_goodB : cloneAbiGoodB cloneWitness = true := by decide

/-- Soundness, jointly instantiated: the decider's `true` delivers `good`
    on the witness table. -/
theorem cloneWitness_sound : cloneWitness.good :=
  cloneAbiGoodB_sound cloneWitness cloneWitness_goodB

/-- The handed register of the witness is bound (first leg, exercised). -/
theorem cloneWitness_stackBound : cloneWitness.stack ∈ cloneWitness.abi.ein.map Prod.fst :=
  cloneStack_bound cloneWitness cloneWitness_good

/-- The planted defect, red direction: handing the ANSWER register (`rax`)
    is no handoff. -/
def cloneBadWitness : CloneAbi :=
  { abi := cloneWitness.abi, stack := .rax }

/-- The defect fails, by computation. -/
theorem cloneBadWitness_fails : ¬ cloneBadWitness.good := by decide

#print axioms Gabbro.Grammatik.cloneAbiGoodB_sound
#print axioms Gabbro.Grammatik.cloneStack_bound
#print axioms Gabbro.Grammatik.cloneStack_notOut
#print axioms Gabbro.Grammatik.cloneStack_notClobber
#print axioms Gabbro.Grammatik.cloneWitness_good
#print axioms Gabbro.Grammatik.cloneWitness_goodB
#print axioms Gabbro.Grammatik.cloneWitness_sound
#print axioms Gabbro.Grammatik.cloneWitness_stackBound
#print axioms Gabbro.Grammatik.cloneBadWitness_fails

/-! ## 4. The run level: no return into the caller frame -/

variable {D : Deklaration}

/-- The log holds a return of `e`: the G reading of "returns". A `grund`
    (reason return) is no value return into the caller frame. -/
def isEntryReturn (D : Deklaration) (e : D.Fn) : RufEreignisF D → Prop
  | .rueck f _ _ _ _ => f = e
  | .eintritt _ _ _ => False
  | .grund _ _ _ _ _ => False

/-- A child thread never returns from its entry: no `.rueck entry` in its
    log. Returns of SUBFUNCTIONS inside the worker are fine -- only the
    ENTRY's return would land in the caller's frame. -/
def ChildNoReturn (D : Deklaration) (M : RufMaschineG D) (child : Faden)
    (entry : D.Fn) : Prop :=
  ∀ ev ∈ (M.faeden child).log, ¬ isEntryReturn D entry ev

/-- The handoff on one machine pair: every thread the start machine places
    at a gate entry never logs its entry's return. -/
def CloneHandoff (D : Deklaration) (gates : List (D.Ax × D.Fn))
    (M0 M : RufMaschineG D) : Prop :=
  ∀ (t : Faden) (g : D.Ax × D.Fn), g ∈ gates →
    (M0.faeden t).kopf.f = g.2 → ChildNoReturn D M t g.2

/-- (d2) the runtime's handoff duty: the handoff on every reached run. The
    premise `GabbroZiel` gains beside `Laufzeit` (Spec.lean). -/
def CloneAssume (D : Deklaration) (P : Programm D) (gates : List (D.Ax × D.Fn))
    (O : Orakel D) (passes : Nat) (M0 : RufMaschineG D) : Prop :=
  ∀ M, RufErreichbarG P O passes M0 M → CloneHandoff D gates M0 M

/-- (d) the population duty: a thread starting at a gate entry is no
    declared start. Entries and starts are distinct populations, so
    `einmal` and the worker fan-out never govern one thread twice. The
    field `Laufzeit` gains beside `start`/`einmal` (Spec.lean). -/
def CloneStart (D : Deklaration) (gates : List (D.Ax × D.Fn)) (starts : List D.Fn)
    (init : Faden → Σ f, Env D (D.params f)) : Prop :=
  ∀ t, (init t).1 ∈ gates.map Prod.snd → (init t).1 ∉ starts

/-! ## 5. The empty laws and the start-machine law -/

/-- No gates, no duty: the handoff holds for every machine pair. -/
theorem cloneHandoff_empty (M0 M : RufMaschineG D) :
    CloneHandoff D [] M0 M := by
  intro t g hg _
  exact absurd hg (by simp)

/-- The (d2) duty with no gates: every run qualifies. -/
theorem cloneAssume_empty (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 : RufMaschineG D) : CloneAssume D P [] O passes M0 := by
  intro M _
  exact cloneHandoff_empty M0 M

/-- The (d) duty with no gates: every start qualifies. -/
theorem cloneStart_empty (starts : List D.Fn)
    (init : Faden → Σ f, Env D (D.params f)) :
    CloneStart D [] starts init := by
  intro t ht
  exact absurd ht (by simp)

/-- At start nothing has returned: the handoff holds on the start machine
    for EVERY gate list, empty or not. The joint instantiation the empty
    laws are not: the start table with the reflexive run, gates admitted
    non-empty -- the `N449`-checked path has logged no return because it
    has logged nothing but its entry. -/
theorem cloneHandoff_start (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f, Env D (D.params f)) (gates : List (D.Ax × D.Fn)) :
    CloneHandoff D gates (RufStartG P sp init) (RufStartG P sp init) := by
  intro t g _ _ ev hev hret
  have hlog : ev = RufEreignisF.eintritt (init t).1 (init t).2 (sp.welt []) := by
    simpa [RufStartG] using hev
  rw [hlog] at hret
  simp [isEntryReturn] at hret

#print axioms Gabbro.Grammatik.cloneHandoff_empty
#print axioms Gabbro.Grammatik.cloneAssume_empty
#print axioms Gabbro.Grammatik.cloneStart_empty
#print axioms Gabbro.Grammatik.cloneHandoff_start

/- CUTS: what is not proved.
   - No leg of `Ziel` follows from the handoff here: that the stub and the
     runtime keep `ChildNoReturn` on every run is the (d2) ASSUMPTION, and
     that it preserves race freedom, contracts and progress is translation
     validation (§2 of TODO.md), not this file.
   - `D.klon` (the gate list, Syntax.lean) is filled by hand models only:
     the exporter refuses `child` (`LG004` in `lean_g.rs`), so no compiled
     unit exhibits a non-empty gate list yet; `Akzeptiert` decides no
     component for it (like lane 208's vacuous components, but without a
     pin -- there is nothing to pin against, the exporter never produces
     one).
   - The handed STACK has no G counterpart: G is address-free, so "starts
     on the handed stack" is C-level (the stub sets it) and lives in the
     (d2) assumption's informal reading, not in `CloneHandoff`.
-/

end Gabbro.Grammatik
