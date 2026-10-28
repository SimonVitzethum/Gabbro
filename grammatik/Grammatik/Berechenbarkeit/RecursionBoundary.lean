/-
  File:      Grammatik/Berechenbarkeit/RecursionBoundary.lean
  Subject:   The unbounded-storage premise of a universality proof, on machine G itself.

  A finite, one-function Gabbro program (`f(); f(); return;`) reaches every finite stack
  depth at EVERY fixed loop budget, including zero. These are actual `RufSchrittG` steps
  from `RufStartG`, not transitions of a separate stack machine or answers from an oracle.
  Consequently no well-founded ranking decreases along all its calls.

  The termination classifier rejects precisely this unmeasured non-tail recursion. This
  is an expressiveness boundary, not a proof of Turing completeness: a complete simulation
  still has to implement communicating push/pop stacks and transfer observable results.
-/
import Grammatik.Logik.Terminierung.KlasseZeuge

namespace Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz.BudgetZeuge
open Gabbro.Grammatik.Terminierung.KlasseZeuge

/-- A finite program whose first call recursively enters itself, with another call pending. -/
def program : Programm bD := prog rZwei

/-- The standard entry, with no foreign functions, registers, data carriers or locks. -/
def initial : RufMaschineG bD := RufStartG program bS bInit

/-- The state produced by its next call, retaining the exact machine-G frame and log data. -/
def push (M : RufMaschineG bD) : RufMaschineG bD :=
  let σ := M.weltVon 0
  ⟨M.speicher,
   rufUpdateG M.faeden 0
    ⟨⟨(M.faeden 0).kopf.f, (M.faeden 0).kopf.rho, (M.faeden 0).kopf.s0,
       ⟨false, [], [], .nil, .ende rEnd⟩⟩ :: (M.faeden 0).stapel,
     ⟨(), .nil, σ, ⟨false, [], [], .nil, .ende rZwei⟩⟩,
     (M.faeden 0).spur, .eintritt () .nil σ :: (M.faeden 0).log⟩,
   M.lauf, M.start⟩

/-- Every push is an actual G call; it consumes no `forever` budget. -/
theorem push_step (p : Nat) (M : RufMaschineG bD)
    (head : (M.faeden 0).kopf.rest = ⟨false, [], [], .nil, .ende rZwei⟩) :
    RufSchrittG program bO p M 0 (push M) := by
  have h := RufSchrittG.ruf (P := program) (O := bO) (passes := p) M 0 false [] [] () .nil hpB rfl
    rEnd .nil head (by simp only [HeldIn, List.not_mem_nil, false_implies, implies_true]) (M.weltVon 0) rfl .nil rfl [] rfl
  simp only [rufEigenG, List.reverse_nil, List.map_nil, List.append_nil] at h
  exact h

/-- The concrete run, one genuine call per step. -/
def state : Nat → RufMaschineG bD
  | 0 => initial
  | n + 1 => push (state n)

theorem head_zeuge (n : Nat) :
    ((state n).faeden 0).kopf.rest = ⟨false, [], [], .nil, .ende rZwei⟩ := by
  cases n with
  | zero => rfl
  | succ n => simp only [state, push, rufUpdateG, ↓dreduceIte]

theorem step_zeuge (p n : Nat) : RufSchrittG program bO p (state n) 0 (state (n + 1)) :=
  push_step p (state n) (head_zeuge n)

theorem reached_zeuge (p n : Nat) : RufErreichbarG program bO p initial (state n) := by
  induction n with
  | zero => exact .start
  | succ n ih => exact .schritt _ _ 0 ih (step_zeuge p n)

theorem depth_zeuge (n : Nat) : ((state n).faeden 0).stapel.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [state, push, rufUpdateG] using congrArg Nat.succ ih

/-- **No fixed stack bound in the general G model**, even with loop budget zero. -/
theorem unbounded_stack (p n : Nat) :
    ∃ M, RufErreichbarG program bO p initial M ∧ (M.faeden 0).stapel.length = n :=
  ⟨state n, reached_zeuge p n, depth_zeuge n⟩

/-- The same real program is outside the unmeasured terminating fragment. -/
theorem rejected_zeuge : klasse program [()] ohne () = .abgelehnt := by decide

/-- The core safety checker accepts it. The termination classifier and its measure duty
    are additional conditions, not an implicit stack limit in `Akzeptiert`. -/
theorem accepted_zeuge : Akzeptiert program ⟨fun L => L.elim, fun L => L.elim⟩ [()] [] [] [()] = true := by
  decide

/-- Merely claiming that a measure exists does not supply a falling measure: the syntactic
    class changes, but the very same machine run is still present. -/
theorem claimed_measure_zeuge : klasse program [()] mit () = .endet := by decide

private theorem lexLt_self (xs : List Nat) : lexLt xs xs = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [lexLt, Nat.lt_irrefl, decide_false, BEq.rfl, ih, Bool.and_false, Bool.or_self]

/-- **No honest recursive descent measure exists for this program.** Its recursive call
    has the same arguments and world as its entry, so every candidate measure stays equal.
    This refutes the actual semantic duty, not just one proposed numeric bound. -/
theorem no_measure_duty (p : Nat) (m : Mass bD) (Q : AxEns bD) (S : SperrInv bD)
    (T : bD.Tab ⊕ bD.Glob → Prop) :
    ¬ MassPflicht program p Q S T m (zykS program [()]) () := by
  intro duty
  let R : ∀ f : bD.Fn, World bD → Env bD (bD.params f) → RufAusgang f :=
    fun _ _ _ => .logik .schleife
  have frame : RespektiertRahmen program R := by
    constructor
    · intro f σ ρ _ σ' v h; cases h
    · intro f σ ρ σ' v h; cases h
  have noDescent : OhneAbstieg R := by intro g σ ρ h; intro bad; cases bad
  have noPre : OhneVorbedingung R := by intro g σ ρ e h g' bad; cases h; cases bad
  have cycle : zykS program [()] () () = true := by decide
  have bad := duty bO (fun a => a.elim)
    ⟨fun r => r.elim, fun g => g.elim⟩ (fun a => a.elim)
    (fun L => L.elim) (fun L => L.elim) idA (havocA_id T) R frame noDescent noPre
    (bS.welt []) .nil (by rfl) () cycle
  apply bad
  rw [show program.rumpf () = rZwei from rfl]
  simp only [rZwei, execEndHA, execStmtHA, massTor, cycle, leseA, idA, World.lese, World.merke, Args.orte,
  List.map_nil, List.nil_append, evalArgs, lexLt_self, Bool.not_false, Bool.and_self, ↓reduceIte]

/-- **Termination boundary.** No well-founded measure can decrease along all steps of this
    program. Hence a proof of its recursive descent duty cannot be replaced by a class flag. -/
theorem no_wellFounded_ranking (p : Nat) {α : Sort _} (r : α → α → Prop) (wf : WellFounded r) :
    ¬ ∃ rank : RufMaschineG bD → α,
      ∀ M M', RufSchrittG program bO p M 0 M' → r (rank M') (rank M) := by
  rintro ⟨rank, decrease⟩
  have impossible : ∀ a, ∀ n, rank (state n) = a → False := fun a =>
    wf.induction (C := fun a => ∀ n, rank (state n) = a → False) a fun a ih n hn =>
      ih (rank (state (n + 1))) (hn ▸ decrease _ _ (step_zeuge p n)) (n + 1) rfl
  exact impossible (rank (state 0)) 0 rfl

end Gabbro.Grammatik.Berechenbarkeit.RecursionBoundary
