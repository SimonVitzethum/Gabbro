module

public import Grammatik.Logik.Vertraege.Pruefer.Measures

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer

open Invarianten Invarianten.Frag Invarianten.Elim Invarianten.VC Invarianten.Pruefer

variable {D : Deklaration}

/-- Source hints contain no proof of truth or preservation. -/
abbrev LoopHints (D : Deklaration) := ∀ f : D.Fn,
  Option (Expr D [] (Signatur.anfang D (D.signatur f)) .bool)

def loopHint (hints : LoopHints D) (f : D.Fn) : Except Invarianten.Frag.Refusal (Option (QF (Observation D))) :=
  match hints f with
  | none => .ok none
  | some expression => do
      let encoded ← translate expression .nil
      return some (lower encoded.payload)

/-- Certificate-producing program gate. Every function in the supplied list
    is checked; soundness uses the same complete enumeration as AkzeptiertX. -/
def checkContracts (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (budget : VCBudget := {}) (hints : LoopHints D := fun _ => none) :
    Except Invarianten.Frag.Refusal (PLift (∀ f ∈ functions, ContractDuties program S f)) :=
  collect functions (ContractDuties program S) (fun f => do
    let hint ← loopHint hints f
    checkFunction program S sources budget hint f)

def KontrakteGeprueftB (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S := fun _ => none) (budget : VCBudget := {})
    (hints : LoopHints D := fun _ => none) : Bool :=
  (checkContracts program S functions sources budget hints).toOption.isSome

def KontrakteGeprueft (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (budget : VCBudget) (hints : LoopHints D) : Prop :=
  ∃ certificate, checkContracts program S functions sources budget hints = .ok certificate

theorem KontrakteGeprueftB_iff (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (budget : VCBudget) (hints : LoopHints D) :
    KontrakteGeprueftB program S functions sources budget hints = true ↔
      KontrakteGeprueft program S functions sources budget hints := by
  unfold KontrakteGeprueftB KontrakteGeprueft
  cases checkContracts program S functions sources budget hints <;> simp

theorem KontrakteGeprueftB_sound {program : Programm D} {S : SperrInv D} {functions : List D.Fn}
    {sources : LockSources S} {budget : VCBudget} {hints : LoopHints D}
    (complete : ∀ f, f ∈ functions)
    (accepted : KontrakteGeprueftB program S functions sources budget hints = true) :
    ∀ f, ContractDuties program S f := by
  obtain ⟨certificate, computed⟩ := (KontrakteGeprueftB_iff program S functions sources budget hints).mp accepted
  exact fun f => certificate.down f (complete f)

/-- On rejection expose the actual contract counterexample or fragment reason.
    Successful compilation does not rerun the contract checker for diagnostics. -/
def contractVerdict (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (accepted : Bool) : Except String Bool :=
  if accepted then .ok true else
    match checkContracts program S functions sources with
    | .error cause => .error cause.message
    | .ok _ => .ok false

theorem contractVerdict_true_iff (program : Programm D) (S : SperrInv D) (functions : List D.Fn)
    (sources : LockSources S) (accepted : Bool) :
    contractVerdict program S functions sources accepted = .ok true ↔ accepted = true := by
  cases accepted with
  | true => simp only [contractVerdict, ↓reduceIte]
  | false =>
      simp only [contractVerdict, Bool.false_eq_true, ↓reduceIte]
      cases checkContracts program S functions sources <;> simp

/-- Changing unrelated bodies never invalidates a checked function. Used by
    linking; no checker is rerun and no new semantic assumption is inserted. -/
theorem contractDuties_congr {left right : Programm D} {S S' : SperrInv D} (f : D.Fn)
    (invariants : left.invariante = right.invariante)
    (requires : left.requires = right.requires) (ensures : left.ensures = right.ensures)
    (body : left.rumpf f = right.rumpf f) (locks : S = S')
    (checked : ContractDuties left S f) : ContractDuties right S' f := by
  subst S'
  intro passes Q shared subset
  have facts := checked passes (axWahr D) shared subset
  unfold KoerperGutSA InvGutSA InvGutGrundA RespektiertRahmen RespektiertVertraege
    ReqAmEintritt EnsAmRueck InvAmRueck InvHaelt torRuf at facts ⊢
  rw [← invariants, ← requires, ← ensures, ← body]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro O frame local contract U havoc A atomic R respects noPre
    exact facts.1.1 O frame local (axVertragOP_of_O _ (axVertragO_wahr O))
      U havoc A atomic R respects noPre
  · intro O frame local contract U havoc A atomic R respects noLogic
    exact facts.1.2 O frame local (axVertragOP_of_O _ (axVertragO_wahr O))
      U havoc A atomic R respects noLogic
  · intro O frame local contract U havoc A atomic R respects noPre
    exact facts.2.1 O frame local (axVertragOP_of_O _ (axVertragO_wahr O))
      U havoc A atomic R respects noPre
  · intro O frame local contract U havoc A atomic R respects noPre
    exact facts.2.2 O frame local (axVertragOP_of_O _ (axVertragO_wahr O))
      U havoc A atomic R respects noPre

end Gabbro.Grammatik.Vertraege.Pruefer
