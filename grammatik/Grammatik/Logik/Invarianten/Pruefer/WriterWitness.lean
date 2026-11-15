module

public import Grammatik.Logik.Invarianten.Pruefer.Checker
public import Grammatik.Logik.Invarianten.Modell.Decision
public import Grammatik.Zielsatz.Atomar.AkzeptiertSchnell
public import Grammatik.Logik.Invarianten.Frag.Witness
import all Batteries.Data.Except

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer.WriterWitness

open Frag Zielsatz

/-- A real writer with an invariant that is false in some typed worlds. -/
def declaration : Deklaration :=
  { Frag.Witness.declaration with
    Fn := Unit
    sig := fun _ => 0
    sigNr := fun _ =>
      { params := [], erg := none, gruende := 0, haelt := []
        schreibt := fun _ => false, gschreibt := fun name => !name
        konsumiert := [], produziert := [] }
    passt := fun _ _ => false
    passt_ok := fun _ _ impossible => by cases impossible
    rzusage := fun item => nomatch item
    traeger := fun _ => [.inr false]
    invarianten_gehalten := fun _ _ _ _ _ lock => nomatch lock }

instance : DecidableEq declaration.Fn := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq declaration.Ax := inferInstanceAs (DecidableEq Empty)

abbrev contract := vertragVon declaration ()

def access (name : declaration.Glob) : gdarf declaration name [] := fun _ member => nomatch member

def invariant : Expr declaration [] [] .bool := .eq (.glob false (access false)) (.lit 0)

def store (value : Nat) (bounded : value ≤ 10) : Stmt declaration contract false [] [] [] :=
  .assignGlob false (.widen (by omega) (by omega) (.lit (value : Int))) rfl (access false)

def restoring : Endblock declaration contract false [] [] :=
  .cons (store 1 (by decide))
    (.cons (store 0 (by decide)) (.ret .empty (List.Perm.refl _)))

def breaking : Endblock declaration contract false [] [] :=
  .cons (store 1 (by decide)) (.ret .empty (List.Perm.refl _))

def program : Programm declaration where
  invariante := fun _ => invariant
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => restoring

def world : World declaration where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun _ => ⟨0, by decide, by decide⟩
  spur := []

def unit : Einheit declaration where
  P := program
  S := SperrInv.leer declaration
  Q := fun item => nomatch item
  starts := [⟨(), .nil⟩]
  sp0 := world.speicher

def badUnit : Einheit declaration := { unit with P := { program with rumpf := fun _ => breaking } }

theorem start_zeuge : StartPflicht unit :=
  ⟨(fun lock => nomatch lock), fun _ _ => rfl⟩

theorem initial_zeuge : InvHaelt unit.P () (unit.sp0.welt []) := by
  change wahr? (eval (unit.sp0.welt []) invariant (unit.sp0.welt []) .nil) = true
  decide +kernel

def oracle : Orakel declaration where
  wirktL := fun item => nomatch item
  regLiesL := fun item => nomatch item
  regSchreib := fun item => nomatch item
  sichtbarL := fun _ _ => true

def calls (f : declaration.Fn) (entry : World declaration)
    (_ : Env declaration (declaration.params f)) : RufAusgang f := .ok entry ()

/-- The refused writer actually destroys an initially true invariant. -/
theorem breaking_execution_zeuge :
    (match execEnd oracle 0 calls breaking world .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => true) = false := by decide +kernel

/-- The accepted writer also has an actual value return with the invariant
    restored, after its intermediate write of one. -/
theorem restoring_execution_zeuge :
    (match execEnd oracle 0 calls restoring world .nil with
      | .zurueck next _ => eval next invariant next .nil
      | _ => false) = true := by decide +kernel

theorem restoring_accepted_zeuge : invariantVCB unit.P unit.S [()] = true := by decide +kernel

/-- The generated idle root also has a satisfiable VC gate. Its return owes
    no writer invariant; the translated real writer still restores zero. -/
theorem idle_accepted_zeuge :
    invariantVCB unit.P.mitRuhe unit.S.mitRuhe (fsRuhe [()]) = true := by decide +kernel

theorem breaking_refused_zeuge : invariantVCB badUnit.P badUnit.S [()] = false := by decide +kernel

/-- A writer restoring zero is accepted even though zero is not universally
    true. This rules out replacing preservation by declaration validity. -/
theorem invariant_not_valid_zeuge :
    Modell.decideInvariant (declaration.traeger ()) invariant = .ok false := by decide +kernel

def preserving : Programm declaration :=
  { program with
    requires := fun _ => invariant
    rumpf := fun _ => .ret .empty (List.Perm.refl _) }

/-- Ordinary preservation uses the entry invariant when requires states it. -/
theorem preservation_accepted_zeuge : invariantVCB preserving unit.S [()] = true := by decide +kernel

/-- Existing InvGut duties do not grant an unstated entry invariant. This
    boundary must remain visible until the owner changes that semantic duty. -/
theorem unstated_entry_refused_zeuge :
    invariantVCB { preserving with requires := fun _ => .tru } unit.S [()] = false := by decide +kernel

theorem checker_accepted_zeuge :
    AkzeptiertX unit.P unit.S [()] [] [.inl (), .inr false, .inr true] unit.ws = true := by
  unfold AkzeptiertX
  rw [restoring_accepted_zeuge]
  simp only [Bool.and_true, Bool.and_eq_true]
  decide +kernel

theorem checker_refused_zeuge :
    AkzeptiertX badUnit.P badUnit.S [()] [] [.inl (), .inr false, .inr true] badUnit.ws = false := by
  unfold AkzeptiertX
  rw [breaking_refused_zeuge, Bool.and_false]

theorem duties_zeuge (passes : Nat) (Q : AxEns declaration) :
    InvGutS unit.P passes Q unit.S () ∧ InvGutGrund unit.P passes Q unit.S () :=
  invariantVCB_invGut (fun f => by cases f; exact List.mem_cons_self) restoring_accepted_zeuge passes Q ()

/-- The existing user-duty adapter is inhabited on the same accepted unit.
    No invariant proof is passed in its user-logic arguments. -/
theorem adapter_zeuge : LogikPflichtA unit.P unit.S unit.Q (GeteiltA unit.P unit.ws) := by
  have complete : ∀ f : declaration.Fn, f ∈ [()] := by
    intro f; cases f; exact List.mem_cons_self
  have subset : ∀ carrier, GeteiltA unit.P unit.ws carrier → AtomarAusgenommen carrier :=
    fun _ present => present.1
  apply logikPflichtA_of_akzeptiertX complete checker_accepted_zeuge unit.Q
    (GeteiltA unit.P unit.ws) subset
  exact ⟨(fun lock => nomatch lock), (fun item => nomatch item),
    fun _ _ impossible => by cases impossible⟩

theorem user_duty_zeuge : NutzerPflichtA unit := ⟨adapter_zeuge, start_zeuge⟩

def nonlinear : Programm declaration :=
  { program with
    invariante := fun _ =>
      .le (.mul (.glob false (access false)) (.glob false (access false))) (.lit 10) }

/-- Declaration admission is checked even with no enumerated writer. -/
theorem outside_fragment_refused_zeuge : invariantVCB nonlinear unit.S [] = false := by decide +kernel

namespace Reason

/-- A callable body with a nonempty reason type, separate from the entry
    fixture: the model correctly forbids reason-returning thread roots. -/
def declaration : Deklaration :=
  { WriterWitness.declaration with
    sigNr := fun _ => { WriterWitness.declaration.sigNr 0 with gruende := 1 }
    passt_ok := fun _ _ impossible => by cases impossible }

def access : gdarf declaration false [] := fun _ member => nomatch member

def invariant : Expr declaration [] [] .bool := .eq (.glob false access) (.lit 0)

def store (value : Nat) (bounded : value ≤ 10) :
    Stmt declaration (vertragVon declaration ()) false [] [] [] :=
  .assignGlob false (.widen (by omega) (by omega) (.lit (value : Int))) rfl access

def program (restore : Bool) : Programm declaration where
  invariante := fun _ => invariant
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ =>
    .cons (store (if restore then 0 else 1) (by cases restore <;> decide))
      (.retWhy ⟨0, Nat.zero_lt_succ 0⟩ (List.Perm.refl _))

theorem accepted_zeuge : invariantVCB (program true) (SperrInv.leer declaration) [()] = true := by
  decide +kernel

theorem refused_zeuge : invariantVCB (program false) (SperrInv.leer declaration) [()] = false := by
  decide +kernel

theorem duty_zeuge (passes : Nat) (Q : AxEns declaration) :
    InvGutGrund (program true) passes Q (SperrInv.leer declaration) () :=
  (invariantVCB_invGut (fun f => by cases f; exact List.mem_cons_self)
    accepted_zeuge passes Q ()).2

def world : World declaration where
  slots := WriterWitness.world.slots
  globs := WriterWitness.world.globs
  spur := []

def oracle : Orakel declaration where
  wirktL := fun item => nomatch item
  regLiesL := fun item => nomatch item
  regSchreib := fun item => nomatch item
  sichtbarL := fun _ _ => true

def calls (f : declaration.Fn) (entry : World declaration)
    (_ : Env declaration (declaration.params f)) : RufAusgang f := .ok entry ()

theorem returns_reason_zeuge :
    (match execEnd oracle 0 calls ((program true).rumpf ()) world .nil with
      | .why next _ => eval next invariant next .nil
      | _ => false) = true := by decide +kernel

theorem breaks_at_reason_zeuge :
    (match execEnd oracle 0 calls ((program false).rumpf ()) world .nil with
      | .why next _ => eval next invariant next .nil
      | _ => true) = false := by decide +kernel

end Reason

end Gabbro.Grammatik.Invarianten.Pruefer.WriterWitness
