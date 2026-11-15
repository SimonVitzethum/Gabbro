module

public import Grammatik.Logik.Vertraege.Pruefer.Witness.Contracts
public import Grammatik.Zielsatz.Eigenschaften.BudgetZeuge

@[expose] public section

namespace Gabbro.Grammatik.Vertraege.Pruefer.ForeignWitness

open Zielsatz Invarianten.Pruefer

/-- One real lock and one fallible Boolean foreign item; no program calls. -/
abbrev declaration : Deklaration :=
  { BudgetZeuge.bD with
    Lock := Unit
    decLock := inferInstance
    rang := fun _ => 1
    maskiert := fun _ => false
    braucht := fun item => nomatch item
    gbraucht := fun item => nomatch item
    sigNr := fun _ =>
      { params := [], erg := none, gruende := 0, haelt := []
        schreibt := fun item => nomatch item
        gschreibt := fun item => nomatch item
        konsumiert := [], produziert := [], boden := some 0 }
    passt := fun _ _ => false
    passt_ok := fun _ _ impossible => by cases impossible
    rzusage := fun item => nomatch item
    eigner_nie_erzeugt := fun _ item => nomatch item
    invarianten_gehalten := fun _ item => nomatch item
    Ax := Unit
    aparams := fun _ => []
    aerg := fun _ => some .bool
    agruende := fun _ => 1
    aschreibt := fun _ item => nomatch item
    agschreibt := fun _ item => nomatch item
    axHerkunft := fun _ => some .software
    axBeleg := fun _ => none
    anbieter := fun item => nomatch item
    anbieter_passt := fun item => nomatch item
    geteilt_bewacht := fun item => nomatch item
    ggeteilt_bewacht := fun item => nomatch item }

abbrev contract := vertragVon declaration ()

def family : SperrInv declaration := SperrInv.leer declaration

def sources : LockSources family := fun _ => some
  { resources := [], expression := .tru, correct := fun _ => rfl }

def returned {Γ : Ctx} : Endblock declaration contract false Γ [] :=
  .ret .empty (List.Perm.refl _)

def fallibleBlock : Block declaration contract false [] [] [] :=
  .bindAxiomElse () .nil rfl (by decide)
    (fun item => nomatch item) (fun item => nomatch item)
    (fun item => nomatch item) (fun item => nomatch item)
    returned .nil

def fallibleEnd : Endblock declaration contract false [] [] :=
  .bindAxiomElse () .nil rfl (by decide)
    (fun item => nomatch item) (fun item => nomatch item)
    (fun item => nomatch item) (fun item => nomatch item)
    returned returned

def optionalBlock : Block declaration contract false [] [] [] :=
  .bindAxiomOptElse (some .bool) () .nil rfl
    (by decide) (fun item => nomatch item) (fun item => nomatch item) (by decide)
    returned .nil

def optionalEnd : Endblock declaration contract false [] [] :=
  .bindAxiomOptElse (some .bool) () .nil rfl
    (by decide) (fun item => nomatch item) (fun item => nomatch item) (by decide)
    returned returned

/-- Both option-indexed value binders have joint generic certificate premises. -/
theorem optional_some_zeuge :
    (Basic.block family sources 32 optionalBlock).isSome = true ∧
    (Basic.ending family sources 32 optionalEnd).isSome = true := by
  constructor <;> decide +kernel

/-- Both binder forms and an actual acquire/release occur in the same body. -/
def body : Endblock declaration contract false [] [] :=
  .cons (.locks () (fun _ impossible => by cases impossible) .nil)
    (.cons (.ite .tru fallibleBlock .nil) fallibleEnd)

def program : Programm declaration where
  invariante := fun item => nomatch item
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => body

def falseProgram : Programm declaration :=
  { program with ensures := fun _ => .fls }

theorem trivialLock_zeuge : (Basic.trivialLock sources ()).isSome = true := by decide +kernel

def certificate : PLift (Basic.EndSafe family body) :=
  (Basic.ending family sources 32 body).get (by decide +kernel)

/-- The generic certificate has joint premises on a nonempty typed body. -/
theorem noLogic_zeuge (O : Orakel declaration) (U : Umwelt declaration)
    (A : AUmwelt declaration) (passes : Nat)
    (R : ∀ f : declaration.Fn, World declaration → Env declaration (declaration.params f) → RufAusgang f)
    (world : World declaration) (error : Logik declaration) :
    execEndHA family O U A passes R body world .nil ≠ .logik error :=
  Basic.noLogic certificate.down O U A passes R world .nil error

theorem contracts_checked_zeuge :
    KontrakteGeprueftB program family [()] sources = true := by decide +kernel

theorem invariant_gate_checked_zeuge :
    programInvariantsB program family [()] sources {} [()] = true := by decide +kernel

theorem contractDuties_of_basic_zeuge : ContractDuties program family () :=
  contractDuties_of_basic () rfl (by decide) certificate.down

theorem massPflicht_of_basic_zeuge (measure : Mass declaration)
    (cycle : declaration.Fn → declaration.Fn → Bool) (passes : Nat)
    (Q : AxEns declaration) (shared : declaration.Tab ⊕ declaration.Glob → Prop) :
    MassPflicht program passes Q family shared measure cycle () :=
  massPflicht_of_basic () certificate.down measure cycle passes Q shared

/-- The same syntax under a false post remains on the strict path and refuses. -/
theorem false_contract_refused_zeuge :
    KontrakteGeprueftB falseProgram family [()] sources = false := by decide +kernel

theorem same_body_zeuge : falseProgram.rumpf = program.rumpf := rfl

def falseFamily : SperrInv declaration where
  orte := fun _ => []
  inv := fun _ _ => false

def falseSources : LockSources falseFamily := fun _ => some
  { resources := [], expression := .fls, correct := fun _ => rfl }

theorem false_lock_refused_zeuge :
    invariantVCB program falseFamily [()] falseSources {} (fun _ => none) [()] = false := by
  decide +kernel

def world : World declaration where
  slots := fun item => nomatch item
  globs := fun item => nomatch item
  spur := []

/-- Raw zero is a Boolean answer; raw one is the declared reason zero. -/
def oracle (raw : Int) : Orakel declaration where
  wirktL := fun _ state _ => ({ state with spur := [] }, raw)
  regLiesL := fun item => nomatch item
  regSchreib := fun item => nomatch item
  sichtbarL := fun item => nomatch item

def calls (f : declaration.Fn) (_ : World declaration)
    (_ : Env declaration (declaration.params f)) : RufAusgang f := .logik .schleife

theorem optional_answers_return_zeuge :
    (match execEndHA family (oracle 0) (fun _ state => state) idA 0 calls optionalEnd world .nil with
      | .zurueck _ _ => true | _ => false) = true ∧
    (match execEndHA family (oracle 1) (fun _ state => state) idA 0 calls optionalEnd world .nil with
      | .zurueck _ _ => true | _ => false) = true := by
  constructor <;> decide +kernel

/-- Both actual answer classes return, rather than proving a false post vacuously. -/
theorem both_answers_return_zeuge :
    (match execEndHA family (oracle 0) (fun _ state => state) idA 0 calls body world .nil with
      | .zurueck _ _ => true | _ => false) = true ∧
    (match execEndHA family (oracle 1) (fun _ state => state) idA 0 calls body world .nil with
      | .zurueck _ _ => true | _ => false) = true := by decide +kernel

theorem false_contract_counterexample_zeuge :
    ReqAmEintritt falseProgram () world .nil ∧
      ¬ EnsAmRueck falseProgram () world world .nil () := by
  exact ⟨rfl, Bool.false_ne_true⟩

/-- A real conforming target with nonempty argument and result ranges. -/
def trivialPointerProgram : Programm Witness.pointerDeclaration :=
  { Witness.pointerProgram with
    requires := fun _ => .tru
    ensures := fun _ => .tru
    ptrVertrag := fun _ => { pre := .tru, post := .tru } }

theorem trivial_pointer_checked_zeuge :
    (checkPointerTarget trivialPointerProgram {} () 0).toOption.isSome = true := by
  decide +kernel

def pointerCertificate : PLift (∀ target : Witness.pointerDeclaration.passt () 0 = true,
    PtrZielVerfeinert trivialPointerProgram () 0 target) :=
  (checkPointerTarget trivialPointerProgram {} () 0).toOption.get (by decide +kernel)

theorem trivial_pointer_refinement_zeuge :
    PtrZielVerfeinert trivialPointerProgram () 0 (by decide) :=
  pointerCertificate.down (by decide)

def traversalProgram (holds : Bool) : Programm Witness.pointerDeclaration :=
  { trivialPointerProgram with
    rumpf := fun f =>
      .cons (.traverse () (if holds then .tru else .fls) .nil)
        (Witness.pointerProgram.rumpf f) }

theorem traverse_safe_zeuge :
    KontrakteGeprueftB (traversalProgram true) (SperrInv.leer Witness.pointerDeclaration) [()] = true := by
  decide +kernel

theorem false_traversal_refused_zeuge :
    KontrakteGeprueftB (traversalProgram false) (SperrInv.leer Witness.pointerDeclaration) [()] = false := by
  decide +kernel

#print axioms noLogic_zeuge
#print axioms contractDuties_of_basic_zeuge
#print axioms massPflicht_of_basic_zeuge

end Gabbro.Grammatik.Vertraege.Pruefer.ForeignWitness
