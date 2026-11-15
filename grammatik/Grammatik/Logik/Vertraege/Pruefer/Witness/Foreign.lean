module

public import Grammatik.Logik.Vertraege.Pruefer.Goal
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

#print axioms noLogic_zeuge
#print axioms contractDuties_of_basic_zeuge

end Gabbro.Grammatik.Vertraege.Pruefer.ForeignWitness
