module

public import Grammatik.Logik.Invarianten.Pruefer.Witness

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer.LockWitness

open Frag Zielsatz

/-- One protected scalar, a real lock, and no ordinary owed invariant.
    Release must therefore be checked even when D.invs is empty. -/
def declaration : Deklaration :=
  { Witness.declaration with
    Lock := Unit, decLock := inferInstance
    rang := fun _ => 0
    maskiert := fun _ => false
    braucht := fun _ => []
    gbraucht := fun name => if name then [] else [.inl ()]
    sigNr := fun _ =>
      { params := [], erg := none, gruende := 0, haelt := []
        schreibt := fun _ => false, gschreibt := fun name => !name
        konsumiert := [], produziert := [] }
    passt_ok := fun _ _ impossible => by cases impossible
    eigner_nie_erzeugt := fun _ _ _ _ impossible => by cases impossible
    geteilt_bewacht := fun _ impossible => nomatch impossible
    ggeteilt_bewacht := fun _ impossible => nomatch impossible
    Inv := Empty
    traeger := fun item => nomatch item
    invs := []
    invarianten_gehalten := fun _ item => nomatch item }

instance : DecidableEq declaration.Fn := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq declaration.Ax := inferInstanceAs (DecidableEq Empty)

abbrev contract := vertragVon declaration ()

def access : gdarf declaration false [.held ()] := by
  intro guard member
  have same : guard = .inl () := List.mem_singleton.mp member
  subst guard
  exact List.mem_cons_self

def invariant : Expr declaration [] [.held ()] .bool := .eq (.glob false access) (.lit 0)

def family : SperrInv declaration where
  orte := fun _ => [.inr false]
  inv := fun _ memory => eval (memory.welt []) invariant (memory.welt []) .nil

def sources : LockSources family := fun _ => some
  { resources := [.held ()], expression := invariant
    correct := fun _ => rfl }

def store (value : Nat) (bounded : value ≤ 10) :
    Stmt declaration contract false [] [.held ()] [.held ()] :=
  .assignGlob false (.widen (by omega) (by omega) (.lit (value : Int))) rfl access

def body (restore : Bool) : Endblock declaration contract false [] [] :=
  .cons (.locks () (fun _ member => nomatch member)
    (.cons (store 1 (by decide))
      (if restore then .cons (store 0 (by decide)) .nil else .nil)))
    (.ret .empty (List.Perm.refl _))

def program (restore : Bool) : Programm declaration where
  invariante := fun item => nomatch item
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun _ => body restore

def world : World declaration where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun _ => ⟨0, by decide, by decide⟩
  spur := []

def unit (restore : Bool) : Einheit declaration where
  P := program restore
  S := family
  Q := fun item => nomatch item
  starts := [⟨(), .nil⟩]
  sp0 := world.speicher

theorem start_zeuge : StartPflicht (unit true) := by
  refine ⟨?_, fun _ _ => rfl⟩
  intro lock
  cases lock
  decide +kernel

theorem lock_accepted_zeuge : invariantVCB (program true) family [()] sources = true := by decide +kernel

theorem lock_refused_zeuge : invariantVCB (program false) family [()] sources = false := by decide +kernel

theorem missing_syntax_refused_zeuge : invariantVCB (program true) family [()] = false := by decide +kernel

theorem checker_accepted_zeuge :
    AkzeptiertX (program true) family [()] [()] [.inl (), .inr false, .inr true]
      (unit true).ws (sources := sources) = true := by
  unfold AkzeptiertX
  rw [lock_accepted_zeuge]
  simp only [Bool.and_true, Bool.and_eq_true]
  decide +kernel

theorem checker_refused_zeuge :
    AkzeptiertX (program false) family [()] [()] [.inl (), .inr false, .inr true]
      (unit false).ws (sources := sources) = false := by
  unfold AkzeptiertX
  rw [lock_refused_zeuge, Bool.and_false]

end Gabbro.Grammatik.Invarianten.Pruefer.LockWitness
