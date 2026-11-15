module

public import Grammatik.Logik.Invarianten.Pruefer.Witness

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Pruefer.PointerWitness

open Frag Zielsatz

/-- A static table capability is a real typed parameter, not a numeric address. -/
abbrev capability : Ty := .ptr (.table 0 (true, true))

def declaration : Deklaration :=
  { Witness.declaration with
    tabNr := fun n => if n = 0 then some () else none
    anbieter_passt := fun _ item => nomatch item
    sigNr := fun _ =>
      { params := [capability], erg := none, gruende := 0, haelt := []
        schreibt := fun _ => true, gschreibt := fun _ => false
        konsumiert := [], produziert := [] }
    passt_ok := fun _ _ impossible => by cases impossible
    traeger := fun _ => [.inl ()]
    invarianten_gehalten := fun _ _ _ _ _ lock => nomatch lock }

instance : DecidableEq declaration.Fn := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq declaration.Ax := inferInstanceAs (DecidableEq Empty)

def access : darf declaration () [] := fun _ member => nomatch member

def position {Γ : Ctx} : Expr declaration Γ [] (.index (declaration.count ())) :=
  .widen (by decide) (by decide) (.lit 0)

def invariant : Expr declaration [] [] .bool :=
  .eq (.thru (.ptrOf () 0 rfl (true, true)) () rfl () position access) (.lit 0)

abbrev contract := vertragVon declaration ()

def store (value : Nat) (bounded : value ≤ 10) :
    Stmt declaration contract false [capability] [] [] :=
  .assignThru (.var .here) () rfl () position
    (.widen (by omega) (by omega) (.lit (value : Int))) rfl access

def program (restore : Bool) : Programm declaration where
  invariante := fun _ => invariant
  requires := fun _ => .tru
  ensures := fun _ => .eq (.thru (.var .here) () rfl () position access) (.lit 0)
  rumpf := fun _ => .cons (store 1 (by decide))
    (.cons (store (if restore then 0 else 1) (by cases restore <;> decide))
      (.ret .empty (List.Perm.refl _)))

def world : World declaration where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun _ => ⟨0, by decide, by decide⟩
  spur := []

def oracle : Orakel declaration where
  wirktL := fun item => nomatch item
  regLiesL := fun item => nomatch item
  regSchreib := fun item => nomatch item
  sichtbarL := fun _ _ => true

def calls (f : declaration.Fn) (entry : World declaration)
    (_ : Env declaration (declaration.params f)) : RufAusgang f := .ok entry ()

def arguments : Env declaration [capability] := .cons () .nil

theorem accepted_zeuge : invariantVCB (program true) (SperrInv.leer declaration) [()] = true := by
  decide +kernel

theorem refused_zeuge : invariantVCB (program false) (SperrInv.leer declaration) [()] = false := by
  decide +kernel

/-- The accepted function executes both pointer writes before restoring its
    declared invariant and current-state ensures. -/
theorem restoring_execution_zeuge :
    (match execEnd oracle 0 calls ((program true).rumpf ()) world arguments with
      | .zurueck next _ => eval next invariant next .nil
      | _ => false) = true := by decide +kernel

theorem breaking_execution_zeuge :
    (match execEnd oracle 0 calls ((program false).rumpf ()) world arguments with
      | .zurueck next _ => eval next invariant next .nil
      | _ => true) = false := by decide +kernel

end Gabbro.Grammatik.Invarianten.Pruefer.PointerWitness
