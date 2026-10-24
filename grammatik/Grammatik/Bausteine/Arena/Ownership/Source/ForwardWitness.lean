import Grammatik.Bausteine.Arena.Ownership.Source.Admission
import Grammatik.Bausteine.Arena.Ownership.Source.Results
import Grammatik.Bausteine.Arena.Ownership.Witness
import Grammatik.Bausteine.Arena.Ownership.Source.ArgumentFlow

namespace Gabbro.Grammatik.ArenaOwnership.Source.ForwardWitness

open InvDynZeuge

@[reducible] def D : Deklaration :=
  { FD with
    Fn := Bool
    sig := fun _ => 0
    passt := fun _ n => decide (0 = n)
    rzusage := fun e => nomatch e
    sigNr := fun _ =>
      { params := [Ty.index 4]
        erg := some (Ty.index 4)
        gruende := 0
        haelt := []
        schreibt := fun _ => true
        gschreibt := fun _ => true
        konsumiert := []
        produziert := [] }
    passt_ok := by
      intro f n h
      have hn : 0 = n := of_decide_eq_true h
      subst n
      exact SigPasst.refl _ _
    eigner_nie_erzeugt := fun _ _ _ _ h => by cases h
    invarianten_gehalten := fun _ i => nomatch i }

def A : FreiForm D where
  tab := ()
  feld := 0
  zaehl := 0
  hz := rfl
  hpos := by decide
  komm := 1
  hk := rfl
  hzwei := by decide
  kopf := 2
  hkopf := rfl
  nxt := 1
  hnxt := rfl
  hk1 := by decide
  hk2 := by decide
  hf := by decide

def world : World D where
  slots := fun _ _ f => by
    change Wert D (if f = 0 then .int 0 255 else .int 0 4)
    split
    · exact ⟨7, by decide, by decide⟩
    · exact ⟨4, by decide, by decide⟩
  globs := fun g => if g = 0 then ⟨1, by decide, by decide⟩ else ⟨4, by decide, by decide⟩
  spur := []

theorem tab_right : darf D A.tab [] := fun _ h => by cases h
theorem glob_right (g : D.Glob) : gdarf D g [] := fun _ h => by cases h


theorem hp (f g : D.Fn) : RufPasst D (vertragVon D f) (D.signatur g) [] where
  hw := fun _ h => h
  hg := fun _ h => h
  hk := ⟨[], List.Perm.refl [], List.Sublist.refl []⟩
  hh := fun _ h => by cases h

def args : Args D [Ty.index 4] [] (D.params false) := .cons (.var .here) .nil

def P : Programm D where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun f => if f then forwardIdentity A f false args rfl rfl (hp f false) rfl (List.Perm.refl [])
    else identityBody A f .here rfl (List.Perm.refl [])

def C (f : D.Fn) : Contract D f := identityContract A f .here rfl .owned

theorem source_checked : CheckedProgram P A C := by
  intro f
  cases f with
  | false => exact CheckedBody.identity (A := A) (C := C) (f := false) .here rfl .owned (List.Perm.refl [])
  | true =>
    exact CheckedBody.forwardValue (A := A) (C := C) (f := true) false .here .here rfl rfl rfl args (by decide) rfl
      (hp true false) rfl (List.Perm.refl [])

def caller : Frame := ⟨0, 0⟩
def callee : Frame := ⟨0, 1⟩
def handle : Handle := ⟨0, 0, 0⟩
def state : State := ⟨1, fun i => if i = 0 then some ⟨0, 0, caller, []⟩ else none⟩
def rho : Env D [Ty.index 4] := .cons ⟨0, by decide, by decide⟩ .nil

theorem free_ok : A.FreiOk world :=
  ⟨[], FreiForm.Kette.nil, List.nodup_nil, fun _ h => by cases h⟩

theorem live (i : Int) : A.Lebt world i ↔ i = 0 := by
  have hno : ¬ A.AufListe world i := by
    rintro ⟨L, hL, hm⟩
    have heq := FreiForm.Kette.eindeutig hL (FreiForm.Kette.nil (A := A) (σ := world))
    subst L
    cases hm
  change (0 ≤ i ∧ i < 1 ∧ ¬ A.AufListe world i) ↔ i = 0
  constructor
  · intro h; omega
  · rintro rfl; exact ⟨by decide, by decide, hno⟩

theorem agrees : state.agrees A world := by
  refine ⟨ArenaOwnership.Witness.valid, fun i => ?_⟩
  rw [live]
  by_cases hi : i = 0
  · simp [state, hi]
  · simp [state, hi]

def context : Context := Context.parameter (.here : Var [Ty.index 4] (Ty.index 4)) .owned
def ghosts : Ghost := fun i => if i = 0 then some handle else none

theorem realizes : Realizes context ghosts A caller state world rho :=
  parameter_realizes A .here .owned caller state world rho agrees free_ok handle (by change state.owns caller handle; decide) rfl

theorem actual_run (O : Orakel D) (passes : Nat) :
    ∃ σ' v, rufAt P O passes 3 true world rho = .ok σ' v ∧ (ergWert (τ := Ty.index 4) rfl v).n = 0 := by
  exact ⟨_, _, rfl, rfl⟩

/-- One real G function forwards ownership through another, returns the
actual owning result, and its caller frees it. The saved caller name is
refused by the source check even though the runtime numeric index is equal. -/
theorem nested_return_and_release (O : Orakel D) (passes : Nat) :
    CheckedProgram P A C ∧
    ∃ (σ' σ'' : World D) (v : ErgVal D (D.erg true)) (s' s'' : State) (fresh : Handle),
      rufAt P O passes 3 true world rho = .ok σ' v ∧
      Realizes (context.kill 0).bindFresh (ghosts.set context.next fresh) A caller s' σ'
        (.cons (ergWert (τ := Ty.index 4) rfl v) rho) ∧
      (∀ frame, ¬ s'.access frame handle) ∧
      execBlock (V := vertragVon D true) (l := false) O passes (rufAt P O passes 3)
        (Block.freiVar A .here rfl tab_right rfl (glob_right _) .nil) σ'
        (.cons (ergWert (τ := Ty.index 4) rfl v) rho) = .ok σ'' (.cons (ergWert (τ := Ty.index 4) rfl v) rho) ∧
      s''.agrees A σ'' ∧ (∀ frame, ¬ s''.access frame fresh) := by
  obtain ⟨σ', v, hrun, hzero⟩ := actual_run O passes
  obtain ⟨s', old, fresh, hreal, hg, hdead⟩ := checked_owning_result A C (rufAt P O passes 3)
    (checked_calls P A C source_checked O passes 3) true .here rfl rfl args context (context.kill 0)
    ghosts caller callee state world rho 0 rfl rfl realizes (by
      change rufAt P O passes 3 true world rho = .ok σ' v
      exact hrun)
  have hold : old = handle := by simpa [ghosts] using hg.symm
  subst old
  obtain ⟨h, hh, ho⟩ := hreal.2.2.2.2.1 context.next .owned (by simp [Context.bindFresh, Context.kill])
  have hid : h = fresh := by simpa [Ghost.set] using hh.symm
  subst h
  have hx : (ergWert (τ := Ty.index 4) rfl v).n = fresh.slot := by
    obtain ⟨h, hh, hv⟩ := hreal.2.2.2.1.2 (.here : Var (Ty.index 4 :: [Ty.index 4]) _) context.next rfl
    have hid : h = fresh := by simpa [Ghost.set] using hh.symm
    subst h
    exact Option.some.inj hv
  obtain ⟨s'', σ'', _, he, ha'', _, _, hdead'⟩ := release_execution (V := vertragVon D true) O passes (rufAt P O passes 3) A s' caller fresh
    (.here : Var (Ty.index 4 :: [Ty.index 4]) _) rfl tab_right rfl (glob_right _) (l := false) .nil σ'
    (.cons (ergWert (τ := Ty.index 4) rfl v) rho) hreal.1 hreal.2.1 ho hx
  exact ⟨source_checked, σ', σ'', v, s', s'', fresh, hrun, hreal, hdead, he, ha'', hdead'⟩

#print axioms source_checked
#print axioms nested_return_and_release

def savedAlias : Expr D [Ty.index 4, Ty.index 4] [] (D.typ A.tab A.feld) :=
  .slot A.tab A.feld (.var (.there .here)) tab_right

def returnedName : Expr D [Ty.index 4, Ty.index 4] [] (D.typ A.tab A.feld) :=
  .slot A.tab A.feld (.var .here) tab_right

theorem old_alias_refused_new_result_admitted :
    checkExpression A (context.kill 0).bindFresh savedAlias = false ∧
      checkExpression A (context.kill 0).bindFresh returnedName = true := by decide

def duplicateArgs : Args D [Ty.index 4] [] [Ty.index 4, Ty.index 4] :=
  .cons (.var .here) (.cons (.var .here) .nil)

theorem duplicate_owning_arguments_refused :
    checkArgumentFlow A ⟨context, []⟩ duplicateArgs (.cons (some .owned) (.cons (some .owned) .nil)) = none := rfl

theorem loan_and_owner_same_argument_refused :
    checkArgumentFlow A ⟨context, []⟩ duplicateArgs (.cons (some .borrowed) (.cons (some .owned) .nil)) = none ∧
      checkArgumentFlow A ⟨context, []⟩ duplicateArgs (.cons (some .owned) (.cons (some .borrowed) .nil)) = none :=
  ⟨rfl, rfl⟩

#print axioms old_alias_refused_new_result_admitted
#print axioms duplicate_owning_arguments_refused
#print axioms loan_and_owner_same_argument_refused

def borrowProgram : Programm D := { P with
  rumpf := fun f => identityBody A f .here rfl (List.Perm.refl []) }

def borrowContracts (f : D.Fn) : Contract D f := identityContract A f .here rfl .borrowed

theorem borrow_source_checked : CheckedProgram borrowProgram A borrowContracts := by
  intro f
  exact CheckedBody.identity (A := A) (C := borrowContracts) (f := f) .here rfl .borrowed (List.Perm.refl [])

/-- A real source borrow call returns its value while restoring the
lender's original grant; its temporary borrower can never release it. -/
theorem borrowed_call_restores_owner (O : Orakel D) (passes : Nat) :
    CheckedProgram borrowProgram A borrowContracts ∧
    ∃ (loaned : State) (σ' : World D) (v : ErgVal D (D.erg false)),
      state.lend caller callee handle = some loaned ∧
      rufAt borrowProgram O passes 1 false world rho = .ok σ' v ∧
      state.agrees A σ' ∧ state.owns caller handle ∧
      loaned.release callee handle = none ∧ loaned.endLoan callee handle = some state := by
  have hex : ∃ σ' v, rufAt borrowProgram O passes 1 false world rho = .ok σ' v := ⟨_, _, rfl⟩
  obtain ⟨σ', v, hrun⟩ := hex
  let loaned := state.put 0 (some ⟨0, 0, caller, [callee]⟩)
  have hlend : state.lend caller callee handle = some loaned := rfl
  obtain ⟨ha', _, _, hreturn, hrelease⟩ := borrow_result A borrowContracts (rufAt borrowProgram O passes 1)
    (checked_calls borrowProgram A borrowContracts borrow_source_checked O passes 1) false .here rfl rfl
    caller callee state loaned handle world rho agrees free_ok hlend rfl hrun
  exact ⟨borrow_source_checked, loaned, σ', v, hlend, hrun, ha', by decide, hrelease, hreturn⟩

#print axioms borrowed_call_restores_owner

end Gabbro.Grammatik.ArenaOwnership.Source.ForwardWitness
