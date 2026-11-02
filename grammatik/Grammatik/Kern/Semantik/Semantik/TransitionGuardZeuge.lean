module

public import Grammatik.Kern.Semantik.Semantik.TransitionZeuge

public section

namespace Gabbro.Grammatik.TransitionProben

/-- A real held guard is present throughout the generated ordinary call. -/
@[expose] def guardedD : Deklaration :=
  { D with
    Lock := Unit
    decLock := inferInstance
    rang := fun _ => 0
    maskiert := fun _ => false
    braucht := fun _ => [Sum.inl ()]
    gbraucht := fun g => nomatch g
    sigNr := fun _ =>
      { params := [.index 8, .int 0 8192, .int 0 8192]
        erg := none, gruende := 0, haelt := [()]
        schreibt := fun _ => true, gschreibt := fun g => nomatch g
        konsumiert := [], produziert := [] }
    passt_ok := fun _ _ _ => SigPasst.refl _ _
    eigner_nie_erzeugt := fun _ _ _ _ member => by cases member
    geteilt_bewacht := fun _ h => by cases h
    invarianten_gehalten := fun _ i => nomatch i
    ggeteilt_bewacht := fun g => nomatch g }

@[expose] abbrev guardContext : Ctx := [.index 8, .int 0 8192, .int 0 8192]
@[expose] abbrev guardResources : List (Res guardedD) := [.held ()]

@[expose] def guardedWrite : TransitionWrite guardedD guardContext guardResources :=
  .slot () () rfl (.var .here) (.var (.there .here)) (.var (.there (.there .here))) (by
    intro w member
    have same : w = Sum.inl () := List.mem_singleton.mp member
    subst w
    exact List.mem_cons_self)

@[expose] def guardedWrites : List (TransitionWrite guardedD guardContext guardResources) := [guardedWrite]

theorem guardedRights : ∀ w ∈ guardedWrites, w.Permitted (vertragVon guardedD ()) := by
  intro w member
  have same := List.mem_singleton.mp member
  subst w
  rfl

@[expose] def guardFinish : Endblock guardedD (vertragVon guardedD ()) false guardContext guardResources :=
  .ret .empty (List.Perm.refl _)

@[expose] def guardedP (clause : Expr guardedD guardContext guardResources .bool) : Programm guardedD where
  invariante i := nomatch i
  requires _ := transitionRequires guardedWrites clause
  ensures _ := transitionEnsures guardedWrites
  rumpf _ := transitionEnd (vertragVon guardedD ()) guardedWrites guardedRights guardFinish

@[expose] def guardedExpansion (clause : Expr guardedD guardContext guardResources .bool) :
    TransitionExpansion (guardedP clause) () where
  writes := guardedWrites
  clause := clause
  frozen := by
    intro w member
    have same := List.mem_singleton.mp member
    subst w
    exact .slot _ _ rfl .here (.there .here) (.there (.there .here)) _
  rights := guardedRights
  result_none := rfl
  resources := rfl
  requires_exact := rfl
  ensures_exact := HEq.rfl
  body_exact := rfl

@[expose] def guardedEntry : World guardedD :=
  ({ slots := fun _ _ _ => ⟨0, by decide, by decide⟩,
     globs := fun g => nomatch g, spur := [] } : World guardedD).nimmt ()

@[expose] def guardedEnv : Env guardedD guardContext :=
  .cons ⟨0, by decide, by decide⟩
    (.cons ⟨0, by decide, by decide⟩ (.cons ⟨7, by decide, by decide⟩ .nil))

theorem guarded_false_requires_zeuge (O : Orakel guardedD) (passes : Nat) :
    rufAt (guardedP .fls) O passes 1 () guardedEntry guardedEnv = .logik (.vorbedingung ()) := rfl

@[expose] def guardedReturned : World guardedD :=
  let checked := guardedEntry.lese guardResources ((guardedP .tru).requires ()).orte
  (transitionWorld guardedWrites checked guardedEnv checked).lese guardResources
    ((guardedP .tru).ensures ()).orte

theorem guarded_true_requires_zeuge (O : Orakel guardedD) (passes : Nat) :
    rufAt (guardedP .tru) O passes 1 () guardedEntry guardedEnv = .ok guardedReturned () ∧
    (guardedReturned.slots () 0 ()).n = 7 ∧ guardedReturned.haelt = [()] := ⟨rfl, rfl, rfl⟩

/-- Incorrect current state fails the generated requires gate, not the
    primitive shift diagnostic. The store cannot run first. -/
theorem wrong_current_state_refused_zeuge (O : Orakel guardedD) (passes : Nat) :
    rufAt (guardedP .tru) O passes 1 () guardedEntry
      (.cons ⟨0, by decide, by decide⟩
        (.cons ⟨1, by decide, by decide⟩ (.cons ⟨7, by decide, by decide⟩ .nil))) =
      .logik (.vorbedingung ()) := rfl

end Gabbro.Grammatik.TransitionProben
