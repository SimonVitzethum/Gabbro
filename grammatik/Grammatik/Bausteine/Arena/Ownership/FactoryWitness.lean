import Grammatik.Bausteine.Arena.Ownership.Borrow
import Grammatik.Bausteine.Arena.Ownership.Witness

namespace Gabbro.Grammatik.ArenaOwnership.FactoryWitness

open InvDynZeuge

@[reducible] def D : Deklaration :=
  { FD with
    sigNr := fun _ =>
      { params := []
        erg := some (Ty.index 4)
        gruende := 1
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
  slots := (wd 0 4 4 nx0 ln0 rn0).slots
  globs := fun g => if g = 1 then zc 4 else (wd 0 4 4 nx0 ln0 rn0).globs g
  spur := []

theorem tab_right : darf D A.tab [] := fun _ h => by cases h
theorem glob_right (g : D.Glob) : gdarf D g [] := fun _ h => by cases h

def seven : Expr D [] [] (D.typ A.tab A.feld) :=
  .widen (by decide) (by decide) (.lit 7)

def readiness (available : Bool) : Expr D [] [] .bool := if available then .tru else .fls

def oom (f : D.Fn) : Fin (D.gruende f) := ⟨0, by change 0 < 1; decide⟩

def P (available : Bool) : Programm D where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun f => factoryBody A f rfl (oom f) (readiness available) seven rfl tab_right
    rfl (glob_right _) rfl (glob_right _) (glob_right _) (List.Perm.refl [])

def C (f : D.Fn) : Contract D f := factoryContract A f rfl

theorem free_ok : A.FreiOk world :=
  ⟨[], FreiForm.Kette.nil, List.nodup_nil, fun _ h => by cases h⟩

theorem agrees : State.empty.agrees A world := by
  refine ⟨State.empty_valid, fun i => ?_⟩
  change A.Lebt world i ↔ ∃ c, none = some c
  constructor
  · intro h
    have h0 := h.1
    have hlt := h.2.1
    change i < 0 at hlt
    omega
  · rintro ⟨c, h⟩; cases h

theorem source_checked (available : Bool) : Source.CheckedProgram (P available) A C := by
  intro f
  apply Source.CheckedBody.factory (A := A) (C := C) (f := f) rfl (oom f) (readiness available) seven
    (hwT := rfl) (hLT := tab_right) (hwU := rfl) (hLU := glob_right _)
    (hwF := rfl) (hLF := glob_right _) (hLC := glob_right _) (hend := List.Perm.refl [])
  · cases available <;> rfl
  · rfl

theorem bodies (available : Bool) (O : Orakel D) (passes : Nat) : Bodies (P available) A C O passes :=
  Source.checked_bodies (P available) A C (source_checked available) O passes

theorem actual_success (O : Orakel D) (passes : Nat) :
    ∃ (σ' : World D) (v : ErgVal D (D.erg ())),
      rufAt (P true) O passes 1 () world .nil = .ok σ' v ∧
      (ergWert (τ := Ty.index 4) rfl v).n = 0 ∧ A.stand σ' = 1 := by
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem actual_oom (O : Orakel D) (passes : Nat) :
    rufAt (P false) O passes 1 () world .nil = .why world (oom ()) := rfl

/-- Actual allocation in a G callee, owning result handoff, and actual
release in the caller. No user ownership-preservation assumption is used. -/
theorem factory_then_caller_free (O : Orakel D) (passes : Nat) :
    ∃ (σ1 σ2 : World D) (v : ErgVal D (D.erg ())) (s1 s2 : State) (h : Handle),
      rufAt (P true) O passes 1 () world .nil = .ok σ1 v ∧
      s1.owns Witness.caller h ∧ h.slot = (ergWert (τ := Ty.index 4) rfl v).n ∧
      execBlock (V := vertragVon D ()) (l := false) O passes (rufAt (P true) O passes 1)
        (Block.freiVar A (.here : Var [Ty.index 4] _) rfl tab_right rfl (glob_right _) .nil)
        σ1 (.cons (ergWert (τ := Ty.index 4) rfl v) .nil) = .ok σ2 (.cons (ergWert (τ := Ty.index 4) rfl v) .nil) ∧
      s2.agrees A σ2 ∧ (∀ frame, ¬ s2.access frame h) := by
  obtain ⟨σ1, v, hrun, _, _⟩ := actual_success O passes
  obtain ⟨s1, h, ha1, hf1, hown, hslot, _⟩ := factory_result A C (rufAt (P true) O passes 1)
    (rufAt_ownership (P true) A C O passes (bodies true O passes) 1) () rfl rfl
    Witness.caller Witness.callee rfl State.empty world .nil agrees free_ok hrun
  obtain ⟨s2, σ2, _, hfree, ha2, _, _, hdead⟩ := release_execution (V := vertragVon D ()) O passes (rufAt (P true) O passes 1)
    A s1 Witness.caller h (.here : Var [Ty.index 4] _) rfl tab_right rfl (glob_right _) (l := false)
    .nil σ1 (.cons (ergWert (τ := Ty.index 4) rfl v) .nil) ha1 hf1 hown hslot.symm
  exact ⟨σ1, σ2, v, s1, s2, h, hrun, hown, hslot, hfree, ha2, hdead⟩

theorem oom_keeps_empty_ledger (O : Orakel D) (passes : Nat) :
    (C ()).post A Witness.callee State.empty .nil (rufAt (P false) O passes 1 () world .nil) := by
  exact (rufAt_ownership (P false) A C O passes (bodies false O passes) 1 () Witness.callee
    State.empty world .nil agrees free_ok trivial).2 world (oom ()) (actual_oom O passes)

#print axioms factory_then_caller_free
#print axioms oom_keeps_empty_ledger

end Gabbro.Grammatik.ArenaOwnership.FactoryWitness
