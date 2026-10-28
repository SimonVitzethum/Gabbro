import Grammatik.Bausteine.Arena.Ownership.Source.Admission
import Grammatik.Bausteine.Arena.Struktur.ArenaDynZeuge

/-! Joint witnesses over the existing four-slot arena fixture. The source
destructor takes an actual index parameter and is executed by `rufAt` through
an actual G call statement. Ownership is transferred from a different frame.
-/

namespace Gabbro.Grammatik.ArenaOwnership.Witness

open InvDynZeuge

@[reducible] def D : Deklaration :=
  { FD with
    sigNr := fun _ =>
      { params := [Ty.index 4]
        erg := none
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
  slots := (wd 1 4 4 nx0 ln0 rn0).slots
  globs := (wd 1 4 4 nx0 ln0 rn0).globs
  spur := []

theorem tab_right : darf D A.tab [] := fun _ h => by cases h
theorem glob_right (g : D.Glob) : gdarf D g [] := fun _ h => by cases h

def P : Programm D where
  invariante := fun i => nomatch i
  requires := fun _ => .tru
  ensures := fun _ => .tru
  rumpf := fun f => destructorBody A f .here rfl rfl tab_right rfl (glob_right _) (List.Perm.refl [])

def C (f : D.Fn) : Contract D f := destructorContract A f .here

theorem source_checked : Source.CheckedProgram P A C := by
  intro f
  exact Source.CheckedBody.destroy (A := A) (C := C) (f := f) .here rfl rfl tab_right rfl (glob_right _)
    (List.Perm.refl [])

theorem bodies (O : Orakel D) (passes : Nat) : Bodies P A C O passes :=
  Source.checked_bodies P A C source_checked O passes

def caller : Frame := ⟨0, 0⟩
def callee : Frame := ⟨0, 1⟩
def handle : Handle := ⟨0, 0, 0⟩
def state : State := ⟨1, fun i => if i = 0 then some ⟨0, 0, caller, []⟩ else none⟩

theorem valid : state.valid := by
  intro i c hc
  change (if i = 0 then some ⟨0, 0, caller, []⟩ else none) = some c at hc
  split at hc
  · cases hc; exact ⟨by decide, by decide, by decide, by decide⟩
  · cases hc

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
  refine ⟨valid, fun i => ?_⟩
  rw [live]
  by_cases hi : i = 0
  · simp only [hi, state, ↓reduceIte, Option.some.injEq, exists_eq']
  · simp only [hi, state, ↓reduceIte, reduceCtorEq, exists_false]

theorem owns : state.owns caller handle := by decide

def rho : Env D [Ty.index 4] := .cons ⟨0, by decide, by decide⟩ .nil
def args : Args D [Ty.index 4] [] (D.params ()) := .cons (.var .here) .nil

theorem call_rights : RufPasst D (vertragVon D ()) (D.signatur ()) [] where
  hw := fun _ h => h
  hg := fun _ h => h
  hk := ⟨[], List.Perm.refl [], List.Sublist.refl []⟩
  hh := fun _ h => by cases h

def call : Stmt D (vertragVon D ()) false [Ty.index 4] [] [] :=
  .call () args call_rights rfl

theorem actual_run (O : Orakel D) (passes : Nat) :
    ∃ σ' : World D, execStmt O passes (rufAt P O passes 1) call world rho = .ok σ' rho ∧
      A.kopfSt σ' = 0 := by
  exact ⟨_, rfl, rfl⟩

/-- Non-vacuous joint witness of the generic body theorem, recursive call
theorem and consuming-call rule: the call runs, its head word changes from
4 to 0, and the saved caller alias has no access afterwards. -/
theorem consume_call_witness (O : Orakel D) (passes : Nat) :
    Bodies P A C O passes ∧ state.agrees A world ∧ state.owns caller handle ∧
      ∃ (σ' : World D) (s' : State),
        execStmt O passes (rufAt P O passes 1) call world rho = .ok σ' rho ∧
        A.kopfSt world = 4 ∧ A.kopfSt σ' = 0 ∧ s'.agrees A σ' ∧
        (∀ frame, ¬ s'.access frame handle) := by
  obtain ⟨σ', hrun, hhead⟩ := actual_run O passes
  obtain ⟨s', ha, _, _, hdead⟩ := consume_call A C O passes (rufAt P O passes 1)
    (rufAt_ownership P A C O passes (bodies O passes) 1) () .here rfl args call_rights rfl caller callee
    state handle world rho agrees free_ok owns rfl rfl hrun
  exact ⟨bodies O passes, agrees, owns, σ', s', hrun, rfl, hhead, ha, hdead⟩

theorem loan_cannot_release :
    ∃ loaned, state.lend caller callee handle = some loaned ∧ loaned.access callee handle ∧
      loaned.release callee handle = none ∧ loaned.endLoan callee handle = some state := by
  refine ⟨_, rfl, ?_, rfl, ?_⟩
  · decide
  · exact State.lend_endLoan caller callee handle rfl

theorem returned_owner_does_not_revive_alias :
    ∃ middle fresh returned newest,
      state.move caller callee handle = some (middle, fresh) ∧
      middle.move callee caller fresh = some (returned, newest) ∧
      returned.owns caller newest ∧ ¬ returned.access caller handle ∧ newest.allocation = handle.allocation := by
  refine ⟨_, _, _, _, rfl, rfl, ?_, ?_, rfl⟩ <;> decide

#print axioms consume_call_witness
#print axioms loan_cannot_release
#print axioms returned_owner_does_not_revive_alias

end Gabbro.Grammatik.ArenaOwnership.Witness
