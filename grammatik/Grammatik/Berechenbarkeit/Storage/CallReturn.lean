/-
  File:      Grammatik/Berechenbarkeit/Storage/CallReturn.lean
  Subject:   Actual G call/pop fidelity with a retained data bit.

  The caller retains b while its callee receives !b. A real call followed by a real
  return restores the caller's original local environment and continuation. Both
  functions are in the existing terminating class. This is a storage primitive,
  not yet an unbounded command-serving stack worker or a universality theorem.
-/
import Grammatik.Logik.Terminierung.KlasseZeuge

namespace Gabbro.Grammatik.Berechenbarkeit.Storage.CallReturn

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz.BudgetZeuge

/-- Two finite function names, one Boolean parameter, no data carriers or devices. -/
@[reducible] def declaration : Deklaration :=
  { bD with
    Fn := Bool
    sig := fun _ => 0
    sigNr := fun _ => ⟨[.bool], none, 0, [], fun t => t.elim, fun g => g.elim, [], [], none⟩
    passt := fun _ n => decide (0 = n)
    passt_ok := by
      intro f n h
      have hn : 0 = n := of_decide_eq_true h
      subst n
      exact SigPasst.refl _ _
    rzusage := fun r => r.elim }

def environment (b : Bool) : Env declaration [.bool] := .cons b .nil

theorem callFits : RufPasst declaration (vertragVon declaration false) (declaration.signatur true) [] where
  hw := fun t => t.elim
  hg := fun g => g.elim
  hk := ⟨[], List.Perm.refl [], by simp⟩
  hh := fun L => L.elim

def returnedBody (f : Bool) :
    Endblock declaration (vertragVon declaration f) false [.bool] [] :=
  .ret .empty (List.Perm.refl [])

def callerBody : Endblock declaration (vertragVon declaration false) false [.bool] [] :=
  .cons (.call true (.cons (.not (.var .here)) .nil) callFits rfl) (returnedBody false)

def program : Programm declaration where
  invariante := fun i => i.elim
  requires := fun _ => Expr.tru
  ensures := fun _ => Expr.tru
  rumpf := fun f => if f then returnedBody true else callerBody

def memory : Speicher declaration := ⟨fun t => t.elim, fun g => g.elim⟩
def oracle : Orakel declaration :=
  ⟨fun a => a.elim, fun r => r.elim, fun r => r.elim, fun g => g.elim, fun _ => none⟩

def initial (b : Bool) : RufMaschineG declaration :=
  RufStartG program memory (fun _ => ⟨false, environment b⟩)

def saved (b : Bool) : RufRahmenG declaration :=
  ⟨false, environment b, memory.welt [], ⟨false, [.bool], [], environment b, .ende (returnedBody false)⟩⟩

def called (b : Bool) : RufMaschineG declaration :=
  let M := initial b
  ⟨memory, rufUpdateG M.faeden 0
    ⟨[saved b],
     ⟨true, environment (!b), memory.welt [],
       ⟨false, [.bool], [], environment (!b), .ende (returnedBody true)⟩⟩,
     [], .eintritt true (environment (!b)) (memory.welt []) :: (M.faeden 0).log⟩,
   [], M.start⟩

def resumed (b : Bool) : RufMaschineG declaration :=
  let M := called b
  ⟨memory, rufUpdateG M.faeden 0
    ⟨[], saved b, [],
     .rueck true (environment (!b)) () (memory.welt []) (memory.welt []) :: (M.faeden 0).log⟩,
   [], M.start⟩

/-- Genuine call from the standard empty-stack entry, at every loop budget. -/
theorem call_step (budget : Nat) (b : Bool) :
    RufSchrittG program oracle budget (initial b) 0 (called b) := by
  have h := RufSchrittG.ruf (P := program) (O := oracle) (passes := budget)
    (initial b) 0 false [.bool] [] true (.cons (.not (.var .here)) .nil) callFits rfl
    (returnedBody false) (environment b) rfl (by simp [HeldIn]) (memory.welt []) rfl
    (environment (!b)) rfl [] rfl
  simp only [rufEigenG, List.reverse_nil, List.map_nil, List.append_nil] at h
  exact h

/-- Genuine pop restores the retained bit rather than the callee's different bit. -/
theorem return_step (budget : Nat) (b : Bool) :
    RufSchrittG program oracle budget (called b) 0 (resumed b) := by
  have h := RufSchrittG.rueck (P := program) (O := oracle) (passes := budget)
    (called b) 0 (saved b) [] rfl [.bool] [] .empty (List.Perm.refl [])
    (environment (!b)) rfl true rfl (environment (!b)) rfl (memory.welt []) rfl
    (by simp [HeldIn]) (memory.welt []) rfl () rfl [] rfl rfl
  simp only [rufEigenG, List.reverse_nil, List.map_nil, List.append_nil] at h
  exact h

theorem reached_zeuge (budget : Nat) (b : Bool) :
    RufErreichbarG program oracle budget (initial b) (resumed b) :=
  .schritt _ _ 0 (.schritt _ _ 0 .start (call_step budget b)) (return_step budget b)

theorem retained_bit_zeuge (b : Bool) :
    (called b).faeden 0 |>.kopf.rest.2.2.2.1 = environment (!b) ∧
    ((resumed b).faeden 0).kopf.rest.2.2.2.1 = environment b ∧
    ((resumed b).faeden 0).stapel = [] := by
  simp [called, resumed, saved, rufUpdateG]

theorem terminating_classes_zeuge :
    klasse program [false, true] (fun _ => false) false = .endet ∧
    klasse program [false, true] (fun _ => false) true = .endet := by decide

theorem accepted_zeuge :
    Akzeptiert program ⟨fun L => L.elim, fun L => L.elim⟩ [false, true] [] [] [false] = true := by
  decide

end Gabbro.Grammatik.Berechenbarkeit.Storage.CallReturn
