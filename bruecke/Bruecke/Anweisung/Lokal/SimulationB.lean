module
public import Bruecke.Anweisung.Lokal.Kopf
public import Bruecke.Anweisung.Lokal.Rahmen
public import Bruecke.Pruefung
@[expose] public section

/-!
# Decidable binder freshness

The checks follow the flat body and retain the protected names of non-integer entries.
Every local binder has integer kind and does not add a protected source name.
Their soundness lemmas supply `BindFrisch` for the consolidated carried chain.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

def nameFrischB (ns : List String) (x : String) : Bool :=
  decide (x ∉ ns) && decide (x ≠ "result") && decide (x ≠ "#erg") && decide (x ∉ oldNamen)

def bindFrischLB : List String → List UStmt → Bool
  | _, [] => true
  | ns, s :: ss =>
      match binderOf s with
      | some x => nameFrischB ns x && bindFrischLB ns ss
      | none => bindFrischLB ns ss

/-- **`bindFrischB`** -- freshness of every binder of the body of `fn`, decided. -/
def bindFrischB (fn : UFn) : Bool := bindFrischLB (protectedNames fn.params fn.kinds) fn.body

def bindFrischAllB (u : UProg) : Bool := u.fns.all bindFrischB

theorem nameFrischB_ok {ns : List String} {x : String} (h : nameFrischB ns x = true) :
    NameFrisch ns x := by
  simp only [nameFrischB, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1.1, h.1.1.2, h.1.2, fun i e => ?_⟩
  have hm := oldName_mem i
  rw [← e] at hm
  exact h.2 hm

theorem bindFrischLB_ok : ∀ (ns : List String) (ss : List UStmt),
    bindFrischLB ns ss = true → BindFrischL ns ss
  | _, [], _ => trivial
  | ns, s :: ss, h => by
      cases hb : binderOf s with
      | none =>
        have h' : bindFrischLB ns ss = true := by simpa only [bindFrischLB, hb] using h
        have := bindFrischLB_ok ns ss h'
        simp only [BindFrischL, hb]
        exact this
      | some x =>
        have h' : nameFrischB ns x = true ∧ bindFrischLB ns ss = true := by
          simpa only [bindFrischLB, hb, Bool.and_eq_true] using h
        simp only [BindFrischL, hb]
        exact ⟨nameFrischB_ok h'.1, bindFrischLB_ok ns ss h'.2⟩

theorem bindFrischB_ok {fn : UFn} (h : bindFrischB fn = true) : BindFrisch fn :=
  bindFrischLB_ok _ _ h

theorem bindFrischAllB_ok (h : bindFrischAllB u = true) : ∀ c : Fin u.fns.length,
    BindFrisch (fnAt u c) :=
  fun c => bindFrischB_ok (List.all_eq_true.mp h _ (List.get_mem _ _))

end Gabbro.Bruecke
