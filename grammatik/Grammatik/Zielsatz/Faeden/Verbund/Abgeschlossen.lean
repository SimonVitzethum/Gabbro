/-
  The closedness check of the computed call graphs is always true.

  `abgAlleB` asks, for every function as a root, whether its computed call graph is closed
  under calls. With a complete member list the closure is stable (`erreichB_stabil`), so the
  answer never depends on the program; the proof goes through the call sites of each body
  (`mE_stellen`). A caller with a complete list need not evaluate the check.
-/
module
public import Grammatik.Zielsatz.Faeden.Verbund.T1
public import Grammatik.Nebenlaeufigkeit.Allgemein.FadenMerkmal.Stellen
public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil1
@[expose] public section

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration} [DecidableEq D.Fn]

/-- A call site the feature set of `ruftB` rejects is a call of `g`. -/
theorem ruftB_of_stelle {P : Programm D} {f g : D.Fn} {s : Stelle D}
    (member : s ∈ stellenE (P.rumpf f))
    (rejected : (⟨fun h => !(decide (h = g)), fun n => !(D.passt g n), fun _ => true⟩ : Merkmal D).an s = false) :
    ruftB P f g = true := by
  have some : (stellenE (P.rumpf f)).all
      (⟨fun h => !(decide (h = g)), fun n => !(D.passt g n), fun _ => true⟩ : Merkmal D).an = false :=
    List.all_eq_false.mpr ⟨s, member, by rw [rejected]; exact Bool.false_ne_true⟩
  unfold ruftB
  rw [mE_stellen, some]
  rfl

/-- **The computed call graph of every root is closed**, decided form. -/
theorem abgB_reachB (P : Programm D) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (w : D.Fn) :
    abgB P fs (reachB P fs w) = true := by
  unfold abgB
  apply List.all_eq_true.mpr
  intro f _
  cases reached : reachB P fs w f with
  | false => rfl
  | true =>
    rw [Bool.not_true, Bool.false_or, mE_stellen]
    apply List.all_eq_true.mpr
    intro s member
    cases s with
    | ruf g =>
      exact reachB_ruft P hvoll reached
        (ruftB_of_stelle member (by simp only [Merkmal.an, decide_true, Bool.not_true]))
    | ind n =>
      show (fs.all fun g => !(D.passt g n) || reachB P fs w g) = true
      apply List.all_eq_true.mpr
      intro g _
      cases fits : D.passt g n with
      | false => rfl
      | true =>
        rw [Bool.not_true, Bool.false_or]
        exact reachB_ruft P hvoll reached
          (ruftB_of_stelle member (by simp only [Merkmal.an, fits, Bool.not_true]))
    | sperre L => rfl

/-- **The check is constant on a complete member list.** -/
theorem abgAlleB_wahr (P : Programm D) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) :
    abgAlleB P fs = true :=
  List.all_eq_true.mpr fun w _ => abgB_reachB P hvoll w

end Gabbro.Grammatik.Zielsatz
