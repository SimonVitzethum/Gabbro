/-
  File:      stage0/Stage0/Schnell/Lauf.lean
  Subject:   **The run of the fast machine**: the start (the normal form of the start machine), a step of the first
             thread in turn that steps, round robin with the schedule taken. `SStand.steht`: the fast machine is the
             normal form of a machine reachable from the start machine under the machine's oracle.
-/
import Stage0.Schnell.Stand
import Stage0.Lauf.Fertig

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {kf : (a : D.Ax) → Env D (D.aparams a) → List Int}
  {log : List (Antwort D)} {passes : Nat} {ww : World D} {M0 : RufMaschineG D} {K : Kodierung D} {n : Nat}

/-- **The start**: the normal form of the start machine. -/
def FStand.start (K : Kodierung D) (ww : World D) (M0 : RufMaschineG D) (n : Nat) (A : AWelt D) : FStand K n :=
  ⟨A, (Array.range n).map (fun g => fadenNormal ww (M0.faeden g)),
    (Array.range n).map (fun g => fremdZahl (M0.faeden g).spur), by simp only [Array.size_map, Array.size_range], by simp only [Array.size_map, Array.size_range]⟩

theorem SInv.start (P : Programm D) (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (log : List (Antwort D))
    (passes : Nat) (ww : World D) (M0 : RufMaschineG D) (K : Kodierung D) (n : Nat) (A : AWelt D)
    (hA : A.sicht K = M0.speicher) : SInv P kf log passes ww M0 (FStand.start K ww M0 n A) := by
  refine ⟨M0, .start, ?_, ?_, fun _ _ => rfl⟩
  · simp only [FStand.F, FStand.start, sMaschine, normal, RufMaschineG.mk.injEq, hA, true_and, and_true]
    funext g
    by_cases hg : g < n
    · simp only [tabelle, Array.size_map, Array.size_range, hg, getElem?_pos, Array.getElem_map, Array.getElem_range, Option.getD_some]
    · simp only [tabelle, Array.size_map, Array.size_range, hg, not_false_eq_true, getElem?_neg, Option.getD_none]
  · intro g hg
    simp only [FStand.c, FStand.start, Array.size_map, Array.size_range, hg, getElem?_pos, Array.getElem_map, Array.getElem_range, Option.getD_some]

/-- The start of a run. -/
def SStand.start (P : Programm D) (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (log : List (Antwort D))
    (passes : Nat) (ww : World D) (M0 : RufMaschineG D) (K : Kodierung D) (n : Nat) (A : AWelt D)
    (hA : A.sicht K = M0.speicher) : SStand P kf log passes ww M0 K n :=
  ⟨FStand.start K ww M0 n A, SInv.start P kf log passes ww M0 K n A hA⟩

/-- **The fast machine stands for a reachable machine.** -/
theorem SStand.steht (s : SStand P kf log passes ww M0 K n) :
    ∃ M : RufMaschineG D, RufErreichbarG P (orakelZ kf 0 log) passes M0 M ∧ s.s.F ww M0 = normal ww M := by
  obtain ⟨M, hr, hF, _⟩ := s.inv
  exact ⟨M, hr, hF⟩

/-- One step of the first thread in `fs` that steps. -/
def SStand.weiter (h0 : ∀ g, n ≤ g → offen (M0.faeden g).spur = []) (s : SStand P kf log passes ww M0 K n) :
    List {f // f < n} → Option (Faden × SStand P kf log passes ww M0 K n)
  | [] => none
  | ⟨f, hf⟩ :: fs =>
    match s.schritt h0 f hf with
    | .inr s' => some (f, s')
    | .inl s => s.weiter h0 fs

/-- The threads in round-robin order after `f`: those behind it first. -/
def rundeNach (reihe : List {f // f < n}) (f : Faden) : List {f // f < n} :=
  let (vorn, hinten) := reihe.span (fun g => g.1 != f)
  hinten.drop 1 ++ vorn ++ hinten.take 1

/-- **Run** at most `k` steps, round robin; also the schedule taken. -/
def SStand.laufe (h0 : ∀ g, n ≤ g → offen (M0.faeden g).spur = []) :
    Nat → List {f // f < n} → SStand P kf log passes ww M0 K n → List Faden →
      SStand P kf log passes ww M0 K n × List Faden
  | 0, _, s, plan => (s, plan.reverse)
  | k + 1, reihe, s, plan =>
    match s.weiter h0 reihe with
    | some (f, s') => SStand.laufe h0 k (rundeNach reihe f) s' (f :: plan)
    | none => (s, plan.reverse)

/-- All running threads, in order. -/
def alleN (n : Nat) : List {f // f < n} := (List.range n).attach.map fun ⟨f, h⟩ => ⟨f, List.mem_range.mp h⟩

theorem kopfFertig_ohne (r : RufRahmenG D) : kopfFertig (r.ohne ww) = kopfFertig r := by
  rfl

/-- A thread has ended in the normal form exactly when it has in the machine. -/
theorem fertig_normal (M : RufMaschineG D) (g : Faden) : fertig (normal ww M) g = fertig M g := by
  simp only [fertig, normal, fadenNormal, List.isEmpty_map, kopfFertig_ohne]

end Gabbro.Stage0
