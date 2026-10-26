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
  {log : List (Antwort D)} {passes : Nat} {ww : World D} {M0 : RufMaschineG D} {n : Nat}

/-- **The start**: the normal form of the start machine. -/
def FStand.start (ww : World D) (M0 : RufMaschineG D) (n : Nat) : FStand n D :=
  ⟨M0.speicher, (Array.range n).map (fun g => fadenNormal ww (M0.faeden g)),
    (Array.range n).map (fun g => fremdZahl (M0.faeden g).spur), by simp, by simp⟩

theorem SInv.start (P : Programm D) (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (log : List (Antwort D))
    (passes : Nat) (ww : World D) (M0 : RufMaschineG D) (n : Nat) :
    SInv P kf log passes ww M0 (FStand.start ww M0 n) := by
  refine ⟨M0, .start, ?_, ?_, fun _ _ => rfl⟩
  · simp only [FStand.F, FStand.start, sMaschine, normal, RufMaschineG.mk.injEq, true_and, and_true]
    funext g
    by_cases hg : g < n
    · simp [tabelle, hg]
    · simp [tabelle, hg]
  · intro g hg
    simp [FStand.c, FStand.start, hg]

/-- The start of a run. -/
def SStand.start (P : Programm D) (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (log : List (Antwort D))
    (passes : Nat) (ww : World D) (M0 : RufMaschineG D) (n : Nat) : SStand P kf log passes ww M0 n :=
  ⟨FStand.start ww M0 n, SInv.start P kf log passes ww M0 n⟩

/-- **The fast machine stands for a reachable machine.** -/
theorem SStand.steht (s : SStand P kf log passes ww M0 n) :
    ∃ M : RufMaschineG D, RufErreichbarG P (orakelZ kf 0 log) passes M0 M ∧ s.s.F ww M0 = normal ww M := by
  obtain ⟨M, hr, hF, _⟩ := s.inv
  exact ⟨M, hr, hF⟩

/-- One step of the first thread in `fs` that steps. -/
def SStand.weiter (h0 : ∀ g, n ≤ g → offen (M0.faeden g).spur = []) (s : SStand P kf log passes ww M0 n) :
    List {f // f < n} → Option (Faden × SStand P kf log passes ww M0 n)
  | [] => none
  | ⟨f, hf⟩ :: fs =>
    match s.schritt h0 f hf with
    | some s' => some (f, s')
    | none => s.weiter h0 fs

/-- The threads in round-robin order after `f`: those behind it first. -/
def rundeNach (reihe : List {f // f < n}) (f : Faden) : List {f // f < n} :=
  let (vorn, hinten) := reihe.span (fun g => g.1 != f)
  hinten.drop 1 ++ vorn ++ hinten.take 1

/-- **Run** at most `k` steps, round robin; also the schedule taken. -/
def SStand.laufe (h0 : ∀ g, n ≤ g → offen (M0.faeden g).spur = []) :
    Nat → List {f // f < n} → SStand P kf log passes ww M0 n → List Faden →
      SStand P kf log passes ww M0 n × List Faden
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
