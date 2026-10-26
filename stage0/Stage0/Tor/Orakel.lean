/-
  File:      stage0/Stage0/Tor/Orakel.lean
  Subject:   The oracle of a run with real system calls: the answers observed, each filed under a key computed from
             the question (`k`: for stage 0 the number of questions in the asking thread's trace, the gate and the
             argument words; a thread's trace gains a question at every question, `World.fragt`, so a thread asks
             under every key at most once). The answer world is the question world with the cells the call wrote
             (`zellen`, so the fast machine writes them in place: `orakelLog_schreibt`); its trace is kept
             (`orakelLog_treu`), which is what the step needs (`OrakelSpurTreu`).
-/
import Stage0.Schritt.Blatt
import Stage0.Schritt.Schreib

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **An answer from outside**: under which key it was asked, the raw word, the cells it wrote, and the argument
    words of the question (kept to check the replay asks the same). -/
structure Antwort (D : Deklaration) where
  schluessel : Nat × List Int
  roh : Int
  zellen : List (Schreib D)
  worte : List Int

/-- **The oracle of the observed answers.** A question without an answer is answered by the unchanged world and the
    word `0`; registers read `0`; an `awaits` sees (stage 0 runs no device and no weak memory). -/
def orakelLog (k : (a : D.Ax) → World D → Env D (D.aparams a) → Nat × List Int) (log : List (Antwort D)) :
    Orakel D where
  wirkt := fun a σ ρ =>
    match log.find? (fun x => x.schluessel == k a σ ρ) with
    | some a => ((schreibAuf a.zellen σ.speicher).welt σ.spur, a.roh)
    | none => (σ, 0)
  regLies := fun _ _ => 0
  regSchreib := fun _ _ => ()
  sichtbar := fun _ _ => true

theorem orakelLog_treu (k : (a : D.Ax) → World D → Env D (D.aparams a) → Nat × List Int) (log : List (Antwort D)) :
    OrakelSpurTreu (orakelLog k log) := by
  intro a σ ρ
  simp only [orakelLog]
  split <;> rfl

/-- The writes of an answer of the log. -/
def logZellen (k : (a : D.Ax) → World D → Env D (D.aparams a) → Nat × List Int) (log : List (Antwort D))
    (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a)) : List (Schreib D) :=
  match log.find? (fun x => x.schluessel == k a σ ρ) with
  | some x => x.zellen
  | none => []

theorem orakelLog_schreibt (k : (a : D.Ax) → World D → Env D (D.aparams a) → Nat × List Int)
    (log : List (Antwort D)) : OrakelSchreibt (orakelLog k log) (logZellen k log) := by
  intro a σ ρ
  simp only [orakelLog, logZellen]
  split
  · rfl
  · rfl

end Gabbro.Stage0
