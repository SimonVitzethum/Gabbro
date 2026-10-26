/-
  File:      stage0/Stage0/Tor/Orakel.lean
  Subject:   The oracle of a run with real system calls: the answers observed, each filed under the length of the
             trace of the world it was asked in (a thread's trace grows at every question, `World.fragt`, so a
             thread asks under every key at most once). The answer world is the question world with the cells the
             call wrote; its trace is kept (`orakelLog_treu`), which is what the step needs (`OrakelSpurTreu`).
-/
import Stage0.Schritt.Blatt

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **An answer from outside**: under which key it was asked, the raw word, the cells it wrote, and the argument
    words of the question (kept to check the replay asks the same). -/
structure Antwort (D : Deklaration) where
  schluessel : Nat
  roh : Int
  slots : (∀ t : D.Tab, Int → ∀ f : D.Feld t, Wert D (D.typ t f)) → (∀ t : D.Tab, Int → ∀ f : D.Feld t, Wert D (D.typ t f))
  worte : List Int

/-- **The oracle of the observed answers.** A question without an answer is answered by the unchanged world and the
    word `0`; registers read `0`; an `awaits` sees (stage 0 runs no device and no weak memory). -/
def orakelLog (log : List (Antwort D)) : Orakel D where
  wirkt := fun _ σ _ =>
    match log.find? (fun a => a.schluessel == σ.spur.length) with
    | some a => ({ σ with slots := a.slots σ.slots }, a.roh)
    | none => (σ, 0)
  regLies := fun _ _ => 0
  regSchreib := fun _ _ => ()
  sichtbar := fun _ _ => true

theorem orakelLog_treu (log : List (Antwort D)) : OrakelSpurTreu (orakelLog log) := by
  intro a σ ρ
  simp only [orakelLog]
  split <;> rfl

end Gabbro.Stage0
