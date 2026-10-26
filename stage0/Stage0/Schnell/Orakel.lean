/-
  File:      stage0/Stage0/Schnell/Orakel.lean
  Subject:   **The oracle of the fast machine.** `orakelZ kf c log` answers by the log under the key (the number of
             questions in the asking world's trace plus `c`, the argument key `kf`). The machine's oracle is
             `orakelZ kf 0 log`; the fast machine, whose compact trace dropped `c` questions, asks
             `orakelZ kf c log`, and the two answer paired worlds alike (`orakelZ_paar`).
-/
import Stage0.Tor.Orakel
import Stage0.Schnell.BlattPaar

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {D : Deklaration}

/-- **The oracle of a log, questions counted from `c`.** -/
def orakelZ (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (c : Nat) (log : List (Antwort D)) : Orakel D :=
  orakelLog (fun a σ ρ => (fremdZahl σ.spur + c, kf a ρ)) log

theorem orakelZ_treu (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (c : Nat) (log : List (Antwort D)) :
    OrakelSpurTreu (orakelZ kf c log) := orakelLog_treu _ _

/-- **The fast oracle answers as the machine's.** -/
theorem orakelZ_paar (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (c : Nat) (log : List (Antwort D)) :
    OrakelPaar c (orakelZ kf c log) (orakelZ kf 0 log) where
  wirkt := by
    intro sF sM σF σM a ρ hS h
    have hk : (fremdZahl σF.spur + c, kf a ρ) = (fremdZahl σM.spur + 0, kf a ρ) := by
      rw [h.fremd hS, Nat.add_zero]
    simp only [orakelZ, orakelLog, hk]
    split
    · obtain ⟨neu, hF, hM⟩ := h.neu
      refine ⟨⟨?_, ?_, neu, hF, hM⟩, rfl⟩
      · simp only [Speicher.welt, World.speicher, h.slots, h.globs]
      · simp only [Speicher.welt, World.speicher, h.slots, h.globs]
    · exact ⟨h, rfl⟩
  regLies := fun _ _ _ => rfl
  sichtbar := fun _ _ _ => rfl
  zeiger := rfl

/-- The writes of the fast oracle's answers. -/
def orakelZZellen (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (c : Nat) (log : List (Antwort D)) :
    ∀ a : D.Ax, World D → Env D (D.aparams a) → List (Schreib D) :=
  logZellen (fun a σ ρ => (fremdZahl σ.spur + c, kf a ρ)) log

theorem orakelZ_schreibt (kf : (a : D.Ax) → Env D (D.aparams a) → List Int) (c : Nat) (log : List (Antwort D)) :
    OrakelSchreibt (orakelZ kf c log) (orakelZZellen kf c log) := orakelLog_schreibt _ _

end Gabbro.Stage0
