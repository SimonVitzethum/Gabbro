/-
  File:      Grammatik/Gen/Abdeckung/Satz/Quelle.lean
  Subject:   CELLS NO PROGRAM OF THE SOURCE HAS. A program of the source (`Einsatz`) has the lock family of the source
             and no foreign body, so the two atoms of a lock-place cell agree (`einsatz_4`) and no answer cell names a
             foreign body (`einsatz_8_ax`); and a cell no program of the model has, no program of the source has
             (`nie_hat`).
-/
import Grammatik.Gen.Abdeckung.Satz.ZellenVoll

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- A cell no program of the model has. -/
theorem nie_hat {x : Zelle}
    (h : ∀ (D : Deklaration) (_ : Aufz D) (_ : Zahlen) (P : Programm D) (S : SperrInv D) (fs : List D.Fn)
      (ls : List D.Lock) (cs : List (D.Tab ⊕ D.Glob)) (ws : List D.Fn), x ∉ alleZellen P S fs ls cs ws)
    (e : Einsatz) : ¬ e.Hat x :=
  h e.D e.aufz e.zahlen e.P e.S e.fs e.ls e.cs e.ws

/-- A cell no program of the source has needs no test. -/
theorem nie_gut {x : Zelle} (h : ∀ e : Einsatz, ¬ e.Hat x) : ∀ e : Einsatz, e.Hat x → e.gueltig = false :=
  fun e he => absurd he (h e)

/-- A good cell no VALID program of the source has needs no valid test. -/
theorem nie_gueltig {x : Zelle} (h : ∀ e : Einsatz, e.gueltig = true → ¬ e.Hat x) :
    ∀ e : Einsatz, e.Hat x → e.gueltig = false := by
  intro e he
  cases hv : e.gueltig
  · rfl
  · exact absurd he (h e hv)

/-- **Lock places**: the lock family of the source protects exactly the guarded carriers, so the two atoms agree. -/
theorem einsatz_4 (e : Einsatz) {a b : Bool} (h : e.Hat ⟨4, 0, true, [a, b]⟩) : a = b := by
  letI := e.aufz
  letI := e.zahlen
  have h0 := mem_alleZellen_k (4 : Fin 10) rfl h
  simp only [zellen, List.mem_flatMap, List.mem_map, Zelle.mk.injEq, List.cons.injEq] at h0
  obtain ⟨L, _, c, _, -, -, -, ha, hb, -⟩ := h0
  subst ha hb
  have hs := e.hS L c
  cases h1 : istIn (e.S.orte L) c
  · have : c ∉ e.S.orte L := fun hc => by rw [← istIn_iff, h1] at hc; cases hc
    simp [hs.not.1 this]
  · have : c ∈ e.S.orte L := istIn_iff.1 h1
    simp [hs.1 this]

/-- **No foreign body**: an answer cell whose second atom holds names a foreign body, and a program of the source has
    none. -/
theorem einsatz_8_ax (e : Einsatz) {a c : Bool} (h : e.Hat ⟨8, 0, true, [a, true, c]⟩) : False := by
  letI := e.aufz
  letI := e.zahlen
  have h0 := mem_alleZellen_k (8 : Fin 10) rfl h
  simp only [zellen, List.mem_flatMap, List.mem_map, Zelle.mk.injEq, List.cons.injEq] at h0
  obtain ⟨_, _, x, _, -, -, -, -, hb, -⟩ := h0
  cases x with
  | inl ax => exact e.keinAx ax
  | inr _ => simp at hb

end Gabbro.Grammatik.Gen
