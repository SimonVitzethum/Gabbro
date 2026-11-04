/-
  File:      Grammatik/Gen/Abdeckung/Satz/Quelle.lean
  Subject:   CELLS NO PROGRAM OF THE SOURCE HAS. A program of the source (`Einsatz`) has the lock family of the source
             and no foreign body, so the two atoms of a lock-place cell agree (`einsatz_4`) and no answer cell names a
             foreign body (`einsatz_8_ax`); and a cell no program of the model has, no program of the source has
             (`nie_hat`).
-/
module
public import Grammatik.Gen.Abdeckung.Satz.ZellenVoll
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section


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
  have h0 : (⟨4, 0, true, [a, b]⟩ : Zelle) ∈ zellen e.P e.S e.fs e.ls e.cs e.ws 4 :=
    mem_alleZellen_k (4 : Fin 10) rfl h
  rw [zellen] at h0
  obtain ⟨L, _, hc⟩ := List.mem_flatMap.mp h0
  obtain ⟨c, _, equal⟩ := List.mem_map.mp hc
  simp only [Zelle.mk.injEq, List.cons.injEq, true_and, and_true] at equal
  obtain ⟨ha, hb⟩ := equal
  rw [← ha, ← hb]
  have hs := e.hS L c
  cases h1 : istIn (e.S.orte L) c
  · have : c ∉ e.S.orte L := fun hc => by rw [← istIn_iff, h1] at hc; cases hc
    simp only [hs.not.1 this, decide_false]
  · have : c ∈ e.S.orte L := istIn_iff.1 h1
    simp only [hs.1 this, decide_true]

/-- **No foreign body**: an answer cell whose second atom holds names a foreign body, and a program of the source has
    none. -/
theorem einsatz_8_ax (e : Einsatz) {a c : Bool} (h : e.Hat ⟨8, 0, true, [a, true, c]⟩) : False := by
  letI := e.aufz
  letI := e.zahlen
  have h0 : (⟨8, 0, true, [a, true, c]⟩ : Zelle) ∈ zellen e.P e.S e.fs e.ls e.cs e.ws 8 :=
    mem_alleZellen_k (8 : Fin 10) rfl h
  rw [zellen] at h0
  obtain ⟨_, _, hf⟩ := List.mem_flatMap.mp h0
  obtain ⟨x, _, equal⟩ := List.mem_map.mp hf
  simp only [Zelle.mk.injEq, List.cons.injEq, true_and, and_true] at equal
  obtain ⟨_, hb, _⟩ := equal
  cases x with
  | inl ax => exact e.keinAx ax
  | inr _ => simp only [Bool.false_eq_true] at hb

/-- Reset cells keep the original declaration, including unused array globals. -/
theorem einsatz_reset (e : Einsatz) (b : Bool) :
    e.Hat ⟨10, 0, true, [b]⟩ ↔ ∃ c ∈ e.cs, @resetCarrierB e.D c = b := by
  letI := e.aufz
  letI := e.zahlen
  exact mem_alleZellen_reset

/-- A genuine reset refusal is a bad cell of the unchanged conjunctive checker. -/
theorem einsatz_reset_abgelehnt (e : Einsatz) (h : e.Hat ⟨10, 0, true, [false]⟩) :
    e.gueltig = false := by
  cases hv : e.gueltig
  · rfl
  · have rejected := (einsatz_akzeptiert e).mpr hv _ h
    change false = true at rejected
    cases rejected

end Gabbro.Grammatik.Gen
