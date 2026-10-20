/-
  File:      Grammatik/Gen/Abdeckung/Satz/Unmoeglich.lean
  Subject:   The impossibility theorems of `ZellenUnmoeglich.lean` and `Quelle.lean`, stated for the programs of the
             source (`Einsatz`), in the two forms the cell table asks: a cell no program has (`u_…`, `¬ e.Hat x`),
             and a good cell no valid program has (`ug_…`, `e.gueltig = true → ¬ e.Hat x`). The generated closing
             file (`Gen/Zeugen/Schluss.lean`) names one of these for every cell without a witness.
-/
import Grammatik.Gen.Abdeckung.Satz.Quelle

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- `0.0 0bc`: no body outside the fragment. -/
theorem u_0_ohne (b c : Bool) (e : Einsatz) : ¬ e.Hat ⟨0, 0, true, [false, b, c]⟩ :=
  nie_hat (fun _ _ _ P S fs ls cs ws => zelle_0_ohne_gOk P S fs ls cs ws b c) e

/-- `7.1 110`. -/
theorem u_7_1_110 (e : Einsatz) : ¬ e.Hat ⟨7, 1, false, [true, true, false]⟩ :=
  nie_hat (fun _ _ _ P S fs ls cs ws => zelle_7_1_110 P S fs ls cs ws) e

/-- `1.0 110`: a function reachable from a start that calls `g` reaches `g`. -/
theorem u_1_0_110 (e : Einsatz) : ¬ e.Hat ⟨1, 0, true, [true, true, false]⟩ := by
  letI := e.aufz
  letI := e.zahlen
  exact zelle_1_0_110 e.P e.S e.fs e.ls e.cs e.ws e.hvoll

/-- `8.0 a11`: an answer of type `never` has no value. -/
theorem u_8_never (a : Bool) (e : Einsatz) : ¬ e.Hat ⟨8, 0, true, [a, true, true]⟩ :=
  nie_hat (fun _ _ _ P S fs ls cs ws => zelle_8_never P S fs ls cs ws a) e

/-- `8.0 a1c`: no foreign body. -/
theorem u_8_ax (a c : Bool) (e : Einsatz) : ¬ e.Hat ⟨8, 0, true, [a, true, c]⟩ := fun h => einsatz_8_ax e h

/-- `4.0 10`, `4.0 01`: the lock family of the source. -/
theorem u_4_10 (e : Einsatz) : ¬ e.Hat ⟨4, 0, true, [true, false]⟩ := fun h => absurd (einsatz_4 e h) (by decide)

theorem u_4_01 (e : Einsatz) : ¬ e.Hat ⟨4, 0, true, [false, true]⟩ := fun h => absurd (einsatz_4 e h) (by decide)

/-- `6.0 m h g` with `h || g`: a start that holds a lock or has reasons makes the program invalid. -/
theorem ug_6_0 (m hh gg : Bool) (hbad : (hh || gg) = true) (e : Einsatz) (hv : e.gueltig = true) :
    ¬ e.Hat ⟨6, 0, true, [m, hh, gg]⟩ := by
  letI := e.aufz
  letI := e.zahlen
  exact zelle_6_0_nicht_gueltig e.P e.S e.fs e.ls e.cs e.ws e.hvoll e.hls e.hcs hv m hh gg hbad

/-- `6.0 m h g` with `h || g` comes with the bad root cell `5.0 h g`. -/
theorem m_6_0 (m hh gg : Bool) (hbad : (hh || gg) = true) (e : Einsatz) (h : e.Hat ⟨6, 0, true, [m, hh, gg]⟩) :
    e.Hat ⟨5, 0, true, [hh, gg]⟩ ∧ (⟨5, 0, true, [hh, gg]⟩ : Zelle).schlecht = true := by
  letI := e.aufz
  letI := e.zahlen
  exact zelle_6_0_braucht_5 e.P e.S e.fs e.ls e.cs e.ws m hh gg hbad h

/-- `5.0 h g` comes with the pool cell `6.0 m h g` of the same start, `m` saying whether it is declared twice. -/
theorem m_5_0 (hh gg : Bool) (e : Einsatz) (h : e.Hat ⟨5, 0, true, [hh, gg]⟩) :
    ∃ m : Bool, e.Hat ⟨6, 0, true, [m, hh, gg]⟩ := by
  letI := e.aufz
  letI := e.zahlen
  have h0 := mem_alleZellen_k (5 : Fin 10) rfl h
  simp only [zellen, List.mem_map, Zelle.mk.injEq, List.cons.injEq] at h0
  obtain ⟨w, hw, -, -, -, h1, h2, -⟩ := h0
  refine ⟨mehrfachB e.ws w, mem_alleZellen.2 ⟨6, ?_⟩⟩
  simp only [zellen, List.mem_append, List.mem_map]
  exact Or.inl ⟨w, hw, by rw [h1, h2]⟩

end Gabbro.Grammatik.Gen
