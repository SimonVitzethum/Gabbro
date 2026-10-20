/-
  File:      Grammatik/Gen/Abdeckung/Satz/ZellenVoll.lean
  Subject:   THEOREM 5 FOR THE WHOLE MODEL, reduced to a finite table. A program of the model is an `Einsatz`: any
             declaration, any program, lock family, member lists that are complete, and starts. Its cells are
             `alleZellen`, and every cell lies in the universe `zellAlle` (124 cells, `zellen_im_universum`), so the
             four conditions of `Vollstaendig` (`Adaequanz/Vollstaendig.lean`) become one obligation PER CELL of the
             universe: a good cell has a valid test in M or no valid program has it; a bad cell has an isolated test in
             N or every program that has it also has a bad cell with an isolated test in N (`vollstaendig_aus_tafel`).
             With that, every conjunctive checker agreeing with the model on M and N agrees with the model's
             `AkzeptiertX` on every program of the model (`einsatz_hinreichend`).
-/
import Grammatik.Gen.Abdeckung.Satz.ZellenUnmoeglich
import Grammatik.Adaequanz.Vollstaendig

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Gabbro.Grammatik.Adaequanz

/-! ## The universe holds every cell of every program -/

theorem mem_belegungen : ∀ v : List Bool, v ∈ belegungen v.length
  | [] => by simp [belegungen]
  | b :: v => by
    simp only [belegungen, List.length_cons, List.mem_flatMap]
    exact ⟨v, mem_belegungen v, by cases b <;> simp⟩

theorem mem_zellAlle (z : Zelle) (h : (z.komp, z.art, z.urteil, z.atome.length) ∈ zellTafel) : z ∈ zellAlle := by
  simp only [zellAlle, List.mem_flatMap, List.mem_map]
  exact ⟨_, h, z.atome, mem_belegungen _, rfl⟩

section

variable {D : Deklaration} [Aufz D] [Zahlen]

set_option linter.unusedSectionVars false

/-- **Every cell of a program is a cell of the universe.** -/
theorem zellen_im_universum {P : Programm D} {S : SperrInv D} {fs : List D.Fn} {ls : List D.Lock}
    {cs : List (D.Tab ⊕ D.Glob)} {ws : List D.Fn} {z : Zelle} (h : z ∈ alleZellen P S fs ls cs ws) : z ∈ zellAlle := by
  apply mem_zellAlle
  obtain ⟨c, h⟩ := mem_alleZellen.1 h
  rcases c with ⟨n, hn⟩
  match n, hn with
  | 0, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, rfl⟩ := h; simp [zellTafel]
  | 1, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, _, _, rfl⟩ := h; simp [zellTafel]
  | 2, _ =>
    simp only [zellen, getrenntZellen, geteiltZelle, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with ⟨_, _, _, _, (rfl | ⟨_, _, _, _, rfl⟩) | rfl⟩ | ⟨_, _, _, _, rfl | ⟨_, _, _, _, rfl⟩⟩ <;>
      simp [zellTafel]
  | 3, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, rfl⟩ := h; simp [zellTafel]
  | 4, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, rfl⟩ := h; simp [zellTafel]
  | 5, _ => simp only [zellen, List.mem_map] at h; obtain ⟨_, _, rfl⟩ := h; simp [zellTafel]
  | 6, _ =>
    simp only [zellen, List.mem_append, List.mem_flatMap, List.mem_map] at h
    rcases h with ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ <;> simp [zellTafel]
  | 7, _ =>
    simp only [zellen, schreibGetrenntZellen, List.mem_flatMap, List.mem_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false, List.mem_map] at h
    rcases h with ⟨_, _, rfl | ⟨_, _, _, _, rfl⟩⟩ <;> simp [zellTafel]
  | 8, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, rfl⟩ := h; simp [zellTafel]
  | 9, _ => simp only [zellen, List.mem_flatMap, List.mem_map] at h; obtain ⟨_, _, _, _, _, _, rfl⟩ := h; simp [zellTafel]
  | n + 10, hn => exact absurd hn (by omega)

end

/-! ## A program of the model -/

/-- **A program of the source**, under any declaration: the program, the lock family the source gives it, member lists
    that hold every function, lock and carrier, and the declared starts; every body derives its declared floor. These
    are the programs without `extern fn` a Gabbro text elaborates to (`Parser.Cover.Differenz.sperrFamilie`, `Druck/Einheit.lean`). -/
structure Einsatz where
  D : Deklaration
  aufz : Aufz D
  zahlen : Zahlen
  P : Programm D
  S : SperrInv D
  fs : List D.Fn
  ls : List D.Lock
  cs : List (D.Tab ⊕ D.Glob)
  ws : List D.Fn
  hvoll : ∀ g : D.Fn, g ∈ fs
  hls : ∀ L : D.Lock, L ∈ ls
  hcs : ∀ c : D.Tab ⊕ D.Glob, c ∈ cs
  /-- the lock family is the one of the source: each lock protects exactly the carriers it guards (`protects`) -/
  hS : ∀ L c, c ∈ S.orte L ↔ L ∈ waechterVon c
  /-- every body derives its declared floor: the language writes no floor, it is the least rank the body takes -/
  hBoden : ∀ f, @Rumpf.bodenAbgeleitet D aufz f (P.rumpf f) = (D.signatur f).boden
  /-- no foreign body (`extern fn` is outside the test sets, Simon 2026-10-20) -/
  keinAx : D.Ax → False

/-- The cells of a program. -/
def Einsatz.zellen (e : Einsatz) : List Zelle :=
  letI := e.aufz
  alleZellen e.P e.S e.fs e.ls e.cs e.ws

/-- The occurrence relation of Theorem 5: the cell occurs in the program. -/
def Einsatz.Hat (e : Einsatz) (z : Zelle) : Prop := z ∈ e.zellen

instance (e : Einsatz) (z : Zelle) : Decidable (e.Hat z) := inferInstanceAs (Decidable (z ∈ e.zellen))

/-- The Lean model's Bool on a program. -/
def Einsatz.gueltig (e : Einsatz) : Bool :=
  @AkzeptiertX e.D e.aufz.decFn e.P e.S e.fs e.ls e.cs e.ws

/-- The model's table: a cell is admitted when it is not bad. -/
def gutTafel (z : Zelle) : Bool := !z.schlecht

/-- The conjunctive verdict of the model's table IS the model's Bool (step 1, `akzeptiertX_zellen`). -/
theorem einsatz_akzeptiert (e : Einsatz) : akzeptiert Einsatz.Hat gutTafel e ↔ e.gueltig = true := by
  letI := e.aufz
  letI := e.zahlen
  rw [Einsatz.gueltig, akzeptiertX_zellen e.P e.S e.fs e.ls e.cs e.ws e.hvoll e.hls e.hcs]
  simp only [akzeptiert, Einsatz.Hat, Einsatz.zellen, gutTafel, Bool.not_eq_true']

theorem Einsatz.im_universum (e : Einsatz) {z : Zelle} (h : e.Hat z) : z ∈ zellAlle := by
  letI := e.aufz
  letI := e.zahlen
  exact zellen_im_universum (P := e.P) (S := e.S) (fs := e.fs) (ls := e.ls) (cs := e.cs) (ws := e.ws) h

/-! ## The finite table that makes M and N complete -/

/-- **The obligation of the cells**: for each cell of the universe, a test or a theorem. -/
structure Tafel (M N : List Einsatz) : Prop where
  /-- every test of M is valid -/
  gut_m : ∀ m ∈ M, m.gueltig = true
  /-- a good cell: a valid test in M has it, or no valid program has it -/
  gut : ∀ z ∈ zellAlle, z.schlecht = false →
    (∃ m ∈ M, m.Hat z) ∨ (∀ e : Einsatz, e.Hat z → e.gueltig = false)
  /-- every test of N is refused -/
  n_schlecht : ∀ n ∈ N, n.gueltig = false
  /-- a bad cell: every program that has it has a test in N each of whose cells is a cell of the program or a cell
      of a test of M -/
  schlecht : ∀ z ∈ zellAlle, z.schlecht = true → ∀ e : Einsatz, e.Hat z →
    ∃ n ∈ N, ∀ w, n.Hat w → e.Hat w ∨ ∃ m ∈ M, m.Hat w

/-- **The table gives Theorem 5's condition** over every program of the model. -/
theorem vollstaendig_aus_tafel {M N : List Einsatz} (t : Tafel M N) : Vollstaendig Einsatz.Hat gutTafel M N where
  gut_m m hm := (einsatz_akzeptiert m).2 (t.gut_m m hm)
  gut p z hz hp := by
    have hzs : z.schlecht = false := by
      have := hp z hz
      simpa [gutTafel] using this
    rcases t.gut z (p.im_universum hz) hzs with h | h
    · exact h
    · have := h p hz
      rw [(einsatz_akzeptiert p).1 hp] at this
      exact absurd this (by decide)
  n_schlecht n hn ha := by
    have := (einsatz_akzeptiert n).1 ha
    rw [t.n_schlecht n hn] at this
    cases this
  schlecht p hp := by
    have : ∃ z, p.Hat z ∧ z.schlecht = true := by
      simp only [akzeptiert, not_forall] at hp
      obtain ⟨z, hz, hf⟩ := hp
      exact ⟨z, hz, by simpa [gutTafel] using hf⟩
    obtain ⟨z, hz, hzs⟩ := this
    exact t.schlecht z (p.im_universum hz) hzs p hz

/-- **Theorem 5 for the whole model.** When the table holds for M and N, every conjunctive checker over the cells
    that agrees with the model on M and on N agrees with the model's `AkzeptiertX` on EVERY program of the model. -/
theorem einsatz_hinreichend {M N : List Einsatz} (t : Tafel M N) (φ : Zelle → Bool)
    (hM : ∀ m ∈ M, akzeptiert Einsatz.Hat φ m ↔ m.gueltig = true)
    (hN : ∀ n ∈ N, akzeptiert Einsatz.Hat φ n ↔ n.gueltig = true) (e : Einsatz) :
    akzeptiert Einsatz.Hat φ e ↔ e.gueltig = true := by
  rw [← einsatz_akzeptiert e]
  exact vollstaendig_hinreichend Einsatz.Hat (vollstaendig_aus_tafel t) φ
    (fun m hm => (hM m hm).trans (einsatz_akzeptiert m).symm)
    (fun n hn => (hN n hn).trans (einsatz_akzeptiert n).symm) e

end Gabbro.Grammatik.Gen
