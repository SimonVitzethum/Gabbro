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

/-- The least of a list of ranks, folded as `Rumpf.bodenAbgeleitet` folds it, is at most each of them. -/
theorem min_fold_le (rs : List Int) : ∀ (a : Option Int), (∀ c, a = some c → ∀ r ∈ rs, True) →
    ∀ r ∈ rs, ∃ c, rs.foldl (fun a r => match a with | none => some r | some m => some (if m < r then m else r)) a
      = some c ∧ c ≤ r := by
  induction rs with
  | nil => intro _ _ r hr; cases hr
  | cons x xs ih =>
    intro a _ r hr
    simp only [List.foldl_cons]
    -- the fold only decreases: the value after `x` is at most `x`, and every later step keeps it at most
    have mono : ∀ (b : Option Int) (ys : List Int) (c0 : Int), b = some c0 →
        ∃ c, ys.foldl (fun a r => match a with | none => some r | some m => some (if m < r then m else r)) b
          = some c ∧ c ≤ c0 := by
      intro b ys
      induction ys generalizing b with
      | nil => intro c0 hb; exact ⟨c0, hb, le_refl _⟩
      | cons y ys ihy =>
        intro c0 hb
        subst hb
        simp only [List.foldl_cons]
        obtain ⟨c, hc, hle⟩ := ihy (some (if c0 < y then c0 else y)) (if c0 < y then c0 else y) rfl
        refine ⟨c, hc, ?_⟩
        split at hle <;> omega
    rcases List.mem_cons.1 hr with rfl | hr
    · have : ∃ c0, (match a with | none => some r | some m => some (if m < r then m else r)) = some c0 ∧ c0 ≤ r := by
        cases a with
        | none => exact ⟨r, rfl, le_refl _⟩
        | some m => exact ⟨_, rfl, by split <;> omega⟩
      obtain ⟨c0, h0, hle0⟩ := this
      obtain ⟨c, hc, hle⟩ := mono _ xs c0 h0
      exact ⟨c, hc, by omega⟩
    · exact ih _ (fun _ _ _ _ => trivial) r hr

/-- Folding the smaller of two optional ranks never rises above a start that is a rank. -/
theorem foldl_minOpt_le {α : Type} (F : α → Option Int) :
    ∀ (xs : List α) (a : Option Int) (c0 : Int), a = some c0 →
      ∃ c, xs.foldl (fun a g => minOpt a (F g)) a = some c ∧ c ≤ c0 := by
  intro xs
  induction xs with
  | nil => intro a c0 h; exact ⟨c0, h, le_refl _⟩
  | cons x xs ih =>
    intro a c0 h
    subst h
    simp only [List.foldl_cons]
    cases hF : F x with
    | none =>
      simp only [minOpt]
      exact ih _ c0 rfl
    | some d =>
      simp only [minOpt]
      obtain ⟨c, hc, hle⟩ := ih _ (if c0 < d then c0 else d) rfl
      exact ⟨c, hc, by split at hle <;> omega⟩

/-- Every round of the floor relation is at most the least rank the function takes itself. -/
theorem bodenRunden_le {D : Deklaration} [Aufz D] (P : Programm D) (f : D.Fn) (d : Int)
    (hd : Rumpf.bodenAbgeleitet (P.rumpf f) = some d) :
    ∀ n, ∃ c, Programm.bodenRunden P n f = some c ∧ c ≤ d := by
  intro n
  cases n with
  | zero => exact ⟨d, hd, le_refl _⟩
  | succ n => exact foldl_minOpt_le _ _ _ d hd

/-- `3.0 10`: a program of the source takes no lock below its floor -- the floor is at most the least rank the body
    takes. -/
theorem u_3_0_10 (e : Einsatz) : ¬ e.Hat ⟨3, 0, true, [true, false]⟩ := by
  letI := e.aufz
  letI := e.zahlen
  intro h
  have h0 := mem_alleZellen_k (3 : Fin 10) rfl h
  simp only [zellen, List.mem_flatMap, List.mem_map, Zelle.mk.injEq, List.cons.injEq] at h0
  obtain ⟨f, _, L, _, -, -, -, hn, hb, -⟩ := h0
  have hfl := e.hBoden f
  have hL : L ∈ (Aufz.lock (D := e.D)).filter fun L' =>
      !(mE ⟨fun _ => true, fun _ => true, fun L'' => !(decide (L'' = L'))⟩ (e.P.rumpf f)) :=
    List.mem_filter.2 ⟨Aufz.lock_mem L, hn⟩
  obtain ⟨d, hd, hdle⟩ := min_fold_le _ none (fun _ h _ _ => by cases h) (e.D.rang L) (List.mem_map_of_mem hL)
  obtain ⟨c, hc, hcle⟩ := bodenRunden_le e.P f d hd (Aufz.fn (D := e.D)).length
  have hne : (Aufz.lock (D := e.D)).isEmpty = false := by
    cases hl : (Aufz.lock (D := e.D)) with
    | nil => rw [hl] at hL; cases (List.mem_filter.1 hL).1
    | cons _ _ => rfl
  have hcb : some c = (e.D.signatur f).boden := by
    rw [← hfl]; simp only [Programm.bodenP, hne, hc, Bool.false_eq_true, if_false]
  have : (bodenM f).sperre L = true := by
    simp only [bodenM, bodenF, ← hcb, decide_eq_true_eq]
    omega
  rw [this] at hb
  cases hb

/-- `2.0 a b 1 1`: a carrier a lock guards is not an unguarded shared atomic. -/
theorem u_2_0_11 (a b : Bool) (e : Einsatz) : ¬ e.Hat ⟨2, 0, true, [a, b, true, true]⟩ := by
  letI := e.aufz
  letI := e.zahlen
  intro h
  have h0 := mem_alleZellen_k (2 : Fin 10) rfl h
  simp only [zellen, getrenntZellen, geteiltZelle, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false, Zelle.mk.injEq, List.cons.injEq] at h0
  rcases h0 with ⟨_, _, c, _, (⟨-, -, -, -, -, h3, h4, -⟩ | h') | h'⟩ | ⟨_, _, _, _, h' | h'⟩
  · have h4' : geteiltVB e.P e.fs c = true := h4.symm
    have h3' : ((waechterVon c).any fun L => istIn (e.S.orte L) c) = true := h3.symm
    unfold geteiltVB at h4'
    have hl : (waechterVon c).isEmpty = true := by
      revert h4'; cases atomarB c <;> cases (waechterVon c).isEmpty <;> simp only [Bool.and_self, Bool.false_and, Bool.false_eq_true, imp_self, Bool.and_true, implies_true, Bool.and_false, Bool.true_and]
    rw [List.isEmpty_iff] at hl
    rw [hl] at h3'
    cases h3'
  all_goals (obtain ⟨_, _, _, _, h''⟩ := h'; simp only [OfNat.ofNat_ne_zero, Bool.false_eq_true, List.any_eq_true, Bool.and_eq_true, List.ne_cons_self, and_false, and_self, Bool.true_eq, List.cons_ne_self, reduceCtorEq] at h'')

/-- `2.0 1 b 0 d`: a carrier one of whose guards the signature holds is guarded, and in a program of the source the
    lock family protects exactly the guarded carriers. -/
theorem u_2_0_sig (b d : Bool) (e : Einsatz) : ¬ e.Hat ⟨2, 0, true, [true, b, false, d]⟩ := by
  letI := e.aufz
  letI := e.zahlen
  intro h
  have h0 := mem_alleZellen_k (2 : Fin 10) rfl h
  simp only [zellen, getrenntZellen, geteiltZelle, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false, Zelle.mk.injEq, List.cons.injEq] at h0
  rcases h0 with ⟨_, _, c, _, (⟨-, -, -, h1, -, h3, -, -⟩ | h') | h'⟩ | ⟨_, _, _, _, h' | h'⟩
  · obtain ⟨L, hL, -⟩ := List.any_eq_true.1 (show sigB _ c = true from h1.symm)
    have : ((waechterVon c).any fun L => istIn (e.S.orte L) c) = true :=
      List.any_eq_true.2 ⟨L, hL, istIn_iff.2 ((e.hS L c).2 hL)⟩
    rw [← h3] at this
    cases this
  all_goals (obtain ⟨_, _, _, _, h''⟩ := h'; simp only [OfNat.ofNat_ne_zero, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, not_and, Bool.not_eq_true, List.ne_cons_self, and_false, and_self, Bool.false_eq, List.cons_ne_self, reduceCtorEq] at h'')

end Gabbro.Grammatik.Gen
