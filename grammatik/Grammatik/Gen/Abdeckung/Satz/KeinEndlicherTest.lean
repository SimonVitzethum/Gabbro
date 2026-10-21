/-
  File:      Grammatik/Gen/Abdeckung/Satz/KeinEndlicherTest.lean
  Subject:   NO FINITE TEST SET SUFFICES for a checker that is only neutral, terminating and deterministic -- proved
             against the Gabbro model itself. For every finite list `T` of programs of the source there is a checker
             that treats every program by one and the same rule (the model's verdict, turned over above a size
             bound: no reference to any particular program), is a function (terminating, deterministic), agrees with
             `AkzeptiertX` on every program of `T`, and is wrong on a program of the source (`kein_endlicher_test_gabbro`).
             The same for a compiler and any correctness of its translations (`kein_endlicher_test_compiler`).

  The program it is wrong on is real: a body of `k` bindings followed by `return;` in the least member `z0`, for
  every `k` (`lang_groesse`), with every field of `Einsatz` proved (the source lock family, the derived floor, no
  foreign body).
-/
import Grammatik.Gen.Abdeckung.Satz.ErzeugtMN

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- The size of a program of the source. -/
def Einsatz.groesse (e : Einsatz) : Nat := @groesseProg e.D e.aufz e.zahlen e.P

/-- **The counting checker**: the model's verdict up to size `K`, turned over above it. One rule for every program. -/
def zaehler (K : Nat) (e : Einsatz) : Bool := if e.groesse ≤ K then e.gueltig else !e.gueltig

/-- The largest size of a list of programs. -/
def maxGroesse (T : List Einsatz) : Nat := (T.map Einsatz.groesse).foldr max 0

theorem le_maxGroesse {T : List Einsatz} {t : Einsatz} (h : t ∈ T) : t.groesse ≤ maxGroesse T := by
  induction T with
  | nil => cases h
  | cons a T ih =>
    simp only [maxGroesse, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-! ## A program of the source of every size -/

/-- The one function of `z0`. -/
def f0 : z0.deklaration.Fn := ⟨0, by decide⟩

/-- `k` bindings `let _ = true;`, then `return;`. -/
def lang : (k : Nat) → (Γ : Ctx) →
    Endblock z0.deklaration (vertragVon z0.deklaration f0) false Γ (Signatur.anfang z0.deklaration (z0.deklaration.signatur f0))
  | 0, _ => .ret .empty (by decide)
  | k + 1, Γ => .bind .tru (lang k (.bool :: Γ))

theorem lang_groesse : ∀ (k : Nat) (Γ : Ctx), k ≤ @groesseEnd z0.deklaration z0.zahlen _ _ _ _ (lang k Γ)
  | 0, _ => Nat.zero_le _
  | k + 1, Γ => by
    have := lang_groesse k (.bool :: Γ)
    simp only [lang, groesseEnd]
    omega

theorem lang_sperre (L : z0.deklaration.Lock) : ∀ (k : Nat) (Γ : Ctx),
    mE ⟨fun _ => true, fun _ => true, fun L' => !(decide (L' = L))⟩ (lang k Γ) = true
  | 0, _ => rfl
  | k + 1, Γ => by simp only [lang, mE]; exact lang_sperre L k _

/-- The skeleton of `z0` with the long body. -/
def langHaut (k : Nat) : Haut z0.deklaration :=
  ⟨fun f => (show f = f0 from Fin.ext (by have := f.isLt; simp [z0, Spez.deklaration] at this ⊢; omega)) ▸ lang k [],
   fun _ => false⟩

theorem langHaut_rumpf (k : Nat) : (langHaut k).rumpf f0 = lang k [] := rfl

theorem langHaut_boden (k : Nat) : z0.bodenOk (langHaut k).programm = true := by
  simp only [Spez.bodenOk, List.all_eq_true, beq_iff_eq]
  intro f _
  have hf : f = f0 := Fin.ext (by have := f.isLt; simp [z0, Spez.deklaration] at this ⊢; omega)
  subst hf
  rfl

/-- **A program of the source of size at least `k`.** -/
def langEinsatz (k : Nat) : Einsatz := z0.einsatz (langHaut k).programm [] (by decide) (langHaut_boden k)

theorem langEinsatz_groesse (k : Nat) : k ≤ (langEinsatz k).groesse := by
  letI : Zahlen := z0.zahlen
  have h1 := lang_groesse k []
  show k ≤ @groesseProg z0.deklaration z0.aufz z0.zahlen (langHaut k).programm
  unfold groesseProg groesseHaut
  have h2 : @groesseEnd z0.deklaration z0.zahlen _ _ _ _ ((langHaut k).programm.haut.rumpf f0) ≤
      ((Aufz.fn (D := z0.deklaration)).map fun f =>
        @groesseEnd z0.deklaration z0.zahlen _ _ _ _ ((langHaut k).programm.haut.rumpf f)).sum :=
    le_summe (fun f => @groesseEnd z0.deklaration z0.zahlen _ _ _ _ ((langHaut k).programm.haut.rumpf f)) (Aufz.fn_mem f0)
  have h4 := Nat.le_trans h1 h2
  omega

/-! ## The theorem -/

/-- **No finite test set suffices.** For every finite list of programs of the source there is a checker -- one rule
    for every program (`zaehler K`), a function -- that agrees with the model on the whole list and is wrong on a
    program of the source. -/
theorem kein_endlicher_test_gabbro (T : List Einsatz) :
    ∃ C : Einsatz → Bool, (∀ t ∈ T, C t = t.gueltig) ∧ ∃ e : Einsatz, C e ≠ e.gueltig := by
  refine ⟨zaehler (maxGroesse T), fun t ht => ?_, langEinsatz (maxGroesse T + 1), ?_⟩
  · simp [zaehler, le_maxGroesse ht]
  · have := langEinsatz_groesse (maxGroesse T + 1)
    have hn : ¬ (langEinsatz (maxGroesse T + 1)).groesse ≤ maxGroesse T := by omega
    simp only [zaehler, hn, if_false]
    cases (langEinsatz (maxGroesse T + 1)).gueltig <;> decide

/-- **No finite test set suffices for a compiler either.** Let `Korrekt e o` say that `o` is a correct translation of
    the program `e` (whatever the model's semantics demands), with a correct translation `richtig e` and a wrong one
    `falsch e` for every program. For every finite list `M` there is a compiler -- one rule for every program (correct
    up to size `K`, wrong above), a function -- that translates every program of `M` correctly and some program of
    the source wrongly. -/
theorem kein_endlicher_test_compiler {O : Type} (Korrekt : Einsatz → O → Prop) (richtig falsch : Einsatz → O)
    (hr : ∀ e, Korrekt e (richtig e)) (hf : ∀ e, ¬ Korrekt e (falsch e)) (M : List Einsatz) :
    ∃ comp : Einsatz → O, (∀ m ∈ M, Korrekt m (comp m)) ∧ ∃ e : Einsatz, ¬ Korrekt e (comp e) := by
  classical
  refine ⟨fun e => if e.groesse ≤ maxGroesse M then richtig e else falsch e, fun m hm => ?_,
    langEinsatz (maxGroesse M + 1), ?_⟩
  · simp only [le_maxGroesse hm, if_true]; exact hr m
  · have := langEinsatz_groesse (maxGroesse M + 1)
    have hn : ¬ (langEinsatz (maxGroesse M + 1)).groesse ≤ maxGroesse M := by omega
    simp only [hn, if_false]
    exact hf _

end Gabbro.Grammatik.Gen
