module

public import Core.Beobachtung.Fluss.Beschriftung.Einheit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Beobachtung

/-- A frame component that carries a level: a temporary by slot, a local by its position
    from the top of the scope stack. -/
inductive Komp where
  | temp (slot : Nat)
  | lokal (index : Nat)

def Rahmen.komp (r : Rahmen) : Komp → Option Dynamisch
  | .temp s => r.temp s
  | .lokal i => r.lokale[i]?.join

def Beschriftung.stufe (β : Beschriftung) (pc : Nat) : Komp → Etikett
  | .temp s => β.temp pc s
  | .lokal i => β.lokal pc i

/-- The label rule of an instruction at `pc` that falls through to `pc + 1` and writes only
    the temporary `dst`, computed from the components `liest`: a component public after the
    step was public before it, and the written one is public only if all its sources are. -/
def Beschriftung.SchreibRegel (β : Beschriftung) (pc dst : Nat) (liest : List Komp) : Prop :=
  (∀ s, s ≠ dst → oeffentlich (β.temp (pc + 1) s) = true → oeffentlich (β.temp pc s) = true) ∧
  (∀ i, oeffentlich (β.lokal (pc + 1) i) = true → oeffentlich (β.lokal pc i) = true) ∧
  (oeffentlich (β.temp (pc + 1) dst) = true → ∀ k ∈ liest, oeffentlich (β.stufe pc k) = true)

/-- The instruction takes one step that sets the program counter to its successor and writes
    one temporary, as a function of the listed components alone. -/
def Befehl.Schreibform (f : Befehl) (dst : Nat) (liest : List Komp) : Prop :=
  ∃ g : Rahmen → Option Dynamisch, (∀ r live, f.auswerten r live = r.schreibe dst (g r)) ∧
    ∀ r₁ r₂ : Rahmen, (∀ k ∈ liest, r₁.komp k = r₂.komp k) → g r₁ = g r₂

theorem maskiere_laenge (l : Nat → Etikett) :
    ∀ (i : Nat) (xs : List (Option Dynamisch)), (maskiere l i xs).length = xs.length
  | _, [] => rfl
  | i, _ :: xs => by
    simp only [maskiere, List.length_cons, maskiere_laenge l (i + 1) xs]

theorem maskiere_gleich_mono {l₀ l₁ : Nat → Etikett}
    (h : ∀ i, oeffentlich (l₁ i) = true → oeffentlich (l₀ i) = true) :
    ∀ (i : Nat) (xs ys : List (Option Dynamisch)),
      maskiere l₀ i xs = maskiere l₀ i ys → maskiere l₁ i xs = maskiere l₁ i ys
  | _, [], ys => by
    intro e
    have laenge : ys.length = 0 := by
      rw [← maskiere_laenge l₀ _ ys, ← e]
      rfl
    cases ys with
    | nil => rfl
    | cons _ _ => cases laenge
  | i, x :: xs, ys => by
    intro e
    cases ys with
    | nil =>
      have laenge := congrArg List.length e
      simp only [maskiere, maskiere_laenge, List.length_cons, List.length_nil] at laenge
      cases laenge
    | cons y ys =>
      simp only [maskiere, List.cons.injEq] at e ⊢
      refine ⟨?_, maskiere_gleich_mono h (i + 1) xs ys e.2⟩
      by_cases hp : oeffentlich (l₁ i) = true
      · have hq := h i hp
        simpa only [hp, hq, if_true] using e.1
      · simp only [if_neg hp]

theorem maskiere_eintrag {l : Nat → Etikett} :
    ∀ (i : Nat) (xs ys : List (Option Dynamisch)) (j : Nat),
      maskiere l i xs = maskiere l i ys → oeffentlich (l (i + j)) = true →
        xs[j]?.join = ys[j]?.join
  | _, [], ys, j => by
    intro e _
    have laenge : ys.length = 0 := by
      rw [← maskiere_laenge l _ ys, ← e]
      rfl
    cases ys with
    | nil => rfl
    | cons _ _ => cases laenge
  | i, x :: xs, ys, j => by
    intro e hp
    cases ys with
    | nil =>
      have laenge := congrArg List.length e
      simp only [maskiere, maskiere_laenge, List.length_cons, List.length_nil] at laenge
      cases laenge
    | cons y ys =>
      simp only [maskiere, List.cons.injEq] at e
      cases j with
      | zero =>
        have hp0 : oeffentlich (l i) = true := hp
        simpa only [hp0, if_true, List.getElem?_cons_zero, Option.join_some] using e.1
      | succ j =>
        have hp1 : oeffentlich (l (i + 1 + j)) = true := by
          rw [show i + 1 + j = i + (j + 1) by omega]
          exact hp
        simpa only [List.getElem?_cons_succ] using maskiere_eintrag (i + 1) xs ys j e.2 hp1

end Gabbro.Core.Ast.Semantik
