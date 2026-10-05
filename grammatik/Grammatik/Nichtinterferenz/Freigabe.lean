/-
  File:      Grammatik/Nichtinterferenz/Freigabe.lean
  Subject:   DECLASSIFICATION -- the STATEMENT of the delimited-release
             variant (`FreigabeNI`), its relation to plain noninterference,
             and why the leak's counterexample is not one against it.

  Plain noninterference forbids every flow from `A` to `B`. A usable system
  needs controlled release: a tenant's own data back to it, an aggregate, an
  error code. Release breaks plain NI by construction, so the statement
  weakens to DELIMITED RELEASE (Sabelfeld and Myers): the program declares
  its escape hatches -- here one function `frei` of the start memory, the
  tuple of every released expression evaluated at the start -- and `B` may
  learn about the start memory exactly what the hatches reveal, nothing
  more: two runs whose starts agree on `B`'s view AND on the released
  values show `B` the same.

  What is proved here: plain NI (the unwinding conditions) implies
  delimited release for every choice of hatches
  (`freigabe_aus_abwicklung`), delimited release with nothing released IS
  plain NI (`freigabe_leer_iff`), and the leak's two runs differ in the
  released bit, so they do not refute delimited release for the hatch
  `tabA[0] == 0` (`n3_freigabe_kein_gegenbeispiel`).

  What is NOT proved: that a program with a `declassify` point satisfies
  `FreigabeNI`. Step-wise unwinding with `NiGleich` breaks at the release
  step (it writes an `A`-derived value to a `B` carrier), and the invariant
  that replaces it must carry "the released values computed so far agree"
  -- which holds only if the `A` data a hatch reads is not updated before
  the release, or the hatch is evaluated on the start memory
  (the side condition of delimited release). See
  `dokumente/NICHTINTERFERENZ.md`, §8.
-/
import Grammatik.Nichtinterferenz.Zeuge

namespace Gabbro.Grammatik

open NIZeuge

variable {D : Deklaration}

/-- **Escape hatches**: what a program releases about the start memory, as
    one value (the tuple of the released expressions). -/
structure Freigabe (D : Deklaration) where
  Wert : Type
  frei : Speicher D → Wert

section Stmt

variable {Dom : Type} (π : Politik Dom) (E : Etiketten D Dom) (B : Dom)
  (P : Programm D) (O : Orakel D) (passes : Nat)
  (init : Faden → Σ f : D.Fn, Env D (D.params f))

/-- **Plain noninterference as a statement** (what `ni_aus_abwicklung`
    concludes). -/
def NIG : Prop :=
  ∀ sp₁ sp₂ : Speicher D, SpeicherGleich (sichtbarC π E B) sp₁ sp₂ →
    ∀ (ms ns : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
      LaufG P O passes (RufStartG P sp₁ init) ms fs n →
      LaufG P O passes (RufStartG P sp₂ init) ns fs n →
      ∀ k, k ≤ n → beob π E B (ms k) = beob π E B (ns k)

/-- **DELIMITED RELEASE (`FreigabeNI`)** for observer `B` and hatches `F`:
    two runs with the same schedule from starts that agree on `B`'s view
    and on the released value show `B` the same observation. -/
def FreigabeNI (F : Freigabe D) : Prop :=
  ∀ sp₁ sp₂ : Speicher D, SpeicherGleich (sichtbarC π E B) sp₁ sp₂ → F.frei sp₁ = F.frei sp₂ →
    ∀ (ms ns : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
      LaufG P O passes (RufStartG P sp₁ init) ms fs n →
      LaufG P O passes (RufStartG P sp₂ init) ns fs n →
      ∀ k, k ≤ n → beob π E B (ms k) = beob π E B (ns k)

/-- Plain NI implies delimited release, for every choice of hatches. -/
theorem freigabe_aus_ni (h : NIG π E B P O passes init) (F : Freigabe D) :
    FreigabeNI π E B P O passes init F :=
  fun sp₁ sp₂ hsp _ ms ns fs n hm hn => h sp₁ sp₂ hsp ms ns fs n hm hn

/-- The unwinding conditions give delimited release for every hatch. -/
theorem freigabe_aus_abwicklung (hA : AbwicklungG π E B P O passes init) (F : Freigabe D) :
    FreigabeNI π E B P O passes init F :=
  freigabe_aus_ni π E B P O passes init
    (fun sp₁ sp₂ hsp ms ns fs n hm hn => ni_aus_abwicklung π E B P O passes init hA
      sp₁ sp₂ hsp ms ns fs n hm hn) F

/-- Nothing released: delimited release is plain noninterference. -/
theorem freigabe_leer_iff :
    FreigabeNI π E B P O passes init ⟨Unit, fun _ => ()⟩ ↔ NIG π E B P O passes init :=
  ⟨fun h sp₁ sp₂ hsp => h sp₁ sp₂ hsp rfl, fun h => freigabe_aus_ni π E B P O passes init h _⟩

end Stmt

/-- The hatch of the leak: the bit `tabA[0] == 0`. -/
def lkFrei : Freigabe nD := ⟨Bool, fun sp => decide ((sp.slots NTab.tabA 0 ()).n = 0)⟩

/-- **The leak's counterexample to plain NI is not one to delimited
    release with the hatch `tabA[0] == 0`**: its two start memories differ
    in the released bit, so the premise `F.frei sp₁ = F.frei sp₂` fails.
    Plain NI fails for the leak (`n3_verletzt`); whether delimited release
    holds for it is the proof this file does not have. -/
theorem n3_freigabe_kein_gegenbeispiel : lkFrei.frei sp0 ≠ lkFrei.frei sp1 := by
  intro h
  have h' : (true : Bool) = false := h
  exact Bool.noConfusion h'

/-- Plain NI fails for the leak at observer `B` (from `n3_verletzt`). -/
theorem n3_nicht_nig :
    ¬ NIG nπ (etiketten (L3 .A) fdom3) NDom.B nP nO 0 init3 := by
  intro h
  obtain ⟨hsp, h1, h2, hne, _⟩ := n3_verletzt
  exact hne (h sp0 sp1 hsp lkRun1 lkRun2 (fun _ => 0) 3 h1 h2 3 (Nat.le_refl 3))

#print axioms Gabbro.Grammatik.freigabe_aus_abwicklung
#print axioms Gabbro.Grammatik.freigabe_leer_iff
#print axioms Gabbro.Grammatik.n3_nicht_nig

end Gabbro.Grammatik
