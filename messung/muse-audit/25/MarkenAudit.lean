/-
  Audit 25 / Marken.lean: demonstrations for read-only findings.

  No existing file is modified.
-/
import Grammatik.Marken

open Gabbro.Grammatik.Marken

namespace Audit25.Marken

/-! ## M1 (pattern b): the step premises of the three `getragen_*_unberuehrt`
    lemmas are never used.

    Each lemma takes the full step hypothesis (`_hfrei`, `_hstufe`,
    `_hfremd` / `_hbesitz`, ...) but the proof only uses `hU : Unbenannt`
    and `hG : Getragen` plus the `*_anders` frame lemmas. Demonstrated:
    the same conclusions with the step premises deleted. -/

theorem m1_erzeuge_ohne_praemissen {σ : Stand}
    (m₀ : Marke) (f₀ : Faden) (s₀ : Nat)
    (l : Lauf) (hU : Unbenannt m₀ l) (hG : Getragen σ l) :
    Getragen (belebe σ m₀ f₀ s₀) l := by
  intro i f ei hi m s hm
  obtain ⟨t, ht⟩ := hG i f ei hi m s hm
  by_cases heq : m = m₀
  · subst heq
    exact absurd hm (hU i f ei hi s)
  · exact ⟨t, by rw [belebe_anders _ _ _ _ _ heq]; exact ht⟩

theorem m1_fuehre_ohne_praemissen {σ : Stand}
    (m₀ : Marke) (f₀ : Faden) (a : Nat)
    (l : Lauf) (hU : Unbenannt m₀ l) (hG : Getragen σ l) :
    Getragen (belebe σ m₀ f₀ (a + 1)) l := by
  intro i f ei hi m s hm
  obtain ⟨t, ht⟩ := hG i f ei hi m s hm
  by_cases heq : m = m₀
  · subst heq
    exact absurd hm (hU i f ei hi s)
  · exact ⟨t, by rw [belebe_anders _ _ _ _ _ heq]; exact ht⟩

theorem m1_verbrauche_ohne_praemissen {σ : Stand}
    (m₀ : Marke)
    (l : Lauf) (hU : Unbenannt m₀ l) (hG : Getragen σ l) :
    Getragen (loesche σ m₀) l := by
  intro i f ei hi m s hm
  obtain ⟨t, ht⟩ := hG i f ei hi m s hm
  by_cases heq : m = m₀
  · subst heq
    exact absurd hm (hU i f ei hi s)
  · exact ⟨t, by rw [loesche_anders _ _ _ heq]; exact ht⟩

/-! ## M2 (pattern a): `einfaedig_aus_verlauf_getragen` is
    `verlauf_aus_lauf` under another name.

    Its statement is identical (same binders, same hypotheses) and its
    proof is the single application. Demonstrated: definitional unfolding
    in both directions. -/

theorem m2_alias_vorwaerts (κ : MarkDekl) {σ : Stand}
    (v : Verlauf κ σ) (l : Lauf) (hT : Getragen σ l) : Einfaedig l :=
  einfaedig_aus_verlauf_getragen κ v l hT

theorem m2_alias_beide_wege (κ : MarkDekl) {σ : Stand}
    (v : Verlauf κ σ) (l : Lauf) (hT : Getragen σ l) : Einfaedig l :=
  verlauf_aus_lauf κ v l hT

/-! ## M3 (pattern c/d): `StandEinfaedig` holds trivially over a function
    type, and the header says so -- but downstream-shaped theorems reuse
    the same name pattern over runs where it is NOT trivial.

    Demonstrated both sides: (i) any `Stand` restricted view is trivially
    single-threaded in the sense that `Stand` cannot even write two owners
    (i.e. `stand_besitz_eindeutig` needs no induction); (ii) by contrast
    `Einfaedig` over `Lauf` is NOT trivial -- a two-step run with two
    threads naming the same mark refutes it. This separates the trivial
    state-form from the genuine run-form that W4 needs. -/

/-- The state form needs no induction: it is the function shape. -/
theorem m3_standform_ohne_induktion {σ : Stand} (hσ : StandEinfaedig σ)
    (m : Marke) (f g : Faden) (s t : Nat)
    (h1 : σ m = some (f, s)) (h2 : σ m = some (g, t)) :
    f = g ∧ s = t :=
  stand_besitz_eindeutig hσ m f g s t h1 h2

/-- The run form is NOT trivial: two threads naming one mark refute it. -/
theorem m3_laufform_nicht_trivial :
    ¬ Einfaedig [{ faden := 0, ereignis := ⟨[Res.marke 7 0]⟩ },
                 { faden := 1, ereignis := ⟨[Res.marke 7 0]⟩ }] := by
  intro h
  have h01 : (0 : Faden) = 1 :=
    h 0 1 0 1 7 0 0 _ _ rfl rfl (by simp) (by simp)
  exact absurd h01 (by decide)

/-! ## M4 (pattern a): `verlauf_treu_und_einfaedig` is the pair of the two
    preceding theorems; `verlauf_besitz_stufe` is `verlauf_stufentreu`
    applied to the unpacked `Besitzt`. Demonstrated by re-derivation. -/

theorem m4_paar_ableitung (κ : MarkDekl) {σ : Stand}
    (v : Verlauf κ σ) : StufenTreu κ σ ∧ StandEinfaedig σ :=
  ⟨verlauf_stufentreu κ v, verlauf_einfaedig κ v⟩

theorem m4_besitz_ableitung (κ : MarkDekl) {σ : Stand} (v : Verlauf κ σ)
    (f : Faden) (m : Marke) (h : Besitzt σ f m) :
    ∃ s, s < κ.stufen m ∧ σ m = some (f, s) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, verlauf_stufentreu κ v m f s hs, hs⟩

/-! ## M5 (pattern e, checked non-finding): `Getragen` is NOT vacuous for
    ordinary carried runs -- the empty run is carried everywhere and a
    mark-owning event extends it. But: `Getragen` over a NON-empty run at
    `Anfang` (no owner anywhere) is unsatisfiable for any run naming a
    mark. Both directions demonstrated, so the predicate is neither
    trivially true nor trivially false. -/

/-- Non-vacuous: a run naming an owned mark IS carried. -/
theorem m5_getragen_erfuellbar :
    Getragen (belebe Anfang 7 0 0) [{ faden := 0, ereignis := ⟨[Res.marke 7 0]⟩ }] := by
  intro i f ei hi m s hm
  cases i with
  | zero =>
      have h1 : ({ faden := 0, ereignis := ({ lambda := [Res.marke 7 0] } : Ereignis) } : Schritt)
          = Schritt.mk f ei := by simpa using hi
      have hf : f = 0 := congrArg Schritt.faden h1.symm
      have he : ei = (⟨[Res.marke 7 0]⟩ : Ereignis) := congrArg Schritt.ereignis h1.symm
      subst hf
      rw [he] at hm
      simp at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact ⟨0, by simp [belebe]⟩
  | succ n => simp at hi

/-- Non-trivial: at `Anfang` no mark-naming run is carried. -/
theorem m5_getragen_nicht_leer :
    ¬ Getragen Anfang [{ faden := 0, ereignis := ⟨[Res.marke 7 0]⟩ }] := by
  intro h
  have := h 0 0 _ rfl 7 0 (by simp)
  obtain ⟨s, hs⟩ := this
  simp [Anfang] at hs

/-
CUTS:
- M1 VERIFIED: m1_* prove the same conclusions with step premises deleted.
- M2 VERIFIED: m2 shows the alias in both directions.
- M3 VERIFIED: m3 separates trivial state-form from non-trivial run-form.
- M4 demonstrated by re-derivation (pair + application).
- M5 checked non-finding: Getragen is satisfiable and not trivially true.
-/

#print axioms Audit25.Marken.m1_erzeuge_ohne_praemissen
#print axioms Audit25.Marken.m2_alias_beide_wege
#print axioms Audit25.Marken.m3_laufform_nicht_trivial
#print axioms Audit25.Marken.m5_getragen_erfuellbar
