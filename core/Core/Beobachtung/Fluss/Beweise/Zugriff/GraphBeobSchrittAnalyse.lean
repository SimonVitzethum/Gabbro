/-
  The step observation analysed as four concatenated parts. For a non-crash step the observed writes
  since the last crash are exactly the writes of `spur.speicher`; a crash step contributes a crash
  boundary and no write.
-/
module

public import Core.Beobachtung.Fluss.Beweise.Zugriff.GraphBeobSchritt

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L] [DecidableEq Ort]
variable {E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form}

/-- Appending a tail with no crash boundary and no write observation leaves the predicate unchanged. -/
private theorem SchreibSeitAbsturz_harmlos_append (x : Ort)
    {a b : List (NiedrigesEreignis Ort Wert Grund Form)}
    (hbCrash : HatAbsturz b = false) (hbNo : ¬ ∃ e ∈ b, SchreibBeob x e) :
    SchreibSeitAbsturz x (a ++ b) ↔ SchreibSeitAbsturz x a := by
  rw [SchreibSeitAbsturz_append, hbCrash]
  have hbNot : ¬ HatAbsturz b := by
    intro ht
    rw [hbCrash] at ht
    cases ht
  have hbFalse : SchreibSeitAbsturz x b = False := by
    rw [SchreibSeitAbsturz_ohne_absturz x hbNot]
    simpa only [hbNo]
  rw [hbFalse, false_or]
  have hfalseNot : ¬ (false : Bool) = true := by
    intro ht
    cases ht
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hfalseNot, h⟩

/-- The four-part analysis: for a non-crash step the observed writes since the last crash are exactly
    the writes of `spur.speicher`, and the step observation carries no crash boundary. -/
theorem vierteil_analyse (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (label : Etiketten Ort)
    (speicher : List (SpeicherAkteur Ort × Speicher.Etikett Ort Wert))
    (aussen : List Ereignis)
    (form abschluss : List (NiedrigesEreignis Ort Wert Grund Form)) (x : Ort)
    (hpub : ∀ y : Ort, oeffentlich (label.ort y) = true)
    (hkeinCrash : ∀ e ∈ aussen, e ≠ .persistenz .crash)
    (hformFilter : form.filter (SB x) = []) (hformCrash : HatAbsturz form = false)
    (habsFilter : abschluss.filter (SB x) = []) (habsCrash : HatAbsturz abschluss = false) :
    ¬ HatAbsturz (speicher.filterMap (speicherBeob (Grund := Grund) (Form := Form) label) ++
        aussen.flatMap (aussenBeob E) ++ form ++ abschluss) ∧
    (SchreibSeitAbsturz x
        (speicher.filterMap (speicherBeob (Grund := Grund) (Form := Form) label) ++
          aussen.flatMap (aussenBeob E) ++ form ++ abschluss) ↔
      ∃ e ∈ speicher, e.2.art.schreibt ∧ e.2.ort = x) := by
  have hspCrash : HatAbsturz (speicher.filterMap (speicherBeob (Grund := Grund) (Form := Form) label)) = false :=
    hatAbsturz_filterMap_speicherBeob label speicher
  have hauCrash : HatAbsturz (aussen.flatMap (aussenBeob E)) = false :=
    hatAbsturz_flatMap_aussenBeob E aussen hkeinCrash
  have hkeinAu : ∀ e ∈ aussen.flatMap (aussenBeob E), ¬ SchreibBeob x e :=
    keinSchreib_aus_filter_nil x (flatMap_aussenBeob_filter_nil E aussen x)
  have hkeinForm : ∀ e ∈ form, ¬ SchreibBeob x e :=
    keinSchreib_aus_filter_nil x hformFilter
  have hkeinAbs : ∀ e ∈ abschluss, ¬ SchreibBeob x e :=
    keinSchreib_aus_filter_nil x habsFilter
  have hauNo : ¬ ∃ e ∈ aussen.flatMap (aussenBeob E), SchreibBeob x e := by
    rintro ⟨e, he, hs⟩
    exact hkeinAu e he hs
  have hformNo : ¬ ∃ e ∈ form, SchreibBeob x e := by
    rintro ⟨e, he, hs⟩
    exact hkeinForm e he hs
  have habsNo : ¬ ∃ e ∈ abschluss, SchreibBeob x e := by
    rintro ⟨e, he, hs⟩
    exact hkeinAbs e he hs
  have hbeobCrash : HatAbsturz (speicher.filterMap (speicherBeob (Grund := Grund) (Form := Form) label) ++
      aussen.flatMap (aussenBeob E) ++ form ++ abschluss) = false := by
    rw [hatAbsturz_append, hatAbsturz_append, hatAbsturz_append, hspCrash, hauCrash,
      hformCrash, habsCrash]
    rfl
  constructor
  · intro htrue
    rw [hbeobCrash] at htrue
    cases htrue
  · rw [SchreibSeitAbsturz_harmlos_append x habsCrash habsNo,
      SchreibSeitAbsturz_harmlos_append x hformCrash hformNo,
      SchreibSeitAbsturz_harmlos_append x hauCrash hauNo]
    have hspNot : ¬ HatAbsturz (speicher.filterMap (speicherBeob (Grund := Grund) (Form := Form) label)) := by
      intro ht
      rw [hspCrash] at ht
      cases ht
    rw [SchreibSeitAbsturz_ohne_absturz x hspNot]
    exact SchreibBeob_filterMap_speicherBeob (x := x) hpub

/-- The observation of one step, with the non-crash premise in the form the four-part analysis needs. -/
theorem schrittBeob_analyse {ρ : Lauf E} {predictor : Praediktor} {t : Nat}
    {s n : Zustand L Ort Wert Raum Lok Grund} {wahl : SchrittWahl Wahl}
    {spur : SchrittSpur Ort Wert} {x : Ort}
    (hz : ρ.zeit.zustand t = some s) (hn : ρ.zeit.zustand (t + 1) = some n)
    (hspur : ρ.zeit.spur t = some (wahl, spur))
    (hpub : ∀ y : Ort, oeffentlich (E.etiketten.ort y) = true)
    (hkeinCrash : ∀ e ∈ spur.aussen, e ≠ .persistenz .crash) :
    ¬ HatAbsturz (schrittBeob ρ predictor t) ∧
      (SchreibSeitAbsturz x (schrittBeob ρ predictor t) ↔
        ∃ e ∈ spur.speicher, e.2.art.schreibt ∧ e.2.ort = x) := by
  classical
  rw [schrittBeob, hspur, hz, hn]
  dsimp only
  cases wahl with
  | kontext c w =>
    dsimp only
    exact vierteil_analyse E E.etiketten spur.speicher spur.aussen
      (kontextBeob ρ predictor t c s n spur)
      (if ∃ d, (neuBeendet s n E.etiketten d).isSome = true
        then [NiedrigesEreignis.ende (Ort := Ort) (Wert := Wert) (Grund := Grund) (Form := Form)
          (neuBeendet s n E.etiketten)] else [])
      x hpub hkeinCrash
      (kontextBeob_filter_nil ρ predictor t c s n spur x)
      (kontextBeob_keinCrash ρ predictor t c s n spur)
      (abschlussBeob_filter_nil (neuBeendet s n E.etiketten) x)
      (abschlussBeob_keinCrash (neuBeendet s n E.etiketten))
  | antwort a =>
    dsimp only
    exact vierteil_analyse E E.etiketten spur.speicher spur.aussen []
      (if ∃ d, (neuBeendet s n E.etiketten d).isSome = true
        then [NiedrigesEreignis.ende (Ort := Ort) (Wert := Wert) (Grund := Grund) (Form := Form)
          (neuBeendet s n E.etiketten)] else [])
      x hpub hkeinCrash rfl rfl
      (abschlussBeob_filter_nil (neuBeendet s n E.etiketten) x)
      (abschlussBeob_keinCrash (neuBeendet s n E.etiketten))
  | interrupt id =>
    dsimp only
    exact vierteil_analyse E E.etiketten spur.speicher spur.aussen []
      (if ∃ d, (neuBeendet s n E.etiketten d).isSome = true
        then [NiedrigesEreignis.ende (Ort := Ort) (Wert := Wert) (Grund := Grund) (Form := Form)
          (neuBeendet s n E.etiketten)] else [])
      x hpub hkeinCrash rfl rfl
      (abschlussBeob_filter_nil (neuBeendet s n E.etiketten) x)
      (abschlussBeob_keinCrash (neuBeendet s n E.etiketten))
  | absturz =>
    dsimp only
    exact vierteil_analyse E E.etiketten spur.speicher spur.aussen []
      (if ∃ d, (neuBeendet s n E.etiketten d).isSome = true
        then [NiedrigesEreignis.ende (Ort := Ort) (Wert := Wert) (Grund := Grund) (Form := Form)
          (neuBeendet s n E.etiketten)] else [])
      x hpub hkeinCrash rfl rfl
      (abschlussBeob_filter_nil (neuBeendet s n E.etiketten) x)
      (abschlussBeob_keinCrash (neuBeendet s n E.etiketten))

/-- A crash step resets the graph and puts a crash boundary into the observation. -/
theorem schrittBeob_absturz (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    {ρ : Lauf E} {predictor : Praediktor} {t : Nat}
    {s n : Zustand L Ort Wert Raum Lok Grund} {x : Ort}
    (hz : ρ.zeit.zustand t = some s) (hn : ρ.zeit.zustand (t + 1) = some n)
    (hspur : ρ.zeit.spur t = some (.absturz, absturzSpur)) :
    HatAbsturz (schrittBeob ρ predictor t) = true ∧
      ¬ SchreibSeitAbsturz x (schrittBeob ρ predictor t) := by
  classical
  rw [schrittBeob, hspur, hz, hn]
  dsimp only
  rw [absturzSpur]
  simp only [List.filterMap_nil, List.flatMap_cons, List.flatMap_nil, List.nil_append,
    List.append_nil, aussenBeob, HatAbsturz, AbsturzBeob, Bool.true_or]
  constructor
  · rfl
  · rw [SchreibSeitAbsturz_append]
    have hcrashFalse : SchreibSeitAbsturz x
        [NiedrigesEreignis.katalog (Ort := Ort) (Wert := Wert) (Grund := Grund) (Form := Form)
          (.persistenz .crash)] = False := by
      simp only [SchreibSeitAbsturz, AbsturzBeob]
    rw [hcrashFalse, and_false, or_false]
    have hkein : ∀ e ∈ (if ∃ d, (neuBeendet s n E.etiketten d).isSome = true
        then [NiedrigesEreignis.ende (Ort := Ort) (Wert := Wert) (Grund := Grund) (Form := Form)
          (neuBeendet s n E.etiketten)] else []), ¬ SchreibBeob x e :=
      keinSchreib_aus_filter_nil x (abschlussBeob_filter_nil (neuBeendet s n E.etiketten) x)
    have hcrash : HatAbsturz (if ∃ d, (neuBeendet s n E.etiketten d).isSome = true
        then [NiedrigesEreignis.ende (Ort := Ort) (Wert := Wert) (Grund := Grund) (Form := Form)
          (neuBeendet s n E.etiketten)] else []) = false :=
      abschlussBeob_keinCrash (neuBeendet s n E.etiketten)
    have hcrashNot : ¬ HatAbsturz (if ∃ d, (neuBeendet s n E.etiketten d).isSome = true
        then [NiedrigesEreignis.ende (Ort := Ort) (Wert := Wert) (Grund := Grund) (Form := Form)
          (neuBeendet s n E.etiketten)] else []) := by
      intro htrue
      rw [hcrash] at htrue
      cases htrue
    rw [SchreibSeitAbsturz_ohne_absturz x hcrashNot]
    rintro ⟨e, he, hs⟩
    exact hkein e he hs

end Gabbro.Core.Beobachtung
