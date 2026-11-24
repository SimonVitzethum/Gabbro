module

public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl)

def AggregatNIAussage : Prop :=
  FamilienNI .aggregat

private theorem zugriffe_leer {Ort : Type} (h : Spekulationshuelle) :
    h.zugriffe ([] : List (Option Ort)) = [] := by
  cases h with
  | mk fenster =>
    cases fenster <;> simp only [Spekulationshuelle.zugriffe, List.take_nil, List.filterMap_nil]

theorem aggregatNI : AggregatNIAussage := by
  classical
  intro p plattform f _ _ h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor
    zustand kopf spurGlied abgedeckt
  refine stummer_schritt_deckt ?_ abgedeckt
  have takt := ρ₁.zeit.takt t
  rw [spurGlied, zustand] at takt
  generalize nachEq : ρ₁.zeit.zustand (t + 1) = nach at takt
  cases takt with
  | wartet unmoeglich _ _ => cases unmoeglich
  | schritt label transition =>
    cases label
    cases transition with
    | schritt step =>
      cases step with
      | kontext _ _ regel aus =>
        obtain ⟨f', kopf', implRegel⟩ := regel
        have ff : f' = f := Option.some.inj (kopf'.symm.trans kopf)
        subst f'
        obtain ⟨spurEq, nachGlied⟩ := Befehl.vollzug_genau (w := w) f implRegel aus
        subst spur
        have zustandNach : ρ₁.zeit.zustand (t + 1) = some (f.nach c vor) := by
          rw [nachEq, nachGlied]
        have kontextLeer :
            kontextBeob ρ₁ predictor t c vor (f.nach c vor) ⟨[], []⟩ = [] := by
          rw [kontextBeob, kopf]
          simp only [Fragment.einheit, Ast.Semantik.fragmentFlussdaten,
            Schrankendaten.leer,
            commitBeob, Befehl.nach, List.drop_length, List.filterMap_nil,
            ausgabeBeob, Flussdaten.ausgabeZuwachs, List.filter_nil, List.map_nil,
            zeitBeob, zugriffe_leer, List.nil_append, Bool.false_eq_true, if_false]
        have endeLeer : ∀ d, neuBeendet vor (f.nach c vor) (p.einheit plattform).etiketten d = none := by
          intro d
          cases hs : vor.status d <;> simp only [neuBeendet, Befehl.nach, hs]
        have keinEnde :
            ¬ ∃ d, (neuBeendet vor (f.nach c vor) (p.einheit plattform).etiketten d).isSome = true := by
          rintro ⟨d, hd⟩
          rw [endeLeer d] at hd
          cases hd
        have abschlussLeer :
            (if ∃ d, (neuBeendet vor (f.nach c vor) (p.einheit plattform).etiketten d).isSome = true
             then [NiedrigesEreignis.ende (neuBeendet vor (f.nach c vor) (p.einheit plattform).etiketten)]
             else []) =
              ([] : List (NiedrigesEreignis Ast.Semantik.Zelle Int PUnit Befehl)) := by
          rw [if_neg keinEnde]
        simp only [schrittBeob, spurGlied, zustand, zustandNach,
          List.filterMap_nil, List.flatMap_nil, List.nil_append, kontextLeer]
        exact abschlussLeer

end Gabbro.Core.Beobachtung
