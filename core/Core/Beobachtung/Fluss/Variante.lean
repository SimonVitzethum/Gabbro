module

public import Core.Beobachtung.Fluss.Fragment

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Fragment Befehl)

def VarianteNIAussage : Prop :=
  FamilienNI .variante

/-- A context step of a source form takes the internal plan, which records no memory access
    and no outside action, and changes only the local frame. Such a step emits no low event. -/
private theorem fragment_kontext_schritt_still
    (p : Fragment) (plattform : Plattform)
    {ρ : Lauf (p.einheit plattform)} {predictor t c w spur}
    (tick : ρ.zeit.spur t = some (.kontext c w, spur)) :
    schrittBeob ρ predictor t = [] := by
  classical
  cases spur with
  | mk speicher aussen =>
    have recorded := ρ.zeit.takt t
    generalize hS : ρ.zeit.zustand t = sOpt at recorded
    generalize hN : ρ.zeit.zustand (t + 1) = nOpt at recorded
    cases recorded with
    | wartet label _ _ =>
      cases label.symm.trans tick
    | schritt label transition =>
      rw [tick] at label
      injection label with evEq
      subst evEq
      cases transition with
      | schritt impl =>
        rename_i s0 n0
        cases impl with
        | kontext _ _ regel aus =>
          unfold System.ImplSchritt at regel
          rcases regel with ⟨b, kopfB, implB⟩
          change (Befehl.regel b).impl c s0 w _ _ at implB
          simp only [Befehl.regel, Befehl.impl] at implB
          rcases implB with ⟨planEq, frameEq⟩
          injection planEq with hplan
          subst hplan
          subst frameEq
          unfold FuehrtSchrittAus at aus
          rcases aus with ⟨_, _, sperren, v, fuehrtAus, speicherfolge, nEqState⟩
          change FuehrtAus (p.einheit plattform).einrichtung t c s0 (b.nach c s0) .intern
            sperren aussen v at fuehrtAus
          cases fuehrtAus
          simp only [List.nil_append, List.append_nil, List.map_nil, List.filter_nil] at speicherfolge
          generalize hGraph : n0.graph = gEnd at speicherfolge
          cases speicherfolge
          have nEqFrame : n0 = b.nach c s0 := by
            rw [nEqState, hGraph]
            rfl
          have nBuchung : n0.buchung = s0.buchung := by
            rw [nEqFrame]
            rfl
          have hStatus : ∀ d, n0.status d = s0.status d := by
            intro d
            rw [nEqFrame]
            rfl
          have hCommit : commitBeob (Form := Befehl) (p.einheit plattform).katalog.plattform s0 n0 = [] := by
            rw [commitBeob, nBuchung, List.drop_length, List.filterMap_nil]
          have hAusgabe : ausgabeBeob (p.einheit plattform) c (s0.lokal c) (n0.lokal c) = [] := by
            rfl
          have hZeit : zeitBeob ρ c (s0.lokal c) (n0.lokal c) = [] := by
            rfl
          have hKontext : kontextBeob ρ predictor t c s0 n0 ⟨[], []⟩ = [] := by
            rw [kontextBeob]
            dsimp only
            rw [hCommit, hAusgabe, hZeit, kopfB]
            have hSpek : (p.einheit plattform).katalog.plattform.spekulationshuelle.zugriffe
                ((p.einheit plattform).fluss.spekulativ b (s0.lokal c) predictor) = [] := by
              cases plattform <;> rfl
            have hKonstant : (p.einheit plattform).fluss.konstantzeit b = false := by
              rfl
            simp only [hSpek, hKonstant, Bool.false_eq_true, if_false, List.map_nil,
              List.nil_append, List.append_nil]
          have hEnde : ∀ d, (neuBeendet s0 n0 (p.einheit plattform).etiketten d).isSome = false := by
            intro d
            rw [neuBeendet, hStatus d]
            cases hst : s0.status d <;> rfl
          have hKeinEnde : ¬ ∃ d, (neuBeendet s0 n0 (p.einheit plattform).etiketten d).isSome = true := by
            rintro ⟨d, hd⟩
            rw [hEnde d] at hd
            cases hd
          rw [schrittBeob, tick, hS, hN]
          simp only [List.filterMap_nil, List.flatMap_nil, List.nil_append, hKontext,
            hKeinEnde, if_false]

theorem varianteNI : VarianteNIAussage := by
  intro p plattform f familie fluss
  intro h₁ h₂ ρ₁ ρ₂ vergleich predictor t c w spur vor vorEq kopf tick abgedeckt
  exact stummer_schritt_deckt (fragment_kontext_schritt_still p plattform tick) abgedeckt

end Gabbro.Core.Beobachtung
