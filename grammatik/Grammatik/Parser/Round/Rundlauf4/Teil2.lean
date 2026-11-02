module

public import Grammatik.Parser.Round.Rundlauf3
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Round.Rundlauf4.Teil1
public import Grammatik.Parser.Round.Rundlauf4.Teil1a

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- Bridge for the `grund` layer (exactly `gut`'s side
-- conditions; stepwise `obtain` -- the flattened four-pattern
-- misfires on the `!`-component, measured in `legsGrund`).
theorem gut_of_grundNeu : ∀ (e : SExpr),
    grundNeu e = true → gut e = true := by
  intro e hg
  cases e with
  | lit m => simp only [grundNeu, Bool.false_eq_true] at hg
  | float s => simp only [grundNeu, Bool.false_eq_true] at hg
  | tru => simp only [grundNeu, Bool.false_eq_true] at hg
  | fls => simp only [grundNeu, Bool.false_eq_true] at hg
  | «variable» s => simp only [grundNeu, Bool.false_eq_true] at hg
  | un o x => simp only [grundNeu, Bool.false_eq_true] at hg
  | bin o l r => simp only [grundNeu, Bool.false_eq_true] at hg
  | field x f => simp only [grundNeu, Bool.false_eq_true] at hg
  | index x i => simp only [grundNeu, Bool.false_eq_true] at hg
  | arrow x f => simp only [grundNeu, Bool.false_eq_true] at hg
  | call f xs => simp only [grundNeu, Bool.false_eq_true] at hg
  | fnref f => simp only [grundNeu, Bool.false_eq_true] at hg
  | built f xs => simp only [grundNeu, Bool.false_eq_true] at hg
  | old x => simp only [grundNeu, Bool.false_eq_true] at hg
  | res => simp only [grundNeu, Bool.false_eq_true] at hg
  | why g f =>
    simp only [grundNeu, Bool.and_eq_true] at hg
    obtain ⟨hABC, hself⟩ := hg
    obtain ⟨hAB, hzuk⟩ := hABC
    obtain ⟨hkp, hit⟩ := hAB
    simp only [gut, Bool.and_eq_true] at ⊢
    exact ⟨⟨⟨hkp, hit⟩, hzuk⟩, hself⟩
  | ext xk xn xs => simp only [grundNeu, Bool.false_eq_true] at hg

-- Bridge for the level-6 predicate (via the four layer
-- bridges above).
theorem gut_of_gutPrim : ∀ (e : SExpr),
    gutPrim e = true → gut e = true := by
  intro e hg
  simp only [gutPrim, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · exact gut_of_gutEmb e hold
  · simp only [primNeu, Bool.or_eq_true] at hnew
    obtain h123 | h4 := hnew
    · obtain h12 | h3 := h123
      · obtain h1 | h2 := h12
        · exact gut_of_altNeu e h1
        · exact gut_of_ergebnisNeu e h2
      · exact gut_of_fnwertNeu e h3
    · exact gut_of_grundNeu e h4

-- Level-6 witnesses, corpus-flavoured (`35-tausch` reads
-- `old(BESITZER)`; `06-annahmen` ensures over `result`;
-- `111-rufzulassung` passes `&hart_senden`): each as a
-- `parse_druck_prim` instance and a kernel-computed `match`
-- check. No two-segment `G::F` occurs in the corpus, so the
-- `grund` witness is neutrally named.
theorem zeuge_alt :
    parseOr (brennstoff (.old (.variable "BESITZER")))
    (druckToks (.old (.variable "BESITZER")) ++ [.ende]) =
      .ok (.old (.variable "BESITZER"), [.ende]) :=
  parse_druck_prim _ (by decide)
theorem zeuge_alt_rech : (match parseOr
    (brennstoff (.old (.variable "BESITZER")))
    (druckToks (.old (.variable "BESITZER")) ++ [.ende]) with
    | .ok (.old (.variable "BESITZER"), [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_ergebnis :
    parseOr (brennstoff .res)
    (druckToks .res ++ [.ende]) =
      .ok (.res, [.ende]) :=
  parse_druck_prim _ (by decide)
theorem zeuge_ergebnis_rech : (match parseOr
    (brennstoff .res)
    (druckToks .res ++ [.ende]) with
    | .ok (.res, [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_fnwert :
    parseOr (brennstoff (.fnref "hart_senden"))
    (druckToks (.fnref "hart_senden") ++ [.ende]) =
      .ok (.fnref "hart_senden", [.ende]) :=
  parse_druck_prim _ (by decide)
theorem zeuge_fnwert_rech : (match parseOr
    (brennstoff (.fnref "hart_senden"))
    (druckToks (.fnref "hart_senden") ++ [.ende]) with
    | .ok (.fnref "hart_senden", [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_grund :
    parseOr (brennstoff (.why "T" "x"))
    (druckToks (.why "T" "x") ++ [.ende]) =
      .ok (.why "T" "x", [.ende]) :=
  parse_druck_prim _ (by decide)
theorem zeuge_grund_rech : (match parseOr
    (brennstoff (.why "T" "x"))
    (druckToks (.why "T" "x") ++ [.ende]) with
    | .ok (.why "T" "x", [.ende]) => true
    | _ => false) = true := by
  decide

end Gabbro.Grammatik.Parser
