module

public import Grammatik.Parser.Round.Rundlauf2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Round.Rundlauf3.Teil5

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- Every level-5 tree has legs.
theorem legsEmb : ∀ (e : SExpr), gutEmb e = true → Legs e := by
  intro e hg
  simp only [gutEmb, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · obtain hold3 | hsz := hold
    · obtain hold2 | hlen := hold3
      · exact legsRuf e hold2
      · cases e with
        | lit m => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | float s => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | tru => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | fls => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | «variable» s => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | un o x => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | bin o l r => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | field x f => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | index x i => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | arrow x f => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | call f xs => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | fnref f => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | built f xs =>
          simp only [sizeofNeu, Bool.and_eq_true] at hlen
          obtain ⟨hw, hargs⟩ := hlen
          cases xs with
          | nil => simp only [argsPlatz1, Bool.false_eq_true] at hargs
          | cons y ys =>
            cases ys with
            | nil =>
              simp only [argsPlatz1, Bool.and_eq_true] at hargs
              obtain ⟨hp, htw⟩ := hargs
              have heq : f = "sizeof" := strKlingt f "sizeof" hw
              subst heq
              exact sizeofLegs y hp htw
            | cons z zs => simp only [argsPlatz1, Bool.false_eq_true] at hargs
        | old x => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | res => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | why g f => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | ext xk xn xs => simp only [sizeofNeu, Bool.false_eq_true] at hlen
    · cases e with
      | lit m => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | float s => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | tru => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | fls => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | «variable» s => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | un o x => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | bin o l r => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | field x f => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | index x i => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | arrow x f => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | call f xs => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | fnref f => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | built f xs =>
        simp only [lenofNeu, Bool.and_eq_true] at hsz
        obtain ⟨hw, hargs⟩ := hsz
        cases xs with
        | nil => simp only [argsPlatz1, Bool.false_eq_true] at hargs
        | cons y ys =>
          cases ys with
          | nil =>
            simp only [argsPlatz1, Bool.and_eq_true] at hargs
            obtain ⟨hp, htw⟩ := hargs
            have heq : f = "lenof" := strKlingt f "lenof" hw
            subst heq
            exact lenofLegs y hp htw
          | cons z zs => simp only [argsPlatz1, Bool.false_eq_true] at hargs
      | old x => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | res => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | why g f => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | ext xk xn xs => simp only [lenofNeu, Bool.false_eq_true] at hsz
  · cases e with
    | lit m => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | float s => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | tru => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | fls => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | «variable» s => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | un o x => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | bin o l r => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | field x f => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | index x i => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | arrow x f => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | call f xs => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | fnref f => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | built f xs =>
      simp only [alignedNeu, Bool.and_eq_true] at hnew
      obtain ⟨hw, hargs⟩ := hnew
      cases xs with
      | nil => simp only [argsRuf2, Bool.false_eq_true] at hargs
      | cons y ys =>
        cases ys with
        | nil => simp only [argsRuf2, Bool.false_eq_true] at hargs
        | cons z zs =>
          cases zs with
          | nil =>
            simp only [argsRuf2, Bool.and_eq_true] at hargs
            obtain ⟨ha, hb⟩ := hargs
            have heq : f = "aligned" := strKlingt f "aligned" hw
            subst heq
            exact alignedLegs y z (legsRuf y ha) (legsRuf z hb)
          | cons w2 ws => simp only [argsRuf2, Bool.false_eq_true] at hargs
    | old x => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | res => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | why g f => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | ext xk xn xs => simp only [alignedNeu, Bool.false_eq_true] at hnew

-- Bridge for the builtins predicate (via lane 161's shape
-- equations `gut_sizeof_one`, `gut_lenof_one`,
-- `gut_aligned_two`).
theorem gut_of_gutEmb : ∀ (e : SExpr), gutEmb e = true → gut e = true := by
  intro e hg
  simp only [gutEmb, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · obtain hold3 | hsz := hold
    · obtain hold2 | hlen := hold3
      · exact gut_of_gutRuf e hold2
      · cases e with
        | lit m => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | float s => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | tru => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | fls => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | «variable» s => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | un o x => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | bin o l r => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | field x f => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | index x i => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | arrow x f => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | call f xs => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | fnref f => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | built f xs =>
          simp only [sizeofNeu, Bool.and_eq_true] at hlen
          obtain ⟨hw, hargs⟩ := hlen
          cases xs with
          | nil => simp only [argsPlatz1, Bool.false_eq_true] at hargs
          | cons y ys =>
            cases ys with
            | nil =>
              simp only [argsPlatz1, Bool.and_eq_true] at hargs
              obtain ⟨hp, htw⟩ := hargs
              have heq : f = "sizeof" := strKlingt f "sizeof" hw
              subst heq
              rw [gut_sizeof_one]
              simp only [Bool.and_eq_true]
              exact ⟨gutPlatz_of_gutKernPlatz y hp, htw⟩
            | cons z zs => simp only [argsPlatz1, Bool.false_eq_true] at hargs
        | old x => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | res => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | why g f => simp only [sizeofNeu, Bool.false_eq_true] at hlen
        | ext xk xn xs => simp only [sizeofNeu, Bool.false_eq_true] at hlen
    · cases e with
      | lit m => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | float s => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | tru => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | fls => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | «variable» s => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | un o x => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | bin o l r => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | field x f => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | index x i => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | arrow x f => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | call f xs => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | fnref f => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | built f xs =>
        simp only [lenofNeu, Bool.and_eq_true] at hsz
        obtain ⟨hw, hargs⟩ := hsz
        cases xs with
        | nil => simp only [argsPlatz1, Bool.false_eq_true] at hargs
        | cons y ys =>
          cases ys with
          | nil =>
            simp only [argsPlatz1, Bool.and_eq_true] at hargs
            obtain ⟨hp, htw⟩ := hargs
            have heq : f = "lenof" := strKlingt f "lenof" hw
            subst heq
            rw [gut_lenof_one]
            simp only [Bool.and_eq_true]
            exact ⟨gutPlatz_of_gutKernPlatz y hp, htw⟩
          | cons z zs => simp only [argsPlatz1, Bool.false_eq_true] at hargs
      | old x => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | res => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | why g f => simp only [lenofNeu, Bool.false_eq_true] at hsz
      | ext xk xn xs => simp only [lenofNeu, Bool.false_eq_true] at hsz
  · cases e with
    | lit m => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | float s => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | tru => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | fls => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | «variable» s => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | un o x => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | bin o l r => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | field x f => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | index x i => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | arrow x f => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | call f xs => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | fnref f => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | built f xs =>
      simp only [alignedNeu, Bool.and_eq_true] at hnew
      obtain ⟨hw, hargs⟩ := hnew
      cases xs with
      | nil => simp only [argsRuf2, Bool.false_eq_true] at hargs
      | cons y ys =>
        cases ys with
        | nil => simp only [argsRuf2, Bool.false_eq_true] at hargs
        | cons z zs =>
          cases zs with
          | nil =>
            simp only [argsRuf2, Bool.and_eq_true] at hargs
            obtain ⟨ha, hb⟩ := hargs
            have heq : f = "aligned" := strKlingt f "aligned" hw
            subst heq
            rw [gut_aligned_two]
            simp only [Bool.and_eq_true]
            exact ⟨gut_of_gutRuf y ha, gut_of_gutRuf z hb⟩
          | cons w2 ws => simp only [argsRuf2, Bool.false_eq_true] at hargs
    | old x => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | res => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | why g f => simp only [alignedNeu, Bool.false_eq_true] at hnew
    | ext xk xn xs => simp only [alignedNeu, Bool.false_eq_true] at hnew

-- Level-5 goal: every `gutEmb` tree parses back from its
-- printed tokens with `brennstoff` fuel.
theorem parse_druck_emb : ∀ (e : SExpr), gutEmb e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) =
      .ok (e, [.ende]) := by
  intro e hg
  have hL := legsEmb e hg
  have hr : ruhig [.ende] = true := rfl
  have hrs : ruhigSuff [.ende] = true := rfl
  have hrg : ruhigGleit [.ende] = true := rfl
  have hF : 12 * (groesse e + 1) + groesse e + 8 ≤ brennstoff e := by
    simp only [brennstoff, Std.le_refl]
  exact hL.2.2.2.2.2.2.2 [.ende] (brennstoff e) hr hrs hrg hF

-- Level-5 witnesses, corpus-flavoured (`02-geraet` and
-- `04-schleifen` measure with `sizeof`/`lenof`; alignment
-- pairs bound buffers): each as a `parse_druck_emb` instance
-- and a kernel-computed `match` check.
theorem zeuge_sizeof :
    parseOr (brennstoff (.built "sizeof" [.variable "x"]))
    (druckToks (.built "sizeof" [.variable "x"]) ++ [.ende]) =
      .ok (.built "sizeof" [.variable "x"], [.ende]) :=
  parse_druck_emb _ (by decide)
theorem zeuge_sizeof_rech : (match parseOr
    (brennstoff (.built "sizeof" [.variable "x"]))
    (druckToks (.built "sizeof" [.variable "x"]) ++ [.ende]) with
    | .ok (.built "sizeof" [.variable "x"], [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_lenof :
    parseOr (brennstoff (.built "lenof" [.field (.variable "m") "slots"]))
    (druckToks (.built "lenof" [.field (.variable "m") "slots"]) ++ [.ende]) =
      .ok (.built "lenof" [.field (.variable "m") "slots"], [.ende]) :=
  parse_druck_emb _ (by decide)
theorem zeuge_lenof_rech : (match parseOr
    (brennstoff (.built "lenof" [.field (.variable "m") "slots"]))
    (druckToks (.built "lenof" [.field (.variable "m") "slots"]) ++ [.ende]) with
    | .ok (.built "lenof" [.field (.variable "m") "slots"], [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_aligned :
    parseOr (brennstoff (.built "aligned" [.variable "a", .lit 8]))
    (druckToks (.built "aligned" [.variable "a", .lit 8]) ++ [.ende]) =
      .ok (.built "aligned" [.variable "a", .lit 8], [.ende]) :=
  parse_druck_emb _ (by decide)
theorem zeuge_aligned_rech : (match parseOr
    (brennstoff (.built "aligned" [.variable "a", .lit 8]))
    (druckToks (.built "aligned" [.variable "a", .lit 8]) ++ [.ende]) with
    | .ok (.built "aligned" [.variable "a", .lit 8], [.ende]) => true
    | _ => false) = true := by
  decide

end Gabbro.Grammatik.Parser
