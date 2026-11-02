module

public import Grammatik.Parser.Round.Rundlauf3.Teil5a
public import Grammatik.Parser.Round.Rundlauf2
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Round.Rundlauf3.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser
-- `sizeof`/`lenof` through `parsePrimary`: head word, place
-- through `parseOrt`, `)` close, type-word gate by lane 161's
-- `eingebaut_ein_ok`. One lemma for both spellings (the arms
-- differ only in the word).
theorem prim_emb1_legs : ∀ (w : String) (x : SExpr)
    (rest : List Token) (F : Nat),
    (w = "sizeof" ∨ w = "lenof") → gutKernPlatz x = true →
    (!istTypWortVar x) = true → ruhigSuff rest = true →
    12 * (groesse (.built w [x]) + 1) + groesse (.built w [x]) + 1 ≤ F →
    parsePrimary F (druckToks (.built w [x]) ++ rest) =
      .ok (.built w [x], rest) := by
  intro w x rest F hw hp htw hrs hF
  obtain rfl | rfl := hw
  · have hF1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, args_einzeln, List.cons_append, parsePrimary] at ⊢
    have hF2 : 1 ≤ F' := by omega
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    simp only [parseEingebaut_ein] at ⊢
    have hpx : gutPlatz x = true := gutPlatz_of_gutKernPlatz x hp
    have hFp : 12 * (groesse x + 1) + groesse x ≤ F'' := by
      simp only [groesse, groesseListe] at hF ⊢
      omega
    have hO := ort_legs_kern x ([.zeichen ")"] ++ rest) F'' hp
      (hrs_paren rest) hFp
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
    simp only [hO] at ⊢
    exact eingebaut_ein_ok "sizeof" x rest hpx htw
  · have hF1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, args_einzeln, List.cons_append, parsePrimary] at ⊢
    have hF2 : 1 ≤ F' := by omega
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    simp only [parseEingebaut_ein] at ⊢
    have hpx : gutPlatz x = true := gutPlatz_of_gutKernPlatz x hp
    have hFp : 12 * (groesse x + 1) + groesse x ≤ F'' := by
      simp only [groesse, groesseListe] at hF ⊢
      omega
    have hO := ort_legs_kern x ([.zeichen ")"] ++ rest) F'' hp
      (hrs_paren rest) hFp
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
    simp only [hO] at ⊢
    exact eingebaut_ein_ok "lenof" x rest hpx htw

-- `aligned` through `parsePrimary`: head word, two whole
-- expressions through `parseOr` with `,` and `)` separators
-- (the pair arm of `parseEingebaut`).
theorem prim_aligned_legs : ∀ (a b : SExpr)
    (rest : List Token) (F : Nat),
    Legs a → Legs b →
    ruhigSuff rest = true →
    12 * (groesse (.built "aligned" [a, b]) + 1) +
      groesse (.built "aligned" [a, b]) + 1 ≤ F →
    parsePrimary F (druckToks (.built "aligned" [a, b]) ++ rest) =
      .ok (.built "aligned" [a, b], rest) := by
  intro a b rest F hLa hLb hrs hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, args_cons, args_einzeln, List.cons_append,
    parsePrimary] at ⊢
  have hF2 : 1 ≤ F' := by omega
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [parseEingebaut_zwei] at ⊢
  -- First argument at `parseOr` with the `,` follow (all
  -- follows `rfl`); second with the `)` follow.
  have hkomma : ruhig ([.zeichen ","] ++ druckToks b ++
      ([.zeichen ")"] ++ rest)) = true := rfl
  have hskomma : ruhigSuff ([.zeichen ","] ++ druckToks b ++
      ([.zeichen ")"] ++ rest)) = true := rfl
  have hgkomma : ruhigGleit ([.zeichen ","] ++ druckToks b ++
      ([.zeichen ")"] ++ rest)) = true := rfl
  have hpos_a := groesse_pos a
  have hpos_b := groesse_pos b
  have hFa : 12 * (groesse a + 1) + groesse a + 8 ≤ F'' := by
    simp only [groesse, groesseListe] at hF ⊢
    omega
  have hOa := hLa.2.2.2.2.2.2.2 ([.zeichen ","] ++ druckToks b ++
    ([.zeichen ")"] ++ rest)) F'' hkomma hskomma hgkomma hFa
  have hFb : 12 * (groesse b + 1) + groesse b + 8 ≤ F'' := by
    simp only [groesse, groesseListe] at hF ⊢
    omega
  have hOb := hLb.2.2.2.2.2.2.2 ([.zeichen ")"] ++ rest) F''
    (hr_paren rest) (hrs_paren rest) (hrg_paren rest) hFb
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOa hOb
  simp only [hOa, hOb] at ⊢

-- Builtin tower from a primary leg: the `parseUnary`
-- fall-through on the `wort` head (no prefix arm fires), then
-- `tower_up`. One builder for all three builtins (the head
-- token is always `wort`, whatever the tail).
theorem embTower : ∀ (w : String) (xs : List SExpr),
    (∀ (rest' : List Token) (G : Nat), ruhigSuff rest' = true →
      ruhigGleit rest' = true →
      12 * (groesse (.built w xs) + 1) + groesse (.built w xs) + 1 ≤ G →
      parsePrimary G (druckToks (.built w xs) ++ rest') =
        .ok (.built w xs, rest')) →
    Legs (.built w xs) := by
  intro w xs hP
  have hU : ∀ (rest' : List Token) (G : Nat),
      ruhigSuff rest' = true → ruhigGleit rest' = true →
      12 * (groesse (.built w xs) + 1) + groesse (.built w xs) + 2 ≤ G →
      parseUnary G (druckToks (.built w xs) ++ rest') =
        .ok (.built w xs, rest') := by
    intro rest' G hrs hrg hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP rest' G' hrs hrg (by omega)
    have hd : druckToks (.built w xs) = [.wort w] ++
        (([.zeichen "("] ++ druckToksListe xs) ++ [.zeichen ")"]) := by
      simp only [druckToks, List.cons_append, List.nil_append]
    simp only [hd, List.append_assoc] at hP' ⊢
    simp only [List.cons_append, List.nil_append] at hP' ⊢
    simp only [parseUnary, hP'] at ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest' G hpf hrs hrg hG
    exact hP rest' G hrs hrg hG
  · intro rest' G hrs hrg hG
    exact hU rest' G hrs hrg hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.built w xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.built w xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.built w xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.built w xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.built w xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.built w xs) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.2 G hG

-- Builtin legs: each spelling over its payload legs.
theorem sizeofLegs : ∀ (x : SExpr),
    gutKernPlatz x = true → (!istTypWortVar x) = true →
    Legs (.built "sizeof" [x]) := by
  intro x hp htw
  apply embTower "sizeof" [x]
  intro rest' G hrs hrg hG
  exact prim_emb1_legs "sizeof" x rest' G (Or.inl rfl) hp htw hrs hG
theorem lenofLegs : ∀ (x : SExpr),
    gutKernPlatz x = true → (!istTypWortVar x) = true →
    Legs (.built "lenof" [x]) := by
  intro x hp htw
  apply embTower "lenof" [x]
  intro rest' G hrs hrg hG
  exact prim_emb1_legs "lenof" x rest' G (Or.inr rfl) hp htw hrs hG
theorem alignedLegs : ∀ (a b : SExpr),
    Legs a → Legs b → Legs (.built "aligned" [a, b]) := by
  intro a b hLa hLb
  apply embTower "aligned" [a, b]
  intro rest' G hrs hrg hG
  exact prim_aligned_legs a b rest' G hLa hLb hrs hG

-- Bridge for the calls predicate: calls are `gut` (via the
-- argument-list bridge).
theorem gut_of_gutRuf : ∀ (e : SExpr), gutRuf e = true → gut e = true := by
  intro e hg
  simp only [gutRuf, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · exact gut_of_gutAM e hold
  · cases e with
    | lit m => simp only [rufNeu, Bool.false_eq_true] at hnew
    | float s => simp only [rufNeu, Bool.false_eq_true] at hnew
    | tru => simp only [rufNeu, Bool.false_eq_true] at hnew
    | fls => simp only [rufNeu, Bool.false_eq_true] at hnew
    | «variable» s => simp only [rufNeu, Bool.false_eq_true] at hnew
    | un o x => simp only [rufNeu, Bool.false_eq_true] at hnew
    | bin o l r => simp only [rufNeu, Bool.false_eq_true] at hnew
    | field x f => simp only [rufNeu, Bool.false_eq_true] at hnew
    | index x i => simp only [rufNeu, Bool.false_eq_true] at hnew
    | arrow x f => simp only [rufNeu, Bool.false_eq_true] at hnew
    | call f xs =>
      simp only [rufNeu, Bool.and_eq_true] at hnew
      obtain ⟨hf, hxs⟩ := hnew
      have hgl := gutListe_of_gutListeAM xs hxs
      simp only [gut, Bool.and_eq_true] at ⊢
      exact ⟨hf, hgl⟩
    | fnref f => simp only [rufNeu, Bool.false_eq_true] at hnew
    | built f xs => simp only [rufNeu, Bool.false_eq_true] at hnew
    | old x => simp only [rufNeu, Bool.false_eq_true] at hnew
    | res => simp only [rufNeu, Bool.false_eq_true] at hnew
    | why g f => simp only [rufNeu, Bool.false_eq_true] at hnew
    | ext xk xn xs => simp only [rufNeu, Bool.false_eq_true] at hnew

-- The three new builtin layers: `sizeof`/`lenof` over kernel
-- places (minus bare type words), `aligned` over level-4
-- trees. Word lawfulness as `strEq` so both directions split
-- mechanically. The list payloads live in their own defs:
-- NESTED list patterns (`.built w [x]`) generate equation
-- lemmas that `simp` never fires on (measured: 74 "made no
-- progress"), while one-level patterns reduce like `gutKern`.
def argsPlatz1 : List SExpr → Bool
  | [x] => gutKernPlatz x && (!istTypWortVar x)
  | _ => false
def argsRuf2 : List SExpr → Bool
  | [a, b] => gutRuf a && gutRuf b
  | _ => false
def sizeofNeu : SExpr → Bool
  | .built w xs => strEq w "sizeof" && argsPlatz1 xs
  | _ => false
def lenofNeu : SExpr → Bool
  | .built w xs => strEq w "lenof" && argsPlatz1 xs
  | _ => false
def alignedNeu : SExpr → Bool
  | .built w xs => strEq w "aligned" && argsRuf2 xs
  | _ => false

-- Level-5 predicate: level 4 plus one builtin layer each.
def gutEmb (e : SExpr) : Bool :=
  gutRuf e || sizeofNeu e || lenofNeu e || alignedNeu e

end Gabbro.Grammatik.Parser
