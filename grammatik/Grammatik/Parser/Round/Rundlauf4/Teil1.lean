/-
  File:      Grammatik/Parser/Rundlauf4.lean
  Subject:   T3 (lane 195): the remaining primaries -- level 6.

  Rundlauf3 closes at level 5 (`gutEmb`: kernel, comparisons,
  bits, add/mul spellings, calls, builtins). MUSE-REPORT-172
  "Open" lists what is left per constructor: `alt`, `res`,
  `fnref`, `grund` ("single-constructor primaries, small, not
  started") and statements (`SAnw`, untouched -- NOT this file).

  This file takes the four primaries, each as one new layer over
  the previous predicate, in the established one-level pattern
  (no nested list patterns -- MUSE-REPORT-172 finding 3):

  - `altNeu`: `.old x` over KERNEL places (`gutKernPlatz`, the
    `sizeof` precedent). Full `gutPlatz` payloads carry arbitrary
    `gut` index expressions and need the joint size induction
    (Rundlauf3 header: the exact remaining blocker).
  - `ergebnisNeu`: `.res`, no payload (lane 161's
    `prim_ergebnis`, reused).
  - `fnwertNeu`: `.fnref p`, no tree payload. `primFrei` is
    false, so there is no primary leg -- the leg below is at
    `parseUnary` (`&` arm, segments stop by `sammleSeg_stop`
    under `ruhigSuff`).
  - `grundNeu`: `.why g f` with exactly `gut`'s side
    conditions (lane 161's `prim_grund`, reused).

  `gutPrim e = gutEmb e || primNeu e`; `parse_druck_prim` is the
  level-6 goal. Statements are NOT entered here.
-/
module

public import Grammatik.Parser.Round.Rundlauf3
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic

@[expose] public section



namespace Gabbro.Grammatik.Parser

-- The four new primary layers, one level each.
def altNeu : SExpr → Bool
  | .old x => gutKernPlatz x
  | _ => false
def ergebnisNeu : SExpr → Bool
  | .res => true
  | _ => false
def fnwertNeu : SExpr → Bool
  | .fnref _ => true
  | _ => false
def grundNeu : SExpr → Bool
  | .why g _ =>
    !istKopfWort g && !istIntWort g && !istZuckerBreite g &&
      !strEq g "Self"
  | _ => false

-- The new primary layer: one of the four above.
def primNeu (e : SExpr) : Bool :=
  altNeu e || ergebnisNeu e || fnwertNeu e || grundNeu e

-- Level-6 predicate: level 5 plus one primary layer.
def gutPrim (e : SExpr) : Bool := gutEmb e || primNeu e

-- `old` through `parsePrimary`: head word, kernel place through
-- `parseOrt` (`ort_legs_kern`), `)` close. Mirror of lane 161's
-- `prim_alt` with `R n` replaced by the kernel-place leg (no
-- size bound needed anywhere), and of `prim_emb1_legs` minus
-- the type-word gate (`old` takes any place).
theorem prim_alt_legs : ∀ (x : SExpr) (rest : List Token) (F : Nat),
    gutKernPlatz x = true → ruhigSuff rest = true →
    12 * (groesse (.old x) + 1) + groesse (.old x) + 1 ≤ F →
    parsePrimary F (druckToks (.old x) ++ rest) =
      .ok (.old x, rest) := by
  intro x rest F hp hrs hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, List.nil_append,
    parsePrimary] at ⊢
  have hFp : 12 * (groesse x + 1) + groesse x ≤ F' := by
    simp only [groesse] at hF ⊢
    omega
  have hO := ort_legs_kern x ([.zeichen ")"] ++ rest) F' hp
    (hrs_paren rest) hFp
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
  simp only [hO] at ⊢

-- `&p` through `parseUnary`: the `&` arm reads one name, stops
-- the segments by `sammleSeg_stop` (the follow is `ruhigSuff`),
-- and the singleton intercalate is the name back.
theorem un_fnwert_legs : ∀ (p : String) (rest : List Token) (F : Nat),
    ruhigSuff rest = true →
    12 * (groesse (.fnref p) + 1) + groesse (.fnref p) + 2 ≤ F →
    parseUnary F (druckToks (.fnref p) ++ rest) =
      .ok (.fnref p, rest) := by
  intro p rest F hrs hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, List.nil_append,
    parseUnary, nameText_nameTok] at ⊢
  rw [sammleSeg_stop [p] rest hrs] at ⊢
  simp only [String.intercalate_singleton]

-- Primary tower from a `wort`-headed print: the `parseUnary`
-- fall-through (no prefix arm fires on `wort`), then `tower_up`.
-- Generalises lane 179's `embTower` (whose head is always
-- `wort`, whatever the tail).
theorem wortTurm : ∀ (w : String) {S : List Token} (e : SExpr),
    druckToks e = [.wort w] ++ S →
    (∀ (rest' : List Token) (G : Nat), ruhigSuff rest' = true →
      ruhigGleit rest' = true →
      12 * (groesse e + 1) + groesse e + 1 ≤ G →
      parsePrimary G (druckToks e ++ rest') = .ok (e, rest')) →
    Legs e := by
  intro w S e hd hP
  have hU : ∀ (rest' : List Token) (G : Nat),
      ruhigSuff rest' = true → ruhigGleit rest' = true →
      12 * (groesse e + 1) + groesse e + 2 ≤ G →
      parseUnary G (druckToks e ++ rest') = .ok (e, rest') := by
    intro rest' G hrs hrg hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP rest' G' hrs hrg (by omega)
    simp only [hd, List.append_assoc] at hP' ⊢
    simp only [List.cons_append, List.nil_append] at hP' ⊢
    simp only [parseUnary, hP'] at ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest' G hpf hrs hrg hG
    exact hP rest' G hrs hrg hG
  · intro rest' G hrs hrg hG
    exact hU rest' G hrs hrg hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.2 G hG

-- Primary tower from an `ident`-headed print: same fall-through
-- (no prefix arm fires on `ident`), then `tower_up`. The
-- `ruf` level inlines this shape (`rufLegs`); here it is shared
-- by `grund`.
theorem identTurm : ∀ (g : String) {S : List Token} (e : SExpr),
    druckToks e = [nameTok g] ++ S →
    (∀ (rest' : List Token) (G : Nat), ruhigSuff rest' = true →
      ruhigGleit rest' = true →
      12 * (groesse e + 1) + groesse e + 1 ≤ G →
      parsePrimary G (druckToks e ++ rest') = .ok (e, rest')) →
    Legs e := by
  intro g S e hd hP
  have hU : ∀ (rest' : List Token) (G : Nat),
      ruhigSuff rest' = true → ruhigGleit rest' = true →
      12 * (groesse e + 1) + groesse e + 2 ≤ G →
      parseUnary G (druckToks e ++ rest') = .ok (e, rest') := by
    intro rest' G hrs hrg hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP rest' G' hrs hrg (by omega)
    simp only [hd, List.append_assoc] at hP' ⊢
    simp only [List.cons_append, List.nil_append] at hP' ⊢
    rw [parseUnary_nameTok, hP']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest' G hpf hrs hrg hG
    exact hP rest' G hrs hrg hG
  · intro rest' G hrs hrg hG
    exact hU rest' G hrs hrg hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up e rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.2 G hG

-- `old` legs over a kernel place.
theorem altLegs : ∀ (x : SExpr),
    gutKernPlatz x = true → Legs (.old x) := by
  intro x hp
  have hd : druckToks (.old x) = [.wort "old"] ++
      (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
    simp only [druckToks, List.cons_append, List.nil_append]
  apply wortTurm _ _ hd
  intro rest' G hrs hrg hG
  exact prim_alt_legs x rest' G hp hrs hG

-- `result` legs (primary leg by lane 161's `prim_ergebnis`).
theorem ergebnisLegs : Legs .res := by
  have hd : druckToks .res = [.wort "result"] ++ [] := by
    simp only [druckToks, List.append_nil]
  apply wortTurm _ _ hd
  intro rest' G hrs hrg hG
  exact prim_ergebnis rest' G (by omega)

end Gabbro.Grammatik.Parser
