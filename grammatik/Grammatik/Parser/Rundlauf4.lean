/-
  File:      Grammatik/Parser/Rundlauf4.lean
  Subject:   T3 (lane 195): the remaining primaries -- level 6.

  Rundlauf3 closes at level 5 (`gutEmb`: kernel, comparisons,
  bits, add/mul spellings, calls, builtins). MUSE-REPORT-172
  "Open" lists what is left per constructor: `alt`, `ergebnis`,
  `fnwert`, `grund` ("single-constructor primaries, small, not
  started") and statements (`SAnw`, untouched -- NOT this file).

  This file takes the four primaries, each as one new layer over
  the previous predicate, in the established one-level pattern
  (no nested list patterns -- MUSE-REPORT-172 finding 3):

  - `altNeu`: `.alt x` over KERNEL places (`gutKernPlatz`, the
    `sizeof` precedent). Full `gutPlatz` payloads carry arbitrary
    `gut` index expressions and need the joint size induction
    (Rundlauf3 header: the exact remaining blocker).
  - `ergebnisNeu`: `.ergebnis`, no payload (lane 161's
    `prim_ergebnis`, reused).
  - `fnwertNeu`: `.fnwert p`, no tree payload. `primFrei` is
    false, so there is no primary leg -- the leg below is at
    `parseUnary` (`&` arm, segments stop by `sammleSeg_stop`
    under `ruhigSuff`).
  - `grundNeu`: `.grund g f` with exactly `gut`'s side
    conditions (lane 161's `prim_grund`, reused).

  `gutPrim e = gutEmb e || primNeu e`; `parse_druck_prim` is the
  level-6 goal. Statements are NOT entered here.
-/
import Grammatik.Parser.Rundlauf3

namespace Gabbro.Grammatik.Parser

-- The four new primary layers, one level each.
def altNeu : SExpr → Bool
  | .alt x => gutKernPlatz x
  | _ => false
def ergebnisNeu : SExpr → Bool
  | .ergebnis => true
  | _ => false
def fnwertNeu : SExpr → Bool
  | .fnwert _ => true
  | _ => false
def grundNeu : SExpr → Bool
  | .grund g _ =>
    !istKeinPlatz g && !istIntWort g && !istZuckerBreite g &&
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
    12 * (groesse (.alt x) + 1) + groesse (.alt x) + 1 ≤ F →
    parsePrimary F (druckToks (.alt x) ++ rest) =
      .ok (.alt x, rest) := by
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
    12 * (groesse (.fnwert p) + 1) + groesse (.fnwert p) + 2 ≤ F →
    parseUnary F (druckToks (.fnwert p) ++ rest) =
      .ok (.fnwert p, rest) := by
  intro p rest F hrs hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, List.nil_append,
    parseUnary] at ⊢
  simp only [nameText] at ⊢
  rw [sammleSeg_stop [p] rest hrs] at ⊢
  simp

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
    druckToks e = [.ident g] ++ S →
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

-- `old` legs over a kernel place.
theorem altLegs : ∀ (x : SExpr),
    gutKernPlatz x = true → Legs (.alt x) := by
  intro x hp
  have hd : druckToks (.alt x) = [.wort "old"] ++
      (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
    simp [druckToks]
  apply wortTurm _ _ hd
  intro rest' G hrs hrg hG
  exact prim_alt_legs x rest' G hp hrs hG

-- `result` legs (primary leg by lane 161's `prim_ergebnis`).
theorem ergebnisLegs : Legs .ergebnis := by
  have hd : druckToks .ergebnis = [.wort "result"] ++ [] := by
    simp [druckToks]
  apply wortTurm _ _ hd
  intro rest' G hrs hrg hG
  exact prim_ergebnis rest' G (by omega)

-- `&p` legs from the unary `&` arm; the primary component is
-- vacuous (`primFrei` is false for `fnwert`).
theorem fnwertLegs : ∀ (p : String), Legs (.fnwert p) := by
  intro p
  have hU : ∀ (rest' : List Token) (G : Nat),
      ruhigSuff rest' = true → ruhigGleit rest' = true →
      12 * (groesse (.fnwert p) + 1) + groesse (.fnwert p) + 2 ≤ G →
      parseUnary G (druckToks (.fnwert p) ++ rest') =
        .ok (.fnwert p, rest') := by
    intro rest' G hrs hrg hG
    exact un_fnwert_legs p rest' G hrs hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest' G hpf hrs hrg hG
    simp [primFrei] at hpf
  · intro rest' G hrs hrg hG
    exact hU rest' G hrs hrg hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnwert p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnwert p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnwert p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnwert p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnwert p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.1 G hG
  · intro rest' G hr hrs hrg hG
    exact (tower_up (.fnwert p) rest' hr
      (fun G hG => hU rest' G hrs hrg hG)).2.2.2.2.2 G hG

-- `G::F` legs (primary leg by lane 161's `prim_grund`).
theorem grundLegs : ∀ (g f : String),
    (!istKeinPlatz g) = true → (!istIntWort g) = true →
    (!istZuckerBreite g) = true → (!(strEq g "Self")) = true →
    Legs (.grund g f) := by
  intro g f hkp hit hzuk hself
  have hd : druckToks (.grund g f) = [.ident g] ++
      [.zeichen "::", .ident f] := by
    simp [druckToks]
  apply identTurm _ _ hd
  intro rest' G hrs hrg hG
  exact prim_grund g f rest' G hkp hit hzuk hself hrs (by omega)

-- Every `altNeu` tree has legs.
theorem legsAlt : ∀ (e : SExpr), altNeu e = true → Legs e := by
  intro e hg
  cases e with
  | lit m => simp [altNeu] at hg
  | gleit s => simp [altNeu] at hg
  | wahr => simp [altNeu] at hg
  | falsch => simp [altNeu] at hg
  | «variable» s => simp [altNeu] at hg
  | un o x => simp [altNeu] at hg
  | bin o l r => simp [altNeu] at hg
  | feld x f => simp [altNeu] at hg
  | index x i => simp [altNeu] at hg
  | pfeil x f => simp [altNeu] at hg
  | ruf f xs => simp [altNeu] at hg
  | fnwert f => simp [altNeu] at hg
  | eingebaut f xs => simp [altNeu] at hg
  | alt x =>
    simp only [altNeu] at hg
    exact altLegs x hg
  | ergebnis => simp [altNeu] at hg
  | grund g f => simp [altNeu] at hg

-- Every `ergebnisNeu` tree has legs.
theorem legsErgebnis : ∀ (e : SExpr), ergebnisNeu e = true → Legs e := by
  intro e hg
  cases e with
  | lit m => simp [ergebnisNeu] at hg
  | gleit s => simp [ergebnisNeu] at hg
  | wahr => simp [ergebnisNeu] at hg
  | falsch => simp [ergebnisNeu] at hg
  | «variable» s => simp [ergebnisNeu] at hg
  | un o x => simp [ergebnisNeu] at hg
  | bin o l r => simp [ergebnisNeu] at hg
  | feld x f => simp [ergebnisNeu] at hg
  | index x i => simp [ergebnisNeu] at hg
  | pfeil x f => simp [ergebnisNeu] at hg
  | ruf f xs => simp [ergebnisNeu] at hg
  | fnwert f => simp [ergebnisNeu] at hg
  | eingebaut f xs => simp [ergebnisNeu] at hg
  | alt x => simp [ergebnisNeu] at hg
  | ergebnis => exact ergebnisLegs
  | grund g f => simp [ergebnisNeu] at hg

-- Every `fnwertNeu` tree has legs.
theorem legsFnwert : ∀ (e : SExpr), fnwertNeu e = true → Legs e := by
  intro e hg
  cases e with
  | lit m => simp [fnwertNeu] at hg
  | gleit s => simp [fnwertNeu] at hg
  | wahr => simp [fnwertNeu] at hg
  | falsch => simp [fnwertNeu] at hg
  | «variable» s => simp [fnwertNeu] at hg
  | un o x => simp [fnwertNeu] at hg
  | bin o l r => simp [fnwertNeu] at hg
  | feld x f => simp [fnwertNeu] at hg
  | index x i => simp [fnwertNeu] at hg
  | pfeil x f => simp [fnwertNeu] at hg
  | ruf f xs => simp [fnwertNeu] at hg
  | fnwert p => exact fnwertLegs p
  | eingebaut f xs => simp [fnwertNeu] at hg
  | alt x => simp [fnwertNeu] at hg
  | ergebnis => simp [fnwertNeu] at hg
  | grund g f => simp [fnwertNeu] at hg

-- Every `grundNeu` tree has legs.
theorem legsGrund : ∀ (e : SExpr), grundNeu e = true → Legs e := by
  intro e hg
  cases e with
  | lit m => simp [grundNeu] at hg
  | gleit s => simp [grundNeu] at hg
  | wahr => simp [grundNeu] at hg
  | falsch => simp [grundNeu] at hg
  | «variable» s => simp [grundNeu] at hg
  | un o x => simp [grundNeu] at hg
  | bin o l r => simp [grundNeu] at hg
  | feld x f => simp [grundNeu] at hg
  | index x i => simp [grundNeu] at hg
  | pfeil x f => simp [grundNeu] at hg
  | ruf f xs => simp [grundNeu] at hg
  | fnwert f => simp [grundNeu] at hg
  | eingebaut f xs => simp [grundNeu] at hg
  | alt x => simp [grundNeu] at hg
  | ergebnis => simp [grundNeu] at hg
  | grund g f =>
    simp only [grundNeu, Bool.and_eq_true] at hg
    obtain ⟨hABC, hself⟩ := hg
    obtain ⟨hAB, hzuk⟩ := hABC
    obtain ⟨hkp, hit⟩ := hAB
    exact grundLegs g f hkp hit hzuk hself

-- Every level-6-new tree has legs (the `obtain` shape mirrors
-- `legsEmb`: the four-way `||` splits left-nested).
theorem legsPrimNeu : ∀ (e : SExpr), primNeu e = true → Legs e := by
  intro e hg
  simp only [primNeu, Bool.or_eq_true] at hg
  obtain h123 | h4 := hg
  · obtain h12 | h3 := h123
    · obtain h1 | h2 := h12
      · exact legsAlt e h1
      · exact legsErgebnis e h2
    · exact legsFnwert e h3
  · exact legsGrund e h4

-- Every level-6 tree has legs.
theorem legsPrim : ∀ (e : SExpr), gutPrim e = true → Legs e := by
  intro e hg
  simp only [gutPrim, Bool.or_eq_true] at hg
  obtain hold | hnew := hg
  · exact legsEmb e hold
  · exact legsPrimNeu e hnew

-- Level-6 goal: every `gutPrim` tree parses back from its
-- printed tokens with `brennstoff` fuel.
theorem parse_druck_prim : ∀ (e : SExpr), gutPrim e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) =
      .ok (e, [.ende]) := by
  intro e hg
  have hL := legsPrim e hg
  have hr : ruhig [.ende] = true := rfl
  have hrs : ruhigSuff [.ende] = true := rfl
  have hrg : ruhigGleit [.ende] = true := rfl
  have hF : 12 * (groesse e + 1) + groesse e + 8 ≤ brennstoff e := by
    simp [brennstoff]
  exact hL.2.2.2.2.2.2.2 [.ende] (brennstoff e) hr hrs hrg hF

-- Bridge for the `alt` layer (kernel places are places).
theorem gut_of_altNeu : ∀ (e : SExpr), altNeu e = true → gut e = true := by
  intro e hg
  cases e with
  | lit m => simp [altNeu] at hg
  | gleit s => simp [altNeu] at hg
  | wahr => simp [altNeu] at hg
  | falsch => simp [altNeu] at hg
  | «variable» s => simp [altNeu] at hg
  | un o x => simp [altNeu] at hg
  | bin o l r => simp [altNeu] at hg
  | feld x f => simp [altNeu] at hg
  | index x i => simp [altNeu] at hg
  | pfeil x f => simp [altNeu] at hg
  | ruf f xs => simp [altNeu] at hg
  | fnwert f => simp [altNeu] at hg
  | eingebaut f xs => simp [altNeu] at hg
  | alt x =>
    simp only [altNeu] at hg
    simp only [gut]
    exact gutPlatz_of_gutKernPlatz x hg
  | ergebnis => simp [altNeu] at hg
  | grund g f => simp [altNeu] at hg

-- Bridge for the `ergebnis` layer.
theorem gut_of_ergebnisNeu : ∀ (e : SExpr),
    ergebnisNeu e = true → gut e = true := by
  intro e hg
  cases e with
  | lit m => simp [ergebnisNeu] at hg
  | gleit s => simp [ergebnisNeu] at hg
  | wahr => simp [ergebnisNeu] at hg
  | falsch => simp [ergebnisNeu] at hg
  | «variable» s => simp [ergebnisNeu] at hg
  | un o x => simp [ergebnisNeu] at hg
  | bin o l r => simp [ergebnisNeu] at hg
  | feld x f => simp [ergebnisNeu] at hg
  | index x i => simp [ergebnisNeu] at hg
  | pfeil x f => simp [ergebnisNeu] at hg
  | ruf f xs => simp [ergebnisNeu] at hg
  | fnwert f => simp [ergebnisNeu] at hg
  | eingebaut f xs => simp [ergebnisNeu] at hg
  | alt x => simp [ergebnisNeu] at hg
  | ergebnis => rfl
  | grund g f => simp [ergebnisNeu] at hg

-- Bridge for the `fnwert` layer.
theorem gut_of_fnwertNeu : ∀ (e : SExpr),
    fnwertNeu e = true → gut e = true := by
  intro e hg
  cases e with
  | lit m => simp [fnwertNeu] at hg
  | gleit s => simp [fnwertNeu] at hg
  | wahr => simp [fnwertNeu] at hg
  | falsch => simp [fnwertNeu] at hg
  | «variable» s => simp [fnwertNeu] at hg
  | un o x => simp [fnwertNeu] at hg
  | bin o l r => simp [fnwertNeu] at hg
  | feld x f => simp [fnwertNeu] at hg
  | index x i => simp [fnwertNeu] at hg
  | pfeil x f => simp [fnwertNeu] at hg
  | ruf f xs => simp [fnwertNeu] at hg
  | fnwert p => rfl
  | eingebaut f xs => simp [fnwertNeu] at hg
  | alt x => simp [fnwertNeu] at hg
  | ergebnis => simp [fnwertNeu] at hg
  | grund g f => simp [fnwertNeu] at hg

-- Bridge for the `grund` layer (exactly `gut`'s side
-- conditions; stepwise `obtain` -- the flattened four-pattern
-- misfires on the `!`-component, measured in `legsGrund`).
theorem gut_of_grundNeu : ∀ (e : SExpr),
    grundNeu e = true → gut e = true := by
  intro e hg
  cases e with
  | lit m => simp [grundNeu] at hg
  | gleit s => simp [grundNeu] at hg
  | wahr => simp [grundNeu] at hg
  | falsch => simp [grundNeu] at hg
  | «variable» s => simp [grundNeu] at hg
  | un o x => simp [grundNeu] at hg
  | bin o l r => simp [grundNeu] at hg
  | feld x f => simp [grundNeu] at hg
  | index x i => simp [grundNeu] at hg
  | pfeil x f => simp [grundNeu] at hg
  | ruf f xs => simp [grundNeu] at hg
  | fnwert f => simp [grundNeu] at hg
  | eingebaut f xs => simp [grundNeu] at hg
  | alt x => simp [grundNeu] at hg
  | ergebnis => simp [grundNeu] at hg
  | grund g f =>
    simp only [grundNeu, Bool.and_eq_true] at hg
    obtain ⟨hABC, hself⟩ := hg
    obtain ⟨hAB, hzuk⟩ := hABC
    obtain ⟨hkp, hit⟩ := hAB
    simp only [gut, Bool.and_eq_true] at ⊢
    exact ⟨⟨⟨hkp, hit⟩, hzuk⟩, hself⟩

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
-- check. No two-segment `G::F` occurs in the corpus --
-- three-segment paths lower to field chains via `grundKette`
-- -- so the `grund` witness is neutrally named.
theorem zeuge_alt :
    parseOr (brennstoff (.alt (.variable "BESITZER")))
    (druckToks (.alt (.variable "BESITZER")) ++ [.ende]) =
      .ok (.alt (.variable "BESITZER"), [.ende]) :=
  parse_druck_prim _ (by decide)
theorem zeuge_alt_rech : (match parseOr
    (brennstoff (.alt (.variable "BESITZER")))
    (druckToks (.alt (.variable "BESITZER")) ++ [.ende]) with
    | .ok (.alt (.variable "BESITZER"), [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_ergebnis :
    parseOr (brennstoff .ergebnis)
    (druckToks .ergebnis ++ [.ende]) =
      .ok (.ergebnis, [.ende]) :=
  parse_druck_prim _ (by decide)
theorem zeuge_ergebnis_rech : (match parseOr
    (brennstoff .ergebnis)
    (druckToks .ergebnis ++ [.ende]) with
    | .ok (.ergebnis, [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_fnwert :
    parseOr (brennstoff (.fnwert "hart_senden"))
    (druckToks (.fnwert "hart_senden") ++ [.ende]) =
      .ok (.fnwert "hart_senden", [.ende]) :=
  parse_druck_prim _ (by decide)
theorem zeuge_fnwert_rech : (match parseOr
    (brennstoff (.fnwert "hart_senden"))
    (druckToks (.fnwert "hart_senden") ++ [.ende]) with
    | .ok (.fnwert "hart_senden", [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_grund :
    parseOr (brennstoff (.grund "T" "x"))
    (druckToks (.grund "T" "x") ++ [.ende]) =
      .ok (.grund "T" "x", [.ende]) :=
  parse_druck_prim _ (by decide)
theorem zeuge_grund_rech : (match parseOr
    (brennstoff (.grund "T" "x"))
    (druckToks (.grund "T" "x") ++ [.ende]) with
    | .ok (.grund "T" "x", [.ende]) => true
    | _ => false) = true := by
  decide

end Gabbro.Grammatik.Parser
