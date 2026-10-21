/-
  File:      Grammatik/Parser/Round/RundlaufTok.lean
  Subject:   Layer L2a of the syntax round trip, with TOKEN fuel: every printable expression
             (`gut`) parses back from its tokens with fuel linear in the NUMBER OF TOKENS, so the
             whole reader `parseTop` (fuel `8 * length + 32`) returns it.

  Why a second bound. `RundlaufVoll.legs_gut` gives the legs at the size bound
  `12 * (groesse e + 1) + groesse e` (lane 172's `Legs`): thirteen fuel per tree node. The readers
  of the front end run with fuel `8 * length + 32` (`parseTop`, `parseStmtTop`, `parseTopTief`), and
  a tree with many one-token nodes (`a[!x][!x]...`: three nodes per four tokens) has thirteen fuel
  per node > eight per token -- so the size bound cannot reach `parseTop`, although the reader's
  real fuel use is a nesting depth, far below it. Here the legs carry an ABSTRACT bound
  (`LegsB m e`, `Legs e = LegsB (12 * (groesse e + 1) + groesse e) e` definitionally), the steps
  combine the bounds of the children by MAXIMUM (one `m` for both operands), and the induction
  proves `LegsB (fb e) e` with `fb e = 6 * (druckToks e).length + 26`.

  The towers and inner traces are lane 172/179's (Rundlauf2/3), restated over `m` (the proofs are
  the same `omega` strips with the size terms replaced by `m`); the places, calls and builtins are
  lane 161's (Rundlauf.lean), restated over the token measure.

  Main statements:
  - `legs_tok : ∀ e, gut e = true → LegsB (fb e) e`;
  - `parse_druck_tok : gut e → fb e + 8 ≤ F → ruhig/ruhigSuff/ruhigGleit rest →
     parseOr F (druckToks e ++ rest) = .ok (e, rest)`;
  - `parseTop_druck_gut : gut e → parseTop (druckToks e ++ [.ende]) = .ok e`;
  - `rundlauf_text_gut : gut e → (∀ t ∈ druckToks e, TokGut t) →
     parseTopAusText (renderText (druckToks e)) = .ok e` (with L1, from source text).
-/
import Grammatik.Parser.Round.RundlaufVoll

namespace Gabbro.Grammatik.Parser

/-- The eight round-trip legs at an abstract fuel bound `m` (`Legs` is the instance at the size
    bound). -/
def LegsB (m : Nat) (e : SExpr) : Prop :=
  (∀ (rest : List Token) (G : Nat), primFrei e = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 1 ≤ G →
    parsePrimary G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhigSuff rest = true →
    ruhigGleit rest = true → m + 2 ≤ G →
    parseUnary G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 3 ≤ G →
    parseMul G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 4 ≤ G →
    parseAdd G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 5 ≤ G →
    parseBit G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 6 ≤ G →
    parseCmp G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 7 ≤ G →
    parseAnd G (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (rest : List Token) (G : Nat), ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true → m + 8 ≤ G →
    parseOr G (druckToks e ++ rest) = .ok (e, rest))

/-- `Legs` is `LegsB` at the size bound. -/
theorem legsB_of_legs (e : SExpr) (h : Legs e) : LegsB (12 * (groesse e + 1) + groesse e) e := h

/-- A bound may always be raised. -/
theorem LegsB_mono {m m' : Nat} {e : SExpr} (hm : m ≤ m') (h : LegsB m e) : LegsB m' e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest G a b c hG; exact h1 rest G a b c (by omega)
  · intro rest G a b hG; exact h2 rest G a b (by omega)
  · intro rest G a b c hG; exact h3 rest G a b c (by omega)
  · intro rest G a b c hG; exact h4 rest G a b c (by omega)
  · intro rest G a b c hG; exact h5 rest G a b c (by omega)
  · intro rest G a b c hG; exact h6 rest G a b c (by omega)
  · intro rest G a b c hG; exact h7 rest G a b c (by omega)
  · intro rest G a b c hG; exact h8 rest G a b c (by omega)

/-! ### Towers and inner traces over an abstract bound (Rundlauf2/3, restated over `m`) -/

theorem tower_upM : ∀ (m : Nat) (e : SExpr) (rest : List Token),
    ruhig rest = true →
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks e ++ rest) = .ok (e, rest)) →
    (∀ (G : Nat), m + 3 ≤ G →
      parseMul G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), m + 4 ≤ G →
      parseAdd G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), m + 5 ≤ G →
      parseBit G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), m + 6 ≤ G →
      parseCmp G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), m + 7 ≤ G →
      parseAnd G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), m + 8 ≤ G →
      parseOr G (druckToks e ++ rest) = .ok (e, rest)) := by
  intro m e rest hr hU
  have hM : ∀ (G : Nat),
      m + 3 ≤ G →
      parseMul G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopMul rest hr
    simp only [parseMul, parseMulL, hU', hstop] at ⊢
  have hA : ∀ (G : Nat),
      m + 4 ≤ G →
      parseAdd G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopAdd rest hr
    simp only [parseAdd, parseAddL, hM', hstop] at ⊢
  have hB : ∀ (G : Nat),
      m + 5 ≤ G →
      parseBit G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopBit rest hr
    simp only [parseBit, parseBitL, hA', hstop] at ⊢
  have hC : ∀ (G : Nat),
      m + 6 ≤ G →
      parseCmp G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hstop := stopVgl rest hr
    simp only [parseCmp, hB', hstop] at ⊢
  have hN : ∀ (G : Nat),
      m + 7 ≤ G →
      parseAnd G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hC' := hC G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopUnd rest hr
    simp only [parseAnd, parseAndL, hC', hstop] at ⊢
  have hO : ∀ (G : Nat),
      m + 8 ≤ G →
      parseOr G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hN' := hN G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopOder rest hr
    simp only [parseOr, parseOrL, hN', hstop] at ⊢
  exact ⟨hM, hA, hB, hC, hN, hO⟩

theorem tower_up_orbarM : ∀ (m : Nat) (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    opVgl S1 = none → opUnd S1 = none →
    (∀ (G : Nat), m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 7 ≤ G →
      parseAnd G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro m l S1 hU hMul hAdd hBit hVgl hUnd
  have hM : ∀ (G : Nat),
      m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  have hB : ∀ (G : Nat),
      m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseBit, parseBitL, hA', hBit] at ⊢
  have hC : ∀ (G : Nat),
      m + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    simp only [parseCmp, hB', hVgl] at ⊢
  have hN : ∀ (G : Nat),
      m + 7 ≤ G →
      parseAnd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hC' := hC G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAnd, parseAndL, hC', hUnd] at ⊢
  exact ⟨hM, hA, hB, hC, hN⟩

theorem tower_up_andbarM : ∀ (m : Nat) (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    opVgl S1 = none →
    (∀ (G : Nat), m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro m l S1 hU hMul hAdd hBit hVgl
  have hM : ∀ (G : Nat),
      m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  have hB : ∀ (G : Nat),
      m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseBit, parseBitL, hA', hBit] at ⊢
  have hC : ∀ (G : Nat),
      m + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    simp only [parseCmp, hB', hVgl] at ⊢
  exact ⟨hM, hA, hB, hC⟩

theorem tower_up_cmpbarM : ∀ (m : Nat) (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    (∀ (G : Nat), m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro m l S1 hU hMul hAdd hBit
  have hM : ∀ (G : Nat),
      m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  have hB : ∀ (G : Nat),
      m + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseBit, parseBitL, hA', hBit] at ⊢
  exact ⟨hM, hA, hB⟩

theorem tower_up_bitbarM : ∀ (m : Nat) (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none →
    (∀ (G : Nat), m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro m l S1 hU hMul hAdd
  have hM : ∀ (G : Nat),
      m + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      m + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  exact ⟨hM, hA⟩

theorem cmpB_stepM : ∀ (m : Nat) (op : String) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W)) →
    opMul ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opAdd ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opBit ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opVgl ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) =
      some (op, druckToks r ++ ([.zeichen ")"] ++ W)) →
    ∀ (G : Nat),
      m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
  intro m op l r W hUl hUr hMul hAdd hBit hop G hG
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  -- Left operand at `parseBit` with the operator follow.
  have hBl : ∀ (G5 : Nat),
      m + 5 ≤ G5 →
      parseBit G5 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G5 hG5
    have hbar := tower_up_cmpbarM m l ([.zeichen op] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) hUl hMul hAdd hBit
    exact hbar.2.2 G5 hG5
  -- Right operand at `parseBit` with the `)` follow.
  have hBr : ∀ (G5x : Nat),
      m + 5 ≤ G5x →
      parseBit G5x (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W) := by
    intro G5x hG5x
    have hup := tower_upM m r ([.zeichen ")"] ++ W) (hr_paren W) hUr
    exact hup.2.2.1 G5x hG5x
  -- The `parseCmp` core: `l`, consume the operator, `r`. No
  -- loop stop: the single-shot level has no loop.
  have hCmp : ∀ (G2 : Nat),
      m + 8 ≤ G2 →
      parseCmp G2 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBl' := hBl G3 (by omega)
    have hBr' := hBr G3 (by omega)
    simp only [parseCmp, hBl', hop, hBr'] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
  have hAnd : ∀ (G1 : Nat),
      m + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    have h11 : 1 ≤ G1 := by omega
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hCmp' := hCmp G2 (by omega)
    have h12 : 1 ≤ G2 := by omega
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hCmp', hstop] at ⊢
  have hOr : ∀ (G0 : Nat),
      m + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr G hG

theorem bitB_stepM : ∀ (m : Nat) (op : String) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W)) →
    opMul ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opAdd ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opBit ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) =
      some (op, druckToks r ++ ([.zeichen ")"] ++ W)) →
    ∀ (G : Nat),
      m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
  intro m op l r W hUl hUr hMul hAdd hop G hG
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  -- Left operand at `parseAdd` with the operator follow.
  have hAl : ∀ (G5 : Nat),
      m + 4 ≤ G5 →
      parseAdd G5 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G5 hG5
    have hbar := tower_up_bitbarM m l ([.zeichen op] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) hUl hMul hAdd
    exact hbar.2 G5 hG5
  -- Right operand at `parseAdd` with the `)` follow.
  have hAr : ∀ (G5x : Nat),
      m + 4 ≤ G5x →
      parseAdd G5x (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W) := by
    intro G5x hG5x
    have hup := tower_upM m r ([.zeichen ")"] ++ W) (hr_paren W) hUr
    exact hup.2.1 G5x hG5x
  -- The `parseBit` core: `l`, consume the operator, `r`, stop
  -- at `)` (one flat-loop iteration, then the second
  -- `parseBitL` strip stops fuel-free).
  have hBit : ∀ (G3 : Nat),
      m + 7 ≤ G3 →
      parseBit G3 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G3 hG3
    have h31 : 1 ≤ G3 := by omega
    obtain ⟨G4, rfl⟩ : ∃ G4, G3 = G4 + 1 := ⟨G3 - 1, by omega⟩
    have hAl' := hAl G4 (by omega)
    have h32 : 1 ≤ G4 := by omega
    obtain ⟨G4x, rfl⟩ : ∃ G4x, G4 = G4x + 1 := ⟨G4 - 1, by omega⟩
    have hAr' := hAr G4x (by omega)
    have h33 : 1 ≤ G4x := by omega
    obtain ⟨G4y, rfl⟩ : ∃ G4y, G4x = G4y + 1 := ⟨G4x - 1, by omega⟩
    have hstop := opBit_paren W
    simp only [parseBit, parseBitL, hAl', hop, hAr', hstop] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
  have hCmp : ∀ (G2 : Nat),
      m + 8 ≤ G2 →
      parseCmp G2 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBit' := hBit G3 (by omega)
    have hstop := opVgl_paren W
    simp only [parseCmp, hBit', hstop] at ⊢
  have hAnd : ∀ (G1 : Nat),
      m + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    have h11 : 1 ≤ G1 := by omega
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hCmp' := hCmp G2 (by omega)
    have h12 : 1 ≤ G2 := by omega
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hCmp', hstop] at ⊢
  have hOr : ∀ (G0 : Nat),
      m + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr G hG

theorem addB_stepM : ∀ (m : Nat) (op : String) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W)) →
    opMul ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = none →
    opAdd ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) =
      some (op, druckToks r ++ ([.zeichen ")"] ++ W)) →
    ruhigSuff ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = true →
    ruhigGleit ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = true →
    ∀ (G : Nat),
      m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
  intro m op l r W hUl hUr hMulmiss hop hrsS1 hrgS1 G hG
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  -- Left operand through `parseMul` with the operator follow.
  have hMl : ∀ (G5 : Nat),
      m + 3 ≤ G5 →
      parseMul G5 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G5 hG5
    have h51 : 1 ≤ G5 := by omega
    obtain ⟨G6, rfl⟩ : ∃ G6, G5 = G6 + 1 := ⟨G5 - 1, by omega⟩
    have hUl' := hUl G6 (by omega)
    have h52 : 1 ≤ G6 := by omega
    obtain ⟨G7, rfl⟩ : ∃ G7, G6 = G7 + 1 := ⟨G6 - 1, by omega⟩
    simp only [parseMul, parseMulL, hUl', hMulmiss] at ⊢
  -- Right operand through `parseMul` with the `)` follow.
  have hMr : ∀ (G5x : Nat),
      m + 3 ≤ G5x →
      parseMul G5x (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W) := by
    intro G5x hG5x
    have h53 : 1 ≤ G5x := by omega
    obtain ⟨G6x, rfl⟩ : ∃ G6x, G5x = G6x + 1 := ⟨G5x - 1, by omega⟩
    have hUr' := hUr G6x (by omega)
    have h54 : 1 ≤ G6x := by omega
    obtain ⟨G7x, rfl⟩ : ∃ G7x, G6x = G7x + 1 := ⟨G6x - 1, by omega⟩
    have hstop := opMul_paren W
    simp only [parseMul, parseMulL, hUr', hstop] at ⊢
  -- The `parseAdd` core: `l`, consume the operator, `r`, stop
  -- at `)`.
  have hAdd : ∀ (G4 : Nat),
      m + 6 ≤ G4 →
      parseAdd G4 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G4 hG4
    have h41 : 1 ≤ G4 := by omega
    obtain ⟨G5, rfl⟩ : ∃ G5, G4 = G5 + 1 := ⟨G4 - 1, by omega⟩
    have hMl' := hMl G5 (by omega)
    have h42 : 1 ≤ G5 := by omega
    obtain ⟨G5x, rfl⟩ : ∃ G5x, G5 = G5x + 1 := ⟨G5 - 1, by omega⟩
    have hMr' := hMr G5x (by omega)
    have hstop := stopAdd ([.zeichen ")"] ++ W) (hr_paren W)
    have h43 : 1 ≤ G5x := by omega
    obtain ⟨G5y, rfl⟩ : ∃ G5y, G5x = G5y + 1 := ⟨G5x - 1, by omega⟩
    simp only [parseAdd, parseAddL, hMl', hop, hMr', hstop] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
  have hBit : ∀ (G3 : Nat),
      m + 7 ≤ G3 →
      parseBit G3 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G3 hG3
    have h31 : 1 ≤ G3 := by omega
    obtain ⟨G4, rfl⟩ : ∃ G4, G3 = G4 + 1 := ⟨G3 - 1, by omega⟩
    have hAdd' := hAdd G4 (by omega)
    have h32 : 1 ≤ G4 := by omega
    obtain ⟨G4x, rfl⟩ : ∃ G4x, G4 = G4x + 1 := ⟨G4 - 1, by omega⟩
    have hstop := stopBit ([.zeichen ")"] ++ W) (hr_paren W)
    simp only [parseBit, parseBitL, hAdd', hstop] at ⊢
  have hCmp : ∀ (G2 : Nat),
      m + 8 ≤ G2 →
      parseCmp G2 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBit' := hBit G3 (by omega)
    have hstop := opVgl_paren W
    simp only [parseCmp, hBit', hstop] at ⊢
  have hAnd : ∀ (G1 : Nat),
      m + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    have h11 : 1 ≤ G1 := by omega
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hCmp' := hCmp G2 (by omega)
    have h12 : 1 ≤ G2 := by omega
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hCmp', hstop] at ⊢
  have hOr : ∀ (G0 : Nat),
      m + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr G hG

theorem mulB_stepM : ∀ (m : Nat) (op : String) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen op] ++
          (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W)) →
    opMul ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) =
      some (op, druckToks r ++ ([.zeichen ")"] ++ W)) →
    ruhigSuff ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = true →
    ruhigGleit ([.zeichen op] ++ (druckToks r ++ ([.zeichen ")"] ++ W))) = true →
    ∀ (G : Nat),
      m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
  intro m op l r W hUl hUr hop hrsS1 hrgS1 G hG
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  simp only [List.append_assoc] at ⊢
  -- The `parseAdd` core with the operator consumed inside
  -- `parseMul` (mirror of `kernB_step_star`, spelling
  -- generalised).
  have hAdd : ∀ (G4 : Nat),
      m + 6 ≤ G4 →
      parseAdd G4 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G4 hG4
    have h41 : 1 ≤ G4 := by omega
    obtain ⟨G5, rfl⟩ : ∃ G5, G4 = G5 + 1 := ⟨G4 - 1, by omega⟩
    have h42 : 1 ≤ G5 := by omega
    obtain ⟨G6, rfl⟩ : ∃ G6, G5 = G6 + 1 := ⟨G5 - 1, by omega⟩
    have hUl' := hUl G6 (by omega)
    have h43 : 1 ≤ G6 := by omega
    obtain ⟨G6x, rfl⟩ : ∃ G6x, G6 = G6x + 1 := ⟨G6 - 1, by omega⟩
    have hUr' := hUr G6x (by omega)
    have h44 : 1 ≤ G6x := by omega
    obtain ⟨G6y, rfl⟩ : ∃ G6y, G6x = G6y + 1 := ⟨G6x - 1, by omega⟩
    have hstopM := opMul_paren W
    have hstopA := stopAdd ([.zeichen ")"] ++ W) (hr_paren W)
    simp only [parseAdd, parseMul, parseMulL, hUl', hop, hUr', hstopM] at ⊢
    -- Four strips numeral-fold the loop fuel to `+ 3`, which no
    -- equation fires on: unfold once more by explicit rewrite
    -- (same as `kernB_step_star`).
    have h45 : G6y + 3 = (G6y + 2) + 1 := by omega
    rw [h45] at ⊢
    simp only [parseAddL, hstopA] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
  have hBit : ∀ (G3 : Nat),
      m + 7 ≤ G3 →
      parseBit G3 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G3 hG3
    have h31 : 1 ≤ G3 := by omega
    obtain ⟨G4, rfl⟩ : ∃ G4, G3 = G4 + 1 := ⟨G3 - 1, by omega⟩
    have hAdd' := hAdd G4 (by omega)
    have h32 : 1 ≤ G4 := by omega
    obtain ⟨G4x, rfl⟩ : ∃ G4x, G4 = G4x + 1 := ⟨G4 - 1, by omega⟩
    have hstop := stopBit ([.zeichen ")"] ++ W) (hr_paren W)
    simp only [parseBit, parseBitL, hAdd', hstop] at ⊢
  have hCmp : ∀ (G2 : Nat),
      m + 8 ≤ G2 →
      parseCmp G2 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBit' := hBit G3 (by omega)
    have hstop := opVgl_paren W
    simp only [parseCmp, hBit', hstop] at ⊢
  have hAnd : ∀ (G1 : Nat),
      m + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    have h11 : 1 ≤ G1 := by omega
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hCmp' := hCmp G2 (by omega)
    have h12 : 1 ≤ G2 := by omega
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hCmp', hstop] at ⊢
  have hOr : ∀ (G0 : Nat),
      m + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen op] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin op l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr G hG


/-- Legs from a primary leg and a unary leg (the upper six by `tower_upM`). -/
theorem legsB_aus (m : Nat) (e : SExpr)
    (hP : ∀ (rest : List Token) (G : Nat), primFrei e = true → ruhigSuff rest = true →
      ruhigGleit rest = true → m + 1 ≤ G → parsePrimary G (druckToks e ++ rest) = .ok (e, rest))
    (hU : ∀ (rest : List Token) (G : Nat), ruhigSuff rest = true → ruhigGleit rest = true →
      m + 2 ≤ G → parseUnary G (druckToks e ++ rest) = .ok (e, rest)) : LegsB m e := by
  refine ⟨hP, hU, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).1 G hG
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).2.1 G hG
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).2.2.1 G hG
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).2.2.2.1 G hG
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).2.2.2.2.1 G hG
  · intro rest G hr hrs hrg hG
    exact (tower_upM m e rest hr (fun G hG => hU rest G hrs hrg hG)).2.2.2.2.2 G hG

theorem unary_name_fall (G : Nat) (t : Token) (M R : List Token) (v : SExpr)
    (ht : (∃ g, t = .ident g) ∨ (∃ w, t = .wort w))
    (h : parsePrimary G (t :: M) = .ok (v, R)) : parseUnary (G + 1) (t :: M) = .ok (v, R) := by
  rcases ht with ⟨g, rfl⟩ | ⟨w, rfl⟩ <;> simp only [parseUnary, h]

/-- Legs of a tree printed with a name head (`ident` or `wort`: no prefix arm fires): its primary
    leg suffices. -/
theorem legsB_kopf (m : Nat) (t : Token) {S : List Token} (e : SExpr)
    (ht : (∃ g, t = .ident g) ∨ (∃ w, t = .wort w))
    (hd : druckToks e = [t] ++ S)
    (hP : ∀ (rest : List Token) (G : Nat), ruhigSuff rest = true → ruhigGleit rest = true →
      m + 1 ≤ G → parsePrimary G (druckToks e ++ rest) = .ok (e, rest)) : LegsB m e := by
  apply legsB_aus m e (fun rest G _ hrs hrg hG => hP rest G hrs hrg hG)
  intro rest G hrs hrg hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hP' := hP rest G' hrs hrg (by omega)
  rw [hd] at hP' ⊢
  simp only [List.append_assoc, List.singleton_append] at hP' ⊢
  exact unary_name_fall G' t _ _ _ ht hP'

/-- The binary tower from an inner trace at bound `m`: the primary leg runs the `(` arm, the unary
    leg falls through on `(`. -/
theorem bin_turmM (m : Nat) (op : String) (l r : SExpr)
    (hB : ∀ (T : List Token) (G : Nat), m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen op] ++ druckToks r ++ [.zeichen ")"] ++ T) =
        .ok (.bin op l r, [.zeichen ")"] ++ T)) :
    LegsB (m + 10) (.bin op l r) := by
  have hd : druckToks (.bin op l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen op] ++ druckToks r ++ [.zeichen ")"] := by
    simp [druckToks]
  have hP : ∀ (rest' : List Token) (G : Nat), m + 10 + 1 ≤ G →
      parsePrimary G (druckToks (.bin op l r) ++ rest') = .ok (.bin op l r, rest') := by
    intro rest' G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB rest' G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  apply legsB_aus _ _ (fun rest G _ _ _ hG => hP rest G hG)
  intro rest' G _ _ hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hP' := hP rest' G' (by omega)
  simp only [hd, List.append_assoc] at hP' ⊢
  exact un_paren_fall _ _ _ _ hP'

/-- The `||` inner trace over a bound (mirror of `orB_step`). -/
theorem orB_stepM : ∀ (m : Nat) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen "||"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "||"] ++ (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), m + 7 ≤ G →
      parseAnd G (druckToks r ++ ([.zeichen ")"] ++ W)) = .ok (r, [.zeichen ")"] ++ W)) →
    ∀ (G : Nat), m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin "||" l r, [.zeichen ")"] ++ W) := by
  intro m l r W hUl hAr G0 hG0
  simp only [List.append_assoc] at ⊢
  have hup := tower_up_orbarM m l ([.zeichen "||"] ++
    (druckToks r ++ ([.zeichen ")"] ++ W))) hUl
    (opMul_orbar _) (opAdd_orbar _) (opBit_orbar _) (opVgl_orbar _)
    (opUnd_orbar _)
  obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
  have hN' := hup.2.2.2.2 G1 (by omega)
  obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
  have hop := opOder_or_some (druckToks r ++ ([.zeichen ")"] ++ W))
  have hMr := hAr G1x (by omega)
  obtain ⟨G1y, rfl⟩ : ∃ G1y, G1x = G1y + 1 := ⟨G1x - 1, by omega⟩
  have hstop := opOder_paren W
  simp only [parseOr, parseOrL, hN', hop, hMr, hstop] at ⊢

/-- The `&&` inner trace over a bound (mirror of `andB_step`). -/
theorem andB_stepM : ∀ (m : Nat) (l r : SExpr) (W : List Token),
    (∀ (G : Nat), m + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen "&&"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "&&"] ++ (druckToks r ++ ([.zeichen ")"] ++ W)))) →
    (∀ (G : Nat), m + 6 ≤ G →
      parseCmp G (druckToks r ++ ([.zeichen ")"] ++ W)) = .ok (r, [.zeichen ")"] ++ W)) →
    ∀ (G : Nat), m + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
        [.zeichen ")"] ++ W) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ W) := by
  intro m l r W hUl hCr F hF
  simp only [List.append_assoc] at ⊢
  have hup := tower_up_andbarM m l ([.zeichen "&&"] ++
    (druckToks r ++ ([.zeichen ")"] ++ W))) hUl
    (opMul_andbar _) (opAdd_andbar _) (opBit_andbar _) (opVgl_andbar _)
  have hAnd : ∀ (G1 : Nat), m + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen "&&"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hC' := hup.2.2.2 G2 (by omega)
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hop := opUnd_and_some (druckToks r ++ ([.zeichen ")"] ++ W))
    have hMr := hCr G2x (by omega)
    obtain ⟨G2y, rfl⟩ : ∃ G2y, G2x = G2y + 1 := ⟨G2x - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hC', hop, hMr, hstop] at ⊢
  obtain ⟨G1, rfl⟩ : ∃ G1, F = G1 + 1 := ⟨F - 1, by omega⟩
  have hAnd' := hAnd G1 (by omega)
  obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
  have hstop := opOder_paren W
  simp only [parseOr, parseOrL, hAnd', hstop] at ⊢

/-- Every lawful binary spelling over two operands at one bound `m`: the parent is at `m + 10`. -/
theorem binLegsM (m : Nat) (o : String) (l r : SExpr) (ho : gutOpBin o = true)
    (Hl : LegsB m l) (Hr : LegsB m r) : LegsB (m + 10) (.bin o l r) := by
  apply bin_turmM m o l r
  intro T G hG
  have hUr : ∀ (G' : Nat), m + 2 ≤ G' →
      parseUnary G' (druckToks r ++ ([.zeichen ")"] ++ T)) = .ok (r, [.zeichen ")"] ++ T) :=
    fun G' hG' => Hr.2.1 _ G' (hrs_paren T) (hrg_paren T) hG'
  simp only [gutOpBin, Bool.or_eq_true] at ho
  rcases ho with ((((ho | ho) | ho) | ho) | ho) | ho
  · have : o = "||" := strKlingt o "||" ho
    subst this
    exact orB_stepM m l r T (fun G' hG' => Hl.2.1 _ G' (hrs_orbar _) (hrg_orbar _) hG')
      (fun G' hG' => Hr.2.2.2.2.2.2.1 _ G' (hr_paren T) (hrs_paren T) (hrg_paren T) hG') G hG
  · have : o = "&&" := strKlingt o "&&" ho
    subst this
    exact andB_stepM m l r T (fun G' hG' => Hl.2.1 _ G' (hrs_andbar _) (hrg_andbar _) hG')
      (fun G' hG' => Hr.2.2.2.2.2.1 _ G' (hr_paren T) (hrs_paren T) (hrg_paren T) hG') G hG
  · obtain ⟨hmMul, hmAdd, hmBit, hrsS1, hrgS1⟩ :=
      cmpbar_facts o (druckToks r ++ ([.zeichen ")"] ++ T)) ho
    exact cmpB_stepM m o l r T (fun G' hG' => Hl.2.1 _ G' hrsS1 hrgS1 hG') hUr hmMul hmAdd hmBit
      (opVgl_cmp_hit o _ ho) G hG
  · obtain ⟨hmMul, hmAdd, hrsS1, hrgS1⟩ :=
      bitbar_facts o (druckToks r ++ ([.zeichen ")"] ++ T)) ho
    exact bitB_stepM m o l r T (fun G' hG' => Hl.2.1 _ G' hrsS1 hrgS1 hG') hUr hmMul hmAdd
      (opBit_bit_hit o _ ho) G hG
  · obtain ⟨hmMul, hrsS1, hrgS1⟩ :=
      addbar_facts o (druckToks r ++ ([.zeichen ")"] ++ T)) ho
    exact addB_stepM m o l r T (fun G' hG' => Hl.2.1 _ G' hrsS1 hrgS1 hG') hUr hmMul
      (opAdd_add_hit o _ ho) hrsS1 hrgS1 G hG
  · obtain ⟨hrsS1, hrgS1⟩ :=
      mulbar_facts o (druckToks r ++ ([.zeichen ")"] ++ T)) ho
    exact mulB_stepM m o l r T (fun G' hG' => Hl.2.1 _ G' hrsS1 hrgS1 hG') hUr
      (opMul_mul_hit o _ ho) hrsS1 hrgS1 G hG

/-! ### Prefix operators -/

/-- A prefix over an ATOM operand costs no fuel beyond the operand's bound. -/
theorem unLegsM_atom (m : Nat) (o : String) (x : SExpr) (ho : gutOpUn o = true)
    (hat : istAtom x = true) (Hx : LegsB m x) : LegsB m (.un o x) := by
  have hpf := primFrei_of_istAtom x hat
  have hd : druckToks (.un o x) = [.zeichen o] ++ druckToks x := by
    simp [druckToks, hat]
  apply legsB_aus m _ (fun rest G h => by simp [primFrei] at h)
  intro rest G hrs hrg hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hP' := Hx.1 rest G' hpf hrs hrg (by omega)
  simp only [hd, List.append_assoc] at ⊢
  exact bang_arm_gen _ _ _ _ _ ho hP'

/-- A prefix over a parenthesised operand: eight more (the `(` arm runs `parseOr`). -/
theorem unLegsM_klammer (m : Nat) (o : String) (x : SExpr) (ho : gutOpUn o = true)
    (hat : istAtom x = false) (Hx : LegsB m x) : LegsB (m + 8) (.un o x) := by
  have hd : druckToks (.un o x) = [.zeichen o] ++
      (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
    simp [druckToks, hat]
  apply legsB_aus _ _ (fun rest G h => by simp [primFrei] at h)
  intro rest G hrs hrg hG
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
  have hO' := Hx.2.2.2.2.2.2.2 _ G'' (hr_paren rest) (hrs_paren rest) (hrg_paren rest)
    (by omega)
  have hPar := paren_arm _ _ _ _ hO'
  have hBang := bang_arm_gen _ _ _ _ _ ho hPar
  simp only [hd, List.append_assoc] at ⊢
  exact hBang

/-! ### The token measure -/

/-- The fuel bound of the token measure: six per printed token, twenty-six spare (the leaves'
    size bound is twenty-five). -/
def fb (e : SExpr) : Nat := 6 * (druckToks e).length + 26

/-! ### Places -/

/-- Every index payload of a suffix chain has legs at its token bound. -/
def SuffLegs (suff : List SuffFrag) : Prop := ∀ i, SuffFrag.idx i ∈ suff → LegsB (fb i) i

theorem suffLegs_tail {f : SuffFrag} {s : List SuffFrag} (h : SuffLegs (f :: s)) : SuffLegs s :=
  fun i hi => h i (List.mem_cons_of_mem _ hi)

/-- Suffix chains through `parseSuffixe` at token fuel (lane 161's `suff_rund`, restated). -/
theorem suffM : ∀ (suff : List SuffFrag) (base : SExpr) (rest : List Token) (F : Nat),
    SuffLegs suff → ruhigSuff rest = true →
    6 * (suffToks suff).length + 29 ≤ F →
    parseSuffixe F base (suffToks suff ++ rest) = .ok (applySuff base suff, rest) := by
  intro suff
  induction suff with
  | nil =>
    intro base rest F _ hr hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [suffToks, List.nil_append]
    exact stopSuffix F' base rest hr
  | cons frag suff ih =>
    intro base rest F hs hr hF
    have hs' := suffLegs_tail hs
    cases frag with
    | dot f =>
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append]
      simp only [parseSuffixe]
      simp only [applySuff]
      simp only [suffToks, List.length_cons] at hF
      exact ih _ rest F' hs' hr (by omega)
    | arrow f =>
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append]
      simp only [parseSuffixe]
      simp only [applySuff]
      simp only [suffToks, List.length_cons] at hF
      exact ih _ rest F' hs' hr (by omega)
    | idx i =>
      have hLi := hs i (by simp)
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.length_cons, List.length_append, List.length_singleton] at hF
      simp only [suffToks, List.cons_append]
      simp only [parseSuffixe]
      have hr1 : ruhig ([.zeichen "]"] ++ suffToks suff ++ rest) = true := rfl
      have hr2 : ruhigSuff ([.zeichen "]"] ++ suffToks suff ++ rest) = true := rfl
      have hr3 : ruhigGleit ([.zeichen "]"] ++ suffToks suff ++ rest) = true := rfl
      have hOi := hLi.2.2.2.2.2.2.2 ([.zeichen "]"] ++ suffToks suff ++ rest) F' hr1 hr2 hr3
        (by simp only [fb]; omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOi
      simp only [hOi, List.cons_append]
      simp only [applySuff]
      exact ih _ rest F' hs' hr (by omega)

/-- Places through `parseOrt` at token fuel. -/
theorem ortM (a : String) (suff : List SuffFrag) (rest : List Token) (F : Nat)
    (hka : (!istKeinPlatz a) = true) (hs : SuffLegs suff) (hr : ruhigSuff rest = true)
    (hF : 6 * (suffToks suff).length + 30 ≤ F) :
    parseOrt F (druckToks (applySuff (.variable a) suff) ++ rest) =
      .ok (applySuff (.variable a) suff, rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  rw [druckToks_applySuff]
  have hkaf : istKeinPlatz a = false := nichtWahr_falsch _ hka
  simp only [parseOrt, druckToks, nameText, hkaf, List.cons_append, List.nil_append,
    List.append_assoc]
  simp only [Bool.false_eq_true, ite_false]
  exact suffM suff (.variable a) rest F' hs hr (by omega)

/-- Places through `parsePrimary` at token fuel (lane 161's `prim_platz`, restated). -/
theorem prim_platzM (a : String) (suff : List SuffFrag) (rest : List Token) (F : Nat)
    (hka : (!istKeinPlatz a) = true) (hs : SuffLegs suff) (hr : ruhigSuff rest = true)
    (hF : 6 * (suffToks suff).length + 31 ≤ F) :
    parsePrimary F (druckToks (applySuff (.variable a) suff) ++ rest) =
      .ok (applySuff (.variable a) suff, rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  rw [druckToks_applySuff]
  have hkaf : istKeinPlatz a = false := nichtWahr_falsch _ hka
  simp only [parsePrimary, druckToks, nameText, hkaf, List.cons_append,
    parseKopf]
  simp only [List.nil_append]
  simp only [sammleSeg_suffToks, hr]
  have hmiss : ∀ (R : List Token), suffToks suff ++ rest ≠ .zeichen "(" :: R := by
    intro R hcon
    exact suffToks_nopar suff rest R hr hcon
  simp only [hmiss]
  exact suffM suff (.variable a) rest F'' hs hr (by omega)

/-- Size and printability of index payloads. -/
theorem suff_idx_mem : ∀ (suff : List SuffFrag) (i : SExpr), SuffFrag.idx i ∈ suff →
    suffGut suff = true → groesse i ≤ suffGroesse suff ∧ gut i = true := by
  intro suff
  induction suff with
  | nil => intro i h; simp at h
  | cons f s ih =>
    intro i h hg
    simp only [List.mem_cons] at h
    cases f with
    | dot g =>
      simp only [suffGut] at hg
      rcases h with h | h
      · cases h
      · obtain ⟨h1, h2⟩ := ih i h hg; exact ⟨by simp only [suffGroesse]; omega, h2⟩
    | arrow g =>
      simp only [suffGut] at hg
      rcases h with h | h
      · cases h
      · obtain ⟨h1, h2⟩ := ih i h hg; exact ⟨by simp only [suffGroesse]; omega, h2⟩
    | idx j =>
      simp only [suffGut, Bool.and_eq_true] at hg
      rcases h with h | h
      · cases h; simp only [suffGroesse]; exact ⟨by omega, hg.1⟩
      · obtain ⟨h1, h2⟩ := ih i h hg.2; exact ⟨by simp only [suffGroesse]; omega, h2⟩

/-! ### Calls -/

/-- One argument through `parseArg` at token fuel (mirror of `arg_legs`). -/
theorem argM (x : SExpr) (sep : Token) (S : List Token) (F : Nat)
    (hL : LegsB (fb x) x) (hxg : gut x = true)
    (hsep : sep = .zeichen "," ∨ sep = .zeichen ")") (hF : fb x + 9 ≤ F) :
    parseArg F (druckToks x ++ [sep] ++ S) = .ok (x, [sep] ++ S) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hmiss : ∀ (t0 : Token) (rest : List Token),
      druckToks x ++ [sep] ++ S ≠ t0 :: .zeichen ":" :: rest := by
    intro t0 rest hcon
    have hne : druckToks x ≠ [] := by
      intro he
      have hlen := toksLang (groesse x) x (Nat.le_refl _)
      rw [he] at hlen
      simp at hlen
    obtain ⟨a, R2, hxb⟩ := List.exists_cons_of_ne_nil hne
    rw [hxb] at hcon
    simp only [List.cons_append] at hcon
    injection hcon with _ ht
    cases hR : R2 with
    | nil =>
      rw [hR] at ht
      simp only [List.nil_append, List.cons_append] at ht
      injection ht with hsep2 _
      cases hsep with
      | inl h => subst h; simp at hsep2
      | inr h => subst h; simp at hsep2
    | cons b R3 =>
      rw [hR] at ht
      simp only [List.cons_append] at ht
      injection ht with hb _
      have hbmem : b ∈ druckToks x := by simp [hxb, hR]
      exact keinDP_tree (groesse x) x (Nat.le_refl _) hxg b hbmem hb
  simp only [parseArg]
  have hr1 : ruhig ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hr2 : ruhigSuff ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hr3 : ruhigGleit ([sep] ++ S) = true := by
    cases hsep with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hOr := hL.2.2.2.2.2.2.2 ([sep] ++ S) F' hr1 hr2 hr3 (by omega)
  simpa only [List.append_assoc] using hOr

theorem kopf_nicht_zu (x : SExpr) (hxg : gut x = true) (S : List Token) (R2 : List Token) :
    druckToks x ++ S ≠ .zeichen ")" :: R2 := by
  intro hcon
  have hkop := toksKopf (groesse x) x (Nat.le_refl _) hxg
  have hne : druckToks x ≠ [] := by
    intro he
    have hlen := toksLang (groesse x) x (Nat.le_refl _)
    rw [he] at hlen
    simp at hlen
  obtain ⟨a, R3, hxb⟩ := List.exists_cons_of_ne_nil hne
  have ha := hkop a R3 hxb
  rw [hxb] at hcon
  simp only [List.cons_append] at hcon
  injection hcon with ha2 _
  exact ha ha2

/-- Whole argument lists through `parseArgs` at token fuel (mirror of `args_legs`). -/
theorem argsM : ∀ (xs : List SExpr) (rest : List Token) (F : Nat),
    (∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true) →
    6 * (druckToksListe xs).length + 36 ≤ F →
    parseArgs F (druckToksListe xs ++ [.zeichen ")"] ++ rest) = .ok (xs, rest) := by
  intro xs
  induction xs with
  | nil =>
    intro rest F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseArgs, druckToksListe, List.nil_append, List.cons_append]
  | cons x zs ihzs =>
    intro rest F hs hF
    obtain ⟨hLx, hxg⟩ := hs x (by simp)
    have hzs : ∀ y ∈ zs, LegsB (fb y) y ∧ gut y = true :=
      fun y hy => hs y (List.mem_cons_of_mem _ hy)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases zs with
    | nil =>
      rw [args_einzeln] at ⊢ hF
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ")"] ++ rest ≠ .zeichen ")" :: R2 := by
        intro R2; rw [List.append_assoc]; exact kopf_nicht_zu x hxg _ R2
      simp only [parseArgs, hmiss2]
      have harg := argM x (.zeichen ")") rest F' hLx hxg (Or.inr rfl)
        (by simp only [fb] at ⊢; omega)
      simp only [harg, List.cons_append]
      rfl
    | cons y ys =>
      rw [args_cons] at ⊢ hF
      simp only [List.length_append, List.length_cons, List.length_nil] at hF
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ","] ++ druckToksListe (y :: ys) ++
            [.zeichen ")"] ++ rest ≠ .zeichen ")" :: R2 := by
        intro R2; simp only [List.append_assoc]; exact kopf_nicht_zu x hxg _ R2
      simp only [parseArgs, hmiss2]
      have harg := argM x (.zeichen ",")
        (druckToksListe (y :: ys) ++ [.zeichen ")"] ++ rest) F'
        hLx hxg (Or.inl rfl) (by simp only [fb] at ⊢; omega)
      have htail := ihzs rest F' hzs (by omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ harg htail
      simp only [harg, htail, List.cons_append, List.nil_append]

/-- Calls through `parsePrimary` at token fuel (mirror of `prim_ruf_legs`). -/
theorem prim_rufM (f : String) (xs : List SExpr) (rest : List Token) (F : Nat)
    (hf : (!istKeinPlatz f) = true) (hxs : ∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true)
    (hF : 6 * (druckToksListe xs).length + 38 ≤ F) :
    parsePrimary F (druckToks (.call f xs) ++ rest) = .ok (.call f xs, rest) := by
  have hkaf : istKeinPlatz f = false := nichtWahr_falsch _ hf
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, parsePrimary]
  simp only [nameText, hkaf]
  have hne : ¬(false = true) := by decide
  simp only [if_neg hne]
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [kopf_ruf_head]
  have hA := argsM xs rest F'' hxs (by omega)
  simp only [List.append_assoc] at hA ⊢
  simp only [List.nil_append, hA]

/-! ### `old`, `sizeof`, `lenof`, `aligned` -/

theorem prim_altM (a : String) (suff : List SuffFrag) (rest : List Token) (F : Nat)
    (hka : (!istKeinPlatz a) = true) (hs : SuffLegs suff) (hr : ruhigSuff rest = true)
    (hF : 6 * (suffToks suff).length + 31 ≤ F) :
    parsePrimary F (druckToks (.old (applySuff (.variable a) suff)) ++ rest) =
      .ok (.old (applySuff (.variable a) suff), rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, parsePrimary]
  have hO := ortM a suff ([.zeichen ")"] ++ rest) F' hka hs (hrs_paren rest) (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
  simp only [hO, List.cons_append]

theorem prim_emb1M (w : String) (a : String) (suff : List SuffFrag) (rest : List Token) (F : Nat)
    (hw : w = "sizeof" ∨ w = "lenof") (hka : (!istKeinPlatz a) = true) (hs : SuffLegs suff)
    (hp : gutPlatz (applySuff (.variable a) suff) = true)
    (htw : (!istTypWortVar (applySuff (.variable a) suff)) = true)
    (hr : ruhigSuff rest = true) (hF : 6 * (suffToks suff).length + 32 ≤ F) :
    parsePrimary F (druckToks (.built w [applySuff (.variable a) suff]) ++ rest) =
      .ok (.built w [applySuff (.variable a) suff], rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  have hO := ortM a suff ([.zeichen ")"] ++ rest) F'' hka hs (hrs_paren rest) (by omega)
  obtain rfl | rfl := hw
  · simp only [druckToks, args_einzeln, List.cons_append, parsePrimary]
    simp only [parseEingebaut_ein]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
    simp only [hO]
    exact eingebaut_ein_ok "sizeof" _ rest hp htw
  · simp only [druckToks, args_einzeln, List.cons_append, parsePrimary]
    simp only [parseEingebaut_ein]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hO
    simp only [hO]
    exact eingebaut_ein_ok "lenof" _ rest hp htw

theorem prim_alignedM (m : Nat) (a b : SExpr) (rest : List Token) (F : Nat)
    (hLa : LegsB m a) (hLb : LegsB m b)
    (hF : m + 10 ≤ F) :
    parsePrimary F (druckToks (.built "aligned" [a, b]) ++ rest) =
      .ok (.built "aligned" [a, b], rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, args_cons, args_einzeln, List.cons_append, parsePrimary]
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [parseEingebaut_zwei]
  have hkomma : ruhig ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) = true := rfl
  have hskomma : ruhigSuff ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) = true :=
    rfl
  have hgkomma : ruhigGleit ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) = true :=
    rfl
  have hOa := hLa.2.2.2.2.2.2.2 ([.zeichen ","] ++ druckToks b ++ ([.zeichen ")"] ++ rest)) F''
    hkomma hskomma hgkomma (by omega)
  have hOb := hLb.2.2.2.2.2.2.2 ([.zeichen ")"] ++ rest) F''
    (hr_paren rest) (hrs_paren rest) (hrg_paren rest) (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOa hOb
  simp only [hOa, hOb]

/-! ### The joint induction at token fuel -/

theorem legs_tok_n : ∀ (n : Nat) (e : SExpr), groesse e ≤ n → gut e = true → LegsB (fb e) e := by
  intro n
  induction n with
  | zero =>
    intro e hs _
    have := groesse_pos e
    omega
  | succ n ih =>
    intro e hs hg
    -- Leaves: the size-bound legs (`Legs`, bound 25) raised to the token bound.
    have blatt : Legs e → groesse e = 1 → LegsB (fb e) e := by
      intro hL h1
      apply LegsB_mono _ (legsB_of_legs e hL)
      simp only [fb, h1]
      omega
    -- Places: decompose, payload legs from the hypothesis, the primary leg by `prim_platzM`.
    have platz : gutPlatz e = true → LegsB (fb e) e := by
      intro hp
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := zerlege (n + 1) e hs hp
      have hsl : SuffLegs suff := by
        intro i hi
        obtain ⟨hgi, hi'⟩ := suff_idx_mem suff i hi hgs
        exact ih i (by omega) hi'
      have hd : druckToks (applySuff (.variable a) suff) = [.ident a] ++ suffToks suff := by
        rw [druckToks_applySuff]; rfl
      apply legsB_kopf _ (.ident a) _ (Or.inl ⟨a, rfl⟩) hd
      intro rest' G hrs _ hG
      apply prim_platzM a suff rest' G hka hsl hrs
      simp only [fb, hd, List.length_append, List.length_singleton] at hG
      omega
    cases e with
    | lit m => exact blatt (legsKern _ rfl) rfl
    | float s => exact blatt (legsKern _ rfl) rfl
    | tru => exact blatt (legsKern _ rfl) rfl
    | fls => exact blatt (legsKern _ rfl) rfl
    | «variable» s => exact blatt (legsKern _ hg) rfl
    | field x f => exact platz hg
    | index x i => exact platz hg
    | arrow x f => exact platz hg
    | un o x =>
      simp only [gut, Bool.and_eq_true] at hg
      have hx : groesse x ≤ n := by simp only [groesse] at hs; omega
      have Hx := ih x hx hg.2
      cases hat : istAtom x with
      | true =>
        apply LegsB_mono _ (unLegsM_atom _ o x hg.1 hat Hx)
        simp only [fb, druckToks, hat, ite_true, List.length_append, List.length_singleton]
        omega
      | false =>
        apply LegsB_mono _ (unLegsM_klammer _ o x hg.1 hat Hx)
        simp only [fb, druckToks, hat, Bool.false_eq_true, ite_false, List.length_append,
          List.length_singleton]
        omega
    | bin o l r =>
      simp only [gut, Bool.and_eq_true] at hg
      have hl : groesse l ≤ n := by simp only [groesse] at hs; omega
      have hr : groesse r ≤ n := by simp only [groesse] at hs; omega
      have Hl := LegsB_mono (Nat.le_max_left (fb l) (fb r)) (ih l hl hg.1.2)
      have Hr := LegsB_mono (Nat.le_max_right (fb l) (fb r)) (ih r hr hg.2)
      apply LegsB_mono _ (binLegsM _ o l r hg.1.1 Hl Hr)
      simp only [fb, druckToks, List.length_append, List.length_singleton]
      omega
    | call f xs =>
      simp only [gut, Bool.and_eq_true] at hg
      have hxs : ∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true := by
        intro x hx
        have hgx := gutListe_mem xs x hx hg.2
        have hsx : groesse x ≤ n := by
          have := groesse_mem_le xs x hx
          simp only [groesse] at hs; omega
        exact ⟨ih x hsx hgx, hgx⟩
      have hd : druckToks (.call f xs) = [.ident f] ++
          ([.zeichen "("] ++ druckToksListe xs ++ [.zeichen ")"]) := by
        simp [druckToks]
      apply legsB_kopf _ (.ident f) _ (Or.inl ⟨f, rfl⟩) hd
      intro rest' G _ _ hG
      apply prim_rufM f xs rest' G hg.1 hxs
      simp only [fb, hd, List.length_append, List.length_singleton] at hG
      omega
    | fnref p => exact blatt (fnwertLegs p) rfl
    | built w xs =>
      rcases gut_built_faelle w xs hg with ⟨x, hw, rfl, hp, htw⟩ | ⟨a, b, rfl, rfl, ha, hb⟩
      · obtain ⟨c, suff, rfl, hka, hgs, hsz⟩ := zerlege (n + 1) x
          (by simp only [groesse, groesseListe] at hs; omega) hp
        have hsl : SuffLegs suff := by
          intro i hi
          obtain ⟨hgi, hi'⟩ := suff_idx_mem suff i hi hgs
          have : groesse (applySuff (.variable c) suff) ≤ n := by
            simp only [groesse, groesseListe] at hs; omega
          rw [groesse_applySuff] at this
          exact ih i (by simp only [groesse] at this; omega) hi'
        have hd : druckToks (.built w [applySuff (.variable c) suff]) = [.wort w] ++
            ([.zeichen "("] ++ druckToksListe [applySuff (.variable c) suff] ++
              [.zeichen ")"]) := by
          simp [druckToks]
        apply legsB_kopf _ (.wort w) _ (Or.inr ⟨w, rfl⟩) hd
        intro rest' G hrs _ hG
        apply prim_emb1M w c suff rest' G hw hka hsl hp htw hrs
        simp only [fb, hd, args_einzeln, druckToks_applySuff, List.length_append,
          List.length_singleton] at hG
        simp only [druckToks, List.length_singleton] at hG
        omega
      · have ha' : groesse a ≤ n := by simp only [groesse, groesseListe] at hs; omega
        have hb' : groesse b ≤ n := by simp only [groesse, groesseListe] at hs; omega
        have hd : druckToks (.built "aligned" [a, b]) = [.wort "aligned"] ++
            ([.zeichen "("] ++ druckToksListe [a, b] ++ [.zeichen ")"]) := by
          simp [druckToks]
        apply legsB_kopf _ (.wort "aligned") _ (Or.inr ⟨_, rfl⟩) hd
        intro rest' G _ _ hG
        apply prim_alignedM (max (fb a) (fb b)) a b rest' G
          (LegsB_mono (Nat.le_max_left _ _) (ih a ha' ha))
          (LegsB_mono (Nat.le_max_right _ _) (ih b hb' hb))
        simp only [fb, hd, args_cons, args_einzeln, List.length_append,
          List.length_singleton] at hG ⊢
        omega
    | old x =>
      simp only [gut] at hg
      obtain ⟨c, suff, rfl, hka, hgs, hsz⟩ := zerlege (n + 1) x
        (by simp only [groesse] at hs; omega) hg
      have hsl : SuffLegs suff := by
        intro i hi
        obtain ⟨hgi, hi'⟩ := suff_idx_mem suff i hi hgs
        exact ih i (by omega) hi'
      have hd : druckToks (.old (applySuff (.variable c) suff)) = [.wort "old"] ++
          ([.zeichen "("] ++ druckToks (applySuff (.variable c) suff) ++ [.zeichen ")"]) := by
        simp [druckToks]
      apply legsB_kopf _ (.wort "old") _ (Or.inr ⟨_, rfl⟩) hd
      intro rest' G hrs _ hG
      apply prim_altM c suff rest' G hka hsl hrs
      simp only [fb, hd, druckToks_applySuff, List.length_append,
        List.length_singleton] at hG
      simp only [druckToks, List.length_singleton] at hG
      omega
    | res => exact blatt ergebnisLegs rfl
    | why g f =>
      simp only [gut, Bool.and_eq_true] at hg
      exact blatt (grundLegs g f hg.1.1.1 hg.1.1.2 hg.1.2 hg.2) rfl
    | ext k ns xs => simp [gut] at hg

/-- **Every printable expression has its legs at the token bound.** -/
theorem legs_tok : ∀ (e : SExpr), gut e = true → LegsB (fb e) e :=
  fun e hg => legs_tok_n (groesse e) e (Nat.le_refl _) hg

/-- **L2a at token fuel**: a printable expression parses back through `parseOr` before any benign
    follow, with any fuel from `fb e + 8` up. -/
theorem parse_druck_tok : ∀ (e : SExpr) (rest : List Token) (F : Nat), gut e = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    fb e + 8 ≤ F → parseOr F (druckToks e ++ rest) = .ok (e, rest) :=
  fun e rest F hg hr hrs hrg hF => (legs_tok e hg).2.2.2.2.2.2.2 rest F hr hrs hrg hF

/-- **The whole expression reader** (`parseTop`, fuel `8 * length + 32`) returns every printable
    expression from its tokens. -/
theorem parseTop_druck_gut : ∀ (e : SExpr), gut e = true →
    parseTop (druckToks e ++ [.ende]) = .ok e := by
  intro e hg
  unfold parseTop
  rw [parse_druck_tok e [.ende] _ hg rfl rfl rfl (by
    simp only [fb, List.length_append, List.length_cons, List.length_nil]; omega)]

/-- **Composition with L1: from source text.** A printable expression whose print is lexically
    clean is read back from its rendered text by the front end (lexer, then `parseTop`). -/
theorem rundlauf_text_gut : ∀ (e : SExpr), gut e = true → (∀ t ∈ druckToks e, TokGut t) →
    parseTopAusText (renderText (druckToks e)) = .ok e := by
  intro e hg ht
  unfold parseTopAusText
  rw [lex_render _ ht]
  exact parseTop_druck_gut e hg

/-! ### Witnesses -/

/-- The many-small-nodes shape the size bound cannot reach (`a[!x][!y][!z]` -- three nodes per
    four tokens), through the whole reader. -/
theorem parseTop_druck_gut_zeuge :
    parseTop (druckToks (.index (.index (.index (.variable "a") (.un "!" (.variable "x")))
      (.un "!" (.variable "y"))) (.un "!" (.variable "z"))) ++ [.ende]) =
      .ok (.index (.index (.index (.variable "a") (.un "!" (.variable "x")))
      (.un "!" (.variable "y"))) (.un "!" (.variable "z"))) :=
  parseTop_druck_gut _ (by decide)

/-- The deep witness of `RundlaufVoll` from its rendered source text. -/
theorem rundlauf_text_gut_zeuge :
    parseTopAusText (renderText (druckToks zeugeTief)) = .ok zeugeTief :=
  rundlauf_text_gut zeugeTief zeugeTief_gut (tokGut_of_all _ (by decide))

end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.legs_tok
#print axioms Gabbro.Grammatik.Parser.parse_druck_tok
#print axioms Gabbro.Grammatik.Parser.parseTop_druck_gut
#print axioms Gabbro.Grammatik.Parser.rundlauf_text_gut
#print axioms Gabbro.Grammatik.Parser.parseTop_druck_gut_zeuge
#print axioms Gabbro.Grammatik.Parser.rundlauf_text_gut_zeuge
