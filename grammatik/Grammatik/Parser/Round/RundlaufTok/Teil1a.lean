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
module

public import Grammatik.Parser.Round.RundlaufVoll

@[expose] public section



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


end Gabbro.Grammatik.Parser
