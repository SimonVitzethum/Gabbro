/-
  File:      Grammatik/Parser/Rundlauf2.lean
  Subject:   T3 (lane 172): the round-trip MAIN induction, one level at a
             time (MUSE-REPORT-161 "Open" first).

  Lane 161 built the printer (`druckToks`), the fuel bound
  (`brennstoff`), the printability predicate (`gut`), the stop lemmas
  and the single-constructor primaries, but left `prim_bin`,
  `un_X_all`, `B_one`, `rundlauf_n` and `parse_druck` open: aiming at
  all constructors at once never closed.

  This file avoids that trap: it proves the round trip for a
  SUB-grammar first and widens the predicate level by level, each
  step green before the next starts.

  Step A (this chunk and the next): `gutKern` -- literals, variables,
  unary `!` and parenthesised binary operators of ONE precedence
  level (`+`). The invariant `RKern n` is lane 161's `R n`
  restricted to `gutKern`, with one deliberate change: `parseUnary`
  and `parsePrimary` take NO `ruhig` premise (they run no loop, so a
  loop operator behind the tree never reaches them -- the inner left
  operand of `B` parses with a `+` behind it). `BKern n` is the
  binary-inner parse for `+` with a general tail `W` (the tail
  behind `)` is never inspected, so it takes no follow premise).
  Both are proved together (`kernRB`) by size induction on `n`,
  following the file conventions (no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`; every premise used).
-/
import Grammatik.Parser.Rundlauf

namespace Gabbro.Grammatik.Parser

-- Step A predicate: literals (all four leaf shapes), variables,
-- unary `!`, parenthesised `+`. Everything else is `false`
-- (calls, places/suffixes, the other five operator levels,
-- `sizeof`/`old`/`Grund` come in step B).
def gutKern : SExpr → Bool
  | .lit _ => true
  | .gleit _ => true
  | .wahr => true
  | .falsch => true
  | .variable s => !istKeinPlatz s
  | .un o x => strEq o "!" && gutKern x
  | .bin o l r => strEq o "+" && gutKern l && gutKern r
  | _ => false

-- Unfolding equations for the two recursive arms, as plain rewrite
-- rules (kernel-checked; the `gutKern` match has literal arms that
-- `simp` equations do not select -- same reason as lane 161's
-- `gut_sizeof_one` family).
theorem gutKern_un : ∀ (o : String) (x : SExpr),
    gutKern (.un o x) = (strEq o "!" && gutKern x) := by
  intro o x
  rfl
theorem gutKern_bin : ∀ (o : String) (l r : SExpr),
    gutKern (.bin o l r) = (strEq o "+" && gutKern l && gutKern r) := by
  intro o l r
  rfl

-- A `gutKern` tree is printable (`gut`): the bridge step B needs
-- when it reuses lane 161's lemmas. By cases (places only exclude
-- more; `+` is a lawful `gutOpBin` spelling by `decide`).
theorem gut_of_gutKern : ∀ (e : SExpr),
    gutKern e = true → gut e = true := by
  intro e h
  cases e with
  | lit m => rfl
  | gleit s => rfl
  | wahr => rfl
  | falsch => rfl
  | «variable» s =>
    simp only [gutKern] at h
    simp only [gut] at ⊢
    exact h
  | feld x f => simp [gutKern] at h
  | index x i => simp [gutKern] at h
  | pfeil x f => simp [gutKern] at h
  | un o x =>
    rw [gutKern_un] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hop, hx⟩ := h
    have ho : o = "!" := strKlingt o "!" hop
    subst ho
    simp only [gut, Bool.and_eq_true] at ⊢
    refine ⟨?_, gut_of_gutKern x hx⟩
    decide
  | bin o l r =>
    rw [gutKern_bin] at h
    simp only [Bool.and_eq_true, and_assoc] at h
    obtain ⟨hop, hl, hr⟩ := h
    have ho : o = "+" := strKlingt o "+" hop
    subst ho
    simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
    refine ⟨?_, gut_of_gutKern l hl, gut_of_gutKern r hr⟩
    decide
  | ruf f xs => simp [gutKern] at h
  | fnwert f => simp [gutKern] at h
  | eingebaut f xs => simp [gutKern] at h
  | alt x => simp [gutKern] at h
  | ergebnis => simp [gutKern] at h
  | grund g f => simp [gutKern] at h

-- The round-trip invariant at size bound `n`, restricted to
-- `gutKern`. Seven loop levels take the benign follow (`ruhig`
-- for the loops, `ruhigSuff` for the suffixes, `ruhigGleit` for
-- the float tail); `parseUnary` and `parsePrimary` take NO `ruhig`
-- premise (no loop inspects the tail there) and `parsePrimary`
-- takes `primFrei` (prefix trees live at the unary level).
-- Fuel copies lane 161's `R` (twelve per node, one spare per
-- node), but STAGGERED per level: every descent from a level to
-- the one below strips one fuel from the SAME tree, so a uniform
-- bound cannot thread (measured 2026-09-14: `omega` refuses
-- `X + 8 ≤ G'` from `X + 8 ≤ G' + 1`, and it is right). `parseOr`
-- takes `+8`, each level below one less, `parsePrimary` `+1`;
-- every application below a strip closes by `omega` with the
-- size terms opaque, and every application at a smaller tree by
-- `omega` with the size equation.
def RKern (n : Nat) : Prop :=
  (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 8 ≤ F →
    parseOr F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 7 ≤ F →
    parseAnd F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 6 ≤ F →
    parseCmp F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 5 ≤ F →
    parseBit F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 4 ≤ F →
    parseAdd F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 3 ≤ F →
    parseMul F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gutKern e = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 2 ≤ F →
    parseUnary F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gutKern e = true → primFrei e = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 1 ≤ F →
    parsePrimary F (druckToks e ++ rest) = .ok (e, rest))

-- The binary-inner parse for `+`: a parenthesised `+`'s inside
-- (`l + r` between the parens) with a general tail `W`. No follow
-- premise: the tail behind `)` is never inspected. Fuel `+10`:
-- twelve same-tree strips along the inner trace (six descents,
-- six loop closes), counted 2026-09-14 -- lane 161's `+8` never
-- reached this lemma (`B_one` stayed open).
def BKern (n : Nat) : Prop :=
  ∀ (l r : SExpr) (W : List Token) (F : Nat),
    groesse l + groesse r ≤ n → gutKern l = true → gutKern r = true →
    12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ F →
    parseOr F (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
      [.zeichen ")"] ++ W) =
      .ok (.bin "+" l r, [.zeichen ")"] ++ W)

-- Places through `parsePrimary` for a bare variable head: the
-- `(` call arm misses (the tail is benign), the segment reader
-- stops, the suffix reader stops. Needs no induction hypothesis
-- (the fragment list is empty), hence standalone.
theorem kern_prim_var : ∀ (a : String) (rest : List Token) (F : Nat),
    (!istKeinPlatz a) = true → ruhigSuff rest = true →
    12 * (groesse (.variable a) + 1) + groesse (.variable a) + 1 ≤ F →
    parsePrimary F (druckToks (.variable a) ++ rest) =
      .ok (.variable a, rest) := by
  intro a rest F hka hrs hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hkaf : istKeinPlatz a = false := nichtWahr_falsch _ hka
  simp only [druckToks, List.cons_append, List.nil_append, parsePrimary,
    nameText, hkaf] at ⊢
  -- ⊢ : `parseKopf` on the head word. One more strip, the
  -- segment reader stops on the benign tail, the `([a], …)` arm
  -- runs the suffix reader, which stops too.
  have hF2 : 1 ≤ F' := by omega
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  have hseg := sammleSeg_stop [a] rest hrs
  -- The `(` call arm of the `parseKopf` match cannot fire on a
  -- benign tail (prunes the stuck arm); the `if` residue closes
  -- by constructor discrimination.
  have hmiss : ∀ (R : List Token), rest ≠ .zeichen "(" :: R :=
    ruhigSuff_nopar rest hrs
  simp only [parseKopf, nameText, hseg, hkaf, hmiss,
    Bool.false_ne_true] at ⊢
  have hF3 : 1 ≤ F'' := by omega
  obtain ⟨F''', rfl⟩ : ∃ F''', F'' = F''' + 1 := ⟨F'' - 1, by omega⟩
  exact stopSuffix F''' _ _ hrs

-- The full eight-level tower for one literal shape. Every
-- leg is generalised over its own fuel (so upper levels reuse
-- lower ones at stripped fuel, and every `RKern` level
-- instantiates at its own staggered bound). Pattern for every
-- atom shape in step A.
theorem turm_lit : ∀ (m : Nat) (rest : List Token),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 1 ≤ G →
      parsePrimary G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 2 ≤ G →
      parseUnary G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 3 ≤ G →
      parseMul G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 4 ≤ G →
      parseAdd G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 5 ≤ G →
      parseBit G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 6 ≤ G →
      parseCmp G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 7 ≤ G →
      parseAnd G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 8 ≤ G →
      parseOr G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest)) := by
  intro m rest hr hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 1 ≤ G →
      parsePrimary G (druckToks (.lit m) ++ rest) =
        .ok (.lit m, rest) := by
    intro G hG
    exact prim_lit m rest G (by omega)
  have hU : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 2 ≤ G →
      parseUnary G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    simp only [parseUnary] at ⊢
    exact hP G' (by omega)
  have hM : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 3 ≤ G →
      parseMul G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopMul rest hr
    simp only [parseMul, parseMulL, hU', hstop] at ⊢
  have hA : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 4 ≤ G →
      parseAdd G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopAdd rest hr
    simp only [parseAdd, parseAddL, hM', hstop] at ⊢
  have hB : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 5 ≤ G →
      parseBit G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopBit rest hr
    simp only [parseBit, parseBitL, hA', hstop] at ⊢
  have hC : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 6 ≤ G →
      parseCmp G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hstop := stopVgl rest hr
    simp only [parseCmp, hB', hstop] at ⊢
  have hN : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 7 ≤ G →
      parseAnd G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hC' := hC G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopUnd rest hr
    simp only [parseAnd, parseAndL, hC', hstop] at ⊢
  have hO : ∀ (G : Nat),
      12 * (groesse (.lit m) + 1) + groesse (.lit m) + 8 ≤ G →
      parseOr G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hN' := hN G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hstop := stopOder rest hr
    simp only [parseOr, parseOrL, hN', hstop] at ⊢
  exact ⟨hP, hU, hM, hA, hB, hC, hN, hO⟩

-- The shape-independent upper tower (`parseMul` up to
-- `parseOr`): every level runs its child and stops its loop on
-- the benign follow. Callers supply the `parseUnary` leg (which
-- is the only head-dependent step) generalised over its fuel;
-- every leg is returned generalised, so each `RKern` level
-- instantiates at its own staggered bound.
theorem tower_up : ∀ (e : SExpr) (rest : List Token),
    ruhig rest = true →
    (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 2 ≤ G →
      parseUnary G (druckToks e ++ rest) = .ok (e, rest)) →
    (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 3 ≤ G →
      parseMul G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 4 ≤ G →
      parseAdd G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 5 ≤ G →
      parseBit G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 6 ≤ G →
      parseCmp G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 7 ≤ G →
      parseAnd G (druckToks e ++ rest) = .ok (e, rest))
    ∧ (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 8 ≤ G →
      parseOr G (druckToks e ++ rest) = .ok (e, rest)) := by
  intro e rest hr hU
  have hM : ∀ (G : Nat),
      12 * (groesse e + 1) + groesse e + 3 ≤ G →
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
      12 * (groesse e + 1) + groesse e + 4 ≤ G →
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
      12 * (groesse e + 1) + groesse e + 5 ≤ G →
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
      12 * (groesse e + 1) + groesse e + 6 ≤ G →
      parseCmp G (druckToks e ++ rest) = .ok (e, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hstop := stopVgl rest hr
    simp only [parseCmp, hB', hstop] at ⊢
  have hN : ∀ (G : Nat),
      12 * (groesse e + 1) + groesse e + 7 ≤ G →
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
      12 * (groesse e + 1) + groesse e + 8 ≤ G →
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

-- A bare atom head is `primFrei` (only prefix trees and
-- `fnwert` are not).
theorem primFrei_of_atom : ∀ (x : SExpr), istAtom x = true →
    gutKern x = true → primFrei x = true := by
  intro x hat hgx
  cases x with
  | lit m => rfl
  | gleit s => rfl
  | wahr => rfl
  | falsch => rfl
  | «variable» s => rfl
  | feld x f => simp [gutKern] at hgx
  | index x i => simp [gutKern] at hgx
  | pfeil x f => simp [gutKern] at hgx
  | un o y => simp [istAtom] at hat
  | bin o l r => simp [istAtom] at hat
  | ruf f xs => simp [gutKern] at hgx
  | fnwert f => simp [istAtom] at hat
  | eingebaut f xs => simp [gutKern] at hgx
  | alt x => simp [gutKern] at hgx
  | ergebnis => simp [gutKern] at hgx
  | grund g f => simp [gutKern] at hgx

-- Atom towers, one per remaining leaf shape: the `parsePrimary`
-- leg (concrete head) plus the `parseUnary` fall-through (head is
-- no prefix operator), then `tower_up` for the six loop levels.
theorem turm_gleit : ∀ (s : String) (rest : List Token),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 1 ≤ G →
      parsePrimary G (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 2 ≤ G →
      parseUnary G (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 3 ≤ G →
      parseMul G (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 4 ≤ G →
      parseAdd G (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 5 ≤ G →
      parseBit G (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 6 ≤ G →
      parseCmp G (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 7 ≤ G →
      parseAnd G (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 8 ≤ G →
      parseOr G (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest)) := by
  intro s rest hr hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 1 ≤ G →
      parsePrimary G (druckToks (.gleit s) ++ rest) =
        .ok (.gleit s, rest) := by
    intro G hG
    exact prim_gleit s rest G hrg (by omega)
  have hU : ∀ (G : Nat),
      12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 2 ≤ G →
      parseUnary G (druckToks (.gleit s) ++ rest) =
        .ok (.gleit s, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    simp only [parseUnary] at ⊢
    exact hP G' (by omega)
  have hup := tower_up (.gleit s) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

theorem turm_wahr : ∀ (rest : List Token),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse .wahr + 1) + groesse .wahr + 1 ≤ G →
      parsePrimary G (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .wahr + 1) + groesse .wahr + 2 ≤ G →
      parseUnary G (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .wahr + 1) + groesse .wahr + 3 ≤ G →
      parseMul G (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .wahr + 1) + groesse .wahr + 4 ≤ G →
      parseAdd G (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .wahr + 1) + groesse .wahr + 5 ≤ G →
      parseBit G (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .wahr + 1) + groesse .wahr + 6 ≤ G →
      parseCmp G (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .wahr + 1) + groesse .wahr + 7 ≤ G →
      parseAnd G (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .wahr + 1) + groesse .wahr + 8 ≤ G →
      parseOr G (druckToks .wahr ++ rest) = .ok (.wahr, rest)) := by
  intro rest hr hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse .wahr + 1) + groesse .wahr + 1 ≤ G →
      parsePrimary G (druckToks .wahr ++ rest) = .ok (.wahr, rest) := by
    intro G hG
    exact prim_wahr rest G (by omega)
  have hU : ∀ (G : Nat),
      12 * (groesse .wahr + 1) + groesse .wahr + 2 ≤ G →
      parseUnary G (druckToks .wahr ++ rest) = .ok (.wahr, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    simp only [parseUnary] at ⊢
    exact hP G' (by omega)
  have hup := tower_up .wahr rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

theorem turm_falsch : ∀ (rest : List Token),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse .falsch + 1) + groesse .falsch + 1 ≤ G →
      parsePrimary G (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .falsch + 1) + groesse .falsch + 2 ≤ G →
      parseUnary G (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .falsch + 1) + groesse .falsch + 3 ≤ G →
      parseMul G (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .falsch + 1) + groesse .falsch + 4 ≤ G →
      parseAdd G (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .falsch + 1) + groesse .falsch + 5 ≤ G →
      parseBit G (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .falsch + 1) + groesse .falsch + 6 ≤ G →
      parseCmp G (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .falsch + 1) + groesse .falsch + 7 ≤ G →
      parseAnd G (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (∀ (G : Nat), 12 * (groesse .falsch + 1) + groesse .falsch + 8 ≤ G →
      parseOr G (druckToks .falsch ++ rest) = .ok (.falsch, rest)) := by
  intro rest hr hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse .falsch + 1) + groesse .falsch + 1 ≤ G →
      parsePrimary G (druckToks .falsch ++ rest) = .ok (.falsch, rest) := by
    intro G hG
    exact prim_falsch rest G (by omega)
  have hU : ∀ (G : Nat),
      12 * (groesse .falsch + 1) + groesse .falsch + 2 ≤ G →
      parseUnary G (druckToks .falsch ++ rest) = .ok (.falsch, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    simp only [parseUnary] at ⊢
    exact hP G' (by omega)
  have hup := tower_up .falsch rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

theorem turm_var : ∀ (a : String) (rest : List Token),
    (!istKeinPlatz a) = true → ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 1 ≤ G →
      parsePrimary G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 2 ≤ G →
      parseUnary G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 3 ≤ G →
      parseMul G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 4 ≤ G →
      parseAdd G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 5 ≤ G →
      parseBit G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 6 ≤ G →
      parseCmp G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 7 ≤ G →
      parseAnd G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 8 ≤ G →
      parseOr G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest)) := by
  intro a rest hka hr hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse (.variable a) + 1) + groesse (.variable a) + 1 ≤ G →
      parsePrimary G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest) := by
    intro G hG
    exact kern_prim_var a rest G hka hrs (by omega)
  have hU : ∀ (G : Nat),
      12 * (groesse (.variable a) + 1) + groesse (.variable a) + 2 ≤ G →
      parseUnary G (druckToks (.variable a) ++ rest) =
        .ok (.variable a, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    simp only [parseUnary] at ⊢
    exact hP G' (by omega)
  have hup := tower_up (.variable a) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- Standalone arm lemmas with WHOLE-SUBTERM middles (`M`)
-- and tails (`R`): callers align by canonicalising with
-- `append_assoc` (confluent), unification assigns whole
-- subterms, so association never enters unification. This
-- isolates all match-reduction risk in three tiny probes.
theorem bang_arm : ∀ (G' : Nat) (M R : List Token) (v : SExpr),
    parsePrimary G' M = .ok (v, R) →
    parseUnary (G' + 1) ([.zeichen "!"] ++ M) =
      .ok (.un "!" v, R) := by
  intro G' M R v h
  simp only [List.cons_append, List.nil_append] at h ⊢
  simp only [parseUnary, h] at ⊢

theorem paren_arm : ∀ (G'' : Nat) (M R : List Token) (v : SExpr),
    parseOr G'' M = .ok (v, [.zeichen ")"] ++ R) →
    parsePrimary (G'' + 1) ([.zeichen "("] ++ M) =
      .ok (v, R) := by
  intro G'' M R v h
  simp only [List.cons_append, List.nil_append] at h ⊢
  simp only [parsePrimary, h] at ⊢

-- A parenthesised tree falls through `parseUnary` to
-- `parsePrimary` (`(` is no prefix operator). The catch-all arm
-- needs the four string inequalities spelled out (same pattern
-- as lane 161's `stopSuffix`: `simp` prunes the match arms from
-- the `≠` facts).
theorem un_paren_fall : ∀ (G' : Nat) (M R : List Token) (v : SExpr),
    parsePrimary G' ([.zeichen "("] ++ M) = .ok (v, R) →
    parseUnary (G' + 1) ([.zeichen "("] ++ M) = .ok (v, R) := by
  intro G' M R v h
  have n1 : ("(" : String) ≠ "!" := by decide
  have n2 : ("(" : String) ≠ "-" := by decide
  have n3 : ("(" : String) ≠ "~" := by decide
  have n4 : ("(" : String) ≠ "&" := by decide
  simp only [List.cons_append, List.nil_append] at h ⊢
  simp [parseUnary, h, n1, n2, n3, n4] at ⊢

-- The `un "!"` tower for ATOM children: the `parsePrimary`
-- leg (same follow) through the `!` arm, then `tower_up`. Split
-- from the joint tower because the primary leg is provable only
-- for atoms (`parsePrimary` fails on operator heads). No
-- `parsePrimary` component (`primFrei` is false for `un`).
theorem kern_un_atom_turm : ∀ (x : SExpr) (rest : List Token),
    istAtom x = true → ruhig rest = true →
    (∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 1 ≤ G →
      parsePrimary G (druckToks x ++ rest) = .ok (x, rest)) →
    (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 2 ≤ G →
      parseUnary G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 3 ≤ G →
      parseMul G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 4 ≤ G →
      parseAdd G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 5 ≤ G →
      parseBit G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 6 ≤ G →
      parseCmp G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 7 ≤ G →
      parseAnd G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 8 ≤ G →
      parseOr G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest)) := by
  intro x rest hat hr hPx
  have hsize : groesse (.un "!" x) = groesse x + 1 := rfl
  have hU : ∀ (G : Nat),
      12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 2 ≤ G →
      parseUnary G (druckToks (.un "!" x) ++ rest) =
        .ok (.un "!" x, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hd : druckToks (.un "!" x) =
        [.zeichen "!"] ++ druckToks x := by
      simp [druckToks, hat]
    have hP' := hPx G' (by omega)
    simp only [hd, List.append_assoc] at ⊢
    exact bang_arm _ _ _ _ hP'
  have hup := tower_up (.un "!" x) rest hr hU
  exact ⟨hU, hup.1, hup.2.1, hup.2.2.1, hup.2.2.2.1,
    hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `un "!"` tower for PARENTHESISED (non-atom) children: the
-- `parseOr` leg (`)` follow) through the `!` arm into the `(`
-- arm, then `tower_up`.
theorem kern_un_paren_turm : ∀ (x : SExpr) (rest : List Token),
    istAtom x = false → ruhig rest = true →
    (∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 8 ≤ G →
      parseOr G (druckToks x ++ ([.zeichen ")"] ++ rest)) =
        .ok (x, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 2 ≤ G →
      parseUnary G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 3 ≤ G →
      parseMul G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 4 ≤ G →
      parseAdd G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 5 ≤ G →
      parseBit G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 6 ≤ G →
      parseCmp G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 7 ≤ G →
      parseAnd G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 8 ≤ G →
      parseOr G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest)) := by
  intro x rest hat hr hOx
  have hsize : groesse (.un "!" x) = groesse x + 1 := rfl
  have hU : ∀ (G : Nat),
      12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 2 ≤ G →
      parseUnary G (druckToks (.un "!" x) ++ rest) =
        .ok (.un "!" x, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hd : druckToks (.un "!" x) = [.zeichen "!"] ++
        (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
      simp [druckToks, hat]
    have hF2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hO' := hOx G'' (by omega)
    have hPar := paren_arm _ _ _ _ hO'
    have hBang := bang_arm _ _ _ _ hPar
    simp only [hd, List.append_assoc] at ⊢
    exact hBang
  have hup := tower_up (.un "!" x) rest hr hU
  exact ⟨hU, hup.1, hup.2.1, hup.2.2.1, hup.2.2.2.1,
    hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `bin "+"` tower from a binary-inner leg: the
-- `parsePrimary` leg runs the `(` arm over the inner parse, the
-- `parseUnary` leg falls through on `(`, then `tower_up`. Every
-- leg generalised over its own fuel.
theorem kern_bin_turm : ∀ (l r : SExpr) (rest : List Token),
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest)) := by
  intro l r rest hgl hgr hr hrs hrg hB
  have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "+" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "+"] ++ druckToks r ++ [.zeichen ")"] := by
    simp [druckToks]
  have hP : ∀ (G : Nat),
      12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    -- Inner token shape for `paren_arm`: `(` head, `l + r`
    -- body, `)` tail, all left-nested exactly as printed.
    have hB' := hB G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    -- `hPar` and the goal differ by association only:
    -- canonicalise both, then they coincide.
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  have hU : ∀ (G : Nat),
      12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP G' (by omega)
    -- Canonicalise both sides; the underscores let unification
    -- infer the middle and tail (the lemma holds for any tail).
    simp only [hd, List.append_assoc] at hP' ⊢
    exact un_paren_fall _ _ _ _ hP'
  have hup := tower_up (.bin "+" l r) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- Concrete op-table and benign-follow facts for the `+`
-- inner trace (probe piece: each must close by kernel
-- evaluation on the concrete head; tails stay variable).
theorem opMul_plus : ∀ (T : List Token),
    opMul ([.zeichen "+"] ++ T) = none := by
  intro T
  rfl
theorem opAdd_plus : ∀ (T : List Token),
    opAdd ([.zeichen "+"] ++ T) = some ("+", T) := by
  intro T
  rfl
theorem opAdd_paren : ∀ (T : List Token),
    opAdd ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
theorem opBit_paren : ∀ (T : List Token),
    opBit ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
theorem opVgl_paren : ∀ (T : List Token),
    opVgl ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
theorem opUnd_paren : ∀ (T : List Token),
    opUnd ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
theorem opOder_paren : ∀ (T : List Token),
    opOder ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
theorem opMul_paren : ∀ (T : List Token),
    opMul ([.zeichen ")"] ++ T) = none := by
  intro T
  rfl
theorem hrs_plus : ∀ (T : List Token),
    ruhigSuff ([.zeichen "+"] ++ T) = true := by
  intro T
  rfl
theorem hrg_plus : ∀ (T : List Token),
    ruhigGleit ([.zeichen "+"] ++ T) = true := by
  intro T
  rfl
theorem hr_paren : ∀ (T : List Token),
    ruhig ([.zeichen ")"] ++ T) = true := by
  intro T
  rfl
theorem hrs_paren : ∀ (T : List Token),
    ruhigSuff ([.zeichen ")"] ++ T) = true := by
  intro T
  rfl
theorem hrg_paren : ∀ (T : List Token),
    ruhigGleit ([.zeichen ")"] ++ T) = true := by
  intro T
  rfl

-- The `+` inner trace (`BKern` from `RKern`): `parseOr`
-- descends Or->And->Cmp->Bit->Add, `parseAdd` runs `parseMul`
-- on `l` (the `+` follow needs no `ruhig`: `parseUnary` runs no
-- loop and `parseMulL` stops on the concrete `+`), consumes `+`
-- and `r`, stops at `)`, and every level above stops at `)`.
-- Only the `parseUnary` leg of `RKern` is used (weak premises);
-- no `ruhig` hypothesis appears anywhere. Each leg is
-- generalised over its own fuel, exactly like `tower_up`, and
-- every token list is written right-nested (the canonical form).
theorem kernB_step : ∀ (n : Nat), RKern n → BKern (n + 1) := by
  intro n rkn l r W F hsum hgl hgr hF
  obtain ⟨-, -, -, -, -, -, hUn, -⟩ := rkn
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  have hln : groesse l ≤ n := by omega
  have hrn : groesse r ≤ n := by omega
  -- Canonicalise the goal once (right-nested); every leg below
  -- is stated in this shape.
  simp only [List.append_assoc] at ⊢
  -- Left operand through `parseMul` with the `+` follow.
  have hMl : ∀ (G5 : Nat),
      12 * (groesse l + 1) + groesse l + 3 ≤ G5 →
      parseMul G5 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "+"] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G5 hG5
    have h51 : 1 ≤ G5 := by omega
    obtain ⟨G6, rfl⟩ : ∃ G6, G5 = G6 + 1 := ⟨G5 - 1, by omega⟩
    have hUl := hUn l ([.zeichen "+"] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) G6 hln hgl
      (hrs_plus _) (hrg_plus _) (by omega)
    have h52 : 1 ≤ G6 := by omega
    obtain ⟨G7, rfl⟩ : ∃ G7, G6 = G7 + 1 := ⟨G6 - 1, by omega⟩
    have hstop := opMul_plus (druckToks r ++ ([.zeichen ")"] ++ W))
    simp only [parseMul, parseMulL, hUl, hstop] at ⊢
  -- Right operand through `parseMul` with the `)` follow.
  have hMr : ∀ (G5x : Nat),
      12 * (groesse r + 1) + groesse r + 3 ≤ G5x →
      parseMul G5x (druckToks r ++ ([.zeichen ")"] ++ W)) =
        .ok (r, [.zeichen ")"] ++ W) := by
    intro G5x hG5x
    have h53 : 1 ≤ G5x := by omega
    obtain ⟨G6x, rfl⟩ : ∃ G6x, G5x = G6x + 1 := ⟨G5x - 1, by omega⟩
    have hUr := hUn r ([.zeichen ")"] ++ W) G6x hrn hgr
      (hrs_paren W) (hrg_paren W) (by omega)
    have h54 : 1 ≤ G6x := by omega
    obtain ⟨G7x, rfl⟩ : ∃ G7x, G6x = G7x + 1 := ⟨G6x - 1, by omega⟩
    have hstop := opMul_paren W
    simp only [parseMul, parseMulL, hUr, hstop] at ⊢
  -- The `parseAdd` core: `l`, consume `+`, `r`, stop at `)`.
  have hAdd : ∀ (G4 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 6 ≤ G4 →
      parseAdd G4 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ W) := by
    intro G4 hG4
    have h41 : 1 ≤ G4 := by omega
    obtain ⟨G5, rfl⟩ : ∃ G5, G4 = G5 + 1 := ⟨G4 - 1, by omega⟩
    have hMl' := hMl G5 (by omega)
    have h42 : 1 ≤ G5 := by omega
    obtain ⟨G5x, rfl⟩ : ∃ G5x, G5 = G5x + 1 := ⟨G5 - 1, by omega⟩
    have hop := opAdd_plus (druckToks r ++ ([.zeichen ")"] ++ W))
    have hMr' := hMr G5x (by omega)
    have hstop := stopAdd ([.zeichen ")"] ++ W) (hr_paren W)
    -- One more strip for the SECOND `parseAddL` (after the
    -- consume step); fuel-free (`omega` from the bound).
    have h43 : 1 ≤ G5x := by omega
    obtain ⟨G5y, rfl⟩ : ∃ G5y, G5x = G5y + 1 := ⟨G5x - 1, by omega⟩
    simp only [parseAdd, parseAddL, hMl', hop, hMr', hstop] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
  have hBit : ∀ (G3 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 7 ≤ G3 →
      parseBit G3 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ W) := by
    intro G3 hG3
    have h31 : 1 ≤ G3 := by omega
    obtain ⟨G4, rfl⟩ : ∃ G4, G3 = G4 + 1 := ⟨G3 - 1, by omega⟩
    have hAdd' := hAdd G4 (by omega)
    have h32 : 1 ≤ G4 := by omega
    obtain ⟨G4x, rfl⟩ : ∃ G4x, G4 = G4x + 1 := ⟨G4 - 1, by omega⟩
    have hstop := stopBit ([.zeichen ")"] ++ W) (hr_paren W)
    simp only [parseBit, parseBitL, hAdd', hstop] at ⊢
  have hCmp : ∀ (G2 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 8 ≤ G2 →
      parseCmp G2 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBit' := hBit G3 (by omega)
    have hstop := opVgl_paren W
    simp only [parseCmp, hBit', hstop] at ⊢
  have hAnd : ∀ (G1 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    have h11 : 1 ≤ G1 := by omega
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hCmp' := hCmp G2 (by omega)
    have h12 : 1 ≤ G2 := by omega
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hCmp', hstop] at ⊢
  have hOr : ∀ (G0 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen "+"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr F hF

-- The `un "!"` legs from the induction hypothesis: atoms
-- take the primary leg (via `primFrei_of_atom`), parenthesised
-- children the `parseOr` leg with `)` follow. Returns the seven
-- generalised legs (no primary: `primFrei` is false for `un`).
theorem turm_un : ∀ (n : Nat), RKern n →
    ∀ (x : SExpr) (rest : List Token),
    groesse (.un "!" x) ≤ n + 1 → gutKern x = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 2 ≤ G →
      parseUnary G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 3 ≤ G →
      parseMul G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 4 ≤ G →
      parseAdd G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 5 ≤ G →
      parseBit G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 6 ≤ G →
      parseCmp G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 7 ≤ G →
      parseAnd G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 8 ≤ G →
      parseOr G (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest)) := by
  intro n rkn x rest hs hgx hr hrs hrg
  obtain ⟨rOr, -, -, -, -, -, -, rPr⟩ := rkn
  have hsize : groesse (.un "!" x) = groesse x + 1 := rfl
  have hxn : groesse x ≤ n := by omega
  cases hat : istAtom x with
  | true =>
    have hpf : primFrei x = true := primFrei_of_atom x hat hgx
    have hPx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 1 ≤ G →
        parsePrimary G (druckToks x ++ rest) = .ok (x, rest) := by
      intro G hG
      exact rPr x rest G hxn hgx hpf hrs hrg hG
    exact kern_un_atom_turm x rest hat hr hPx
  | false =>
    have hOx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 8 ≤ G →
        parseOr G (druckToks x ++ ([.zeichen ")"] ++ rest)) =
          .ok (x, [.zeichen ")"] ++ rest) := by
      intro G hG
      exact rOr x ([.zeichen ")"] ++ rest) G hxn hgx
        (hr_paren rest) (hrs_paren rest) (hrg_paren rest) hG
    exact kern_un_paren_turm x rest hat hr hOx

-- The `bin "+"` legs from the binary-inner invariant: a thin
-- wrapper adapting `BKern n` to the leg shape `kern_bin_turm`
-- takes. Returns the eight generalised legs.
theorem turm_bin : ∀ (n : Nat), BKern n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "+" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest)) := by
  intro n bkn l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bkn l r rest G hsum hl hr2 hG
  exact kern_bin_turm l r rest hl hr2 hrr hrs hrg hB

-- The main induction, one level per lemma: each step lifts
-- one `RKern` component from `n` to `n + 1` by cases over the
-- tree (atoms via the standalone towers, `un` via `turm_un`,
-- `bin` via `turm_bin`, everything else contradicts `gutKern`).
-- Projections: atom/bin 8-tuples end `.2.2.2.2.2.2.2` at `Or`.
theorem kernOr_step : ∀ (n : Nat), RKern n → BKern n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 8 ≤ F →
      parseOr F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn e rest F hs hg hr hrs hrg hF
  cases e with
  | lit m => exact (turm_lit m rest hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | gleit s => exact (turm_gleit s rest hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | wahr => exact (turm_wahr rest hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | falsch => exact (turm_falsch rest hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | «variable» a =>
    have hka : (!istKeinPlatz a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact (turm_var a rest hka hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    have ho : o = "!" := strKlingt o "!" hop
    subst ho
    exact (turm_un n rkn x rest hs hgx hr hrs hrg).2.2.2.2.2.2 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    have ho : o = "+" := strKlingt o "+" hop
    subst ho
    exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | feld x f => simp [gutKern] at hg
  | index x i => simp [gutKern] at hg
  | pfeil x f => simp [gutKern] at hg
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

theorem kernAnd_step : ∀ (n : Nat), RKern n → BKern n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 7 ≤ F →
      parseAnd F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn e rest F hs hg hr hrs hrg hF
  cases e with
  | lit m => exact (turm_lit m rest hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | gleit s => exact (turm_gleit s rest hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | wahr => exact (turm_wahr rest hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | falsch => exact (turm_falsch rest hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | «variable» a =>
    have hka : (!istKeinPlatz a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact (turm_var a rest hka hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    have ho : o = "!" := strKlingt o "!" hop
    subst ho
    exact (turm_un n rkn x rest hs hgx hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    have ho : o = "+" := strKlingt o "+" hop
    subst ho
    exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | feld x f => simp [gutKern] at hg
  | index x i => simp [gutKern] at hg
  | pfeil x f => simp [gutKern] at hg
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

theorem kernCmp_step : ∀ (n : Nat), RKern n → BKern n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 6 ≤ F →
      parseCmp F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn e rest F hs hg hr hrs hrg hF
  cases e with
  | lit m => exact (turm_lit m rest hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | gleit s => exact (turm_gleit s rest hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | wahr => exact (turm_wahr rest hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | falsch => exact (turm_falsch rest hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | «variable» a =>
    have hka : (!istKeinPlatz a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact (turm_var a rest hka hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    have ho : o = "!" := strKlingt o "!" hop
    subst ho
    exact (turm_un n rkn x rest hs hgx hr hrs hrg).2.2.2.2.1 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    have ho : o = "+" := strKlingt o "+" hop
    subst ho
    exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | feld x f => simp [gutKern] at hg
  | index x i => simp [gutKern] at hg
  | pfeil x f => simp [gutKern] at hg
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

theorem kernBit_step : ∀ (n : Nat), RKern n → BKern n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 5 ≤ F →
      parseBit F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn e rest F hs hg hr hrs hrg hF
  cases e with
  | lit m => exact (turm_lit m rest hr hrs hrg).2.2.2.2.1 F (by omega)
  | gleit s => exact (turm_gleit s rest hr hrs hrg).2.2.2.2.1 F (by omega)
  | wahr => exact (turm_wahr rest hr hrs hrg).2.2.2.2.1 F (by omega)
  | falsch => exact (turm_falsch rest hr hrs hrg).2.2.2.2.1 F (by omega)
  | «variable» a =>
    have hka : (!istKeinPlatz a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact (turm_var a rest hka hr hrs hrg).2.2.2.2.1 F (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    have ho : o = "!" := strKlingt o "!" hop
    subst ho
    exact (turm_un n rkn x rest hs hgx hr hrs hrg).2.2.2.1 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    have ho : o = "+" := strKlingt o "+" hop
    subst ho
    exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.2.1 F (by omega)
  | feld x f => simp [gutKern] at hg
  | index x i => simp [gutKern] at hg
  | pfeil x f => simp [gutKern] at hg
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

end Gabbro.Grammatik.Parser
