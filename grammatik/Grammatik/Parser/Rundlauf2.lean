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
-- premise: the tail behind `)` is never inspected.
def BKern (n : Nat) : Prop :=
  ∀ (l r : SExpr) (W : List Token) (F : Nat),
    groesse l + groesse r ≤ n → gutKern l = true → gutKern r = true →
    12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 8 ≤ F →
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

-- The full eight-level tower for one literal shape. Each level is
-- generalised over its own fuel (so upper levels reuse lower ones
-- at stripped fuel); the conjunction instantiates all at `F`.
-- Pattern for every atom shape in step A.
theorem turm_lit : ∀ (m : Nat) (rest : List Token) (F : Nat),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse (.lit m) + 1) + groesse (.lit m) + 8 ≤ F →
    (parsePrimary F (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (parseUnary F (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (parseMul F (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (parseAdd F (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (parseBit F (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (parseCmp F (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (parseAnd F (druckToks (.lit m) ++ rest) = .ok (.lit m, rest))
    ∧ (parseOr F (druckToks (.lit m) ++ rest) = .ok (.lit m, rest)) := by
  intro m rest F hr hrs hrg hF
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
  exact ⟨hP F (by omega), hU F (by omega), hM F (by omega), hA F (by omega),
    hB F (by omega), hC F (by omega), hN F (by omega), hO F hF⟩

-- The shape-independent upper tower (`parseMul` up to
-- `parseOr`): every level runs its child and stops its loop on
-- the benign follow. Callers supply the `parseUnary` leg (which
-- is the only head-dependent step) generalised over its fuel.
theorem tower_up : ∀ (e : SExpr) (rest : List Token) (F : Nat),
    ruhig rest = true →
    (∀ (G : Nat), 12 * (groesse e + 1) + groesse e + 2 ≤ G →
      parseUnary G (druckToks e ++ rest) = .ok (e, rest)) →
    12 * (groesse e + 1) + groesse e + 8 ≤ F →
    (parseMul F (druckToks e ++ rest) = .ok (e, rest))
    ∧ (parseAdd F (druckToks e ++ rest) = .ok (e, rest))
    ∧ (parseBit F (druckToks e ++ rest) = .ok (e, rest))
    ∧ (parseCmp F (druckToks e ++ rest) = .ok (e, rest))
    ∧ (parseAnd F (druckToks e ++ rest) = .ok (e, rest))
    ∧ (parseOr F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro e rest F hr hU hF
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
  exact ⟨hM F (by omega), hA F (by omega), hB F (by omega),
    hC F (by omega), hN F (by omega), hO F hF⟩

-- Atom towers, one per remaining leaf shape: the `parsePrimary`
-- leg (concrete head) plus the `parseUnary` fall-through (head is
-- no prefix operator), then `tower_up` for the six loop levels.
theorem turm_gleit : ∀ (s : String) (rest : List Token) (F : Nat),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 8 ≤ F →
    (parsePrimary F (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (parseUnary F (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (parseMul F (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (parseAdd F (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (parseBit F (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (parseCmp F (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (parseAnd F (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest))
    ∧ (parseOr F (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest)) := by
  intro s rest F hr hrs hrg hF
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
  have hup := tower_up (.gleit s) rest F hr hU hF
  exact ⟨hP F (by omega), hU F (by omega), hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

theorem turm_wahr : ∀ (rest : List Token) (F : Nat),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse .wahr + 1) + groesse .wahr + 8 ≤ F →
    (parsePrimary F (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (parseUnary F (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (parseMul F (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (parseAdd F (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (parseBit F (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (parseCmp F (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (parseAnd F (druckToks .wahr ++ rest) = .ok (.wahr, rest))
    ∧ (parseOr F (druckToks .wahr ++ rest) = .ok (.wahr, rest)) := by
  intro rest F hr hrs hrg hF
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
  have hup := tower_up .wahr rest F hr hU hF
  exact ⟨hP F (by omega), hU F (by omega), hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

theorem turm_falsch : ∀ (rest : List Token) (F : Nat),
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse .falsch + 1) + groesse .falsch + 8 ≤ F →
    (parsePrimary F (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (parseUnary F (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (parseMul F (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (parseAdd F (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (parseBit F (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (parseCmp F (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (parseAnd F (druckToks .falsch ++ rest) = .ok (.falsch, rest))
    ∧ (parseOr F (druckToks .falsch ++ rest) = .ok (.falsch, rest)) := by
  intro rest F hr hrs hrg hF
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
  have hup := tower_up .falsch rest F hr hU hF
  exact ⟨hP F (by omega), hU F (by omega), hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

theorem turm_var : ∀ (a : String) (rest : List Token) (F : Nat),
    (!istKeinPlatz a) = true → ruhig rest = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    12 * (groesse (.variable a) + 1) + groesse (.variable a) + 8 ≤ F →
    (parsePrimary F (druckToks (.variable a) ++ rest) =
      .ok (.variable a, rest))
    ∧ (parseUnary F (druckToks (.variable a) ++ rest) =
      .ok (.variable a, rest))
    ∧ (parseMul F (druckToks (.variable a) ++ rest) =
      .ok (.variable a, rest))
    ∧ (parseAdd F (druckToks (.variable a) ++ rest) =
      .ok (.variable a, rest))
    ∧ (parseBit F (druckToks (.variable a) ++ rest) =
      .ok (.variable a, rest))
    ∧ (parseCmp F (druckToks (.variable a) ++ rest) =
      .ok (.variable a, rest))
    ∧ (parseAnd F (druckToks (.variable a) ++ rest) =
      .ok (.variable a, rest))
    ∧ (parseOr F (druckToks (.variable a) ++ rest) =
      .ok (.variable a, rest)) := by
  intro a rest F hka hr hrs hrg hF
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
  have hup := tower_up (.variable a) rest F hr hU hF
  exact ⟨hP F (by omega), hU F (by omega), hup.1, hup.2.1, hup.2.2.1,
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

-- The `un "!"` tower from induction-hypothesis legs: the
-- `parsePrimary` leg for atom children (same follow), the
-- `parseOr` leg for parenthesised children (`)` follow), then
-- `tower_up`. No `parsePrimary` component (`primFrei` is false
-- for `un`).
theorem kern_un_turm : ∀ (x : SExpr) (rest : List Token) (F : Nat),
    gutKern x = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 1 ≤ G →
      parsePrimary G (druckToks x ++ rest) = .ok (x, rest)) →
    (∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 8 ≤ G →
      parseOr G (druckToks x ++ [.zeichen ")"] ++ rest) =
        .ok (x, [.zeichen ")"] ++ rest)) →
    12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 8 ≤ F →
    (parseUnary F (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (parseMul F (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (parseAdd F (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (parseBit F (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (parseCmp F (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (parseAnd F (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest))
    ∧ (parseOr F (druckToks (.un "!" x) ++ rest) = .ok (.un "!" x, rest)) := by
  intro x rest F hgx hr hrs hrg hPx hOx hF
  have hsize : groesse (.un "!" x) = groesse x + 1 := rfl
  have hU : ∀ (G : Nat),
      12 * (groesse (.un "!" x) + 1) + groesse (.un "!" x) + 2 ≤ G →
      parseUnary G (druckToks (.un "!" x) ++ rest) =
        .ok (.un "!" x, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    cases hat : istAtom x with
    | true =>
      have hd : druckToks (.un "!" x) =
          [.zeichen "!"] ++ druckToks x := by
        simp [druckToks, hat]
      have hP' := hPx G' (by omega)
      simp only [hd, List.append_assoc] at ⊢
      exact bang_arm _ _ _ _ hP'
    | false =>
      have hd : druckToks (.un "!" x) = [.zeichen "!"] ++
          (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
        simp [druckToks, hat]
      have hF2 : 1 ≤ G' := by omega
      obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
      have hO' := hOx G'' (by omega)
      simp only [List.append_assoc] at hO'
      have hPar := paren_arm _ _ _ _ hO'
      have hBang := bang_arm _ _ _ _ hPar
      simp only [hd, List.append_assoc] at ⊢
      exact hBang
  have hup := tower_up (.un "!" x) rest F hr hU (by omega)
  exact ⟨hU F (by omega), hup.1, hup.2.1, hup.2.2.1, hup.2.2.2.1,
    hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `bin "+"` tower from a binary-inner leg: the
-- `parsePrimary` leg runs the `(` arm over the inner parse, the
-- `parseUnary` leg falls through on `(`, then `tower_up`.
theorem kern_bin_turm : ∀ (l r : SExpr) (rest : List Token) (F : Nat),
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 8 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ rest)) →
    12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 8 ≤ F →
    (parsePrimary F (druckToks (.bin "+" l r) ++ rest) =
      .ok (.bin "+" l r, rest))
    ∧ (parseUnary F (druckToks (.bin "+" l r) ++ rest) =
      .ok (.bin "+" l r, rest))
    ∧ (parseMul F (druckToks (.bin "+" l r) ++ rest) =
      .ok (.bin "+" l r, rest))
    ∧ (parseAdd F (druckToks (.bin "+" l r) ++ rest) =
      .ok (.bin "+" l r, rest))
    ∧ (parseBit F (druckToks (.bin "+" l r) ++ rest) =
      .ok (.bin "+" l r, rest))
    ∧ (parseCmp F (druckToks (.bin "+" l r) ++ rest) =
      .ok (.bin "+" l r, rest))
    ∧ (parseAnd F (druckToks (.bin "+" l r) ++ rest) =
      .ok (.bin "+" l r, rest))
    ∧ (parseOr F (druckToks (.bin "+" l r) ++ rest) =
      .ok (.bin "+" l r, rest)) := by
  intro l r rest F hgl hgr hr hrs hrg hB hF
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
  have hup := tower_up (.bin "+" l r) rest F hr hU (by omega)
  exact ⟨hP F (by omega), hU F (by omega), hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

end Gabbro.Grammatik.Parser
