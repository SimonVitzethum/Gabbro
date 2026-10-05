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

-- Kernel places: variables and suffix chains over kernel
-- trees (index payloads are `gutKern`, so the suffix runner
-- parses them through `RKern`).
--
-- Step A predicate, widened in step B1 to the full unary
-- level, in step B2 to two binary levels, and in step B3 to
-- places: literals (all four leaf shapes), variables, unary
-- `!`/`-`/`~`, parenthesised `+`/`*`, places over kernel
-- trees. Everything else is `false` (calls, the other four
-- operator levels, `sizeof`/`old`/`Grund` come later in step B).
-- The two predicates call each other (index base vs payload),
-- so they are defined mutually.
mutual
def gutKernPlatz : SExpr → Bool
  | .variable s => !istKeinPlatz s
  | .feld x _ => gutKernPlatz x
  | .index x i => gutKernPlatz x && gutKern i
  | .pfeil x _ => gutKernPlatz x
  | _ => false
def gutKern : SExpr → Bool
  | .lit _ => true
  | .gleit _ => true
  | .wahr => true
  | .falsch => true
  | .variable s => !istKeinPlatz s
  | .un o x =>
    (strEq o "!" || strEq o "-" || strEq o "~") && gutKern x
  | .bin o l r =>
    (strEq o "+" || strEq o "*" || strEq o "||" || strEq o "&&") &&
      gutKern l && gutKern r
  | .feld x f => gutKernPlatz x
  | .index x i => gutKernPlatz x && gutKern i
  | .pfeil x f => gutKernPlatz x
  | _ => false
end

-- Which suffix fragments are kernel-printable (index payloads
-- are `gutKern`).
def suffGutKern : List SuffFrag → Bool
  | [] => true
  | .dot _ :: s => suffGutKern s
  | .arrow _ :: s => suffGutKern s
  | .idx i :: s => gutKern i && suffGutKern s

-- `suffGutKern` splits over appends (mirror of lane 161's
-- `suffGut_append`).
theorem suffGutKern_append : ∀ (s1 s2 : List SuffFrag),
    suffGutKern (s1 ++ s2) = (suffGutKern s1 && suffGutKern s2) := by
  intro s1
  induction s1 with
  | nil => simp [suffGutKern]
  | cons f s ih =>
    cases f with
    | dot g => simp [suffGutKern, ih]
    | arrow g => simp [suffGutKern, ih]
    | idx i => simp [suffGutKern, ih, Bool.and_assoc]

-- Unfolding equations for the two recursive arms, as plain rewrite
-- rules (kernel-checked; the `gutKern` match has literal arms that
-- `simp` equations do not select -- same reason as lane 161's
-- `gut_sizeof_one` family).
theorem gutKern_un : ∀ (o : String) (x : SExpr),
    gutKern (.un o x) =
      ((strEq o "!" || strEq o "-" || strEq o "~") && gutKern x) := by
  intro o x
  rfl
theorem gutKern_bin : ∀ (o : String) (l r : SExpr),
    gutKern (.bin o l r) =
      ((strEq o "+" || strEq o "*" || strEq o "||" || strEq o "&&") &&
        gutKern l && gutKern r) := by
  intro o l r
  rfl
theorem gutKern_feld : ∀ (x : SExpr) (f : String),
    gutKern (.feld x f) = gutKernPlatz x := by
  intro x f
  rfl
theorem gutKern_index : ∀ (x i : SExpr),
    gutKern (.index x i) = (gutKernPlatz x && gutKern i) := by
  intro x i
  rfl
theorem gutKern_pfeil : ∀ (x : SExpr) (f : String),
    gutKern (.pfeil x f) = gutKernPlatz x := by
  intro x f
  rfl
theorem gutKernPlatz_feld : ∀ (x : SExpr) (f : String),
    gutKernPlatz (.feld x f) = gutKernPlatz x := by
  intro x f
  rfl
theorem gutKernPlatz_index : ∀ (x i : SExpr),
    gutKernPlatz (.index x i) = (gutKernPlatz x && gutKern i) := by
  intro x i
  rfl
theorem gutKernPlatz_pfeil : ∀ (x : SExpr) (f : String),
    gutKernPlatz (.pfeil x f) = gutKernPlatz x := by
  intro x f
  rfl

-- A lawful prefix spelling names itself: the three cases
-- of the widened `gutKern` un-arm.
theorem un_is_pre : ∀ (o : String),
    (strEq o "!" || strEq o "-" || strEq o "~") = true →
    o = "!" ∨ o = "-" ∨ o = "~" := by
  intro o h
  simp only [Bool.or_eq_true] at h
  obtain ⟨h | h⟩ | h := h
  · exact Or.inl (strKlingt o "!" h)
  · exact Or.inr (Or.inl (strKlingt o "-" h))
  · exact Or.inr (Or.inr (strKlingt o "~" h))

-- A lawful `+`/`*` spelling names itself: the two cases of
-- the widened `gutKern` bin-arm.
theorem bin_is_pm : ∀ (o : String),
    (strEq o "+" || strEq o "*" || strEq o "||" || strEq o "&&") = true →
    o = "+" ∨ o = "*" ∨ o = "||" ∨ o = "&&" := by
  intro o h
  simp only [Bool.or_eq_true] at h
  obtain ⟨⟨h | h⟩ | h⟩ | h := h
  · exact Or.inl (strKlingt o "+" h)
  · exact Or.inr (Or.inl (strKlingt o "*" h))
  · exact Or.inr (Or.inr (Or.inl (strKlingt o "||" h)))
  · exact Or.inr (Or.inr (Or.inr (strKlingt o "&&" h)))

-- A `gutKern` tree is printable (`gut`), and a kernel
-- place is a lane-161 place: the two bridges call each other
-- on strict subterms (index base and payload), so they are
-- proved mutually.
mutual
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
  | feld x f =>
    rw [gutKern_feld] at h
    simp only [gut] at ⊢
    exact gutPlatz_of_gutKernPlatz x h
  | index x i =>
    rw [gutKern_index] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hpx, hi⟩ := h
    simp only [gut, Bool.and_eq_true] at ⊢
    exact ⟨gutPlatz_of_gutKernPlatz x hpx, gut_of_gutKern i hi⟩
  | pfeil x f =>
    rw [gutKern_pfeil] at h
    simp only [gut] at ⊢
    exact gutPlatz_of_gutKernPlatz x h
  | un o x =>
    rw [gutKern_un] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hop, hx⟩ := h
    obtain rfl | rfl | rfl := un_is_pre o hop
    · simp only [gut, Bool.and_eq_true] at ⊢
      refine ⟨?_, gut_of_gutKern x hx⟩
      decide
    · simp only [gut, Bool.and_eq_true] at ⊢
      refine ⟨?_, gut_of_gutKern x hx⟩
      decide
    · simp only [gut, Bool.and_eq_true] at ⊢
      refine ⟨?_, gut_of_gutKern x hx⟩
      decide
  | bin o l r =>
    rw [gutKern_bin] at h
    simp only [Bool.and_eq_true, and_assoc] at h
    obtain ⟨hop, hl, hr⟩ := h
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
      refine ⟨?_, gut_of_gutKern l hl, gut_of_gutKern r hr⟩
      decide
    · simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
      refine ⟨?_, gut_of_gutKern l hl, gut_of_gutKern r hr⟩
      decide
    · simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
      refine ⟨?_, gut_of_gutKern l hl, gut_of_gutKern r hr⟩
      decide
    · simp only [gut, Bool.and_eq_true, and_assoc] at ⊢
      refine ⟨?_, gut_of_gutKern l hl, gut_of_gutKern r hr⟩
      decide
  | ruf f xs => simp [gutKern] at h
  | fnwert f => simp [gutKern] at h
  | eingebaut f xs => simp [gutKern] at h
  | alt x => simp [gutKern] at h
  | ergebnis => simp [gutKern] at h
  | grund g f => simp [gutKern] at h
theorem gutPlatz_of_gutKernPlatz : ∀ (p : SExpr),
    gutKernPlatz p = true → gutPlatz p = true := by
  intro p h
  cases p with
  | lit m => simp [gutKernPlatz] at h
  | gleit s => simp [gutKernPlatz] at h
  | wahr => simp [gutKernPlatz] at h
  | falsch => simp [gutKernPlatz] at h
  | «variable» s =>
    simp only [gutKernPlatz] at h
    simp only [gutPlatz] at ⊢
    exact h
  | feld x f =>
    simp only [gutKernPlatz] at h
    simp only [gutPlatz] at ⊢
    exact gutPlatz_of_gutKernPlatz x h
  | index x i =>
    simp only [gutKernPlatz, Bool.and_eq_true] at h
    obtain ⟨hpx, hi⟩ := h
    simp only [gutPlatz, Bool.and_eq_true] at ⊢
    exact ⟨gutPlatz_of_gutKernPlatz x hpx, gut_of_gutKern i hi⟩
  | pfeil x f =>
    simp only [gutKernPlatz] at h
    simp only [gutPlatz] at ⊢
    exact gutPlatz_of_gutKernPlatz x h
  | un o x => simp [gutKernPlatz] at h
  | bin o l r => simp [gutKernPlatz] at h
  | ruf f xs => simp [gutKernPlatz] at h
  | fnwert f => simp [gutKernPlatz] at h
  | eingebaut f xs => simp [gutKernPlatz] at h
  | alt x => simp [gutKernPlatz] at h
  | ergebnis => simp [gutKernPlatz] at h
  | grund g f => simp [gutKernPlatz] at h
end

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

-- The binary-inner parse for `*`: like `BKern`, but the inner
-- operator consumes at the `parseMul` level. Same `+10` fuel
-- (same twelve-strip count).
def BKernStar (n : Nat) : Prop :=
  ∀ (l r : SExpr) (W : List Token) (F : Nat),
    groesse l + groesse r ≤ n → gutKern l = true → gutKern r = true →
    12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ F →
    parseOr F (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
      [.zeichen ")"] ++ W) =
      .ok (.bin "*" l r, [.zeichen ")"] ++ W)

-- The binary-inner parse for `||`: the inner operator
-- consumes at the `parseOrL` loop level (one iteration, then
-- the loop stops at `)`). Same `+10` fuel.
def BKernOr (n : Nat) : Prop :=
  ∀ (l r : SExpr) (W : List Token) (F : Nat),
    groesse l + groesse r ≤ n → gutKern l = true → gutKern r = true →
    12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ F →
    parseOr F (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
      [.zeichen ")"] ++ W) =
      .ok (.bin "||" l r, [.zeichen ")"] ++ W)

-- The binary-inner parse for `&&`: the inner operator
-- consumes at the `parseAndL` loop level (one iteration, then
-- the loop stops at `)`, and the outer `parseOrL` stops
-- too). Same `+10` fuel.
def BKernAnd (n : Nat) : Prop :=
  ∀ (l r : SExpr) (W : List Token) (F : Nat),
    groesse l + groesse r ≤ n → gutKern l = true → gutKern r = true →
    12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ F →
    parseOr F (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
      [.zeichen ")"] ++ W) =
      .ok (.bin "&&" l r, [.zeichen ")"] ++ W)
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

-- The `||`-follow upper tower (`parseMul` up to `parseAnd`):
-- mirror of `tower_up`, but every loop stops on the concrete
-- `||` head (miss facts as hypotheses) instead of a benign
-- follow. Needed for the left operand of the `||` inner
-- trace, whose follow is the operator itself.
theorem tower_up_orbar : ∀ (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    opVgl S1 = none → opUnd S1 = none →
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 7 ≤ G →
      parseAnd G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro l S1 hU hMul hAdd hBit hVgl hUnd
  have hM : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  have hB : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseBit, parseBitL, hA', hBit] at ⊢
  have hC : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    simp only [parseCmp, hB', hVgl] at ⊢
  have hN : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 7 ≤ G →
      parseAnd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hC' := hC G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAnd, parseAndL, hC', hUnd] at ⊢
  exact ⟨hM, hA, hB, hC, hN⟩

-- The `&&`-follow upper tower (`parseMul` up to `parseCmp`):
-- mirror of `tower_up_orbar` one level down (the single
-- comparison check misses the concrete `&&`).
theorem tower_up_andbar : ∀ (l : SExpr) (S1 : List Token),
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ S1) = .ok (l, S1)) →
    opMul S1 = none → opAdd S1 = none → opBit S1 = none →
    opVgl S1 = none →
    (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1))
    ∧ (∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1)) := by
  intro l S1 hU hMul hAdd hBit hVgl
  have hM : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 3 ≤ G →
      parseMul G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hU' := hU G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseMul, parseMulL, hU', hMul] at ⊢
  have hA : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 4 ≤ G →
      parseAdd G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hM' := hM G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseAdd, parseAddL, hM', hAdd] at ⊢
  have hB : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 5 ≤ G →
      parseBit G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hA' := hA G' (by omega)
    have hG2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    simp only [parseBit, parseBitL, hA', hBit] at ⊢
  have hC : ∀ (G : Nat),
      12 * (groesse l + 1) + groesse l + 6 ≤ G →
      parseCmp G (druckToks l ++ S1) = .ok (l, S1) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    simp only [parseCmp, hB', hVgl] at ⊢
  exact ⟨hM, hA, hB, hC⟩

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
  | feld x f => rfl
  | index x i => rfl
  | pfeil x f => rfl
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
-- The prefix-operator arm generalised over the spelling:
-- `!`, `-` and `~` all run `parsePrimary` identically.
theorem bang_arm_gen : ∀ (G' : Nat) (M R : List Token) (o : String) (v : SExpr),
    (strEq o "!" || strEq o "-" || strEq o "~") = true →
    parsePrimary G' M = .ok (v, R) →
    parseUnary (G' + 1) ([.zeichen o] ++ M) = .ok (.un o v, R) := by
  intro G' M R o v hop h
  obtain rfl | rfl | rfl := un_is_pre o hop
  · simp only [List.cons_append, List.nil_append] at h ⊢
    simp only [parseUnary, h] at ⊢
  · simp only [List.cons_append, List.nil_append] at h ⊢
    simp only [parseUnary, h] at ⊢
  · simp only [List.cons_append, List.nil_append] at h ⊢
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

-- The `un` tower for ATOM children, generalised over the
-- prefix spelling: the `parsePrimary` leg (same follow)
-- through the prefix arm, then `tower_up`. Split from the
-- joint tower because the primary leg is provable only for
-- atoms (`parsePrimary` fails on operator heads). No
-- `parsePrimary` component (`primFrei` is false for `un`).
theorem kern_un_atom_turm : ∀ (o : String) (x : SExpr) (rest : List Token),
    (strEq o "!" || strEq o "-" || strEq o "~") = true →
    istAtom x = true → ruhig rest = true →
    (∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 1 ≤ G →
      parsePrimary G (druckToks x ++ rest) = .ok (x, rest)) →
    (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 3 ≤ G →
      parseMul G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 4 ≤ G →
      parseAdd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 5 ≤ G →
      parseBit G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 6 ≤ G →
      parseCmp G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 7 ≤ G →
      parseAnd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 8 ≤ G →
      parseOr G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest)) := by
  intro o x rest hop hat hr hPx
  have hsize : groesse (.un o x) = groesse x + 1 := rfl
  have hU : ∀ (G : Nat),
      12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) =
        .ok (.un o x, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hd : druckToks (.un o x) =
        [.zeichen o] ++ druckToks x := by
      simp [druckToks, hat]
    have hP' := hPx G' (by omega)
    simp only [hd, List.append_assoc] at ⊢
    exact bang_arm_gen _ _ _ _ _ hop hP'
  have hup := tower_up (.un o x) rest hr hU
  exact ⟨hU, hup.1, hup.2.1, hup.2.2.1, hup.2.2.2.1,
    hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `un` tower for PARENTHESISED (non-atom) children: the
-- `parseOr` leg (`)` follow) through the prefix arm into the
-- `(` arm, then `tower_up`.
theorem kern_un_paren_turm : ∀ (o : String) (x : SExpr) (rest : List Token),
    (strEq o "!" || strEq o "-" || strEq o "~") = true →
    istAtom x = false → ruhig rest = true →
    (∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 8 ≤ G →
      parseOr G (druckToks x ++ ([.zeichen ")"] ++ rest)) =
        .ok (x, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 3 ≤ G →
      parseMul G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 4 ≤ G →
      parseAdd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 5 ≤ G →
      parseBit G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 6 ≤ G →
      parseCmp G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 7 ≤ G →
      parseAnd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 8 ≤ G →
      parseOr G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest)) := by
  intro o x rest hop hat hr hOx
  have hsize : groesse (.un o x) = groesse x + 1 := rfl
  have hU : ∀ (G : Nat),
      12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) =
        .ok (.un o x, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hd : druckToks (.un o x) = [.zeichen o] ++
        (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
      simp [druckToks, hat]
    have hF2 : 1 ≤ G' := by omega
    obtain ⟨G'', rfl⟩ : ∃ G'', G' = G'' + 1 := ⟨G' - 1, by omega⟩
    have hO' := hOx G'' (by omega)
    have hPar := paren_arm _ _ _ _ hO'
    have hBang := bang_arm_gen _ _ _ _ _ hop hPar
    simp only [hd, List.append_assoc] at ⊢
    exact hBang
  have hup := tower_up (.un o x) rest hr hU
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

-- The `bin "*"` tower from a binary-inner leg: word for word
-- the `+` tower with the spelling swapped (no proof step
-- inspects the spelling -- the printer, the paren arm and the
-- fall-through are all spelling-blind).
theorem kern_bin_star_turm : ∀ (l r : SExpr) (rest : List Token),
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest)) := by
  intro l r rest hgl hgr hr hrs hrg hB
  have hsize : groesse (.bin "*" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "*" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "*"] ++ druckToks r ++ [.zeichen ")"] := by
    simp [druckToks]
  have hP : ∀ (G : Nat),
      12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  have hU : ∀ (G : Nat),
      12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP G' (by omega)
    simp only [hd, List.append_assoc] at hP' ⊢
    exact un_paren_fall _ _ _ _ hP'
  have hup := tower_up (.bin "*" l r) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `bin "||"` tower from a binary-inner leg: word for word
-- the `*` tower with the spelling swapped (no proof step
-- inspects the spelling).
theorem kern_bin_or_turm : ∀ (l r : SExpr) (rest : List Token),
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "||" l r, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest)) := by
  intro l r rest hgl hgr hr hrs hrg hB
  have hsize : groesse (.bin "||" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "||" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "||"] ++ druckToks r ++ [.zeichen ")"] := by
    simp [druckToks]
  have hP : ∀ (G : Nat),
      12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  have hU : ∀ (G : Nat),
      12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP G' (by omega)
    simp only [hd, List.append_assoc] at hP' ⊢
    exact un_paren_fall _ _ _ _ hP'
  have hup := tower_up (.bin "||" l r) rest hr hU
  exact ⟨hP, hU, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The `bin "&&"` tower from a binary-inner leg: word for word
-- the `||` tower with the spelling swapped.
theorem kern_bin_and_turm : ∀ (l r : SExpr) (rest : List Token),
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ rest)) →
    (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest)) := by
  intro l r rest hgl hgr hr hrs hrg hB
  have hsize : groesse (.bin "&&" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "&&" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "&&"] ++ druckToks r ++ [.zeichen ")"] := by
    simp [druckToks]
  have hP : ∀ (G : Nat),
      12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hB' := hB G' (by omega)
    have hPar := paren_arm _ _ _ _ hB'
    simp only [hd, List.append_assoc] at ⊢
    simp only [List.append_assoc] at hPar
    exact hPar
  have hU : ∀ (G : Nat),
      12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hP' := hP G' (by omega)
    simp only [hd, List.append_assoc] at hP' ⊢
    exact un_paren_fall _ _ _ _ hP'
  have hup := tower_up (.bin "&&" l r) rest hr hU
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
-- Facts for the `*` inner trace: `parseMulL` consumes the
-- concrete `*`, and a `*` follow is benign for the suffix and
-- float tails (loop levels never see it -- it is consumed
-- inside `parseMul`).
theorem opMul_star_some : ∀ (T : List Token),
    opMul ([.zeichen "*"] ++ T) = some ("*", T) := by
  intro T
  rfl
theorem hrs_star : ∀ (T : List Token),
    ruhigSuff ([.zeichen "*"] ++ T) = true := by
  intro T
  rfl
theorem hrg_star : ∀ (T : List Token),
    ruhigGleit ([.zeichen "*"] ++ T) = true := by
  intro T
  rfl
-- Facts for the `||` inner trace: every loop below `Or`
-- misses the concrete `||`, and `parseOrL` consumes it.
theorem opMul_orbar : ∀ (T : List Token),
    opMul ([.zeichen "||"] ++ T) = none := by
  intro T
  rfl
theorem opAdd_orbar : ∀ (T : List Token),
    opAdd ([.zeichen "||"] ++ T) = none := by
  intro T
  rfl
theorem opBit_orbar : ∀ (T : List Token),
    opBit ([.zeichen "||"] ++ T) = none := by
  intro T
  rfl
theorem opVgl_orbar : ∀ (T : List Token),
    opVgl ([.zeichen "||"] ++ T) = none := by
  intro T
  rfl
theorem opUnd_orbar : ∀ (T : List Token),
    opUnd ([.zeichen "||"] ++ T) = none := by
  intro T
  rfl
theorem opOder_or_some : ∀ (T : List Token),
    opOder ([.zeichen "||"] ++ T) = some T := by
  intro T
  rfl
theorem hrs_orbar : ∀ (T : List Token),
    ruhigSuff ([.zeichen "||"] ++ T) = true := by
  intro T
  rfl
theorem hrg_orbar : ∀ (T : List Token),
    ruhigGleit ([.zeichen "||"] ++ T) = true := by
  intro T
  rfl
-- Facts for the `&&` inner trace: every loop below `And`
-- misses the concrete `&&`, and `parseAndL` consumes it.
theorem opMul_andbar : ∀ (T : List Token),
    opMul ([.zeichen "&&"] ++ T) = none := by
  intro T
  rfl
theorem opAdd_andbar : ∀ (T : List Token),
    opAdd ([.zeichen "&&"] ++ T) = none := by
  intro T
  rfl
theorem opBit_andbar : ∀ (T : List Token),
    opBit ([.zeichen "&&"] ++ T) = none := by
  intro T
  rfl
theorem opVgl_andbar : ∀ (T : List Token),
    opVgl ([.zeichen "&&"] ++ T) = none := by
  intro T
  rfl
theorem opUnd_and_some : ∀ (T : List Token),
    opUnd ([.zeichen "&&"] ++ T) = some T := by
  intro T
  rfl
theorem hrs_andbar : ∀ (T : List Token),
    ruhigSuff ([.zeichen "&&"] ++ T) = true := by
  intro T
  rfl
theorem hrg_andbar : ∀ (T : List Token),
    ruhigGleit ([.zeichen "&&"] ++ T) = true := by
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

-- The `*` inner trace (`BKernStar` from `RKern`): like
-- `kernB_step`, but the inner operator consumes at the
-- `parseMul` level -- `parseMul` runs `parseUnary` on `l`,
-- `parseMulL` consumes `*` and `r`, stops at `)`, and every
-- level above stops at `)`. Same `+10` fuel (same strip
-- count); only the `parseUnary` leg of `RKern` is used.
theorem kernB_step_star : ∀ (n : Nat), RKern n → BKernStar (n + 1) := by
  intro n rkn l r W F hsum hgl hgr hF
  obtain ⟨-, -, -, -, -, -, hUn, -⟩ := rkn
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  have hln : groesse l ≤ n := by omega
  have hrn : groesse r ≤ n := by omega
  simp only [List.append_assoc] at ⊢
  -- The `parseAdd` core with `*` consumed inside `parseMul`.
  have hAdd : ∀ (G4 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 6 ≤ G4 →
      parseAdd G4 (druckToks l ++ ([.zeichen "*"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ W) := by
    intro G4 hG4
    have h41 : 1 ≤ G4 := by omega
    obtain ⟨G5, rfl⟩ : ∃ G5, G4 = G5 + 1 := ⟨G4 - 1, by omega⟩
    have h42 : 1 ≤ G5 := by omega
    obtain ⟨G6, rfl⟩ : ∃ G6, G5 = G6 + 1 := ⟨G5 - 1, by omega⟩
    have hUl := hUn l ([.zeichen "*"] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) G6 hln hgl
      (hrs_star _) (hrg_star _) (by omega)
    have h43 : 1 ≤ G6 := by omega
    obtain ⟨G6x, rfl⟩ : ∃ G6x, G6 = G6x + 1 := ⟨G6 - 1, by omega⟩
    have hop := opMul_star_some (druckToks r ++ ([.zeichen ")"] ++ W))
    have hUr := hUn r ([.zeichen ")"] ++ W) G6x hrn hgr
      (hrs_paren W) (hrg_paren W) (by omega)
    have h44 : 1 ≤ G6x := by omega
    obtain ⟨G6y, rfl⟩ : ∃ G6y, G6x = G6y + 1 := ⟨G6x - 1, by omega⟩
    have hstopM := opMul_paren W
    have hstopA := stopAdd ([.zeichen ")"] ++ W) (hr_paren W)
    simp only [parseAdd, parseMul, parseMulL, hUl, hop, hUr, hstopM] at ⊢
    -- Four strips numeral-fold the loop fuel to `+ 3`, which no
    -- equation fires on: unfold once more by explicit rewrite.
    have h45 : G6y + 3 = (G6y + 2) + 1 := by omega
    rw [h45] at ⊢
    simp only [parseAddL, hstopA] at ⊢
  -- Up the pass-through levels, each stopping at `)`.
  have hBit : ∀ (G3 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 7 ≤ G3 →
      parseBit G3 (druckToks l ++ ([.zeichen "*"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ W) := by
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
      parseCmp G2 (druckToks l ++ ([.zeichen "*"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ W) := by
    intro G2 hG2
    have h21 : 1 ≤ G2 := by omega
    obtain ⟨G3, rfl⟩ : ∃ G3, G2 = G3 + 1 := ⟨G2 - 1, by omega⟩
    have hBit' := hBit G3 (by omega)
    have hstop := opVgl_paren W
    simp only [parseCmp, hBit', hstop] at ⊢
  have hAnd : ∀ (G1 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen "*"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ W) := by
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
      parseOr G0 (druckToks l ++ ([.zeichen "*"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr F hF

-- The `||` inner trace (`BKernOr` from `RKern`): the left
-- operand runs the `||`-follow up-tower (every loop below
-- `Or` stops on the concrete `||`), then `parseOrL` consumes
-- `||` and `r` and stops at `)`. Same `+10` fuel.
theorem kernB_step_or : ∀ (n : Nat), RKern n → BKernOr (n + 1) := by
  intro n rkn l r W F hsum hgl hgr hF
  obtain ⟨-, hAnd, -, -, -, -, hUn, -⟩ := rkn
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  have hln : groesse l ≤ n := by omega
  have hrn : groesse r ≤ n := by omega
  simp only [List.append_assoc] at ⊢
  have hUleg : ∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen "||"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "||"] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G hG
    exact hUn l ([.zeichen "||"] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) G hln hgl
      (hrs_orbar _) (hrg_orbar _) hG
  have hup := tower_up_orbar l ([.zeichen "||"] ++
    (druckToks r ++ ([.zeichen ")"] ++ W))) hUleg
    (opMul_orbar _) (opAdd_orbar _) (opBit_orbar _) (opVgl_orbar _)
    (opUnd_orbar _)
  have hOr : ∀ (G0 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen "||"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "||" l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hN' := hup.2.2.2.2 G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hop := opOder_or_some (druckToks r ++ ([.zeichen ")"] ++ W))
    have hMr := hAnd r ([.zeichen ")"] ++ W) G1x hrn hgr
      (hr_paren W) (hrs_paren W) (hrg_paren W) (by omega)
    have h03 : 1 ≤ G1x := by omega
    obtain ⟨G1y, rfl⟩ : ∃ G1y, G1x = G1y + 1 := ⟨G1x - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hN', hop, hMr, hstop] at ⊢
  exact hOr F hF

-- The `&&` inner trace (`BKernAnd` from `RKern`): the left
-- operand runs the `&&`-follow up-tower (every loop below
-- `And` stops on the concrete `&&`, the single comparison
-- misses it), then `parseAndL` consumes `&&` and `r`, stops
-- at `)`, and the outer `parseOrL` stops too. Same `+10` fuel.
theorem kernB_step_and : ∀ (n : Nat), RKern n → BKernAnd (n + 1) := by
  intro n rkn l r W F hsum hgl hgr hF
  obtain ⟨-, -, hCmp, -, -, -, hUn, -⟩ := rkn
  have hpos_l := groesse_pos l
  have hpos_r := groesse_pos r
  have hln : groesse l ≤ n := by omega
  have hrn : groesse r ≤ n := by omega
  simp only [List.append_assoc] at ⊢
  have hUleg : ∀ (G : Nat), 12 * (groesse l + 1) + groesse l + 2 ≤ G →
      parseUnary G (druckToks l ++ ([.zeichen "&&"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (l, [.zeichen "&&"] ++
          (druckToks r ++ ([.zeichen ")"] ++ W))) := by
    intro G hG
    exact hUn l ([.zeichen "&&"] ++
      (druckToks r ++ ([.zeichen ")"] ++ W))) G hln hgl
      (hrs_andbar _) (hrg_andbar _) hG
  have hup := tower_up_andbar l ([.zeichen "&&"] ++
    (druckToks r ++ ([.zeichen ")"] ++ W))) hUleg
    (opMul_andbar _) (opAdd_andbar _) (opBit_andbar _) (opVgl_andbar _)
  have hAnd : ∀ (G1 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 9 ≤ G1 →
      parseAnd G1 (druckToks l ++ ([.zeichen "&&"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ W) := by
    intro G1 hG1
    have h11 : 1 ≤ G1 := by omega
    obtain ⟨G2, rfl⟩ : ∃ G2, G1 = G2 + 1 := ⟨G1 - 1, by omega⟩
    have hC' := hup.2.2.2 G2 (by omega)
    have h12 : 1 ≤ G2 := by omega
    obtain ⟨G2x, rfl⟩ : ∃ G2x, G2 = G2x + 1 := ⟨G2 - 1, by omega⟩
    have hop := opUnd_and_some (druckToks r ++ ([.zeichen ")"] ++ W))
    have hMr := hCmp r ([.zeichen ")"] ++ W) G2x hrn hgr
      (hr_paren W) (hrs_paren W) (hrg_paren W) (by omega)
    have h13 : 1 ≤ G2x := by omega
    obtain ⟨G2y, rfl⟩ : ∃ G2y, G2x = G2y + 1 := ⟨G2x - 1, by omega⟩
    have hstop := opUnd_paren W
    simp only [parseAnd, parseAndL, hC', hop, hMr, hstop] at ⊢
  have hOr : ∀ (G0 : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G0 →
      parseOr G0 (druckToks l ++ ([.zeichen "&&"] ++
        (druckToks r ++ ([.zeichen ")"] ++ W)))) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ W) := by
    intro G0 hG0
    have h01 : 1 ≤ G0 := by omega
    obtain ⟨G1, rfl⟩ : ∃ G1, G0 = G1 + 1 := ⟨G0 - 1, by omega⟩
    have hAnd' := hAnd G1 (by omega)
    have h02 : 1 ≤ G1 := by omega
    obtain ⟨G1x, rfl⟩ : ∃ G1x, G1 = G1x + 1 := ⟨G1 - 1, by omega⟩
    have hstop := opOder_paren W
    simp only [parseOr, parseOrL, hAnd', hstop] at ⊢
  exact hOr F hF

-- The `un` legs from the induction hypothesis, generalised
-- over the prefix spelling: atoms take the primary leg (via
-- `primFrei_of_atom`), parenthesised children the `parseOr` leg
-- with `)` follow. Returns the seven generalised legs (no
-- primary: `primFrei` is false for `un`).
theorem turm_un : ∀ (n : Nat), RKern n →
    ∀ (o : String) (x : SExpr) (rest : List Token),
    (strEq o "!" || strEq o "-" || strEq o "~") = true →
    groesse (.un o x) ≤ n + 1 → gutKern x = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 2 ≤ G →
      parseUnary G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 3 ≤ G →
      parseMul G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 4 ≤ G →
      parseAdd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 5 ≤ G →
      parseBit G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 6 ≤ G →
      parseCmp G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 7 ≤ G →
      parseAnd G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.un o x) + 1) + groesse (.un o x) + 8 ≤ G →
      parseOr G (druckToks (.un o x) ++ rest) = .ok (.un o x, rest)) := by
  intro n rkn o x rest hop hs hgx hr hrs hrg
  obtain ⟨rOr, -, -, -, -, -, -, rPr⟩ := rkn
  have hsize : groesse (.un o x) = groesse x + 1 := rfl
  have hxn : groesse x ≤ n := by omega
  cases hat : istAtom x with
  | true =>
    have hpf : primFrei x = true := primFrei_of_atom x hat hgx
    have hPx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 1 ≤ G →
        parsePrimary G (druckToks x ++ rest) = .ok (x, rest) := by
      intro G hG
      exact rPr x rest G hxn hgx hpf hrs hrg hG
    exact kern_un_atom_turm o x rest hop hat hr hPx
  | false =>
    have hOx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 8 ≤ G →
        parseOr G (druckToks x ++ ([.zeichen ")"] ++ rest)) =
          .ok (x, [.zeichen ")"] ++ rest) := by
      intro G hG
      exact rOr x ([.zeichen ")"] ++ rest) G hxn hgx
        (hr_paren rest) (hrs_paren rest) (hrg_paren rest) hG
    exact kern_un_paren_turm o x rest hop hat hr hOx

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

-- The `bin "*"` legs from the star invariant: word for word
-- the `+` wrapper with the spelling swapped.
theorem turm_bin_star : ∀ (n : Nat), BKernStar n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "*" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest)) := by
  intro n bStar l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "*" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bStar l r rest G hsum hl hr2 hG
  exact kern_bin_star_turm l r rest hl hr2 hrr hrs hrg hB

-- The `bin "||"` legs from the or invariant: word for word
-- the `*` wrapper with the spelling swapped.
theorem turm_bin_or : ∀ (n : Nat), BKernOr n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "||" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest)) := by
  intro n bOr l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "||" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "||" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bOr l r rest G hsum hl hr2 hG
  exact kern_bin_or_turm l r rest hl hr2 hrr hrs hrg hB

-- The `bin "&&"` legs from the and invariant: word for word
-- the `||` wrapper with the spelling swapped.
theorem turm_bin_and : ∀ (n : Nat), BKernAnd n →
    ∀ (l r : SExpr) (rest : List Token),
    groesse (.bin "&&" l r) ≤ n + 1 →
    gutKern l = true → gutKern r = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 2 ≤ G →
      parseUnary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 3 ≤ G →
      parseMul G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 4 ≤ G →
      parseAdd G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 5 ≤ G →
      parseBit G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 6 ≤ G →
      parseCmp G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 7 ≤ G →
      parseAnd G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest))
    ∧ (∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 8 ≤ G →
      parseOr G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest)) := by
  intro n bAnd l r rest hs hl hr2 hrr hrs hrg
  have hsize : groesse (.bin "&&" l r) = groesse l + groesse r + 1 := rfl
  have hsum : groesse l + groesse r ≤ n := by omega
  have hB : ∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ rest) := by
    intro G hG
    exact bAnd l r rest G hsum hl hr2 hG
  exact kern_bin_and_turm l r rest hl hr2 hrr hrs hrg hB

-- Every `gutKernPlatz` tree is a head variable plus
-- kernel-lawful fragments: lane 161's `zerlege` with the
-- conclusion strengthened to `suffGutKern`.
theorem zerlege_kern : ∀ (n : Nat) (p : SExpr), groesse p ≤ n →
    gutKernPlatz p = true →
    ∃ (a : String) (suff : List SuffFrag),
      p = applySuff (.variable a) suff ∧
      (!istKeinPlatz a) = true ∧
      suffGutKern suff = true ∧
      suffGroesse suff + 1 ≤ n := by
  intro n
  induction n with
  | zero =>
    intro p hs _
    have hp := groesse_pos p
    omega
  | succ n ih =>
    intro p hs hg
    cases p with
    | lit m => simp [gutKernPlatz] at hg
    | gleit s => simp [gutKernPlatz] at hg
    | wahr => simp [gutKernPlatz] at hg
    | falsch => simp [gutKernPlatz] at hg
    | «variable» a =>
      simp only [gutKernPlatz] at hg
      exact ⟨a, [], rfl, hg, rfl, by simp only [suffGroesse]; omega⟩
    | feld x f =>
      simp only [gutKernPlatz] at hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hg
      refine ⟨a, suff ++ [.dot f], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hsg : suffGutKern (suff ++ [.dot f]) = suffGutKern suff := by
          simp [suffGutKern_append, suffGutKern]
        rw [hsg]
        exact hgs
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        omega
    | index x i =>
      simp only [gutKernPlatz, Bool.and_eq_true] at hg
      obtain ⟨hpx, hi⟩ := hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hpx
      refine ⟨a, suff ++ [.idx i], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hgi : gutKern i = true := hi
        have hsg : suffGutKern (suff ++ [.idx i]) =
            (suffGutKern suff && gutKern i) := by
          simp [suffGutKern_append, suffGutKern, Bool.and_assoc]
        rw [hsg]
        simp [hgs, hgi]
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        simp only [groesse, groesse_applySuff] at hs
        omega
    | pfeil x f =>
      simp only [gutKernPlatz] at hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hg
      refine ⟨a, suff ++ [.arrow f], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hsg : suffGutKern (suff ++ [.arrow f]) = suffGutKern suff := by
          simp [suffGutKern_append, suffGutKern]
        rw [hsg]
        exact hgs
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        omega
    | un o x => simp [gutKernPlatz] at hg
    | bin o l r => simp [gutKernPlatz] at hg
    | ruf f xs => simp [gutKernPlatz] at hg
    | fnwert f => simp [gutKernPlatz] at hg
    | eingebaut f xs => simp [gutKernPlatz] at hg
    | alt x => simp [gutKernPlatz] at hg
    | ergebnis => simp [gutKernPlatz] at hg
    | grund g f => simp [gutKernPlatz] at hg

-- Suffix chains through `parseSuffixe` over kernel trees:
-- lane 161's `suff_rund` with index payloads parsed through
-- `RKern` (they are `gutKern` by `suffGutKern`).
theorem kern_suff_rund : ∀ (n : Nat) (rkn : RKern n)
    (suff : List SuffFrag) (base : SExpr) (rest : List Token) (F : Nat),
    suffGroesse suff + groesse base ≤ n + 1 →
    suffGutKern suff = true →
    ruhigSuff rest = true →
    12 * (suffGroesse suff + groesse base + 1) + suffGroesse suff ≤ F →
    parseSuffixe F base (suffToks suff ++ rest) =
      .ok (applySuff base suff, rest) := by
  intro n rkn suff
  obtain ⟨rOr, -, -, -, -, -, -, -⟩ := rkn
  induction suff with
  | nil =>
    intro base rest F hs hg hr hF
    have hF1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [suffToks, List.nil_append] at ⊢
    exact stopSuffix F' base rest hr
  | cons frag suff ih =>
    cases frag with
    | dot f =>
      intro base rest F hs hg hr hF
      simp only [suffGutKern] at hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe] at ⊢
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.feld base f) ≤ n + 1 := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.feld base f) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.feld base f) rest F' hs2 hg hr hF2
    | arrow f =>
      intro base rest F hs hg hr hF
      simp only [suffGutKern] at hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe] at ⊢
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.pfeil base f) ≤ n + 1 := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.pfeil base f) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.pfeil base f) rest F' hs2 hg hr hF2
    | idx i =>
      intro base rest F hs hg hr hF
      simp only [suffGutKern, Bool.and_eq_true] at hg
      obtain ⟨hi, hgs⟩ := hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe] at ⊢
      have hii : groesse i ≤ n := by
        simp only [suffGroesse] at hs
        omega
      have hr1 : ruhig ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hr2 : ruhigSuff ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hr3 : ruhigGleit ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hFi : 12 * (groesse i + 1) + groesse i + 8 ≤ F' := by
        simp only [suffGroesse] at hs hF ⊢
        omega
      have hOi := rOr i ([.zeichen "]"] ++ suffToks suff ++ rest) F'
        hii hi hr1 hr2 hr3 hFi
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOi
      simp only [hOi, List.cons_append] at ⊢
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.index base i) ≤ n + 1 := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.index base i) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.index base i) rest F' hs2 hgs hr hF2

-- Kernel places through `parsePrimary`: decompose by
-- `zerlege_kern`, read the head, run the chain by
-- `kern_suff_rund`. The `parseKopf` steps reuse lane 161's
-- spelling-blind lemmas.
theorem kern_prim_platz : ∀ (n : Nat) (rkn : RKern n)
    (p : SExpr) (rest : List Token) (F : Nat),
    groesse p ≤ n + 1 → gutKernPlatz p = true → ruhigSuff rest = true →
    12 * (groesse p + 1) + groesse p + 1 ≤ F →
    parsePrimary F (druckToks p ++ rest) = .ok (p, rest) := by
  intro n rkn p rest F hs hg hr hF
  obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := zerlege_kern (n + 1) p hs hg
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hF2 : 1 ≤ F' := by omega
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  rw [druckToks_applySuff] at ⊢
  have hkaf : istKeinPlatz a = false := nichtWahr_falsch _ hka
  simp only [parsePrimary, druckToks, nameText, hkaf, List.cons_append,
    parseKopf] at ⊢
  simp only [List.nil_append] at ⊢
  simp only [sammleSeg_suffToks, hr] at ⊢
  have hmiss : ∀ (R : List Token),
      suffToks suff ++ rest ≠ .zeichen "(" :: R := by
    intro R hcon
    exact suffToks_nopar suff rest R hr hcon
  simp only [hmiss] at ⊢
  have hs2 : suffGroesse suff + groesse (.variable a) ≤ n + 1 := by
    simp only [groesse] at ⊢
    omega
  have hF3 : 12 * (suffGroesse suff + groesse (.variable a) + 1) +
      suffGroesse suff ≤ F'' := by
    simp only [groesse, groesse_applySuff] at hs hF ⊢
    omega
  exact kern_suff_rund n rkn suff (.variable a) rest F'' hs2 hgs hr hF3

-- The place tower, uniform over all place shapes: the
-- `parsePrimary` leg by `kern_prim_platz`, the `parseUnary`
-- leg by decomposing (`zerlege_kern` exposes the head
-- variable, so the prefix-operator match falls through to
-- `parsePrimary`), then `tower_up` for the six loop levels.
-- The place weak legs (no `ruhig`: the Unary step lacks
-- it): `parsePrimary` by `kern_prim_platz`, `parseUnary` by
-- decomposing.
theorem turm_platz_PU : ∀ (n : Nat), RKern n →
    ∀ (p : SExpr) (rest : List Token),
    groesse p ≤ n + 1 → gutKernPlatz p = true →
    ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 1 ≤ G →
      parsePrimary G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 2 ≤ G →
      parseUnary G (druckToks p ++ rest) = .ok (p, rest)) := by
  intro n rkn p rest hs hpp hrs hrg
  have hP : ∀ (G : Nat),
      12 * (groesse p + 1) + groesse p + 1 ≤ G →
      parsePrimary G (druckToks p ++ rest) = .ok (p, rest) := by
    intro G hG
    exact kern_prim_platz n rkn p rest G hs hpp hrs hG
  have hU : ∀ (G : Nat),
      12 * (groesse p + 1) + groesse p + 2 ≤ G →
      parseUnary G (druckToks p ++ rest) = .ok (p, rest) := by
    intro G hG
    have hG1 : 1 ≤ G := by omega
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ :=
      zerlege_kern (n + 1) p hs hpp
    have hP' := hP G' (by omega)
    rw [druckToks_applySuff] at hP' ⊢
    simp only [druckToks, List.cons_append, List.nil_append] at hP' ⊢
    simp only [parseUnary] at ⊢
    exact hP'
  exact ⟨hP, hU⟩

theorem turm_platz : ∀ (n : Nat), RKern n →
    ∀ (p : SExpr) (rest : List Token),
    groesse p ≤ n + 1 → gutKernPlatz p = true →
    ruhig rest = true → ruhigSuff rest = true → ruhigGleit rest = true →
    (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 1 ≤ G →
      parsePrimary G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 2 ≤ G →
      parseUnary G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 3 ≤ G →
      parseMul G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 4 ≤ G →
      parseAdd G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 5 ≤ G →
      parseBit G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 6 ≤ G →
      parseCmp G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 7 ≤ G →
      parseAnd G (druckToks p ++ rest) = .ok (p, rest))
    ∧ (∀ (G : Nat), 12 * (groesse p + 1) + groesse p + 8 ≤ G →
      parseOr G (druckToks p ++ rest) = .ok (p, rest)) := by
  intro n rkn p rest hs hpp hr hrs hrg
  have hPU := turm_platz_PU n rkn p rest hs hpp hrs hrg
  have hup := tower_up p rest hr hPU.2
  exact ⟨hPU.1, hPU.2, hup.1, hup.2.1, hup.2.2.1,
    hup.2.2.2.1, hup.2.2.2.2.1, hup.2.2.2.2.2⟩

-- The main induction, one level per lemma: each step lifts
-- one `RKern` component from `n` to `n + 1` by cases over the
-- tree (atoms via the standalone towers, `un` via `turm_un`,
-- `bin` via `turm_bin`, everything else contradicts `gutKern`).
-- Projections: atom/bin 8-tuples end `.2.2.2.2.2.2.2` at `Or`.
theorem kernOr_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 8 ≤ F →
      parseOr F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hr hrs hrg hF
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
    exact (turm_un n rkn o x rest hop hs hgx hr hrs hrg).2.2.2.2.2.2 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
    · exact (turm_bin_star n bStar l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
    · exact (turm_bin_or n bOr l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
    · exact (turm_bin_and n bAnd l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | feld x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.feld x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz n rkn (.feld x f) rest hs hpp hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz n rkn (.index x i) rest hs hpp hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | pfeil x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.pfeil x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz n rkn (.pfeil x f) rest hs hpp hr hrs hrg).2.2.2.2.2.2.2 F (by omega)
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

theorem kernAnd_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 7 ≤ F →
      parseAnd F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hr hrs hrg hF
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
    exact (turm_un n rkn o x rest hop hs hgx hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
    · exact (turm_bin_star n bStar l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
    · exact (turm_bin_or n bOr l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
    · exact (turm_bin_and n bAnd l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | feld x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.feld x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz n rkn (.feld x f) rest hs hpp hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz n rkn (.index x i) rest hs hpp hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | pfeil x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.pfeil x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz n rkn (.pfeil x f) rest hs hpp hr hrs hrg).2.2.2.2.2.2.1 F (by omega)
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

theorem kernCmp_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 6 ≤ F →
      parseCmp F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hr hrs hrg hF
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
    exact (turm_un n rkn o x rest hop hs hgx hr hrs hrg).2.2.2.2.1 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.1 F (by omega)
    · exact (turm_bin_star n bStar l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.1 F (by omega)
    · exact (turm_bin_or n bOr l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.1 F (by omega)
    · exact (turm_bin_and n bAnd l r rest hs hl hr2 hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | feld x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.feld x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz n rkn (.feld x f) rest hs hpp hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz n rkn (.index x i) rest hs hpp hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | pfeil x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.pfeil x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz n rkn (.pfeil x f) rest hs hpp hr hrs hrg).2.2.2.2.2.1 F (by omega)
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

theorem kernBit_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 5 ≤ F →
      parseBit F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hr hrs hrg hF
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
    exact (turm_un n rkn o x rest hop hs hgx hr hrs hrg).2.2.2.1 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.2.1 F (by omega)
    · exact (turm_bin_star n bStar l r rest hs hl hr2 hr hrs hrg).2.2.2.2.1 F (by omega)
    · exact (turm_bin_or n bOr l r rest hs hl hr2 hr hrs hrg).2.2.2.2.1 F (by omega)
    · exact (turm_bin_and n bAnd l r rest hs hl hr2 hr hrs hrg).2.2.2.2.1 F (by omega)
  | feld x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.feld x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz n rkn (.feld x f) rest hs hpp hr hrs hrg).2.2.2.2.1 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz n rkn (.index x i) rest hs hpp hr hrs hrg).2.2.2.2.1 F (by omega)
  | pfeil x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.pfeil x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz n rkn (.pfeil x f) rest hs hpp hr hrs hrg).2.2.2.2.1 F (by omega)
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

-- The `bin "*"` primary leg from a star-inner leg: word
-- for word the `+` leg with the spelling swapped.
theorem kern_bin_prim_star : ∀ (l r : SExpr) (rest : List Token),
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "*" l r, [.zeichen ")"] ++ rest)) →
    ∀ (G : Nat), 12 * (groesse (.bin "*" l r) + 1) + groesse (.bin "*" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "*" l r) ++ rest) =
        .ok (.bin "*" l r, rest) := by
  intro l r rest hB G hG
  have hsize : groesse (.bin "*" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "*" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "*"] ++ druckToks r ++ [.zeichen ")"] := by
    simp [druckToks]
  have hG1 : 1 ≤ G := by omega
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hB' := hB G' (by omega)
  have hPar := paren_arm _ _ _ _ hB'
  simp only [hd, List.append_assoc] at ⊢
  simp only [List.append_assoc] at hPar
  exact hPar

-- The `bin "||"` primary leg from an or-inner leg: word for
-- word the `*` leg with the spelling swapped.
theorem kern_bin_prim_or : ∀ (l r : SExpr) (rest : List Token),
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "||" l r, [.zeichen ")"] ++ rest)) →
    ∀ (G : Nat), 12 * (groesse (.bin "||" l r) + 1) + groesse (.bin "||" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "||" l r) ++ rest) =
        .ok (.bin "||" l r, rest) := by
  intro l r rest hB G hG
  have hsize : groesse (.bin "||" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "||" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "||"] ++ druckToks r ++ [.zeichen ")"] := by
    simp [druckToks]
  have hG1 : 1 ≤ G := by omega
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hB' := hB G' (by omega)
  have hPar := paren_arm _ _ _ _ hB'
  simp only [hd, List.append_assoc] at ⊢
  simp only [List.append_assoc] at hPar
  exact hPar

-- The `bin "&&"` primary leg from an and-inner leg: word for
-- word the `||` leg with the spelling swapped.
theorem kern_bin_prim_and : ∀ (l r : SExpr) (rest : List Token),
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "&&" l r, [.zeichen ")"] ++ rest)) →
    ∀ (G : Nat), 12 * (groesse (.bin "&&" l r) + 1) + groesse (.bin "&&" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "&&" l r) ++ rest) =
        .ok (.bin "&&" l r, rest) := by
  intro l r rest hB G hG
  have hsize : groesse (.bin "&&" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "&&" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "&&"] ++ druckToks r ++ [.zeichen ")"] := by
    simp [druckToks]
  have hG1 : 1 ≤ G := by omega
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hB' := hB G' (by omega)
  have hPar := paren_arm _ _ _ _ hB'
  simp only [hd, List.append_assoc] at ⊢
  simp only [List.append_assoc] at hPar
  exact hPar

-- The `bin "+"` primary leg from a binary-inner leg: no
-- follow premises at all (the `(` arm runs the inner parse).
-- Extracted for the `RKern`-primary component, which has no
-- `ruhig` (same proof as `kern_bin_turm`'s leg).
theorem kern_bin_prim : ∀ (l r : SExpr) (rest : List Token),
    (∀ (G : Nat),
      12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
      parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
        [.zeichen ")"] ++ rest) =
        .ok (.bin "+" l r, [.zeichen ")"] ++ rest)) →
    ∀ (G : Nat), 12 * (groesse (.bin "+" l r) + 1) + groesse (.bin "+" l r) + 1 ≤ G →
      parsePrimary G (druckToks (.bin "+" l r) ++ rest) =
        .ok (.bin "+" l r, rest) := by
  intro l r rest hB G hG
  have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
  have hd : druckToks (.bin "+" l r) = [.zeichen "("] ++ druckToks l ++
      [.zeichen "+"] ++ druckToks r ++ [.zeichen ")"] := by
    simp [druckToks]
  have hG1 : 1 ≤ G := by omega
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  have hB' := hB G' (by omega)
  have hPar := paren_arm _ _ _ _ hB'
  simp only [hd, List.append_assoc] at ⊢
  simp only [List.append_assoc] at hPar
  exact hPar

theorem kernAdd_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 4 ≤ F →
      parseAdd F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hr hrs hrg hF
  cases e with
  | lit m => exact (turm_lit m rest hr hrs hrg).2.2.2.1 F (by omega)
  | gleit s => exact (turm_gleit s rest hr hrs hrg).2.2.2.1 F (by omega)
  | wahr => exact (turm_wahr rest hr hrs hrg).2.2.2.1 F (by omega)
  | falsch => exact (turm_falsch rest hr hrs hrg).2.2.2.1 F (by omega)
  | «variable» a =>
    have hka : (!istKeinPlatz a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact (turm_var a rest hka hr hrs hrg).2.2.2.1 F (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    exact (turm_un n rkn o x rest hop hs hgx hr hrs hrg).2.2.1 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.2.1 F (by omega)
    · exact (turm_bin_star n bStar l r rest hs hl hr2 hr hrs hrg).2.2.2.1 F (by omega)
    · exact (turm_bin_or n bOr l r rest hs hl hr2 hr hrs hrg).2.2.2.1 F (by omega)
    · exact (turm_bin_and n bAnd l r rest hs hl hr2 hr hrs hrg).2.2.2.1 F (by omega)
  | feld x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.feld x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz n rkn (.feld x f) rest hs hpp hr hrs hrg).2.2.2.1 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz n rkn (.index x i) rest hs hpp hr hrs hrg).2.2.2.1 F (by omega)
  | pfeil x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.pfeil x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz n rkn (.pfeil x f) rest hs hpp hr hrs hrg).2.2.2.1 F (by omega)
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

theorem kernMul_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhig rest = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 3 ≤ F →
      parseMul F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hr hrs hrg hF
  cases e with
  | lit m => exact (turm_lit m rest hr hrs hrg).2.2.1 F (by omega)
  | gleit s => exact (turm_gleit s rest hr hrs hrg).2.2.1 F (by omega)
  | wahr => exact (turm_wahr rest hr hrs hrg).2.2.1 F (by omega)
  | falsch => exact (turm_falsch rest hr hrs hrg).2.2.1 F (by omega)
  | «variable» a =>
    have hka : (!istKeinPlatz a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact (turm_var a rest hka hr hrs hrg).2.2.1 F (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    exact (turm_un n rkn o x rest hop hs hgx hr hrs hrg).2.1 F (by omega)
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · exact (turm_bin n bkn l r rest hs hl hr2 hr hrs hrg).2.2.1 F (by omega)
    · exact (turm_bin_star n bStar l r rest hs hl hr2 hr hrs hrg).2.2.1 F (by omega)
    · exact (turm_bin_or n bOr l r rest hs hl hr2 hr hrs hrg).2.2.1 F (by omega)
    · exact (turm_bin_and n bAnd l r rest hs hl hr2 hr hrs hrg).2.2.1 F (by omega)
  | feld x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.feld x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz n rkn (.feld x f) rest hs hpp hr hrs hrg).2.2.1 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz n rkn (.index x i) rest hs hpp hr hrs hrg).2.2.1 F (by omega)
  | pfeil x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.pfeil x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz n rkn (.pfeil x f) rest hs hpp hr hrs hrg).2.2.1 F (by omega)
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

-- The `parseUnary` step: no `ruhig` premise (loops never see
-- the tail here), so atoms prove their fall-through legs
-- directly from the primary legs, and `un`/`bin` replay their
-- tower proofs with induction-hypothesis legs.
theorem kernUnary_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 2 ≤ F →
      parseUnary F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hrs hrg hF
  have rkn' := rkn
  obtain ⟨rOr, -, -, -, -, -, -, rPr⟩ := rkn
  cases e with
  | lit m =>
    have hP : ∀ (G : Nat), 12 * (groesse (.lit m) + 1) + groesse (.lit m) + 1 ≤ G →
        parsePrimary G (druckToks (.lit m) ++ rest) = .ok (.lit m, rest) := by
      intro G hG
      exact prim_lit m rest G (by omega)
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    simp only [parseUnary] at ⊢
    exact hP F' (by omega)
  | gleit s =>
    have hP : ∀ (G : Nat), 12 * (groesse (.gleit s) + 1) + groesse (.gleit s) + 1 ≤ G →
        parsePrimary G (druckToks (.gleit s) ++ rest) = .ok (.gleit s, rest) := by
      intro G hG
      exact prim_gleit s rest G hrg (by omega)
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    simp only [parseUnary] at ⊢
    exact hP F' (by omega)
  | wahr =>
    have hP : ∀ (G : Nat), 12 * (groesse .wahr + 1) + groesse .wahr + 1 ≤ G →
        parsePrimary G (druckToks .wahr ++ rest) = .ok (.wahr, rest) := by
      intro G hG
      exact prim_wahr rest G (by omega)
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    simp only [parseUnary] at ⊢
    exact hP F' (by omega)
  | falsch =>
    have hP : ∀ (G : Nat), 12 * (groesse .falsch + 1) + groesse .falsch + 1 ≤ G →
        parsePrimary G (druckToks .falsch ++ rest) = .ok (.falsch, rest) := by
      intro G hG
      exact prim_falsch rest G (by omega)
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    simp only [parseUnary] at ⊢
    exact hP F' (by omega)
  | «variable» a =>
    have hka : (!istKeinPlatz a) = true := by
      simp only [gutKern] at hg
      exact hg
    have hP : ∀ (G : Nat), 12 * (groesse (.variable a) + 1) + groesse (.variable a) + 1 ≤ G →
        parsePrimary G (druckToks (.variable a) ++ rest) =
          .ok (.variable a, rest) := by
      intro G hG
      exact kern_prim_var a rest G hka hrs (by omega)
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckToks, List.cons_append, List.nil_append] at ⊢
    simp only [parseUnary] at ⊢
    exact hP F' (by omega)
  | un o x =>
    rw [gutKern_un] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hop, hgx⟩ := hg
    have hsize : groesse (.un o x) = groesse x + 1 := rfl
    have hxn : groesse x ≤ n := by omega
    have hG1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases hat : istAtom x with
    | true =>
      have hpf : primFrei x = true := primFrei_of_atom x hat hgx
      have hPx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 1 ≤ G →
          parsePrimary G (druckToks x ++ rest) = .ok (x, rest) := by
        intro G hG
        exact rPr x rest G hxn hgx hpf hrs hrg hG
      have hd : druckToks (.un o x) =
          [.zeichen o] ++ druckToks x := by
        simp [druckToks, hat]
      have hP' := hPx F' (by omega)
      simp only [hd, List.append_assoc] at ⊢
      exact bang_arm_gen _ _ _ _ _ hop hP'
    | false =>
      have hOx : ∀ (G : Nat), 12 * (groesse x + 1) + groesse x + 8 ≤ G →
          parseOr G (druckToks x ++ ([.zeichen ")"] ++ rest)) =
            .ok (x, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact rOr x ([.zeichen ")"] ++ rest) G hxn hgx
          (hr_paren rest) (hrs_paren rest) (hrg_paren rest) hG
      have hd : druckToks (.un o x) = [.zeichen o] ++
          (([.zeichen "("] ++ druckToks x) ++ [.zeichen ")"]) := by
        simp [druckToks, hat]
      have hF2 : 1 ≤ F' := by omega
      obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
      have hO' := hOx F'' (by omega)
      have hPar := paren_arm _ _ _ _ hO'
      have hBang := bang_arm_gen _ _ _ _ _ hop hPar
      simp only [hd, List.append_assoc] at ⊢
      exact hBang
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hd : druckToks (.bin "+" l r) = [.zeichen "("] ++ druckToks l ++
          [.zeichen "+"] ++ druckToks r ++ [.zeichen ")"] := by
        simp [druckToks]
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "+" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bkn l r rest G hsum hl hr2 hG
      have hG1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hP' := kern_bin_prim l r rest hB F' (by omega)
      simp only [hd, List.append_assoc] at hP' ⊢
      exact un_paren_fall _ _ _ _ hP'
    · have hsize : groesse (.bin "*" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hd : druckToks (.bin "*" l r) = [.zeichen "("] ++ druckToks l ++
          [.zeichen "*"] ++ druckToks r ++ [.zeichen ")"] := by
        simp [druckToks]
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "*" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bStar l r rest G hsum hl hr2 hG
      have hG1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hP' := kern_bin_prim_star l r rest hB F' (by omega)
      simp only [hd, List.append_assoc] at hP' ⊢
      exact un_paren_fall _ _ _ _ hP'
    · have hsize : groesse (.bin "||" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hd : druckToks (.bin "||" l r) = [.zeichen "("] ++ druckToks l ++
          [.zeichen "||"] ++ druckToks r ++ [.zeichen ")"] := by
        simp [druckToks]
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "||" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bOr l r rest G hsum hl hr2 hG
      have hG1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hP' := kern_bin_prim_or l r rest hB F' (by omega)
      simp only [hd, List.append_assoc] at hP' ⊢
      exact un_paren_fall _ _ _ _ hP'
    · have hsize : groesse (.bin "&&" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hd : druckToks (.bin "&&" l r) = [.zeichen "("] ++ druckToks l ++
          [.zeichen "&&"] ++ druckToks r ++ [.zeichen ")"] := by
        simp [druckToks]
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "&&" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bAnd l r rest G hsum hl hr2 hG
      have hG1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hP' := kern_bin_prim_and l r rest hB F' (by omega)
      simp only [hd, List.append_assoc] at hP' ⊢
      exact un_paren_fall _ _ _ _ hP'
  | feld x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.feld x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact (turm_platz_PU n rkn' (.feld x f) rest hs hpp hrs hrg).2 F (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact (turm_platz_PU n rkn' (.index x i) rest hs hpp hrs hrg).2 F (by omega)
  | pfeil x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.pfeil x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact (turm_platz_PU n rkn' (.pfeil x f) rest hs hpp hrs hrg).2 F (by omega)
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

-- The `parsePrimary` step: no `ruhig` premise (suffixes never
-- see loop operators), prefix trees vacuous by `primFrei`.
theorem kernPrimary_step : ∀ (n : Nat), RKern n → BKern n → BKernStar n → BKernOr n → BKernAnd n →
    (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n + 1 →
      gutKern e = true → primFrei e = true → ruhigSuff rest = true →
      ruhigGleit rest = true →
      12 * (groesse e + 1) + groesse e + 1 ≤ F →
      parsePrimary F (druckToks e ++ rest) = .ok (e, rest)) := by
  intro n rkn bkn bStar bOr bAnd e rest F hs hg hpf hrs hrg hF
  cases e with
  | lit m => exact prim_lit m rest F (by omega)
  | gleit s => exact prim_gleit s rest F hrg (by omega)
  | wahr => exact prim_wahr rest F (by omega)
  | falsch => exact prim_falsch rest F (by omega)
  | «variable» a =>
    have hka : (!istKeinPlatz a) = true := by
      simp only [gutKern] at hg
      exact hg
    exact kern_prim_var a rest F hka hrs (by omega)
  | un o x => simp [primFrei] at hpf
  | bin o l r =>
    rw [gutKern_bin] at hg
    simp only [Bool.and_eq_true, and_assoc] at hg
    obtain ⟨hop, hl, hr2⟩ := hg
    obtain rfl | rfl | rfl | rfl := bin_is_pm o hop
    · have hsize : groesse (.bin "+" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "+"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "+" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bkn l r rest G hsum hl hr2 hG
      exact kern_bin_prim l r rest hB F (by omega)
    · have hsize : groesse (.bin "*" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "*"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "*" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bStar l r rest G hsum hl hr2 hG
      exact kern_bin_prim_star l r rest hB F (by omega)
    · have hsize : groesse (.bin "||" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "||"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "||" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bOr l r rest G hsum hl hr2 hG
      exact kern_bin_prim_or l r rest hB F (by omega)
    · have hsize : groesse (.bin "&&" l r) = groesse l + groesse r + 1 := rfl
      have hsum : groesse l + groesse r ≤ n := by omega
      have hB : ∀ (G : Nat),
          12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 10 ≤ G →
          parseOr G (druckToks l ++ [.zeichen "&&"] ++ druckToks r ++
            [.zeichen ")"] ++ rest) =
            .ok (.bin "&&" l r, [.zeichen ")"] ++ rest) := by
        intro G hG
        exact bAnd l r rest G hsum hl hr2 hG
      exact kern_bin_prim_and l r rest hB F (by omega)
  | feld x f =>
    rw [gutKern_feld] at hg
    have hpp : gutKernPlatz (.feld x f) = true := by
      rw [gutKernPlatz_feld]; exact hg
    exact kern_prim_platz n rkn (.feld x f) rest F hs hpp hrs (by omega)
  | index x i =>
    rw [gutKern_index] at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨hpx, hi⟩ := hg
    have hpp : gutKernPlatz (.index x i) = true := by
      rw [gutKernPlatz_index]; simp only [Bool.and_eq_true]; exact ⟨hpx, hi⟩
    exact kern_prim_platz n rkn (.index x i) rest F hs hpp hrs (by omega)
  | pfeil x f =>
    rw [gutKern_pfeil] at hg
    have hpp : gutKernPlatz (.pfeil x f) = true := by
      rw [gutKernPlatz_pfeil]; exact hg
    exact kern_prim_platz n rkn (.pfeil x f) rest F hs hpp hrs (by omega)
  | ruf f xs => simp [gutKern] at hg
  | fnwert f => simp [gutKern] at hg
  | eingebaut f xs => simp [gutKern] at hg
  | alt x => simp [gutKern] at hg
  | ergebnis => simp [gutKern] at hg
  | grund g f => simp [gutKern] at hg

-- The joint invariant by size induction: base cases are
-- vacuous (every tree has size at least one, every pair at
-- least two), steps assemble the eight level lemmas plus all
-- four inner traces.
theorem kernRB : ∀ (n : Nat), RKern n ∧ BKern n ∧ BKernStar n ∧ BKernOr n ∧ BKernAnd n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _
        have hp := groesse_pos e
        omega
      · intro e rest F hs _ _ _ _ _
        have hp := groesse_pos e
        omega
    · intro l r W F hsum _ _ _
      have hpl := groesse_pos l
      have hpr := groesse_pos r
      omega
    · intro l r W F hsum _ _ _
      have hpl := groesse_pos l
      have hpr := groesse_pos r
      omega
    · intro l r W F hsum _ _ _
      have hpl := groesse_pos l
      have hpr := groesse_pos r
      omega
    · intro l r W F hsum _ _ _
      have hpl := groesse_pos l
      have hpr := groesse_pos r
      omega
  | succ n ih =>
    obtain ⟨rkn, bkn, bStar, bOr, bAnd⟩ := ih
    exact ⟨⟨kernOr_step n rkn bkn bStar bOr bAnd, kernAnd_step n rkn bkn bStar bOr bAnd,
      kernCmp_step n rkn bkn bStar bOr bAnd, kernBit_step n rkn bkn bStar bOr bAnd,
      kernAdd_step n rkn bkn bStar bOr bAnd, kernMul_step n rkn bkn bStar bOr bAnd,
      kernUnary_step n rkn bkn bStar bOr bAnd, kernPrimary_step n rkn bkn bStar bOr bAnd⟩,
      kernB_step n rkn, kernB_step_star n rkn, kernB_step_or n rkn,
      kernB_step_and n rkn⟩

-- Step A goal: every `gutKern` tree parses back from its
-- printed tokens with `brennstoff` fuel. The `Or` leg of the
-- invariant at `groesse e`, with `ende` follows (all `rfl`) and
-- fuel exactly `brennstoff` (which was grown to the `RKern`
-- bound -- measured, see its doc comment).
theorem parse_druck_kern : ∀ (e : SExpr), gutKern e = true →
    parseOr (brennstoff e) (druckToks e ++ [.ende]) =
      .ok (e, [.ende]) := by
  intro e hg
  have hRB := kernRB (groesse e)
  obtain ⟨⟨rOr, -, -, -, -, -, -, -⟩, -, -, -, -⟩ := hRB
  have hr : ruhig [.ende] = true := rfl
  have hrs : ruhigSuff [.ende] = true := rfl
  have hrg : ruhigGleit [.ende] = true := rfl
  have hF : 12 * (groesse e + 1) + groesse e + 8 ≤ brennstoff e := by
    simp [brennstoff]
  exact rOr e [.ende] (brennstoff e) (Nat.le_refl _) hg hr hrs hrg hF

-- Witnesses on small expressions, each in two forms: the
-- `parse_druck_kern` instance (the round trip at work), and a
-- kernel-computed shape check. (`decide` on `Except`-equality
-- fails: no `DecidableEq SExpr` -- the `match` form needs only
-- discrimination, so the kernel evaluates both sides.)
theorem zeuge_kern_lit : parseOr (brennstoff (.lit 5))
    (druckToks (.lit 5) ++ [.ende]) = .ok (.lit 5, [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_lit_rech : (match parseOr (brennstoff (.lit 5))
    (druckToks (.lit 5) ++ [.ende]) with
    | .ok (.lit 5, [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_kern_plus :
    parseOr (brennstoff (.bin "+" (.lit 1) (.lit 2)))
    (druckToks (.bin "+" (.lit 1) (.lit 2)) ++ [.ende]) =
      .ok (.bin "+" (.lit 1) (.lit 2), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_plus_rech : (match parseOr
    (brennstoff (.bin "+" (.lit 1) (.lit 2)))
    (druckToks (.bin "+" (.lit 1) (.lit 2)) ++ [.ende]) with
    | .ok (.bin "+" (.lit 1) (.lit 2), [.ende]) => true
    | _ => false) = true := by
  decide
-- Step B1 witnesses: the widened predicate at work (negation
-- of a literal, bitwise-not of a variable).
theorem zeuge_kern_neg : parseOr (brennstoff (.un "-" (.lit 3)))
    (druckToks (.un "-" (.lit 3)) ++ [.ende]) =
      .ok (.un "-" (.lit 3), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_neg_rech : (match parseOr (brennstoff (.un "-" (.lit 3)))
    (druckToks (.un "-" (.lit 3)) ++ [.ende]) with
    | .ok (.un "-" (.lit 3), [.ende]) => true
    | _ => false) = true := by
  decide
-- Step B2 witnesses: the second binary level at work (a
-- product, nested in a sum).
theorem zeuge_kern_mul : parseOr (brennstoff (.bin "*" (.lit 2) (.lit 3)))
    (druckToks (.bin "*" (.lit 2) (.lit 3)) ++ [.ende]) =
      .ok (.bin "*" (.lit 2) (.lit 3), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_mul_rech : (match parseOr
    (brennstoff (.bin "*" (.lit 2) (.lit 3)))
    (druckToks (.bin "*" (.lit 2) (.lit 3)) ++ [.ende]) with
    | .ok (.bin "*" (.lit 2) (.lit 3), [.ende]) => true
    | _ => false) = true := by
  decide
-- Step B4 witnesses: the loop level at work (a disjunction).
theorem zeuge_kern_or : parseOr (brennstoff (.bin "||" (.wahr) (.falsch)))
    (druckToks (.bin "||" (.wahr) (.falsch)) ++ [.ende]) =
      .ok (.bin "||" (.wahr) (.falsch), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_or_rech : (match parseOr
    (brennstoff (.bin "||" (.wahr) (.falsch)))
    (druckToks (.bin "||" (.wahr) (.falsch)) ++ [.ende]) with
    | .ok (.bin "||" (.wahr) (.falsch), [.ende]) => true
    | _ => false) = true := by
  decide
-- Step B5 witnesses: the second loop level at work (a
-- conjunction).
theorem zeuge_kern_and : parseOr (brennstoff (.bin "&&" (.wahr) (.wahr)))
    (druckToks (.bin "&&" (.wahr) (.wahr)) ++ [.ende]) =
      .ok (.bin "&&" (.wahr) (.wahr), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_and_rech : (match parseOr
    (brennstoff (.bin "&&" (.wahr) (.wahr)))
    (druckToks (.bin "&&" (.wahr) (.wahr)) ++ [.ende]) with
    | .ok (.bin "&&" (.wahr) (.wahr), [.ende]) => true
    | _ => false) = true := by
  decide
-- Step B3 witnesses: a field chain and an index place.
theorem zeuge_kern_feld : parseOr (brennstoff (.feld (.variable "x") "f"))
    (druckToks (.feld (.variable "x") "f") ++ [.ende]) =
      .ok (.feld (.variable "x") "f", [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_feld_rech : (match parseOr
    (brennstoff (.feld (.variable "x") "f"))
    (druckToks (.feld (.variable "x") "f") ++ [.ende]) with
    | .ok (.feld (.variable "x") "f", [.ende]) => true
    | _ => false) = true := by
  decide
theorem zeuge_kern_index :
    parseOr (brennstoff (.index (.variable "x") (.lit 0)))
    (druckToks (.index (.variable "x") (.lit 0)) ++ [.ende]) =
      .ok (.index (.variable "x") (.lit 0), [.ende]) :=
  parse_druck_kern _ (by decide)
theorem zeuge_kern_index_rech : (match parseOr
    (brennstoff (.index (.variable "x") (.lit 0)))
    (druckToks (.index (.variable "x") (.lit 0)) ++ [.ende]) with
    | .ok (.index (.variable "x") (.lit 0), [.ende]) => true
    | _ => false) = true := by
  decide

end Gabbro.Grammatik.Parser
