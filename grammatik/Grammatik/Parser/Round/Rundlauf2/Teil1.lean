module
public import Grammatik.Parser.Round.Rundlauf2.Teil1a

public import Grammatik.Parser.Round.Rundlauf

@[expose] public section



namespace Gabbro.Grammatik.Parser
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
    (!istKopfWort a) = true → ruhigSuff rest = true →
    12 * (groesse (.variable a) + 1) + groesse (.variable a) + 1 ≤ F →
    parsePrimary F (druckToks (.variable a) ++ rest) =
      .ok (.variable a, rest) := by
  intro a rest F hka hrs hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append, List.nil_append]
  rw [parsePrimary_nameTok _ _ _ (nichtWahr_falsch _ hka)]
  have hkaf : istKeinPlatz a = false := kopf_kp (nichtWahr_falsch _ hka)
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
  have hgeneric : ∀ R, rest ≠ .zeichen "::" :: .zeichen "[" :: R := by
    simpa only [suffToks, List.nil_append] using suffToks_nogeneric [] rest hrs
  simp only [parseKopf, nameText_nameTok, hseg, rufKopf_ohne, hgeneric, hmiss] at ⊢
  have hF3 : 1 ≤ F'' := by omega
  obtain ⟨F''', rfl⟩ : ∃ F''', F'' = F''' + 1 := ⟨F'' - 1, by omega⟩
  exact stopSuffix F''' _ _ hrs

end Gabbro.Grammatik.Parser
