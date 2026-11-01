module

public import Grammatik.Parser.Round.Rundlauf

@[expose] public section



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
  | .variable s => !istKopfWort s
  | .field x _ => gutKernPlatz x
  | .index x i => gutKernPlatz x && gutKern i
  | .arrow x _ => gutKernPlatz x
  | _ => false
def gutKern : SExpr → Bool
  | .lit _ => true
  | .float _ => true
  | .tru => true
  | .fls => true
  | .variable s => !istKopfWort s
  | .un o x =>
    (strEq o "!" || strEq o "-" || strEq o "~") && gutKern x
  | .bin o l r =>
    (strEq o "+" || strEq o "*" || strEq o "||" || strEq o "&&") &&
      gutKern l && gutKern r
  | .field x f => gutKernPlatz x
  | .index x i => gutKernPlatz x && gutKern i
  | .arrow x f => gutKernPlatz x
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
  | nil => simp only [List.nil_append, suffGutKern, Bool.true_and, implies_true]
  | cons f s ih =>
    cases f with
    | dot g => simp only [List.cons_append, suffGutKern, ih, implies_true]
    | arrow g => simp only [List.cons_append, suffGutKern, ih, implies_true]
    | idx i => simp only [List.cons_append, suffGutKern, ih, Bool.and_assoc, implies_true]

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
    gutKern (.field x f) = gutKernPlatz x := by
  intro x f
  rfl
theorem gutKern_index : ∀ (x i : SExpr),
    gutKern (.index x i) = (gutKernPlatz x && gutKern i) := by
  intro x i
  rfl
theorem gutKern_pfeil : ∀ (x : SExpr) (f : String),
    gutKern (.arrow x f) = gutKernPlatz x := by
  intro x f
  rfl
theorem gutKernPlatz_feld : ∀ (x : SExpr) (f : String),
    gutKernPlatz (.field x f) = gutKernPlatz x := by
  intro x f
  rfl
theorem gutKernPlatz_index : ∀ (x i : SExpr),
    gutKernPlatz (.index x i) = (gutKernPlatz x && gutKern i) := by
  intro x i
  rfl
theorem gutKernPlatz_pfeil : ∀ (x : SExpr) (f : String),
    gutKernPlatz (.arrow x f) = gutKernPlatz x := by
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

theorem un_ne_klammer (o : String) (hop : (strEq o "!" || strEq o "-" || strEq o "~") = true) :
    strEq o "-()" = false := by
  obtain rfl | rfl | rfl := un_is_pre o hop <;> decide

/-- The operand condition of the `-` arm for an atom: a numeral prints no `(`. -/
theorem atom_bed (x : SExpr) (rest : List Token) :
    (∀ T, druckToks x ++ rest ≠ .zeichen "(" :: T) ∨ istLit x = false := by
  cases x <;> simp only [druckToks, List.cons_append, List.nil_append, ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true, istLit, Bool.true_eq_false, or_false, or_self, nameTok_ne_zeichen, List.append_assoc, or_true, true_and, forall_eq', Token.zeichen.injEq, String.reduceEq]

theorem nonatom_bed (x : SExpr) (hat : istAtom x = false) : istLit x = false := by
  cases x <;> simp_all [istAtom, istLit]

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
  | float s => rfl
  | tru => rfl
  | fls => rfl
  | «variable» s =>
    simp only [gutKern] at h
    simp only [gut] at ⊢
    exact h
  | field x f =>
    rw [gutKern_feld] at h
    simp only [gut] at ⊢
    exact gutPlatz_of_gutKernPlatz x h
  | index x i =>
    rw [gutKern_index] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hpx, hi⟩ := h
    simp only [gut, Bool.and_eq_true] at ⊢
    exact ⟨gutPlatz_of_gutKernPlatz x hpx, gut_of_gutKern i hi⟩
  | arrow x f =>
    rw [gutKern_pfeil] at h
    simp only [gut] at ⊢
    exact gutPlatz_of_gutKernPlatz x h
  | un o x =>
    rw [gutKern_un] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hop, hx⟩ := h
    obtain rfl | rfl | rfl := un_is_pre o hop
    · simp only [gut, gut_of_gutKern x hx, Bool.and_true, Bool.or_eq_true]
      left; decide
    · simp only [gut, gut_of_gutKern x hx, Bool.and_true, Bool.or_eq_true]
      left; decide
    · simp only [gut, gut_of_gutKern x hx, Bool.and_true, Bool.or_eq_true]
      left; decide
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
  | call f xs => simp only [gutKern, Bool.false_eq_true] at h
  | fnref f => simp only [gutKern, Bool.false_eq_true] at h
  | built f xs => simp only [gutKern, Bool.false_eq_true] at h
  | old x => simp only [gutKern, Bool.false_eq_true] at h
  | res => simp only [gutKern, Bool.false_eq_true] at h
  | why g f => simp only [gutKern, Bool.false_eq_true] at h
  | ext xk xn xs => simp only [gutKern, Bool.false_eq_true] at h
theorem gutPlatz_of_gutKernPlatz : ∀ (p : SExpr),
    gutKernPlatz p = true → gutPlatz p = true := by
  intro p h
  cases p with
  | lit m => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | float s => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | tru => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | fls => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | «variable» s =>
    simp only [gutKernPlatz] at h
    simp only [gutPlatz] at ⊢
    exact h
  | field x f =>
    simp only [gutKernPlatz] at h
    simp only [gutPlatz] at ⊢
    exact gutPlatz_of_gutKernPlatz x h
  | index x i =>
    simp only [gutKernPlatz, Bool.and_eq_true] at h
    obtain ⟨hpx, hi⟩ := h
    simp only [gutPlatz, Bool.and_eq_true] at ⊢
    exact ⟨gutPlatz_of_gutKernPlatz x hpx, gut_of_gutKern i hi⟩
  | arrow x f =>
    simp only [gutKernPlatz] at h
    simp only [gutPlatz] at ⊢
    exact gutPlatz_of_gutKernPlatz x h
  | un o x => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | bin o l r => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | call f xs => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | fnref f => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | built f xs => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | old x => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | res => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | why g f => simp only [gutKernPlatz, Bool.false_eq_true] at h
  | ext xk xn xs => simp only [gutKernPlatz, Bool.false_eq_true] at h
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
  simp only [parseKopf, nameText_nameTok, hseg, hkaf, hmiss,
    Bool.false_ne_true] at ⊢
  have hF3 : 1 ≤ F'' := by omega
  obtain ⟨F''', rfl⟩ : ∃ F''', F'' = F''' + 1 := ⟨F'' - 1, by omega⟩
  exact stopSuffix F''' _ _ hrs

end Gabbro.Grammatik.Parser
