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


end Gabbro.Grammatik.Parser
