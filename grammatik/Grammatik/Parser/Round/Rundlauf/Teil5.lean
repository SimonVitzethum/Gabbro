module
public import Grammatik.Parser.Round.Rundlauf.Teil5a

public import Grammatik.Parser.Expr.Ausdruck
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Lex.WortStellung
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Round.Rundlauf.Teil4

@[expose] public section

namespace Gabbro.Grammatik.Parser
-- The round-trip invariant at size bound `n`: every level parses
-- every `gut` tree from its printed tokens with fuel linear in
-- the tree size, plus one spare per node (the `+ groesse e`
-- covers descent strips and short chains wherever a bound is
-- reused at reduced fuel). Levels take a benign follow (`ruhig`
-- for the loops, `ruhigSuff` for the suffixes); `parsePrimary`
-- takes only the suffix follow (it has no loops) plus `primFrei`
-- (prefix trees live at the unary level), with descent slack
-- (`+7`) for application below a descent.
def R (n : Nat) : Prop :=
  (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 8 ≤ F →
    parseOr F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 8 ≤ F →
    parseAnd F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 8 ≤ F →
    parseCmp F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 8 ≤ F →
    parseBit F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 8 ≤ F →
    parseAdd F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 8 ≤ F →
    parseMul F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → ruhig rest = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 8 ≤ F →
    parseUnary F (druckToks e ++ rest) = .ok (e, rest))
  ∧ (∀ (e : SExpr) (rest : List Token) (F : Nat), groesse e ≤ n →
    gut e = true → primFrei e = true → ruhigSuff rest = true →
    ruhigGleit rest = true →
    12 * (groesse e + 1) + groesse e + 1 ≤ F →
    parsePrimary F (druckToks e ++ rest) = .ok (e, rest))

-- The binary-inner parse: a parenthesised operator's inside
-- (`l op r` between the parens), by operator level. No follow
-- premise: the tail after `)` is never inspected.
def B (n : Nat) : Prop :=
  ∀ (o : String) (l r : SExpr) (W : List Token) (F : Nat),
    groesse l + groesse r ≤ n → gutOpBin o = true →
    gut l = true → gut r = true →
    12 * (groesse l + groesse r + 1) + (groesse l + groesse r) + 8 ≤ F →
    parseOr F (druckToks l ++ [.zeichen o] ++ druckToks r ++
      [.zeichen ")"] ++ W) =
      .ok (.bin o l r, [.zeichen ")"] ++ W)

-- `sammleSegmente` stops on a benign suffix follow (pure: no fuel
-- needed). The `::` arm is the only continuer; anything else
-- returns the accumulator untouched.
theorem sammleSeg_stop : ∀ (segs : List String) (t : List Token),
    ruhigSuff t = true → sammleSegmente t segs = (segs, t) := by
  intro segs t h
  cases t with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | ident s => rfl
    | wort s => rfl
    | num n => rfl
    | float s => rfl
    | text s => rfl
    | doku s => rfl
    | zeichen s =>
      simp only [ruhigSuff] at h
      have hf := nichtWahr_falsch _ h
      simp only [Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨-, -, -, hDc, -⟩ := hf
      have ne := strNe_of s "::" hDc
      simp only [List.cons.injEq, Token.zeichen.injEq, ne, false_and, imp_self, implies_true, sammleSegmente]
    | ende => rfl

-- A benign follow never starts with `(` (for the `parseKopf` call
-- arm, which would otherwise read a call where a place stands).
theorem ruhigSuff_nopar : ∀ (t : List Token), ruhigSuff t = true →
    ∀ (R : List Token), t ≠ .zeichen "(" :: R := by
  intro t h R hcon
  cases t with
  | nil => simp only [List.nil_eq, reduceCtorEq] at hcon
  | cons hd tl =>
    cases hd with
    | ident s => simp only [List.cons.injEq, reduceCtorEq, false_and] at hcon
    | wort s => simp only [List.cons.injEq, reduceCtorEq, false_and] at hcon
    | num n => simp only [List.cons.injEq, reduceCtorEq, false_and] at hcon
    | float s => simp only [List.cons.injEq, reduceCtorEq, false_and] at hcon
    | text s => simp only [List.cons.injEq, reduceCtorEq, false_and] at hcon
    | doku s => simp only [List.cons.injEq, reduceCtorEq, false_and] at hcon
    | zeichen s =>
      simp only [ruhigSuff] at h
      have hf := nichtWahr_falsch _ h
      simp only [Bool.or_eq_false_iff, and_assoc] at hf
      obtain ⟨-, -, -, -, hP⟩ := hf
      have ne := strNe_of s "(" hP
      injection hcon with hs _
      injection hs with hs2
      exact ne hs2
    | ende => simp only [List.cons.injEq, reduceCtorEq, false_and] at hcon

-- One argument through `parseArg`: the label strip misses (the
-- second token is never `:`), then the expression parses. The
-- strip-fire case dies by positional injection (`keinDP_tree` for
-- the tail token, the separator spelling for the empty tail).
theorem arg_einzeln : ∀ (n : Nat) (Rn : R n)
    (x : SExpr) (sep : Token) (S : List Token) (F : Nat),
    groesse x ≤ n → gut x = true →
    (sep = .zeichen "," ∨ sep = .zeichen ")") →
    12 * (groesse x + 1) + groesse x + 9 ≤ F →
    parseArg F (druckToks x ++ [sep] ++ S) = .ok (x, [sep] ++ S) := by
  intro n Rn x sep S F hx hxg hsep hF
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hmiss : ∀ (t0 : Token) (rest : List Token),
      druckToks x ++ [sep] ++ S ≠ t0 :: .zeichen ":" :: rest := by
    intro t0 rest hcon
    have hne : druckToks x ≠ [] := by
      intro he
      have hlen := toksLang (groesse x) x (Nat.le_refl _)
      rw [he] at hlen
      simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
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
      | inl h =>
        subst h
        simp only [Token.zeichen.injEq, String.reduceEq] at hsep2
      | inr h =>
        subst h
        simp only [Token.zeichen.injEq, String.reduceEq] at hsep2
    | cons b R3 =>
      rw [hR] at ht
      simp only [List.cons_append] at ht
      injection ht with hb _
      have hbmem : b ∈ druckToks x := by simp only [hxb, hR, List.mem_cons, true_or, or_true]
      have hne2 := keinDP_tree n x hx hxg b hbmem
      exact hne2 hb
  simp only [parseArg] at ⊢
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
  have hFr : 12 * (groesse x + 1) + groesse x + 8 ≤ F' := by omega
  obtain ⟨hOr, -⟩ := Rn
  simpa only [List.append_assoc] using hOr x ([sep] ++ S) F' hx hxg hr1 hr2 hr3 hFr

end Gabbro.Grammatik.Parser
