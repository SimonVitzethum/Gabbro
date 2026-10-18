/-
  File:      Grammatik/Parser/Round/RundlaufAnw2.lean
  Subject:   Track P: the statement round trip, part two -- the dispatch of `parseStmt`, one simple statement,
             a statement list and a block (see `RundlaufAnw` for the statement of the class and the head
             facts).
-/
import Grammatik.Parser.Round.RundlaufAnw

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

theorem strEq_self (a : String) : strEq a a = true := (strEq_eq a a).mpr rfl
attribute [local simp] strEq_self

/-! ## The statement dispatch -/

theorem strEq_ret_let : strEq "return" "let" = false := by decide
theorem strEq_ret_if : strEq "return" "if" = false := by decide
theorem strEq_ret_match : strEq "return" "match" = false := by decide
theorem strEq_ret_traverse : strEq "return" "traverse" = false := by decide
theorem strEq_ret_retry : strEq "return" "retry" = false := by decide
theorem strEq_ret_forever : strEq "return" "forever" = false := by decide
theorem strEq_ret_breaking : strEq "return" "breaking" = false := by decide
theorem strEq_ret_narrow : strEq "return" "narrow" = false := by decide
theorem strEq_ret_locks : strEq "return" "locks" = false := by decide
theorem strEq_ret_observes : strEq "return" "observes" = false := by decide
theorem strEq_ret_leave : strEq "return" "leave" = false := by decide
theorem strEq_ret_next : strEq "return" "next" = false := by decide
theorem strEq_ret_ret : strEq "return" "return" = true := by decide
theorem strEq_leave_let : strEq "leave" "let" = false := by decide
theorem strEq_leave_if : strEq "leave" "if" = false := by decide
theorem strEq_leave_match : strEq "leave" "match" = false := by decide
theorem strEq_leave_traverse : strEq "leave" "traverse" = false := by decide
theorem strEq_leave_retry : strEq "leave" "retry" = false := by decide
theorem strEq_leave_forever : strEq "leave" "forever" = false := by decide
theorem strEq_leave_breaking : strEq "leave" "breaking" = false := by decide
theorem strEq_leave_narrow : strEq "leave" "narrow" = false := by decide
theorem strEq_leave_locks : strEq "leave" "locks" = false := by decide
theorem strEq_leave_observes : strEq "leave" "observes" = false := by decide
theorem strEq_leave_leave : strEq "leave" "leave" = true := by decide
theorem strEq_next_let : strEq "next" "let" = false := by decide
theorem strEq_next_if : strEq "next" "if" = false := by decide
theorem strEq_next_match : strEq "next" "match" = false := by decide
theorem strEq_next_traverse : strEq "next" "traverse" = false := by decide
theorem strEq_next_retry : strEq "next" "retry" = false := by decide
theorem strEq_next_forever : strEq "next" "forever" = false := by decide
theorem strEq_next_breaking : strEq "next" "breaking" = false := by decide
theorem strEq_next_narrow : strEq "next" "narrow" = false := by decide
theorem strEq_next_locks : strEq "next" "locks" = false := by decide
theorem strEq_next_observes : strEq "next" "observes" = false := by decide
theorem strEq_next_leave : strEq "next" "leave" = false := by decide
theorem strEq_next_next : strEq "next" "next" = true := by decide
theorem strEq_let_let : strEq "let" "let" = true := by decide

theorem parseStmt_ret_eq (f : Nat) (r : List Token) (h : istOrtsFort r = false) :
    parseStmt (f + 1) (.wort "return" :: r) = parseRueck f r := by
  simp [parseStmt, h, strEq_ret_let, strEq_ret_if, strEq_ret_match, strEq_ret_traverse, strEq_ret_retry,
    strEq_ret_forever, strEq_ret_breaking, strEq_ret_narrow, strEq_ret_locks, strEq_ret_observes,
    strEq_ret_leave, strEq_ret_next, strEq_ret_ret]

theorem parseStmt_leave_eq (f : Nat) (r : List Token) (h : istOrtsFort r = false) :
    parseStmt (f + 1) (.wort "leave" :: r) = parseVerlasse f r := by
  simp [parseStmt, h, strEq_leave_let, strEq_leave_if, strEq_leave_match, strEq_leave_traverse,
    strEq_leave_retry, strEq_leave_forever, strEq_leave_breaking, strEq_leave_narrow, strEq_leave_locks,
    strEq_leave_observes, strEq_leave_leave]

theorem parseStmt_next_eq (f : Nat) (r : List Token) (h : istOrtsFort r = false) :
    parseStmt (f + 1) (.wort "next" :: r) = parseWeiter f r := by
  simp [parseStmt, h, strEq_next_let, strEq_next_if, strEq_next_match, strEq_next_traverse,
    strEq_next_retry, strEq_next_forever, strEq_next_breaking, strEq_next_narrow, strEq_next_locks,
    strEq_next_observes, strEq_next_leave, strEq_next_next]

theorem parseStmt_let_eq (f : Nat) (r : List Token) (h : istOrtsFort r = false) :
    parseStmt (f + 1) (.wort "let" :: r) = parseLet f r := by
  simp [parseStmt, h, strEq_let_let]

/-- `return` with no value: a `;` behind it. -/
theorem parseRueck_leer (f : Nat) (r : List Token) :
    parseRueck (f + 1) (.zeichen ";" :: r) = .ok (.ret none, r) := by
  simp [parseRueck]

/-- `return e ;` for a head that is no `;`, given the expression read. -/
theorem parseRueck_aus (f : Nat) (toks : List Token) (x : SExpr) (r : List Token)
    (h : ∀ ts, toks ≠ .zeichen ";" :: ts) (hO : parseOr f toks = .ok (x, .zeichen ";" :: r)) :
    parseRueck (f + 1) toks = .ok (.ret (some x), r) := by
  rcases toks with _ | ⟨t, ts⟩
  · simp [parseRueck, hO, fordereZeichen]
  · cases t with
    | zeichen s =>
      by_cases hs : s = ";"
      · subst hs; exact absurd rfl (h ts)
      · simp [parseRueck, hs, hO, fordereZeichen]
    | _ => simp [parseRueck, hO, fordereZeichen]

theorem kopf_nicht_semi (t : Token) (h : KopfGut t) (ts : List Token) :
    ∀ us, t :: ts ≠ .zeichen ";" :: us := by
  intro us hc
  injection hc with ht _
  subst ht
  simp only [KopfGut] at h
  rcases h with h | h | h | h | h <;> exact absurd h (by decide)

theorem kopf_nicht_ortsfort (t : Token) (h : KopfGut t) (ts : List Token) :
    istOrtsFort (t :: ts) = false := by
  cases t with
  | zeichen s =>
    simp only [KopfGut] at h
    rcases h with h | h | h | h | h <;> subst h <;> simp [istOrtsFort]
  | _ => simp [istOrtsFort]

/-! ## One statement -/

/-- The simple statements of the first theorem. -/
inductive Einfach : SAnw → Prop
  | retLeer : Einfach (.ret none)
  | ret (e : SExpr) : gutPrim e = true → Einfach (.ret (some e))
  | leave (l : String) : Einfach (.leave l)
  | next (l : String) : Einfach (.next l)
  | bind (x : String) (e : SExpr) : gutPrim e = true → Einfach (.bind false x none e)

/-- The fuel one statement needs. -/
def fuelAnw : SAnw → Nat
  | .ret (some e) => brennstoff e + 2
  | .bind _ _ _ e => brennstoff e + 2
  | _ => 2

/-- The legs of an expression followed by `;`. -/
theorem or_vor_semi (e : SExpr) (hg : gutPrim e = true) (r : List Token) (f : Nat)
    (hf : brennstoff e ≤ f) :
    parseOr f (druckToks e ++ .zeichen ";" :: r) = .ok (e, .zeichen ";" :: r) := by
  have hL := (legsPrim e hg).2.2.2.2.2.2.2
  exact hL (.zeichen ";" :: r) f rfl rfl rfl (by simp only [brennstoff] at hf; omega)

theorem parseLet_nach (x : String) (nach : List Token) (f : Nat)
    (h1 : ∀ ts, nach ≠ .zeichen "@" :: ts)
    (h2 : ∀ s t ts, nach = .wort s :: t :: .zeichen "(" :: ts → strEq s "alloc" = false) :
    parseLet (f + 1) (.ident x :: .zeichen "=" :: nach) = parseLetExpr f false x none nach := by
  simp [parseLet, nimmName, nameText, fordereZeichen, bind, Except.bind, pure, Except.pure]
  split
  · rename_i tl
    exact absurd rfl (h1 tl)
  · rename_i s t tl
    have hs := h2 s t tl rfl
    simp [hs]
  · rfl

/-- `let x = e ;` reads as an expression `let`, whatever the head of `e` (`@` and `alloc` stay off it). -/
theorem parseLet_ausdruck (x : String) (e : SExpr) (hg : gut e = true) (r : List Token) (f : Nat) :
    parseLet (f + 1) (.ident x :: .zeichen "=" :: (druckToks e ++ .zeichen ";" :: r)) =
      parseLetExpr f false x none (druckToks e ++ .zeichen ";" :: r) := by
  obtain ⟨t, ts, hk, hkg⟩ := druck_kopf e hg
  apply parseLet_nach
  · rw [hk]
    intro us hc
    injection hc with ht _
    subst ht
    simp only [KopfGut] at hkg
    rcases hkg with h | h | h | h | h <;> exact absurd h (by decide)
  · intro s t2 ts2 hc
    rw [hk] at hc
    injection hc with ht _
    subst ht
    simp only [KopfGut] at hkg
    cases h : strEq s "alloc"
    · rfl
    · exact absurd ((strEq_eq _ _).mp h) hkg

theorem parseLetExpr_aus (x : String) (e : SExpr) (hg : gutPrim e = true) (r : List Token) (f : Nat)
    (hf : brennstoff e ≤ f) :
    parseLetExpr (f + 1) false x none (druckToks e ++ .zeichen ";" :: r) = .ok (.bind false x none e, r) := by
  simp [parseLetExpr, or_vor_semi e hg r f hf, fordereZeichen, bind, Except.bind, pure, Except.pure]

/-- **One simple statement reads back as itself.** -/
theorem parseStmt_einfach (s : SAnw) (hs : Einfach s) (r : List Token) (F : Nat) (hF : fuelAnw s + 1 ≤ F) :
    parseStmt F (druckAnw s ++ r) = .ok (s, r) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases hs with
  | retLeer =>
    simp only [druckAnw, List.cons_append, List.nil_append]
    rw [parseStmt_ret_eq _ _ (by simp [istOrtsFort])]
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by simp [fuelAnw] at hF; omega⟩
    exact parseRueck_leer F'' r
  | ret e hg =>
    obtain ⟨t, ts, hk, hkg⟩ := druck_kopf e (gut_of_gutPrim e hg)
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    have hso : istOrtsFort (druckToks e ++ .zeichen ";" :: r) = false := by
      rw [hk]; exact kopf_nicht_ortsfort t hkg _
    rw [parseStmt_ret_eq _ _ hso]
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by simp [fuelAnw] at hF; omega⟩
    have hne : ∀ ts', druckToks e ++ .zeichen ";" :: r ≠ .zeichen ";" :: ts' := by
      rw [hk]; exact kopf_nicht_semi t hkg _
    exact parseRueck_aus _ _ e r hne (or_vor_semi e hg r F'' (by simp [fuelAnw] at hF; omega))
  | leave l =>
    simp only [druckAnw, List.cons_append, List.nil_append]
    rw [parseStmt_leave_eq _ _ (by simp [istOrtsFort])]
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by simp [fuelAnw] at hF; omega⟩
    simp [parseVerlasse, nimmName, nameText, fordereZeichen, bind, Except.bind, pure, Except.pure]
  | next l =>
    simp only [druckAnw, List.cons_append, List.nil_append]
    rw [parseStmt_next_eq _ _ (by simp [istOrtsFort])]
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by simp [fuelAnw] at hF; omega⟩
    simp [parseWeiter, nimmName, nameText, fordereZeichen, bind, Except.bind, pure, Except.pure]
  | bind x e hg =>
    simp only [druckAnw, druckTypOpt, Bool.false_eq_true, if_false, List.cons_append, List.nil_append,
      List.append_assoc, List.singleton_append]
    rw [parseStmt_let_eq _ _ (by simp [istOrtsFort])]
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by simp [fuelAnw] at hF; omega⟩
    rw [parseLet_ausdruck x e (gut_of_gutPrim e hg) r F'']
    obtain ⟨F3, rfl⟩ : ∃ F3, F'' = F3 + 1 := ⟨F'' - 1, by simp [fuelAnw] at hF; omega⟩
    exact parseLetExpr_aus x e hg r F3 (by simp [fuelAnw] at hF; omega)

end Gabbro.Grammatik.Parser
