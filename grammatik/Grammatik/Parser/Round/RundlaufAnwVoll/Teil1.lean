module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil1a

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000
theorem fbA_ge (s : SAnw) (F : Nat) (h : fbA s ≤ F) : ∃ F', F = F' + 1 :=
  ⟨F - 1, by simp only [fbA] at h; omega⟩

theorem anw_leave (l : String) : AnwBein (.leave l) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  simp only [druckAnw, List.cons_append, List.nil_append]
  rw [parseStmt_leave _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  simp only [parseVerlasse, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte]

theorem anw_next (l : String) : AnwBein (.next l) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  simp only [druckAnw, List.cons_append, List.nil_append]
  rw [parseStmt_next _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  simp only [parseWeiter, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte]

theorem anw_step (a b : String) : AnwBein (.step a b) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  simp only [druckAnw, List.cons_append, List.nil_append]
  rw [parseStmt_advances _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  simp only [parseSchreitet, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte]

theorem anw_ret_leer : AnwBein (.ret none) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  simp only [druckAnw, List.cons_append, List.nil_append]
  rw [parseStmt_return _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  exact parseRueck_leer F' rest

theorem anw_ret (e : SExpr) (hg : gut e = true) : AnwBein (.ret (some e)) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_cons, List.length_nil, List.length_append,
    List.length_singleton] at hF
  obtain ⟨t, ts, hk, hkg⟩ := druck_kopf e hg
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
  have hso : istOrtsFort (druckToks e ++ .zeichen ";" :: rest) = false := by
    rw [hk]; exact kopf_nicht_ortsfort t hkg _
  rw [parseStmt_return _ _ hso]
  have hne : ∀ ts', druckToks e ++ .zeichen ";" :: rest ≠ .zeichen ";" :: ts' := by
    rw [hk]; exact kopf_nicht_semi t hkg _
  exact parseRueck_aus _ _ e rest hne (ausdruck e hg _ F' rfl rfl rfl (by omega))

/-! ### `let` -/

/-- What `parseLet` does behind the `=`. -/
def parseLetNach (f : Nat) (m : Bool) (name : String) (ty : Option STyp) (nach : List Token) :
    Except String (SAnw × List Token) :=
  match nach with
  | .zeichen "@" :: _ => parseLetLib f m name ty nach
  | .wort s :: t :: .zeichen ";" :: rest =>
    if strEq s "alloc" then match nameText t with
      | some tisch => .ok (.allocVon m name ty tisch, rest)
      | none => parseLetExpr f m name ty nach
    else parseLetExpr f m name ty nach
  | .wort s :: t :: .zeichen "(" :: _ =>
    if strEq s "alloc" then match nameText t with
      | some _ => parseLetAlloc f m name ty nach
      | none => parseLetExpr f m name ty nach
    else parseLetExpr f m name ty nach
  | _ => parseLetExpr f m name ty nach

/-- The printable type of a `let`, when there is one. -/
def TypOptGut : Option STyp → Prop
  | none => True
  | some t => TypGut t

/-- The head of `let`: `mut`, the name, the type, the `=`. -/
theorem parseLet_kopf (f : Nat) (m : Bool) (x : String) (hx : x ≠ "mut") (ty : Option STyp)
    (nach : List Token) (hty : TypOptGut ty) (hf : ∀ t, ty = some t → fbT t ≤ f) :
    parseLet (f + 1) ((if m then [.wort "mut"] else []) ++ nameTok x ::
      (druckTypOpt ty ++ .zeichen "=" :: nach)) = parseLetNach f m x ty nach := by
  have hm : ∀ R, parseLet (f + 1) ((if false = true then [Token.wort "mut"] else []) ++ nameTok x :: R) =
      parseLet (f + 1) (.ident x :: R) := by
    intro R; simp only [Bool.false_eq_true, ite_false, List.nil_append]; exact parseLet_nameTok x hx R f
  cases ty with
  | none =>
    cases m <;> (try rw [hm]) <;> simp only [parseLet, nimmFrage, strEq_gleich_frage, strEq_doppelpunkt_frage, bind, Except.bind, nimmName, nameText_ident, druckTypOpt, List.nil_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen, strEq_self, ↓reduceIte, parseLetNach, Bool.false_eq_true, List.cons_append, nameText_nameTok] <;> rfl
  | some t =>
    have hT : parseTyp f (druckTyp t ++ .zeichen "=" :: nach) = .ok (t, .zeichen "=" :: nach) :=
      parse_druckTyp t hty _ f
        ⟨(by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
          (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩ (hf t rfl)
    cases m <;> (try rw [hm]) <;> simp only [parseLet, nimmFrage, strEq_gleich_frage, strEq_doppelpunkt_frage, bind, Except.bind, nimmName, nameText_ident, druckTypOpt, List.cons_append, List.nil_append, hT, pure, Except.pure, fordereZeichen, strEq_self, ↓reduceIte, parseLetNach, Token.zeichen.injEq, String.reduceEq, Bool.false_eq_true, nameText_nameTok] <;> rfl

/-- An expression right side: neither `@` nor `alloc t (` nor `alloc t ;`. -/
theorem parseLetNach_expr (f : Nat) (m : Bool) (x : String) (ty : Option STyp) (e : SExpr)
    (hg : gut e = true) (R : List Token) :
    parseLetNach f m x ty (druckToks e ++ R) = parseLetExpr f m x ty (druckToks e ++ R) := by
  obtain ⟨t, ts, hk, hkg⟩ := druck_kopf e hg
  rw [hk]
  unfold parseLetNach
  split
  · rename_i heq; simp only [List.cons_append, List.cons.injEq] at heq; obtain ⟨rfl, -⟩ := heq; simp only [KopfGut, String.reduceEq, or_self] at hkg
  · rename_i s t2 _ heq
    simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    simp only [KopfGut] at hkg
    have : strEq s "alloc" = false := by
      cases h : strEq s "alloc"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) hkg
    simp only [this, Bool.false_eq_true, ↓reduceIte, List.cons_append]
  · rename_i s t2 _ heq
    simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    simp only [KopfGut] at hkg
    have : strEq s "alloc" = false := by
      cases h : strEq s "alloc"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) hkg
    simp only [this, Bool.false_eq_true, ↓reduceIte, List.cons_append]
  · rfl

theorem fbT_of (ty : Option STyp) (t : STyp) (h : ty = some t) :
    (druckTypOpt ty).length = (druckTyp t).length + 1 := by
  subst h; simp only [druckTypOpt, List.cons_append, List.nil_append, List.length_cons, Nat.add_left_cancel_iff]

theorem anw_bind (m : Bool) (x : String) (hx : x ≠ "mut") (ty : Option STyp) (e : SExpr) (hty : TypOptGut ty)
    (hg : gut e = true) : AnwBein (.bind m x ty e) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_cons, List.length_nil, List.length_append,
    List.length_singleton] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckAnw (.bind m x ty e) ++ rest = .wort "let" :: ((if m then [.wort "mut"] else []) ++
      nameTok x :: (druckTypOpt ty ++ .zeichen "=" :: (druckToks e ++ .zeichen ";" :: rest))) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseStmt_let _ _ (by cases m <;> first | rfl | (simp only [Bool.false_eq_true, ite_false, List.nil_append]; exact ortsFort_nameTok _ _))]
  rw [show F' + 1 + 1 = (F' + 1) + 1 from rfl]
  rw [parseLet_kopf (F' + 1) m x hx ty _ hty (by
      intro t ht; have := fbT_of ty t ht; simp only [fbT]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega),
    parseLetNach_expr _ _ _ _ e hg]
  have hO := ausdruck e hg (.zeichen ";" :: rest) F' rfl rfl rfl (by split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
  simp only [parseLetExpr, strEq_semi_frage, Bool.false_eq_true, bind, Except.bind, hO, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]


/-! ### Statements headed by a place or a call -/

/-- The head words `parseStmt` opens a form with (unless a place continuation follows),
    `transition`, which `parsePlatzStmt` opens whatever follows, and `else`, which ends a statement
    list's follow (`KE`). -/
def anwWortTafel : List (List Char) :=
  ["else", "let", "if", "match", "traverse", "retry", "forever", "breaking", "narrow", "locks", "observes",
   "leave", "next", "return", "reset", "grow", "free", "child", "transition", "advances", "retires"].map
    String.toList

/-- A statement head word (see `anwWortTafel`). -/
def istAnwWort (s : String) : Bool := anwWortTafel.contains s.toList

theorem anwWort_strEq {a : String} (h : istAnwWort a = false) (w : String)
    (hw : istAnwWort w = true) : strEq a w = false := by
  cases hc : strEq a w
  · rfl
  · have := (strEq_eq _ _).mp hc; subst this; rw [h] at hw; exact absurd hw (by decide)

/-- A successfully read printed place retains its complete statement and follow.
    Indexed soft-keyword places keep that result even at the return-array prefix. -/
theorem parseStmt_ident (f : Nat) (a : String) (r : List Token)
    (h : ∀ r', r ≠ .zeichen "{" :: r')
    (hw : istOrtsFort r = true ∨ istAnwWort a = false) {result : SAnw × List Token}
    (placed : parsePlatzStmt f (nameTok a :: r) = .ok result) :
    parseStmt (f + 1) (nameTok a :: r) = .ok result := by
  by_cases keyword : istSchluessel a = true
  · simp only [nameTok, keyword, ↓reduceIte] at placed ⊢
    rw [parseStmt.eq_def]
    split
    · split <;> simp_all
    all_goals
      rcases hw with hw | hw
      · simp_all
      · have e := fun w (hw' : istAnwWort w = true) => anwWort_strEq hw w hw'
        simp_all [e "let" rfl, Bool.false_eq_true, ↓reduceIte, e "if" rfl,
          e "match" rfl, e "traverse" rfl, e "retry" rfl, e "forever" rfl,
          e "breaking" rfl, e "narrow" rfl, e "locks" rfl, e "observes" rfl,
          e "leave" rfl, e "next" rfl, e "return" rfl, e "reset" rfl,
          e "grow" rfl, e "free" rfl, e "child" rfl, e "transition" rfl,
          e "advances" rfl, e "retires" rfl, ite_self]
  · simp only [nameTok, keyword, ↓reduceIte] at placed ⊢
    rw [parseStmt.eq_def]
    simp only
    split <;> simp_all

theorem parsePlatzStmt_ident (f : Nat) (a : String) (r : List Token) (ht : a ≠ "transition") :
    parsePlatzStmt (f + 1) (nameTok a :: r) = parseKopfStmt f (nameTok a :: r) := by
  have : strEq a "transition" = false := by
    cases hc : strEq a "transition"
    · rfl
    · exact absurd ((strEq_eq _ _).mp hc) ht
  unfold nameTok; split <;> simp only [parsePlatzStmt, this, Bool.false_eq_true, ↓reduceIte]

/-- The assignment operators. -/
def istZuweis (o : String) : Bool :=
  strEq o "=" || strEq o "+=" || strEq o "-=" || strEq o "&=" || strEq o "|="

theorem zuweis_is (o : String) (h : istZuweis o = true) :
    o = "=" ∨ o = "+=" ∨ o = "-=" ∨ o = "&=" ∨ o = "|=" := by
  simp only [istZuweis, Bool.or_eq_true, strEq_eq] at h
  rcases h with (((h | h) | h) | h) | h <;> simp only [h, String.reduceEq, or_self, or_false, or_true]

end Gabbro.Grammatik.Parser
