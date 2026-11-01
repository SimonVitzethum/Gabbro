/-
  File:      Grammatik/Parser/Round/RundlaufItem.lean
  Subject:   Layer L2c, the item pieces: each item form the item printer prints (`druckItem`,
             Print/Item.lean) reads back through `parseItemTief` -- `item_use`, `item_const`,
             `item_static`, `item_fn`, `item_proto`, `item_why`, `item_conc`, `item_mod`, `item_atom`,
             `item_lock`, `item_table`, `item_entry` -- with the readers of their parts (constant
             values, effects, clauses, parameters, paths, table fields and parts, register bindings).

  The printability class `ItemGut`, the induction over it and the composition with the lexer are in
  `RundlaufProgramm`; devices are in `RundlaufGeraet`.
-/
module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil5

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ### Name tokens -/

/-- A printed name is its word or its identifier. -/
theorem nameTok_cases (n : String) : nameTok n = .wort n ∨ nameTok n = .ident n := by
  unfold nameTok; split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem strEq_ne {a b : String} (h : a ≠ b) : strEq a b = false := by
  cases e : strEq a b
  · rfl
  · exact absurd ((strEq_eq _ _).mp e) h

/-! ### Dispatch -/

theorem parseItemTief_wort (f : Nat) (w : String) (rest : List Token) (h1 : w ≠ "when") (h2 : w ≠ "pub") :
    parseItemTief (f + 1) (.wort w :: rest) = parseItemKopfTief f (.wort w :: rest) := by
  have e1 : strEq w "when" = false := by
    cases h : strEq w "when"
    · rfl
    · exact absurd ((strEq_eq _ _).mp h) h1
  have e2 : strEq w "pub" = false := by
    cases h : strEq w "pub"
    · rfl
    · exact absurd ((strEq_eq _ _).mp h) h2
  simp only [parseItemTief, e1, Bool.false_eq_true, ↓reduceIte, e2]

theorem parseItemKopf_module (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "module" :: rest) = parseModulTief f (.wort "module" :: rest) := by
  have hm : istMod "module" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "module" "module" = true)]

theorem parseItemKopf_use (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "use" :: rest) = parseUseTief (.wort "use" :: rest) := by
  have hm : istMod "use" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "use" "module" = false), (by decide : strEq "use" "use" = true)]

theorem parseItemKopf_translator (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "translator" :: rest) = parseTranslatorTief f (.wort "translator" :: rest) := by
  have hm : istMod "translator" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "translator" "module" = false), (by decide : strEq "translator" "use" = false), (by decide : strEq "translator" "fn" = false), (by decide : strEq "translator" "translator" = true)]

theorem parseItemKopf_concurrent (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "concurrent" :: rest) = parseNebenTief f (.wort "concurrent" :: rest) := by
  have hm : istMod "concurrent" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "concurrent" "module" = false), (by decide : strEq "concurrent" "use" = false), (by decide : strEq "concurrent" "fn" = false), (by decide : strEq "concurrent" "translator" = false), (by decide : strEq "concurrent" "profile" = false), (by decide : strEq "concurrent" "requires" = false), (by decide : strEq "concurrent" "concurrent" = true)]

theorem parseItemKopf_static (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "static" :: rest) = parseGlobTief f (.wort "static" :: rest) := by
  have hm : istMod "static" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "static" "module" = false), (by decide : strEq "static" "use" = false), (by decide : strEq "static" "fn" = false), (by decide : strEq "static" "translator" = false), (by decide : strEq "static" "profile" = false), (by decide : strEq "static" "requires" = false), (by decide : strEq "static" "concurrent" = false), (by decide : strEq "static" "type" = false), (by decide : strEq "static" "const" = false), (by decide : strEq "static" "static" = true)]

theorem parseItemKopf_format (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "format" :: rest) = parseFormatTief f (.wort "format" :: rest) := by
  have hm : istMod "format" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "format" "module" = false), (by decide : strEq "format" "use" = false), (by decide : strEq "format" "fn" = false), (by decide : strEq "format" "translator" = false), (by decide : strEq "format" "profile" = false), (by decide : strEq "format" "requires" = false), (by decide : strEq "format" "concurrent" = false), (by decide : strEq "format" "type" = false), (by decide : strEq "format" "const" = false), (by decide : strEq "format" "static" = false), (by decide : strEq "format" "format" = true)]

theorem parseItemKopf_table (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "table" :: rest) = parseTabellenTief f (.wort "table" :: rest) := by
  have hm : istMod "table" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "table" "module" = false), (by decide : strEq "table" "use" = false), (by decide : strEq "table" "fn" = false), (by decide : strEq "table" "translator" = false), (by decide : strEq "table" "profile" = false), (by decide : strEq "table" "requires" = false), (by decide : strEq "table" "concurrent" = false), (by decide : strEq "table" "type" = false), (by decide : strEq "table" "const" = false), (by decide : strEq "table" "static" = false), (by decide : strEq "table" "format" = false), (by decide : strEq "table" "table" = true)]

theorem parseItemKopf_reason (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "reason" :: rest) = parseGrundTief f (.wort "reason" :: rest) := by
  have hm : istMod "reason" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "reason" "module" = false), (by decide : strEq "reason" "use" = false), (by decide : strEq "reason" "fn" = false), (by decide : strEq "reason" "translator" = false), (by decide : strEq "reason" "profile" = false), (by decide : strEq "reason" "requires" = false), (by decide : strEq "reason" "concurrent" = false), (by decide : strEq "reason" "type" = false), (by decide : strEq "reason" "const" = false), (by decide : strEq "reason" "static" = false), (by decide : strEq "reason" "format" = false), (by decide : strEq "reason" "table" = false), (by decide : strEq "reason" "arena" = false), (by decide : strEq "reason" "reason" = true)]

theorem parseItemKopf_device (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "device" :: rest) = parseGeraetTief f (.wort "device" :: rest) := by
  have hm : istMod "device" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "device" "module" = false), (by decide : strEq "device" "use" = false), (by decide : strEq "device" "fn" = false), (by decide : strEq "device" "translator" = false), (by decide : strEq "device" "profile" = false), (by decide : strEq "device" "requires" = false), (by decide : strEq "device" "concurrent" = false), (by decide : strEq "device" "type" = false), (by decide : strEq "device" "const" = false), (by decide : strEq "device" "static" = false), (by decide : strEq "device" "format" = false), (by decide : strEq "device" "table" = false), (by decide : strEq "device" "arena" = false), (by decide : strEq "device" "reason" = false), (by decide : strEq "device" "state" = false), (by decide : strEq "device" "device" = true)]

theorem parseItemKopf_atomic (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "atomic" :: rest) = parseAtomarTief f (.wort "atomic" :: rest) := by
  have hm : istMod "atomic" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "atomic" "module" = false), (by decide : strEq "atomic" "use" = false), (by decide : strEq "atomic" "fn" = false), (by decide : strEq "atomic" "translator" = false), (by decide : strEq "atomic" "profile" = false), (by decide : strEq "atomic" "requires" = false), (by decide : strEq "atomic" "concurrent" = false), (by decide : strEq "atomic" "type" = false), (by decide : strEq "atomic" "const" = false), (by decide : strEq "atomic" "static" = false), (by decide : strEq "atomic" "format" = false), (by decide : strEq "atomic" "table" = false), (by decide : strEq "atomic" "arena" = false), (by decide : strEq "atomic" "reason" = false), (by decide : strEq "atomic" "state" = false), (by decide : strEq "atomic" "device" = false), (by decide : strEq "atomic" "assume" = false), (by decide : strEq "atomic" "axiom" = false), (by decide : strEq "atomic" "check" = false), (by decide : strEq "atomic" "atomic" = true)]

theorem parseItemKopf_lock (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "lock" :: rest) = parseSperreTief f (.wort "lock" :: rest) := by
  have hm : istMod "lock" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "lock" "module" = false), (by decide : strEq "lock" "use" = false), (by decide : strEq "lock" "fn" = false), (by decide : strEq "lock" "translator" = false), (by decide : strEq "lock" "profile" = false), (by decide : strEq "lock" "requires" = false), (by decide : strEq "lock" "concurrent" = false), (by decide : strEq "lock" "type" = false), (by decide : strEq "lock" "const" = false), (by decide : strEq "lock" "static" = false), (by decide : strEq "lock" "format" = false), (by decide : strEq "lock" "table" = false), (by decide : strEq "lock" "arena" = false), (by decide : strEq "lock" "reason" = false), (by decide : strEq "lock" "state" = false), (by decide : strEq "lock" "device" = false), (by decide : strEq "lock" "assume" = false), (by decide : strEq "lock" "axiom" = false), (by decide : strEq "lock" "check" = false), (by decide : strEq "lock" "atomic" = false), (by decide : strEq "lock" "lock" = true)]

theorem parseItemKopf_group (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "group" :: rest) = parseGruppeTief f (.wort "group" :: rest) := by
  have hm : istMod "group" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "group" "module" = false), (by decide : strEq "group" "use" = false), (by decide : strEq "group" "fn" = false), (by decide : strEq "group" "translator" = false), (by decide : strEq "group" "profile" = false), (by decide : strEq "group" "requires" = false), (by decide : strEq "group" "concurrent" = false), (by decide : strEq "group" "type" = false), (by decide : strEq "group" "const" = false), (by decide : strEq "group" "static" = false), (by decide : strEq "group" "format" = false), (by decide : strEq "group" "table" = false), (by decide : strEq "group" "arena" = false), (by decide : strEq "group" "reason" = false), (by decide : strEq "group" "state" = false), (by decide : strEq "group" "device" = false), (by decide : strEq "group" "assume" = false), (by decide : strEq "group" "axiom" = false), (by decide : strEq "group" "check" = false), (by decide : strEq "group" "atomic" = false), (by decide : strEq "group" "lock" = false), (by decide : strEq "group" "rcu" = false), (by decide : strEq "group" "group" = true)]

theorem parseItemKopf_entry (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "entry" :: rest) = parseEingangTief f (.wort "entry" :: rest) := by
  have hm : istMod "entry" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "entry" "module" = false), (by decide : strEq "entry" "use" = false), (by decide : strEq "entry" "fn" = false), (by decide : strEq "entry" "translator" = false), (by decide : strEq "entry" "profile" = false), (by decide : strEq "entry" "requires" = false), (by decide : strEq "entry" "concurrent" = false), (by decide : strEq "entry" "type" = false), (by decide : strEq "entry" "const" = false), (by decide : strEq "entry" "static" = false), (by decide : strEq "entry" "format" = false), (by decide : strEq "entry" "table" = false), (by decide : strEq "entry" "arena" = false), (by decide : strEq "entry" "reason" = false), (by decide : strEq "entry" "state" = false), (by decide : strEq "entry" "device" = false), (by decide : strEq "entry" "assume" = false), (by decide : strEq "entry" "axiom" = false), (by decide : strEq "entry" "check" = false), (by decide : strEq "entry" "atomic" = false), (by decide : strEq "entry" "lock" = false), (by decide : strEq "entry" "rcu" = false), (by decide : strEq "entry" "group" = false), (by decide : strEq "entry" "accumulates" = false), (by decide : strEq "entry" "walk" = false), (by decide : strEq "entry" "entry" = true)]

theorem parseItemKopf_fn (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "fn" :: rest) = match parseFnSig f "" (.wort "fn" :: rest) with
      | .error e => .error e
      | .ok (sig, r) => parseFnRest f sig r := by
  have hm : istMod "fn" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "fn" "module" = false), (by decide : strEq "fn" "use" = false),
    (by decide : strEq "fn" "fn" = true), letzteArt]
  rfl

theorem parseItemKopf_art (f : Nat) (art : String) (rest : List Token) (h : istMod art = true) :
    parseItemKopfTief (f + 1) (.wort art :: .wort "fn" :: rest) =
      match parseFnSig f art (.wort "fn" :: rest) with
      | .error e => .error e
      | .ok (sig, r) => parseFnRest f sig r := by
  have hm : istMod "fn" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, h, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "fn" "module" = false), (by decide : strEq "fn" "use" = false),
    (by decide : strEq "fn" "fn" = true), letzteArt]
  rfl

theorem parseItemKopf_constfn (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "const" :: .wort "fn" :: rest) =
      match parseFnSig f "const" (.wort "fn" :: rest) with
      | .error e => .error e
      | .ok (sig, r) => parseFnRest f sig r := by
  have hm : istMod "const" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "const" "module" = false), (by decide : strEq "const" "use" = false),
    (by decide : strEq "const" "fn" = false), (by decide : strEq "const" "translator" = false),
    (by decide : strEq "const" "profile" = false), (by decide : strEq "const" "requires" = false),
    (by decide : strEq "const" "concurrent" = false), (by decide : strEq "const" "type" = false),
    (by decide : strEq "const" "const" = true), (by decide : strEq "fn" "fn" = true)]
  rfl

theorem parseItemKopf_const (f : Nat) (n : String) (hn : n ≠ "fn") (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "const" :: nameTok n :: rest) =
      parseKonstNach f (nameTok n :: rest) := by
  have hm : istMod "const" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "const" "module" = false), (by decide : strEq "const" "use" = false),
    (by decide : strEq "const" "fn" = false), (by decide : strEq "const" "translator" = false),
    (by decide : strEq "const" "profile" = false), (by decide : strEq "const" "requires" = false),
    (by decide : strEq "const" "concurrent" = false), (by decide : strEq "const" "type" = false),
    (by decide : strEq "const" "const" = true), nimmWort, strEq_self]
  rcases nameTok_cases n with h | h <;> rw [h] <;> simp only [strEq_ne hn, Bool.false_eq_true, ↓reduceIte]

/-! ### Paths, constant values -/

theorem nimmPfad_pfad (p : List String) (R : List Token) (hp : p ≠ []) (hR : ∀ r, R ≠ .zeichen "::" :: r) :
    nimmPfad (pfadToks p ++ R) = .ok (p, R) := by
  match p, hp with
  | [a], _ => simp only [nimmPfad, pfadToks, List.cons_append, List.nil_append, nameText_nameTok, sammleSeg_stop2 [a] R hR]
  | a :: b :: cs, _ =>
    have := sammleSeg_pfad (b :: cs) [a] R (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hR
    simp only [pfadToks, List.cons_append, List.nil_append, List.singleton_append] at this ⊢
    simp only [nimmPfad, nameText_nameTok, this]

/-- A printable constant value: an expression, or an array literal of printable values. -/
inductive KonstGut : SKonstWert → Prop
  | one (e : SExpr) : gut e = true → KonstGut (.one e)
  | rows (xs : List SKonstWert) : (∀ x ∈ xs, KonstGut x) → KonstGut (.rows xs)

def fbK (v : SKonstWert) : Nat := 8 * (druckKonstWert v).length + 40

theorem druckKonstWerte_cons (x : SKonstWert) (xs : List SKonstWert) (h : xs ≠ []) :
    druckKonstWert.druckKonstWerte (x :: xs) =
      druckKonstWert x ++ .zeichen "," :: druckKonstWert.druckKonstWerte xs := by
  match xs, h with
  | y :: ys, _ => simp only [druckKonstWert.druckKonstWerte, List.append_assoc, List.cons_append, List.nil_append]

theorem konst_kopf (v : SKonstWert) (hv : KonstGut v) :
    ∃ t ts, druckKonstWert v = t :: ts ∧ t ≠ .zeichen "]" ∧ t ≠ .zeichen "}" := by
  cases hv with
  | one e he =>
    obtain ⟨t, ts, hd, hk⟩ := druck_kopf e he
    refine ⟨t, ts, by simp only [druckKonstWert, hd], ?_, ?_⟩ <;> intro e' <;> subst e' <;> simp only [KopfGut, String.reduceEq, or_self] at hk
  | rows xs _ => exact ⟨.zeichen "[", _, by simp only [druckKonstWert, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl, by simp only [ne_eq, Token.zeichen.injEq, String.reduceEq, not_false_eq_true], by simp only [ne_eq, Token.zeichen.injEq, String.reduceEq, not_false_eq_true]⟩

theorem konst_len (v : SKonstWert) (hv : KonstGut v) : 1 ≤ (druckKonstWert v).length := by
  obtain ⟨t, ts, hd, -⟩ := konst_kopf v hv
  rw [hd]; simp only [List.length_cons, Nat.le_add_left]

/-- Constant values and their rows read back before a benign follow. -/
theorem konst_rund : ∀ (v : SKonstWert), KonstGut v → ∀ (R : List Token) (F : Nat),
    ruhig R = true → ruhigSuff R = true → ruhigGleit R = true → fbK v ≤ F →
    parseKonstWert F (druckKonstWert v ++ R) = .ok (v, R) := by
  intro v hv
  induction hv with
  | one e he =>
    intro R F h1 h2 h3 hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbK] at hF; omega⟩
    obtain ⟨t, ts, hd, hk⟩ := druck_kopf e he
    have hO := ausdruck e he R F' h1 h2 h3 (by simp only [fbK, druckKonstWert] at hF; omega)
    have hnb : ∀ r, druckToks e ++ R ≠ .zeichen "[" :: r := by
      rw [hd]; intro r e'; injection e' with e1; subst e1
      simp only [KopfGut, String.reduceEq, or_self] at hk
    simp only [druckKonstWert]
    rw [parseKonstWert.eq_def]
    simp only [hnb]
    simp only [bind, Except.bind, hO, pure, Except.pure]
  | rows xs hxs ih =>
    intro R F h1 h2 h3 hF
    have hrows : ∀ (ys : List SKonstWert), (∀ y ∈ ys, y ∈ xs) → ∀ (G : Nat),
        8 * (druckKonstWert.druckKonstWerte ys).length + 41 ≤ G →
        parseConstRows G (druckKonstWert.druckKonstWerte ys ++ .zeichen "]" :: R) = .ok (ys, R) := by
      intro ys
      induction ys with
      | nil =>
        intro _ G hG
        obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
        simp only [parseConstRows, druckKonstWert.druckKonstWerte, List.nil_append]
      | cons y ys ihy =>
        intro hsub G hG
        have hyx := hsub y (by simp only [List.mem_cons, true_or])
        have hy := hxs y hyx
        obtain ⟨t, ts, hd, ht1, -⟩ := konst_kopf y hy
        obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
        cases ys with
        | nil =>
          simp only [druckKonstWert.druckKonstWerte] at hG ⊢
          have hV := ih y hyx (.zeichen "]" :: R) G' rfl rfl rfl (by simp only [fbK]; omega)
          have hne : ∀ r, druckKonstWert y ++ .zeichen "]" :: R ≠ .zeichen "]" :: r := by
            rw [hd]; intro r e; injection e with e; exact ht1 e
          rw [parseConstRows.eq_def]
          simp only [hne]
          simp only [bind, Except.bind, hV, pure, Except.pure]
        | cons z zs =>
          rw [druckKonstWerte_cons y (z :: zs) (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])] at hG ⊢
          simp only [List.length_append, List.length_cons] at hG
          have hV := ih y hyx (.zeichen "," :: (druckKonstWert.druckKonstWerte (z :: zs) ++ .zeichen "]" :: R))
            G' rfl rfl rfl (by simp only [fbK]; omega)
          have hR := ihy (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) G' (by omega)
          have hne : ∀ r, druckKonstWert y ++ .zeichen "," :: (druckKonstWert.druckKonstWerte (z :: zs) ++
              .zeichen "]" :: R) ≠ .zeichen "]" :: r := by
            rw [hd]; intro r e; injection e with e; exact ht1 e
          simp only [List.append_assoc, List.cons_append]
          rw [parseConstRows.eq_def]
          simp only [hne]
          simp only [bind, Except.bind, hV, hR, pure, Except.pure]
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbK] at hF; omega⟩
    have hH := hrows xs (fun x hx => hx) F' (by simp only [fbK, druckKonstWert] at hF; simp only [List.cons_append, List.nil_append, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceLeDiff] at hF; omega)
    simp only [druckKonstWert, List.cons_append, List.append_assoc, List.singleton_append]
    simp only [parseKonstWert, List.nil_append, bind, Except.bind, hH, pure, Except.pure]

/-! ### Effects -/

/-- A printable effect arm. -/
def EffGut : SEffekt → Prop
  | .reads p => gut p = true
  | .writes p => gut p = true
  | .locks sh p => gut p = true ∧ (sh = false → ∀ ts, druckToks p ≠ .wort "shared" :: ts)
  | .takes p => gut p = true
  | .posts p => gut p = true
  | _ => True

/-- What follows an effect arm: `,` or `}`. -/
def EffFolge (R : List Token) : Prop := (∃ r, R = .zeichen "," :: r) ∨ (∃ r, R = .zeichen "}" :: r)

theorem effFolge_ruhig (R : List Token) (h : EffFolge R) :
    ruhig R = true ∧ ruhigSuff R = true ∧ ruhigGleit R = true := by
  rcases h with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩

theorem effekt_rund (e : SEffekt) (he : EffGut e) (R : List Token) (hR : EffFolge R) (F : Nat)
    (hF : 6 * (druckEffekt e).length + 36 ≤ F) :
    parseEffekt F (druckEffekt e ++ R) = .ok (e, R) := by
  obtain ⟨h1, h2, h3⟩ := effFolge_ruhig R hR
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases e with
  | reads p =>
    simp only [druckEffekt, List.length_append, List.length_singleton] at hF ⊢
    have hO := ausdruck p he R F' h1 h2 h3 (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseEffekt, (by decide : strEq "reads" "reads" = true), ite_true, List.nil_append, hO]
  | writes p =>
    simp only [druckEffekt, List.length_append, List.length_singleton] at hF ⊢
    have hO := ausdruck p he R F' h1 h2 h3 (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseEffekt, (by decide : strEq "writes" "reads" = false), (by decide : strEq "writes" "writes" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hO]
  | locks sh p =>
    obtain ⟨he, hsh⟩ := he
    have hO := ausdruck p he R F' h1 h2 h3 (by
      simp only [druckEffekt, List.length_append, List.length_singleton] at hF; split at hF <;> simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
    obtain ⟨t, ts, hd, hk⟩ := druck_kopf p he
    cases sh
    · simp only [druckEffekt, Bool.false_eq_true, ite_false, List.nil_append, List.singleton_append,
        List.cons_append]
      rw [hd] at hO ⊢
      simp only [List.cons_append] at hO ⊢
      cases t with
      | wort w =>
        have hw : strEq w "shared" = false := by
          cases h : strEq w "shared"
          · rfl
          · have := (strEq_eq _ _).mp h; subst this
            exact absurd hd (hsh rfl _)
        simp only [parseEffekt, (by decide : strEq "locks" "reads" = false), (by decide : strEq "locks" "writes" = false), (by decide : strEq "locks" "locks" = true), Bool.false_eq_true, ite_false, ite_true, hw, hO]
      | _ => simp only [parseEffekt, (by decide : strEq "locks" "reads" = false), (by decide : strEq "locks" "writes" = false), (by decide : strEq "locks" "locks" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hO]
    · simp only [druckEffekt, ite_true, List.singleton_append, List.cons_append, List.append_assoc,
        List.nil_append]
      simp only [parseEffekt, (by decide : strEq "locks" "reads" = false), (by decide : strEq "locks" "writes" = false), (by decide : strEq "locks" "locks" = true), Bool.false_eq_true, ite_false, ite_true,
        (by decide : strEq "shared" "shared" = true), hO]
  | masks n =>
    simp only [druckEffekt, List.cons_append, List.nil_append]
    simp only [parseEffekt, (by decide : strEq "masks" "reads" = false), (by decide : strEq "masks" "writes" = false), (by decide : strEq "masks" "locks" = false), (by decide : strEq "masks" "masks" = true), Bool.false_eq_true, ite_false, ite_true, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
  | allocs n =>
    simp only [druckEffekt, List.cons_append, List.nil_append]
    simp only [parseEffekt, (by decide : strEq "allocs" "reads" = false), (by decide : strEq "allocs" "writes" = false), (by decide : strEq "allocs" "locks" = false), (by decide : strEq "allocs" "masks" = false), (by decide : strEq "allocs" "allocs" = true), Bool.false_eq_true, ite_false, ite_true, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
  | takes p =>
    simp only [druckEffekt, List.length_append, List.length_singleton] at hF ⊢
    have hO := ausdruck p he R F' h1 h2 h3 (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseEffekt, (by decide : strEq "consumes" "reads" = false), (by decide : strEq "consumes" "writes" = false), (by decide : strEq "consumes" "locks" = false), (by decide : strEq "consumes" "masks" = false), (by decide : strEq "consumes" "allocs" = false), (by decide : strEq "consumes" "consumes" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hO]
  | posts p =>
    simp only [druckEffekt, List.length_append, List.length_singleton] at hF ⊢
    have hO := ausdruck p he R F' h1 h2 h3 (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseEffekt, (by decide : strEq "publishes" "reads" = false), (by decide : strEq "publishes" "writes" = false), (by decide : strEq "publishes" "locks" = false), (by decide : strEq "publishes" "masks" = false), (by decide : strEq "publishes" "allocs" = false), (by decide : strEq "publishes" "consumes" = false), (by decide : strEq "publishes" "publishes" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hO]
  | loops =>
    simp only [druckEffekt, List.cons_append, List.nil_append]
    simp only [parseEffekt, (by decide : strEq "diverges" "reads" = false), (by decide : strEq "diverges" "writes" = false), (by decide : strEq "diverges" "locks" = false), (by decide : strEq "diverges" "masks" = false), (by decide : strEq "diverges" "allocs" = false), (by decide : strEq "diverges" "consumes" = false), (by decide : strEq "diverges" "publishes" = false), (by decide : strEq "diverges" "diverges" = true), Bool.false_eq_true, ite_false, ite_true]
  | pure =>
    simp only [druckEffekt, List.cons_append, List.nil_append]
    simp only [parseEffekt, (by decide : strEq "pure" "reads" = false), (by decide : strEq "pure" "writes" = false), (by decide : strEq "pure" "locks" = false), (by decide : strEq "pure" "masks" = false), (by decide : strEq "pure" "allocs" = false), (by decide : strEq "pure" "consumes" = false), (by decide : strEq "pure" "publishes" = false), (by decide : strEq "pure" "diverges" = false), (by decide : strEq "pure" "pure" = true), Bool.false_eq_true, ite_false, ite_true]

theorem effekte_rund : ∀ (es : List SEffekt) (R : List Token) (F : Nat), es ≠ [] → (∀ e ∈ es, EffGut e) →
    8 * (druckEffekte es).length + 41 ≤ F →
    parseEffektListe F (druckEffekte es ++ .zeichen "}" :: R) = .ok (es, .zeichen "}" :: R) := by
  intro es
  induction es with
  | nil => intro _ _ h; exact absurd rfl h
  | cons e es ih =>
    intro R F _ hg hF
    have he := hg e (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases es with
    | nil =>
      simp only [druckEffekte] at hF ⊢
      have hE := effekt_rund e he (.zeichen "}" :: R) (Or.inr ⟨R, rfl⟩) F' (by omega)
      simp only [parseEffektListe, hE, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]
    | cons e2 es2 =>
      have hd : druckEffekte (e :: e2 :: es2) = druckEffekt e ++ .zeichen "," :: druckEffekte (e2 :: es2) := by
        simp only [druckEffekte, List.append_assoc, List.cons_append, List.nil_append]
      rw [hd] at hF ⊢
      simp only [List.length_append, List.length_cons] at hF
      have hE := effekt_rund e he (.zeichen "," :: (druckEffekte (e2 :: es2) ++ .zeichen "}" :: R))
        (Or.inl ⟨_, rfl⟩) F' (by omega)
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
      have hk : istZeichenZ "}" (druckEffekte (e2 :: es2) ++ .zeichen "}" :: R) = false := by
        cases e2 <;> cases es2 <;> simp only [istZeichenZ, druckEffekte, druckEffekt, List.cons_append, List.nil_append, List.append_assoc] <;> (try split) <;> rfl
      simp only [List.append_assoc, List.cons_append] at hE ⊢
      simp only [parseEffektListe, hE, hk, Bool.false_eq_true, ite_false, hR]

theorem namen_rund : ∀ (ns : List String) (R : List Token) (F : Nat), ns ≠ [] →
    (∀ r, R ≠ .zeichen "," :: r) → ns.length ≤ F →
    parseNamenListe F (druckNamen ns ++ R) = .ok (ns, R) := by
  intro ns
  induction ns with
  | nil => intro _ _ h; exact absurd rfl h
  | cons n ns ih =>
    intro R F _ hR hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    cases ns with
    | nil =>
      simp only [druckNamen, List.cons_append, List.nil_append]
      simp only [parseNamenListe, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende, hR]
    | cons m ms =>
      have hq := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hR (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      have hlook : ∃ v, nimmName (druckNamen (m :: ms) ++ R) = .ok v := by
        cases ms <;> simp only [nimmName, druckNamen, List.cons_append, List.nil_append, nameText_nameTok, Except.ok.injEq, exists_eq']
      obtain ⟨v, hv⟩ := hlook
      have hd : druckNamen (n :: m :: ms) ++ R = nameTok n :: .zeichen "," :: (druckNamen (m :: ms) ++ R) := by
        simp only [druckNamen, List.cons_append, List.nil_append]
      rw [hd]
      have h0 : nimmName (nameTok n :: .zeichen "," :: (druckNamen (m :: ms) ++ R)) =
          .ok (n, .zeichen "," :: (druckNamen (m :: ms) ++ R)) := by simp only [nimmName, nameText_nameTok]
      simp only [parseNamenListe, h0, hv, hq]

/-! ### Clauses -/

/-- The printable clauses (`by`, `retires`, `deadline` ride as reconstructed text: excluded). -/
def KlauselGut : SKlausel → Prop
  | .needs p => PredGut p
  | .gives p => PredGut p
  | .keeps ns => ns ≠ []
  | .refs p => p ≠ []
  | .cost e => gut e = true
  | .drops e => gut e = true
  | .load p => p ≠ []
  | .part _ => True
  | .arch _ => True
  | .moves _ _ => True
  | .effs es => ∀ e ∈ es, EffGut e
  | _ => False

/-- What follows a clause: the next clause word, or the body (`{`, `;`). -/
def KlauselFolge (R : List Token) : Prop :=
  (∃ r, R = .zeichen "{" :: r) ∨ (∃ r, R = .zeichen ";" :: r) ∨
    (∃ w r, R = .wort w :: r ∧ istKlauselKopf w = true)

theorem klauselFolge_pred (R : List Token) (h : KlauselFolge R) :
    PredFolge R ∧ (∀ r, R ≠ .zeichen "," :: r) ∧ (∀ r, R ≠ .zeichen "::" :: r) := by
  rcases h with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨w, r, rfl, hw⟩
  · exact ⟨⟨rfl, rfl, rfl, (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩,
      (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)⟩
  · exact ⟨⟨rfl, rfl, rfl, (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩,
      (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)⟩
  · have hr : w ≠ "rounded" := by intro e; subst e; exact absurd hw (by decide)
    have hi : w ≠ "in" := by intro e; subst e; exact absurd hw (by decide)
    have hre : w ≠ "reaches" := by intro e; subst e; exact absurd hw (by decide)
    have hrs : strEq w "rounded" = false := by
      cases h : strEq w "rounded"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) hr
    refine ⟨⟨rfl, rfl, by simp only [ruhigGleit, hrs, Bool.not_false], (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), ?_, ?_⟩,
      (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩
    · intro x e; simp only [List.cons.injEq, Token.wort.injEq] at e; exact hi e.1
    · intro x e; simp only [List.cons.injEq, Token.wort.injEq] at e; exact hre e.1

end Gabbro.Grammatik.Parser
