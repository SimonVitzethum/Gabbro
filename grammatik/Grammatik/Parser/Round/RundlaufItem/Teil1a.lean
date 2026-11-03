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

private theorem itemGroupKopf_keinTag (w : String) (rest : List Token)
    (hs : w ≠ "spec") (hi : w ≠ "impl") :
    (match .wort w :: rest with
      | .wort "spec" :: .wort "fn" :: _ | .wort "impl" :: .wort "fn" :: _ => none
      | .wort "spec" :: r => some (true, r)
      | .wort "impl" :: r => some (false, r)
      | _ => none) = (none : Option (Bool × List Token)) := by
  split <;> simp_all

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
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "module" "module" = true)]

theorem parseItemKopf_use (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "use" :: rest) = parseUseTief (.wort "use" :: rest) := by
  have hm : istMod "use" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "use" "module" = false), (by decide : strEq "use" "use" = true)]

theorem parseItemKopf_translator (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "translator" :: rest) = parseTranslatorTief f (.wort "translator" :: rest) := by
  have hm : istMod "translator" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "translator" "module" = false), (by decide : strEq "translator" "use" = false), (by decide : strEq "translator" "fn" = false), (by decide : strEq "translator" "translator" = true)]

theorem parseItemKopf_concurrent (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "concurrent" :: rest) = parseNebenTief f (.wort "concurrent" :: rest) := by
  have hm : istMod "concurrent" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "concurrent" "module" = false), (by decide : strEq "concurrent" "use" = false), (by decide : strEq "concurrent" "fn" = false), (by decide : strEq "concurrent" "translator" = false), (by decide : strEq "concurrent" "profile" = false), (by decide : strEq "concurrent" "requires" = false), (by decide : strEq "concurrent" "concurrent" = true)]

theorem parseItemKopf_static (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "static" :: rest) = parseGlobTief f (.wort "static" :: rest) := by
  have hm : istMod "static" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "static" "module" = false), (by decide : strEq "static" "use" = false), (by decide : strEq "static" "fn" = false), (by decide : strEq "static" "translator" = false), (by decide : strEq "static" "profile" = false), (by decide : strEq "static" "requires" = false), (by decide : strEq "static" "concurrent" = false), (by decide : strEq "static" "type" = false), (by decide : strEq "static" "const" = false), (by decide : strEq "static" "static" = true)]

theorem parseItemKopf_format (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "format" :: rest) = parseFormatTief f (.wort "format" :: rest) := by
  have hm : istMod "format" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "format" "module" = false), (by decide : strEq "format" "use" = false), (by decide : strEq "format" "fn" = false), (by decide : strEq "format" "translator" = false), (by decide : strEq "format" "profile" = false), (by decide : strEq "format" "requires" = false), (by decide : strEq "format" "concurrent" = false), (by decide : strEq "format" "type" = false), (by decide : strEq "format" "const" = false), (by decide : strEq "format" "static" = false), (by decide : strEq "format" "format" = true)]

theorem parseItemKopf_table (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "table" :: rest) = parseTabellenTief f (.wort "table" :: rest) := by
  have hm : istMod "table" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "table" "module" = false), (by decide : strEq "table" "use" = false), (by decide : strEq "table" "fn" = false), (by decide : strEq "table" "translator" = false), (by decide : strEq "table" "profile" = false), (by decide : strEq "table" "requires" = false), (by decide : strEq "table" "concurrent" = false), (by decide : strEq "table" "type" = false), (by decide : strEq "table" "const" = false), (by decide : strEq "table" "static" = false), (by decide : strEq "table" "format" = false), (by decide : strEq "table" "table" = true)]

theorem parseItemKopf_reason (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "reason" :: rest) = parseGrundTief f (.wort "reason" :: rest) := by
  have hm : istMod "reason" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "reason" "module" = false), (by decide : strEq "reason" "use" = false), (by decide : strEq "reason" "fn" = false), (by decide : strEq "reason" "translator" = false), (by decide : strEq "reason" "profile" = false), (by decide : strEq "reason" "requires" = false), (by decide : strEq "reason" "concurrent" = false), (by decide : strEq "reason" "type" = false), (by decide : strEq "reason" "const" = false), (by decide : strEq "reason" "static" = false), (by decide : strEq "reason" "format" = false), (by decide : strEq "reason" "table" = false), (by decide : strEq "reason" "arena" = false), (by decide : strEq "reason" "reason" = true)]

theorem parseItemKopf_device (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "device" :: rest) = parseGeraetTief f (.wort "device" :: rest) := by
  have hm : istMod "device" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "device" "module" = false), (by decide : strEq "device" "use" = false), (by decide : strEq "device" "fn" = false), (by decide : strEq "device" "translator" = false), (by decide : strEq "device" "profile" = false), (by decide : strEq "device" "requires" = false), (by decide : strEq "device" "concurrent" = false), (by decide : strEq "device" "type" = false), (by decide : strEq "device" "const" = false), (by decide : strEq "device" "static" = false), (by decide : strEq "device" "format" = false), (by decide : strEq "device" "table" = false), (by decide : strEq "device" "arena" = false), (by decide : strEq "device" "reason" = false), (by decide : strEq "device" "state" = false), (by decide : strEq "device" "device" = true)]

theorem parseItemKopf_atomic (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "atomic" :: rest) = parseAtomarTief f (.wort "atomic" :: rest) := by
  have hm : istMod "atomic" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "atomic" "module" = false), (by decide : strEq "atomic" "use" = false), (by decide : strEq "atomic" "fn" = false), (by decide : strEq "atomic" "translator" = false), (by decide : strEq "atomic" "profile" = false), (by decide : strEq "atomic" "requires" = false), (by decide : strEq "atomic" "concurrent" = false), (by decide : strEq "atomic" "type" = false), (by decide : strEq "atomic" "const" = false), (by decide : strEq "atomic" "static" = false), (by decide : strEq "atomic" "format" = false), (by decide : strEq "atomic" "table" = false), (by decide : strEq "atomic" "arena" = false), (by decide : strEq "atomic" "reason" = false), (by decide : strEq "atomic" "state" = false), (by decide : strEq "atomic" "device" = false), (by decide : strEq "atomic" "assume" = false), (by decide : strEq "atomic" "axiom" = false), (by decide : strEq "atomic" "check" = false), (by decide : strEq "atomic" "atomic" = true)]

theorem parseItemKopf_lock (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "lock" :: rest) = parseSperreTief f (.wort "lock" :: rest) := by
  have hm : istMod "lock" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "lock" "module" = false), (by decide : strEq "lock" "use" = false), (by decide : strEq "lock" "fn" = false), (by decide : strEq "lock" "translator" = false), (by decide : strEq "lock" "profile" = false), (by decide : strEq "lock" "requires" = false), (by decide : strEq "lock" "concurrent" = false), (by decide : strEq "lock" "type" = false), (by decide : strEq "lock" "const" = false), (by decide : strEq "lock" "static" = false), (by decide : strEq "lock" "format" = false), (by decide : strEq "lock" "table" = false), (by decide : strEq "lock" "arena" = false), (by decide : strEq "lock" "reason" = false), (by decide : strEq "lock" "state" = false), (by decide : strEq "lock" "device" = false), (by decide : strEq "lock" "assume" = false), (by decide : strEq "lock" "axiom" = false), (by decide : strEq "lock" "check" = false), (by decide : strEq "lock" "atomic" = false), (by decide : strEq "lock" "lock" = true)]

theorem parseItemKopf_group (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "group" :: rest) = parseGruppeTief f (.wort "group" :: rest) := by
  have hm : istMod "group" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "group" "module" = false), (by decide : strEq "group" "use" = false), (by decide : strEq "group" "fn" = false), (by decide : strEq "group" "translator" = false), (by decide : strEq "group" "profile" = false), (by decide : strEq "group" "requires" = false), (by decide : strEq "group" "concurrent" = false), (by decide : strEq "group" "type" = false), (by decide : strEq "group" "const" = false), (by decide : strEq "group" "static" = false), (by decide : strEq "group" "format" = false), (by decide : strEq "group" "table" = false), (by decide : strEq "group" "arena" = false), (by decide : strEq "group" "reason" = false), (by decide : strEq "group" "state" = false), (by decide : strEq "group" "device" = false), (by decide : strEq "group" "assume" = false), (by decide : strEq "group" "axiom" = false), (by decide : strEq "group" "check" = false), (by decide : strEq "group" "atomic" = false), (by decide : strEq "group" "lock" = false), (by decide : strEq "group" "rcu" = false), (by decide : strEq "group" "group" = true)]

theorem parseItemKopf_entry (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "entry" :: rest) = parseEingangTief f (.wort "entry" :: rest) := by
  have hm : istMod "entry" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "entry" "module" = false), (by decide : strEq "entry" "use" = false), (by decide : strEq "entry" "fn" = false), (by decide : strEq "entry" "translator" = false), (by decide : strEq "entry" "profile" = false), (by decide : strEq "entry" "requires" = false), (by decide : strEq "entry" "concurrent" = false), (by decide : strEq "entry" "type" = false), (by decide : strEq "entry" "const" = false), (by decide : strEq "entry" "static" = false), (by decide : strEq "entry" "format" = false), (by decide : strEq "entry" "table" = false), (by decide : strEq "entry" "arena" = false), (by decide : strEq "entry" "reason" = false), (by decide : strEq "entry" "state" = false), (by decide : strEq "entry" "device" = false), (by decide : strEq "entry" "assume" = false), (by decide : strEq "entry" "axiom" = false), (by decide : strEq "entry" "check" = false), (by decide : strEq "entry" "atomic" = false), (by decide : strEq "entry" "lock" = false), (by decide : strEq "entry" "rcu" = false), (by decide : strEq "entry" "group" = false), (by decide : strEq "entry" "accumulates" = false), (by decide : strEq "entry" "walk" = false), (by decide : strEq "entry" "entry" = true)]

theorem parseItemKopf_fn (f : Nat) (rest : List Token)
    (ha : istAdaptKopf (.wort "fn" :: rest) = false) :
    parseItemKopfTief (f + 1) (.wort "fn" :: rest) = match parseFnSig f "" (.wort "fn" :: rest) with
      | .error e => .error e
      | .ok (sig, r) => parseFnRest f sig r := by
  have hm : istMod "fn" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "fn" "module" = false), (by decide : strEq "fn" "use" = false),
    (by decide : strEq "fn" "fn" = true), letzteArt, ha] <;> rfl

theorem parseItemKopf_art (f : Nat) (art : String) (rest : List Token) (h : istMod art = true)
    (ha : istAdaptKopf (.wort "fn" :: rest) = false) :
    parseItemKopfTief (f + 1) (.wort art :: .wort "fn" :: rest) =
      match parseFnSig f art (.wort "fn" :: rest) with
      | .error e => .error e
      | .ok (sig, r) => parseFnRest f sig r := by
  have hm : istMod "fn" = false := by decide
  have hgroup : (match .wort art :: .wort "fn" :: rest with
      | .wort "spec" :: .wort "fn" :: _ | .wort "impl" :: .wort "fn" :: _ => none
      | .wort "spec" :: r => some (true, r)
      | .wort "impl" :: r => some (false, r)
      | _ => none) = (none : Option (Bool × List Token)) := by
    split <;> simp_all
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, h, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "fn" "module" = false), (by decide : strEq "fn" "use" = false),
    (by decide : strEq "fn" "fn" = true), letzteArt, hgroup, ha] <;> rfl

theorem parseItemKopf_constfn (f : Nat) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "const" :: .wort "fn" :: rest) =
      match parseFnSig f "const" (.wort "fn" :: rest) with
      | .error e => .error e
      | .ok (sig, r) => parseFnRest f sig r := by
  have hm : istMod "const" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "const" "module" = false), (by decide : strEq "const" "use" = false),
    (by decide : strEq "const" "fn" = false), (by decide : strEq "const" "translator" = false),
    (by decide : strEq "const" "profile" = false), (by decide : strEq "const" "requires" = false),
    (by decide : strEq "const" "concurrent" = false), (by decide : strEq "const" "type" = false),
    (by decide : strEq "const" "const" = true), (by decide : strEq "fn" "fn" = true)] <;> rfl

theorem parseItemKopf_const (f : Nat) (n : String) (hn : n ≠ "fn") (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "const" :: nameTok n :: rest) =
      parseKonstNach f (nameTok n :: rest) := by
  have hm : istMod "const" = false := by decide
  simp only [parseItemKopfTief, itemGroupKopf_keinTag, String.reduceEq, not_false_eq_true, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
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


end Gabbro.Grammatik.Parser
