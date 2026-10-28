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
import Grammatik.Parser.Round.RundlaufAnwVoll

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

theorem klausel_rund (k : SKlausel) (hk : KlauselGut k) (R : List Token) (hR : KlauselFolge R) (F : Nat)
    (hF : 8 * (druckKlausel k).length + 41 ≤ F) :
    parseKlausel F (druckKlausel k ++ R) = .ok ([k], R) := by
  obtain ⟨hp, hkomma, hdd⟩ := klauselFolge_pred R hR
  obtain ⟨h1, h2, h3, -⟩ := id hp
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases k with
  | needs p =>
    simp only [druckKlausel, druckPredListe, List.length_append, List.length_singleton] at hF ⊢
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    have hP := pred_voll p hk R hp F'' (by simp only [bP]; omega)
    have hL : parsePredListe (F'' + 1) (druckToks p ++ R) = .ok ([p], R) := by
      simp only [parsePredListe, hP]
    simp only [List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "requires" "requires" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hL, List.map]
  | gives p =>
    simp only [druckKlausel, druckPredListe, List.length_append, List.length_singleton] at hF ⊢
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    have hP := pred_voll p hk R hp F'' (by simp only [bP]; omega)
    have hL : parsePredListe (F'' + 1) (druckToks p ++ R) = .ok ([p], R) := by
      simp only [parsePredListe, hP]
    simp only [List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "ensures" "requires" = false), (by decide : strEq "ensures" "ensures" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hL, List.map]
  | keeps ns =>
    have hlen : ns.length ≤ (druckNamen ns).length := by
      clear hF hk
      induction ns with
      | nil => simp only [List.length_nil, Nat.zero_le]
      | cons n ns ih => cases ns with
        | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckNamen, Std.le_refl]
        | cons m ms => simp only [List.length_cons, druckNamen, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega
    simp only [druckKlausel, List.length_append, List.length_singleton] at hF ⊢
    have hN := namen_rund ns R F' hk hkomma (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "maintains" "requires" = false), (by decide : strEq "maintains" "ensures" = false), (by decide : strEq "maintains" "maintains" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hN]
  | refs p =>
    have hP := nimmPfad_pfad p R hk hdd
    simp only [druckKlausel, List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "refines" "requires" = false), (by decide : strEq "refines" "ensures" = false), (by decide : strEq "refines" "maintains" = false), (by decide : strEq "refines" "refines" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hP]
  | effs es =>
    cases es with
    | nil =>
      simp only [druckKlausel, druckEffekte, List.cons_append, List.nil_append]
      simp only [parseKlausel, (by decide : strEq "effects" "requires" = false), (by decide : strEq "effects" "ensures" = false), (by decide : strEq "effects" "maintains" = false), (by decide : strEq "effects" "refines" = false), (by decide : strEq "effects" "effects" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, fordereZeichen, strEq_self]
    | cons e es' =>
      simp only [druckKlausel, List.length_append, List.length_cons, List.length_singleton] at hF ⊢
      have hE := effekte_rund (e :: es') R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hk (by omega)
      have hne : ∀ r, druckEffekte (e :: es') ++ .zeichen "}" :: R ≠ .zeichen "}" :: r := by
        intro r e'
        cases e <;> cases es' <;> simp only [druckEffekte, druckEffekt, List.cons_append, List.nil_append, List.cons.injEq, reduceCtorEq, false_and, List.append_assoc] at e' <;> (try split at e') <;> simp_all
      simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
      simp only [parseKlausel, (by decide : strEq "effects" "requires" = false), (by decide : strEq "effects" "ensures" = false), (by decide : strEq "effects" "maintains" = false), (by decide : strEq "effects" "refines" = false), (by decide : strEq "effects" "effects" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, fordereZeichen, strEq_self]
      simp only [hne, hE, fordereZeichen, strEq_self, ite_true]
  | cost e =>
    simp only [druckKlausel, List.length_append, List.length_cons, List.length_singleton] at hF ⊢
    have hO := ausdruck e hk (.wort "ops" :: R) F' rfl rfl rfl (by omega)
    simp only [List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    simp only [parseKlausel, (by decide : strEq "costs" "requires" = false), (by decide : strEq "costs" "ensures" = false), (by decide : strEq "costs" "maintains" = false), (by decide : strEq "costs" "refines" = false), (by decide : strEq "costs" "effects" = false), (by decide : strEq "costs" "costs" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, fordereZeichen, strEq_self, hO, nimmWort]
  | drops e =>
    simp only [druckKlausel, List.length_append, List.length_singleton] at hF ⊢
    have hO := ausdruck e hk R F' h1 h2 h3 (by omega)
    simp only [List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "decreases" "requires" = false), (by decide : strEq "decreases" "ensures" = false), (by decide : strEq "decreases" "maintains" = false), (by decide : strEq "decreases" "refines" = false), (by decide : strEq "decreases" "effects" = false), (by decide : strEq "decreases" "costs" = false), (by decide : strEq "decreases" "deadline" = false), (by decide : strEq "decreases" "decreases" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hO]
  | load p =>
    have hP := nimmPfad_pfad p R hk hdd
    simp only [druckKlausel, List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "payload" "requires" = false), (by decide : strEq "payload" "ensures" = false), (by decide : strEq "payload" "maintains" = false), (by decide : strEq "payload" "refines" = false), (by decide : strEq "payload" "effects" = false), (by decide : strEq "payload" "costs" = false), (by decide : strEq "payload" "deadline" = false), (by decide : strEq "payload" "decreases" = false), (by decide : strEq "payload" "by" = false), (by decide : strEq "payload" "section" = false), (by decide : strEq "payload" "arch" = false), (by decide : strEq "payload" "payload" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hP]
  | part s =>
    simp only [druckKlausel, List.cons_append, List.nil_append]
    simp only [parseKlausel, (by decide : strEq "section" "requires" = false), (by decide : strEq "section" "ensures" = false), (by decide : strEq "section" "maintains" = false), (by decide : strEq "section" "refines" = false), (by decide : strEq "section" "effects" = false), (by decide : strEq "section" "costs" = false), (by decide : strEq "section" "deadline" = false), (by decide : strEq "section" "decreases" = false), (by decide : strEq "section" "by" = false), (by decide : strEq "section" "section" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, nimmTextTok]
  | arch n =>
    simp only [druckKlausel, List.cons_append, List.nil_append]
    simp only [parseKlausel, (by decide : strEq "arch" "requires" = false), (by decide : strEq "arch" "ensures" = false), (by decide : strEq "arch" "maintains" = false), (by decide : strEq "arch" "refines" = false), (by decide : strEq "arch" "effects" = false), (by decide : strEq "arch" "costs" = false), (by decide : strEq "arch" "deadline" = false), (by decide : strEq "arch" "decreases" = false), (by decide : strEq "arch" "by" = false), (by decide : strEq "arch" "section" = false), (by decide : strEq "arch" "arch" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
  | moves a b =>
    simp only [druckKlausel, List.cons_append, List.nil_append]
    simp only [parseKlausel, (by decide : strEq "advances" "requires" = false), (by decide : strEq "advances" "ensures" = false), (by decide : strEq "advances" "maintains" = false), (by decide : strEq "advances" "refines" = false), (by decide : strEq "advances" "effects" = false), (by decide : strEq "advances" "costs" = false), (by decide : strEq "advances" "deadline" = false), (by decide : strEq "advances" "decreases" = false), (by decide : strEq "advances" "by" = false), (by decide : strEq "advances" "section" = false), (by decide : strEq "advances" "arch" = false), (by decide : strEq "advances" "payload" = false), (by decide : strEq "advances" "advances" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende, fordereZeichen, strEq_self]
  | induc h => simp only [KlauselGut] at hk
  | quits s => simp only [KlauselGut] at hk
  | limit s => simp only [KlauselGut] at hk

theorem klausel_kopf (k : SKlausel) (hk : KlauselGut k) :
    ∃ w ts, druckKlausel k = .wort w :: ts ∧ istKlauselKopf w = true := by
  cases k <;> (try simp only [KlauselGut, ne_eq] at hk) <;> exact ⟨_, _, rfl, by decide⟩

/-- The body behind a function head: a block or `;`. -/
def KlauselEnde (R : List Token) : Prop := (∃ r, R = .zeichen "{" :: r) ∨ (∃ r, R = .zeichen ";" :: r)

theorem klauseln_rund : ∀ (ks : List SKlausel) (R : List Token) (F : Nat), (∀ k ∈ ks, KlauselGut k) →
    KlauselEnde R → 8 * (druckKlauseln ks).length + 42 ≤ F →
    parseKlauseln F (druckKlauseln ks ++ R) = .ok (ks, R) := by
  intro ks
  induction ks with
  | nil =>
    intro R F _ hR hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp only [parseKlauseln, druckKlauseln, List.nil_append]
  | cons k ks ih =>
    intro R F hg hR hF
    have hk := hg k (by simp only [List.mem_cons, true_or])
    obtain ⟨w, ts, hd, hw⟩ := klausel_kopf k hk
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckKlauseln, List.length_append] at hF ⊢
    have hfolge : KlauselFolge (druckKlauseln ks ++ R) := by
      cases ks with
      | nil => rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩
               · exact Or.inl ⟨r, by simp only [druckKlauseln, List.nil_append]⟩
               · exact Or.inr (Or.inl ⟨r, by simp only [druckKlauseln, List.nil_append]⟩)
      | cons k2 ks2 =>
        obtain ⟨w2, ts2, hd2, hw2⟩ := klausel_kopf k2 (hg k2 (by simp only [List.mem_cons, true_or, or_true]))
        exact Or.inr (Or.inr ⟨w2, ts2 ++ druckKlauseln ks2 ++ R, by simp only [druckKlauseln, hd2, List.cons_append, List.append_assoc], hw2⟩)
    have hl1 : 1 ≤ (druckKlausel k).length := by rw [hd]; simp only [List.length_cons, Nat.le_add_left]
    have hK := klausel_rund k hk (druckKlauseln ks ++ R) hfolge F' (by omega)
    have hR' := ih R F' (fun x hx => hg x (List.mem_cons_of_mem _ hx)) hR (by omega)
    rw [List.append_assoc, hd]
    rw [hd] at hK
    simp only [List.cons_append] at hK ⊢
    simp only [parseKlauseln, hw, ite_true, hK, hR', List.singleton_append]

/-! ### Parameters and the function head -/

theorem paramListe_rund : ∀ (ps : List (String × STyp)) (R : List Token) (F : Nat), ps ≠ [] →
    (∀ p ∈ ps, TypGut p.2) → (∃ r, R = .zeichen ")" :: r) → 8 * (druckParams ps).length + 31 ≤ F →
    parseParamListe F (druckParams ps ++ R) = .ok (ps, R) := by
  intro ps
  induction ps with
  | nil => intro _ _ h; exact absurd rfl h
  | cons p ps ih =>
    intro R F _ hg hR hF
    obtain ⟨n, t⟩ := p
    have ht : TypGut t := hg (n, t) (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases ps with
    | nil =>
      obtain ⟨r, rfl⟩ := hR
      simp only [druckParams, druckParam, List.length_append, List.length_cons, List.length_nil] at hF ⊢
      have hT := parse_druckTyp t ht (.zeichen ")" :: r) F'
        ⟨(by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
          (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩ (by simp only [fbT]; omega)
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      simp only [parseParamListe, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hT, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]
    | cons q qs =>
      obtain ⟨m, u⟩ := q
      obtain ⟨Z, hZ⟩ : ∃ Z, druckParams ((m, u) :: qs) = nameTok m :: Z := by
        cases qs <;> exact ⟨_, rfl⟩
      have hd : druckParams ((n, t) :: (m, u) :: qs) ++ R = nameTok n :: .zeichen ":" ::
          (druckTyp t ++ .zeichen "," :: nameTok m :: (Z ++ R)) := by
        have : druckParams ((n, t) :: (m, u) :: qs) = druckParam (n, t) ++ [.zeichen ","] ++
            druckParams ((m, u) :: qs) := rfl
        rw [this, hZ]; simp only [druckParam, List.cons_append, List.nil_append, List.append_assoc]
      have hlen : (druckParams ((n, t) :: (m, u) :: qs)).length =
          (druckTyp t).length + 3 + (druckParams ((m, u) :: qs)).length := by
        have : druckParams ((n, t) :: (m, u) :: qs) = druckParam (n, t) ++ [.zeichen ","] ++
            druckParams ((m, u) :: qs) := rfl
        rw [this]; simp only [druckParam, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append]; omega
      rw [hlen] at hF
      have hR' := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) hR (by omega)
      rw [hZ] at hR' hF
      have hT := parse_druckTyp t ht (.zeichen "," :: nameTok m :: (Z ++ R)) F'
        ⟨(by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
          (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩ (by simp only [fbT]; simp only [List.length_cons, Nat.reduceLeDiff] at hF; omega)
      rw [hd]
      simp only [List.cons_append] at hR'
      simp only [parseParamListe, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hT, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hR']

theorem params_rund (ps : List (String × STyp)) (hg : ∀ p ∈ ps, TypGut p.2) (R : List Token) (F : Nat)
    (hF : 8 * (druckParams ps).length + 32 ≤ F) :
    parseParams F (.zeichen "(" :: (druckParams ps ++ .zeichen ")" :: R)) = .ok (ps, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases ps with
  | nil => simp only [parseParams, fordereZeichen, strEq_self, ↓reduceIte, druckParams, List.nil_append]
  | cons p ps =>
    obtain ⟨n, t⟩ := p
    obtain ⟨Z, hZ⟩ : ∃ Z, druckParams ((n, t) :: ps) = nameTok n :: Z := by
      cases ps <;> exact ⟨_, rfl⟩
    have hL := paramListe_rund ((n, t) :: ps) (.zeichen ")" :: R) F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hg ⟨R, rfl⟩ (by omega)
    rw [hZ] at hL ⊢
    simp only [List.cons_append] at hL ⊢
    simp only [parseParams, fordereZeichen, strEq_self, ↓reduceIte, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hL]

/-- A printable function head. -/
def SigGut (s : FnSig) : Prop :=
  (s.art = "" ∨ s.art = "const" ∨ istMod s.art = true) ∧ (∀ p ∈ s.params, TypGut p.2) ∧
    TypOptGut s.res ∧ (∀ k ∈ s.klauseln, KlauselGut k)

/-- The function head behind its modifier, up to the body. -/
def sigToks (s : FnSig) : List Token :=
  [.wort "fn", nameTok s.name, .zeichen "("] ++ druckParams s.params ++ [.zeichen ")"] ++
    (match s.res with
      | some t => [.zeichen "->"] ++ druckTyp t
      | none => []) ++
    (match s.fehler with
      | some n => [.wort "or", nameTok n]
      | none => []) ++
    druckKlauseln s.klauseln

theorem druckFnSig_eq (s : FnSig) :
    druckFnSig s = (if strEq s.art "" then [] else [.wort s.art]) ++ sigToks s := by
  simp only [druckFnSig, List.append_assoc, List.cons_append, List.nil_append, sigToks, List.append_cancel_left_eq, List.cons.injEq, true_and]; rfl

/-- The result tokens of a head. -/
def resToks : Option STyp → List Token
  | some t => [.zeichen "->"] ++ druckTyp t
  | none => []

/-- The `or` channel tokens of a head. -/
def fehlerToks : Option String → List Token
  | some n => [.wort "or", nameTok n]
  | none => []

theorem sigToks_eq (s : FnSig) : sigToks s = [.wort "fn", nameTok s.name, .zeichen "("] ++
    druckParams s.params ++ [.zeichen ")"] ++ resToks s.res ++ fehlerToks s.fehler ++ druckKlauseln s.klauseln := by
  simp only [sigToks]
  cases s.res <;> cases s.fehler <;> rfl

/-- The tail of a function head (the `or` channel, clauses) is a type follow. -/
theorem kopfRest_typFolge (fehler : Option String) (ks : List SKlausel) (hk : ∀ k ∈ ks, KlauselGut k)
    (R : List Token) (hR : KlauselEnde R) :
    TypFolge (fehlerToks fehler ++ druckKlauseln ks ++ R) := by
  have gen : ∀ (w : String) (X : List Token), w ≠ "in" → w ≠ "wrapping" → w ≠ "embeds" → w ≠ "rounded" →
      TypFolge (.wort w :: X) := by
    intro w X h1 h2 h3 h4
    have : strEq w "rounded" = false := by
      cases h : strEq w "rounded"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) h4
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, by simp only [ruhigGleit, this, Bool.not_false]⟩ <;> intro r e <;> simp only [List.cons.injEq, Token.wort.injEq, reduceCtorEq, false_and] at e <;> simp_all
  cases fehler with
  | some n => exact gen "or" _ (by decide) (by decide) (by decide) (by decide)
  | none =>
    simp only [fehlerToks, List.nil_append]
    cases ks with
    | nil =>
      rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
        exact ⟨(by intro x e; simp only [druckKlauseln, List.nil_append, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [druckKlauseln, List.nil_append, List.cons.injEq, reduceCtorEq, false_and] at e),
          (by intro x e; simp only [druckKlauseln, List.nil_append, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [druckKlauseln, List.nil_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩
    | cons k ks' =>
      obtain ⟨w, ts, hd, hw⟩ := klausel_kopf k (hk k (by simp only [List.mem_cons, true_or]))
      have : druckKlauseln (k :: ks') ++ R = .wort w :: (ts ++ druckKlauseln ks' ++ R) := by
        simp only [druckKlauseln, hd, List.cons_append, List.append_assoc]
      rw [this]
      apply gen w _ <;> intro e <;> subst e <;> exact absurd hw (by decide)

theorem fnSig_rund (s : FnSig) (hs : SigGut s) (R : List Token) (hR : KlauselEnde R) (F : Nat)
    (hF : 8 * (sigToks s).length + 42 ≤ F) :
    parseFnSig F s.art (sigToks s ++ R) = .ok (s, R) := by
  obtain ⟨-, hp, hres, hk⟩ := hs
  rw [sigToks_eq] at hF ⊢
  obtain ⟨art, name, params, res, fehler, klauseln⟩ := s
  simp only at hp hres hk hF ⊢
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hlenF : (fehlerToks fehler).length ≤ 2 := by cases fehler <;> simp only [fehlerToks, List.length_nil, Nat.zero_le, List.length_cons, Nat.zero_add, Nat.reduceAdd, Std.le_refl]
  simp only [List.length_append, List.length_cons, List.length_nil] at hF
  have hK := klauseln_rund klauseln R F' hk hR (by omega)
  have hFe : parseFehler (fehlerToks fehler ++ druckKlauseln klauseln ++ R) =
      .ok (fehler, druckKlauseln klauseln ++ R) := by
    cases fehler with
    | some n => simp only [parseFehler, fehlerToks, List.cons_append, List.nil_append, strEq_self, ↓reduceIte, nimmName, nameText_nameTok]
    | none =>
      simp only [fehlerToks, List.nil_append]
      cases klauseln with
      | nil =>
        rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp only [parseFehler, druckKlauseln, List.nil_append]
      | cons k ks =>
        obtain ⟨w, ts, hd, hw⟩ := klausel_kopf k (hk k (by simp only [List.mem_cons, true_or]))
        have hwo : strEq w "or" = false := by
          cases h : strEq w "or"
          · rfl
          · have := (strEq_eq _ _).mp h; subst this; exact absurd hw (by decide)
        simp only [parseFehler, druckKlauseln, hd, List.cons_append, List.append_assoc, hwo, Bool.false_eq_true, ↓reduceIte]
  have hTF := kopfRest_typFolge fehler klauseln hk R hR
  have hErg : parseErgebnis F' (resToks res ++ (fehlerToks fehler ++ druckKlauseln klauseln ++ R)) =
      .ok (res, fehler, druckKlauseln klauseln ++ R) := by
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    cases res with
    | some t =>
      have hT := parse_druckTyp t hres _ F'' hTF (by simp only [fbT]; simp only [Nat.zero_add, Nat.reduceAdd, resToks, List.cons_append, List.nil_append, List.length_cons, Nat.reduceLeDiff] at hF; omega)
      simp only [resToks, List.singleton_append, List.cons_append, List.append_assoc] at hT hFe ⊢
      simp only [parseErgebnis, List.nil_append, hT, hFe]
    | none =>
      simp only [resToks, List.nil_append]
      have hne : ∀ r, fehlerToks fehler ++ druckKlauseln klauseln ++ R ≠ .zeichen "->" :: r := by
        intro r e
        cases fehler with
        | some n => simp only [fehlerToks, List.cons_append, List.nil_append, List.cons.injEq, reduceCtorEq, false_and] at e
        | none =>
          cases klauseln with
          | nil => rcases hR with ⟨r', rfl⟩ | ⟨r', rfl⟩ <;> simp only [fehlerToks, druckKlauseln, List.append_nil, List.nil_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e
          | cons k ks =>
            obtain ⟨w, ts, hd, -⟩ := klausel_kopf k (hk k (by simp only [List.mem_cons, true_or]))
            simp only [fehlerToks, druckKlauseln, hd, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, reduceCtorEq, false_and] at e
      rw [parseErgebnis.eq_def]
      simp only [hne]
      simp only [List.append_assoc] at hFe
      simp only [List.append_assoc, hFe]
  have hP := params_rund params hp (resToks res ++ (fehlerToks fehler ++ druckKlauseln klauseln ++ R)) F'
    (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at hP hErg hK ⊢
  simp only [parseFnSig, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hP, hErg, hK]

/-! ### Items -/

/-- The fuel bound of an item: eight per printed token, thirty-eight spare. -/
def fbI (it : SItemTief) : Nat := 8 * (druckItem it).length + 38

/-- An item reads back before every follow. -/
def ItemBein (it : SItemTief) : Prop :=
  ∀ (rest : List Token) (F : Nat), fbI it ≤ F → parseItemTief F (druckItem it ++ rest) = .ok (it, rest)

/-- An item prints with a head word other than `when` and `pub`. -/
def ItemKopf (it : SItemTief) : Prop :=
  ∃ w ts, druckItem it = .wort w :: ts ∧ w ≠ "when" ∧ w ≠ "pub"

/-- What may follow an item list: nothing, `}` or the end marker. -/
def ItemsEnde (R : List Token) : Prop := R = [] ∨ (∃ r, R = .zeichen "}" :: r) ∨ (∃ r, R = .ende :: r)

theorem items_rund : ∀ (its : List SItemTief) (R : List Token) (F : Nat),
    (∀ it ∈ its, ItemBein it ∧ ItemKopf it) → ItemsEnde R → 8 * (druckItems its).length + 39 ≤ F →
    parseItemsTief F (druckItems its ++ R) = .ok (its, R) := by
  intro its
  induction its with
  | nil =>
    intro R F _ hR hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    rcases hR with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp only [parseItemsTief, druckItems, List.append_nil, List.nil_append]
  | cons it its ih =>
    intro R F h hR hF
    obtain ⟨hB, w, ts, hd, -, -⟩ := h it (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckItems, List.length_append] at hF ⊢
    have hl : 1 ≤ (druckItem it).length := by rw [hd]; simp only [List.length_cons, Nat.le_add_left]
    have hI := hB (druckItems its ++ R) F' (by simp only [fbI]; omega)
    have hR' := ih R F' (fun x hx => h x (List.mem_cons_of_mem _ hx)) hR (by omega)
    rw [List.append_assoc, hd]
    rw [hd] at hI
    simp only [List.cons_append] at hI ⊢
    simp only [parseItemsTief, hI, hR']

theorem item_use (p : List String) (hp : p ≠ []) : ItemBein (.useT p) := by
  intro rest F hF
  simp only [fbI] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hd : druckItem (.useT p) ++ rest = .wort "use" :: (pfadToks p ++ .zeichen ";" :: rest) := by
    simp only [druckItem, List.cons_append, List.nil_append, List.append_assoc]
  have hP := nimmPfad_pfad p (.zeichen ";" :: rest) hp
    (by intro r e; injection e with e1; injection e1 with e2; exact absurd e2 (by decide))
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_use]
  simp only [parseUseTief, nimmWort, strEq_self, ↓reduceIte, hP, fordereZeichen]

/-- `= v ;` behind a type: the initialiser follow. -/
theorem typ_gleich (t : STyp) (ht : TypGut t) (X : List Token) (F : Nat) (hF : fbT t ≤ F) :
    parseTyp F (druckTyp t ++ .zeichen "=" :: X) = .ok (t, .zeichen "=" :: X) :=
  parse_druckTyp t ht _ F ⟨(by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
    (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩ hF

theorem item_const (n : String) (hn : n ≠ "fn") (t : STyp) (v : SKonstWert) (ht : TypGut t)
    (hv : KonstGut v) :
    ItemBein (.constT n t v) := by
  intro rest F hF
  simp only [fbI, druckItem, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckItem (.constT n t v) ++ rest = .wort "const" :: nameTok n :: .zeichen ":" ::
      (druckTyp t ++ .zeichen "=" :: (druckKonstWert v ++ .zeichen ";" :: rest)) := by
    simp only [druckItem, List.cons_append, List.nil_append, List.append_assoc]
  have hT := typ_gleich t ht (druckKonstWert v ++ .zeichen ";" :: rest) F' (by simp only [fbT]; omega)
  have hV := konst_rund v hv (.zeichen ";" :: rest) F' rfl rfl rfl (by simp only [fbK]; omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_const _ _ hn]
  simp only [parseKonstNach, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hT, hV]

/-- The tail of a `static`: `[aligned e] [section "s"] [shared] ;`. -/
def globTailToks (al : Option SExpr) (s : Option String) (sh : Bool) : List Token :=
  (match al with
    | some e => [.wort "aligned"] ++ druckToks e
    | none => []) ++
  (match s with
    | some x => [.wort "section", .text x]
    | none => []) ++
  (if sh then [.wort "shared"] else []) ++ [.zeichen ";"]

theorem globTail_rund (al : Option SExpr) (s : Option String) (sh : Bool)
    (hal : ∀ e, al = some e → gut e = true) (rest : List Token) (F : Nat)
    (hF : 8 * (globTailToks al s sh).length + 40 ≤ F) :
    parseGlobTail F (globTailToks al s sh ++ rest) = .ok ((al, s, sh), rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases al with
  | none =>
    cases s <;> cases sh <;>
      simp only [parseGlobTail, bind, Except.bind, globTailToks, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append, pure, Except.pure, fordereZeichen, strEq_self, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, nimmTextTok]
  | some e =>
    have he := hal e rfl
    cases s with
    | none =>
      cases sh with
      | false =>
        have hO := ausdruck e he (.zeichen ";" :: rest) F' rfl rfl rfl (by
          simp only [globTailToks, List.cons_append, List.nil_append, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceLeDiff] at hF; omega)
        simp only [parseGlobTail, bind, Except.bind, globTailToks, List.cons_append, List.nil_append, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.append_assoc, hO, pure, Except.pure, fordereZeichen, strEq_self]
      | true =>
        have hO := ausdruck e he (.wort "shared" :: .zeichen ";" :: rest) F' rfl rfl rfl (by
          simp only [globTailToks, List.cons_append, List.nil_append, List.append_nil, ↓reduceIte, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)
        simp only [parseGlobTail, bind, Except.bind, globTailToks, List.cons_append, List.nil_append, List.append_nil, ↓reduceIte, List.append_assoc, hO, pure, Except.pure, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, fordereZeichen, strEq_self]
    | some x =>
      cases sh with
      | false =>
        have hO := ausdruck e he (.wort "section" :: .text x :: .zeichen ";" :: rest) F' rfl rfl rfl (by
          simp only [globTailToks, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)
        simp only [parseGlobTail, bind, Except.bind, globTailToks, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc, hO, pure, Except.pure, nimmTextTok, fordereZeichen, strEq_self]
      | true =>
        have hO := ausdruck e he (.wort "section" :: .text x :: .wort "shared" :: .zeichen ";" :: rest) F'
          rfl rfl rfl (by simp only [globTailToks, List.cons_append, List.nil_append, ↓reduceIte, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)
        simp only [parseGlobTail, bind, Except.bind, globTailToks, List.cons_append, List.nil_append, ↓reduceIte, List.append_assoc, hO, pure, Except.pure, nimmTextTok, fordereZeichen, strEq_self]

theorem globTail_ruhig (al : Option SExpr) (s : Option String) (sh : Bool) (rest : List Token) :
    ruhig (globTailToks al s sh ++ rest) = true ∧ ruhigSuff (globTailToks al s sh ++ rest) = true ∧
      ruhigGleit (globTailToks al s sh ++ rest) = true := by
  cases al <;> cases s <;> cases sh <;> exact ⟨rfl, rfl, rfl⟩

theorem item_static (m : Bool) (n : String) (hn : n ≠ "mut") (t : STyp) (v : SKonstWert)
    (al : Option SExpr) (s : Option String) (sh : Bool) (ht : TypGut t) (hv : KonstGut v)
    (hal : ∀ e, al = some e → gut e = true) :
    ItemBein (.globT m n t v al s sh) := by
  intro rest F hF
  have hd : druckItem (.globT m n t v al s sh) ++ rest = .wort "static" :: ((if m then [.wort "mut"] else []) ++
      nameTok n :: .zeichen ":" :: (druckTyp t ++ .zeichen "=" :: (druckKonstWert v ++
        (globTailToks al s sh ++ rest)))) := by
    cases al <;> cases s <;> cases sh <;> simp only [druckItem, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, Bool.false_eq_true, ↓reduceIte, globTailToks]
  have hlen : (druckItem (.globT m n t v al s sh)).length = 1 + (if m then 1 else 0) + 2 +
      (druckTyp t).length + 1 + (druckKonstWert v).length + (globTailToks al s sh).length := by
    cases m <;> cases al <;> cases s <;> cases sh <;> simp only [druckItem, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.add_zero, Nat.reduceAdd, globTailToks, Nat.add_right_cancel_iff] <;> omega
  simp only [fbI, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  obtain ⟨h1, h2, h3⟩ := globTail_ruhig al s sh rest
  have hT := typ_gleich t ht (druckKonstWert v ++ (globTailToks al s sh ++ rest)) F'
    (by simp only [fbT]; split at hF <;> omega)
  have hV := konst_rund v hv (globTailToks al s sh ++ rest) F' h1 h2 h3
    (by simp only [fbK]; split at hF <;> omega)
  have hG := globTail_rund al s sh hal rest F' (by split at hF <;> omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_static]
  cases m
  · simp only [Bool.false_eq_true, ite_false, List.nil_append]
    rcases nameTok_cases n with h | h <;> rw [h] <;>
      simp only [parseGlobTief, nimmWort, strEq_self, ↓reduceIte, strEq_ne hn, Bool.false_eq_true, parseGlobAfter, bind, Except.bind, nimmName, nameText_wort, fordereZeichen, hT, hV, hG, pure, Except.pure, nameText_ident]
  · simp only [parseGlobTief, nimmWort, strEq_self, ↓reduceIte, List.cons_append, List.nil_append, parseGlobAfter, bind, Except.bind, nimmName, nameText_nameTok, fordereZeichen, hT, hV, hG, pure, Except.pure]


/-! ### Functions -/

theorem sigToks_kopf (s : FnSig) : ∃ ts, sigToks s = .wort "fn" :: ts := ⟨_, rfl⟩

/-- A function head read by the item reader, up to its body. -/
theorem item_fnkopf (sig : FnSig) (hs : SigGut sig) (R : List Token) (hR : KlauselEnde R) (F : Nat)
    (hF : 8 * (sigToks sig).length + 46 ≤ F) :
    ∃ G, F ≤ G + 4 ∧ parseItemTief F (druckFnSig sig ++ R) = parseFnRest G sig R := by
  obtain ⟨hart, -⟩ := id hs
  obtain ⟨ts, hts⟩ := sigToks_kopf sig
  rw [druckFnSig_eq]
  rcases hart with h | h | h
  · obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hS := fnSig_rund sig hs R hR F' (by omega)
    rw [h] at hS
    refine ⟨F', by omega, ?_⟩
    simp only [h, strEq_self, ite_true, List.nil_append]
    rw [hts, List.cons_append, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_fn,
      ← List.cons_append, ← hts, hS]
  · obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hS := fnSig_rund sig hs R hR F' (by omega)
    rw [h] at hS
    refine ⟨F', by omega, ?_⟩
    simp only [h, (by decide : strEq "const" "" = false), Bool.false_eq_true, ite_false,
      List.singleton_append]
    rw [hts] at hS ⊢
    simp only [List.cons_append] at hS ⊢
    rw [parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_constfn, hS]
  · obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hS := fnSig_rund sig hs R hR F' (by omega)
    have hne : strEq sig.art "" = false := by
      cases e : strEq sig.art ""
      · rfl
      · have := (strEq_eq _ _).mp e; rw [this] at h; exact absurd h (by decide)
    have hw1 : sig.art ≠ "when" := by intro e; rw [e] at h; exact absurd h (by decide)
    have hw2 : sig.art ≠ "pub" := by intro e; rw [e] at h; exact absurd h (by decide)
    refine ⟨F', by omega, ?_⟩
    simp only [hne, Bool.false_eq_true, ite_false, List.singleton_append]
    rw [hts] at hS ⊢
    simp only [List.cons_append] at hS ⊢
    rw [parseItemTief_wort _ _ _ hw1 hw2, parseItemKopf_art _ _ _ h, hS]

theorem druckFnSig_len (sig : FnSig) : (sigToks sig).length ≤ (druckFnSig sig).length := by
  rw [druckFnSig_eq]; simp only [List.length_append, Nat.le_add_left]

theorem item_fn (sig : FnSig) (b : SAnw) (hs : SigGut sig) (hb : BlockBein b) (hk : BlockKopf b) :
    ItemBein (.fnT sig b) := by
  intro rest F hF
  obtain ⟨us, hus⟩ := hk
  have hlen := druckFnSig_len sig
  have hbl : 1 ≤ (druckAnw b).length := by rw [hus]; simp only [List.length_cons, Nat.le_add_left]
  simp only [fbI, druckItem, List.length_append] at hF
  obtain ⟨G, hG, hI⟩ := item_fnkopf sig hs (druckAnw b ++ rest) (Or.inl ⟨us ++ rest, by rw [hus]; rfl⟩) F
    (by omega)
  have hB := hb rest (G - 1) (by simp only [fbA]; omega)
  simp only [druckItem, List.append_assoc]
  rw [hI]
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hB
  rw [hus] at hB ⊢
  simp only [List.cons_append] at hB ⊢
  simp only [parseFnRest, hB]

theorem item_proto (sig : FnSig) (hs : SigGut sig) : ItemBein (.protoT sig) := by
  intro rest F hF
  have hlen := druckFnSig_len sig
  simp only [fbI, druckItem, List.length_append, List.length_singleton] at hF
  obtain ⟨G, hG, hI⟩ := item_fnkopf sig hs (.zeichen ";" :: rest) (Or.inr ⟨rest, rfl⟩) F (by omega)
  simp only [druckItem, List.append_assoc, List.singleton_append]
  rw [hI]
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  simp only [parseFnRest]

/-! ### `reason`, `concurrent`, `module` -/

/-- A printable reason case: its number is printable. -/
def FallGut (c : String × SExpr × String) : Prop := gut c.2.1 = true ∧ c.1 ≠ "exhaustive"

theorem grundFaelle_rund : ∀ (cs : List (String × SExpr × String)) (ex : Bool) (R : List Token) (F : Nat),
    (∀ c ∈ cs, FallGut c) → 8 * (druckGrundFaelle cs).length + 42 ≤ F →
    parseGrundFaelle F (druckGrundFaelle cs ++ ((if ex then [.wort "exhaustive"] else []) ++
      .zeichen "}" :: R)) = .ok ((cs, ex), R) := by
  intro cs
  induction cs with
  | nil =>
    intro ex R F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases ex <;> simp only [parseGrundFaelle, druckGrundFaelle, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.cons_append, strEq_self, fordereZeichen]
  | cons c cs ih =>
    intro ex R F hg hF
    obtain ⟨n, num, t⟩ := c
    have hnum : gut num = true := (hg (n, num, t) (by simp only [List.mem_cons, true_or])).1
    have hx : strEq n "exhaustive" = false := by
      cases h : strEq n "exhaustive"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) (hg (n, num, t) (by simp only [List.mem_cons, true_or])).2
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckGrundFaelle, List.length_append, List.length_cons, List.length_nil] at hF
    have hR := ih ex R F' (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    have hO := ausdruck num hnum (.text t :: .zeichen "," :: (druckGrundFaelle cs ++
      ((if ex then [.wort "exhaustive"] else []) ++ .zeichen "}" :: R))) F'' rfl rfl rfl (by omega)
    simp only [druckGrundFaelle, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append]
    unfold parseGrundFaelle
    rcases nameTok_cases n with h | h <;> rw [h] <;>
      simp only [hx, Bool.false_eq_true, ↓reduceIte, parseGrundFall, nimmName, nameText_wort, fordereZeichen, strEq_self, hO, nimmTextTok, hR, nameText_ident]

theorem item_why (n : String) (cs : List (String × SExpr × String)) (ex : Bool) (hg : ∀ c ∈ cs, FallGut c) :
    ItemBein (.whyT n cs ex) := by
  intro rest F hF
  have hd : druckItem (.whyT n cs ex) ++ rest = .wort "reason" :: nameTok n :: .zeichen "{" ::
      (druckGrundFaelle cs ++ ((if ex then [.wort "exhaustive"] else []) ++ .zeichen "}" :: rest)) := by
    cases ex <;> simp only [druckItem, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc]
  have hlen : (druckGrundFaelle cs).length + 3 ≤ (druckItem (.whyT n cs ex)).length := by
    cases ex <;> simp only [druckItem, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.le_add_right, List.append_assoc, Nat.reduceAdd, Nat.add_le_add_iff_right] <;> omega
  simp only [fbI] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hG := grundFaelle_rund cs ex rest F' hg (by omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_reason]
  simp only [parseGrundTief, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, fordereZeichen, hG]

/-- A path printed as text: segments name-shaped. -/
def PfadGut (segs : List String) : Prop :=
  segs ≠ [] ∧ ∀ a ∈ segs, nameForm a = true

theorem druckWurzeln_pfade : ∀ (ps : List (List String)), (∀ p ∈ ps, PfadGut p) →
    druckWurzeln (ps.map (fun p => "::".intercalate p)) =
      kommaToks (ps.map pfadToks) := by
  intro ps hps
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := hps p (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => hps x (List.mem_cons_of_mem _ hx))
    cases ps with
    | nil => simp only [List.map_cons, List.map_nil, druckWurzeln, rohToks_pfad p hp.1 hp.2, kommaToks]
    | cons q qs =>
      simp only [List.map_cons] at ih' ⊢
      simp only [druckWurzeln, kommaToks, rohToks_pfad p hp.1 hp.2] at ih' ⊢
      rw [ih']

/-- The arguments of a start as printed: in parentheses when there are any. -/
def argToks (as : List SExpr) : List Token :=
  if as.isEmpty then [] else [.zeichen "("] ++ druckToksListe as ++ [.zeichen ")"]

theorem druckStart_eq (p : List String × List SExpr) (hp : PfadGut p.1) :
    druckStart p = pfadToks p.1 ++ argToks p.2 := by
  simp only [druckStart, rohToks_pfad p.1 hp.1 hp.2, List.isEmpty_iff, List.cons_append, List.nil_append, argToks]

/-- After a path, the arguments read back (or none) and the follow `,`/`}` stays. -/
theorem argToks_rund (as : List SExpr) (has : ∀ x ∈ as, gut x = true) (R : List Token) (f : Nat)
    (hR : ∀ r, R ≠ .zeichen "(" :: r) (hF : 6 * (druckToksListe as).length + 36 ≤ f) :
    startArgs f (argToks as ++ R) = .ok (as, R) := by
  cases as with
  | nil =>
    simp only [argToks, List.isEmpty_nil, if_true, List.nil_append]
    unfold startArgs
    split
    · rename_i x; exact absurd rfl (hR x)
    · rfl
  | cons x xs =>
    simp only [argToks, List.isEmpty_cons, Bool.false_eq_true, if_false, List.append_assoc, List.cons_append,
      List.nil_append, startArgs]
    have := argsM (x :: xs) R f (fun y hy => ⟨legs_tok y (has y hy), has y hy⟩) hF
    simpa [List.append_assoc] using this

theorem druckToksListe_le_argToks : ∀ (as : List SExpr), (druckToksListe as).length ≤ (argToks as).length
  | [] => by simp only [druckToksListe, List.length_nil, argToks, List.isEmpty_nil, ↓reduceIte, Std.le_refl]
  | x :: xs => by simp only [argToks, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, List.length_cons, List.length_append, List.length_nil, Nat.zero_add]; omega

/-- The tokens of the starts, as `kommaToks` of each start's tokens. -/
theorem druckStarts_eq : ∀ (ps : List (List String × List SExpr)), (∀ p ∈ ps, PfadGut p.1) →
    druckStarts ps = kommaToks (ps.map fun p => pfadToks p.1 ++ argToks p.2) := by
  intro ps hps
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := hps p (by simp only [List.mem_cons, true_or])
    have ih' := ih (fun x hx => hps x (List.mem_cons_of_mem _ hx))
    cases ps with
    | nil => simp only [druckStarts, druckStart_eq p hp, List.map_cons, List.map_nil, kommaToks]
    | cons q qs =>
      simp only [List.map_cons] at ih' ⊢
      simp only [druckStarts, kommaToks, druckStart_eq p hp] at ih' ⊢
      rw [ih']

theorem startFolge_rund : ∀ (ps : List (List String × List SExpr)) (R : List Token) (F : Nat), ps ≠ [] →
    (∀ p ∈ ps, PfadGut p.1 ∧ ∀ x ∈ p.2, gut x = true) →
    ps.length + 6 * (kommaToks (ps.map fun p => pfadToks p.1 ++ argToks p.2)).length + 37 ≤ F →
    parsePfadFolge F (kommaToks (ps.map fun p => pfadToks p.1 ++ argToks p.2) ++ .zeichen "}" :: R) =
      .ok (ps, R) := by
  intro ps
  induction ps with
  | nil => intro _ _ h; exact absurd rfl h
  | cons p ps ih =>
    intro R F _ hg hF
    have hp := hg p (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons, List.map_cons] at hF; omega⟩
    cases ps with
    | nil =>
      have hP := nimmPfad_pfad p.1 (argToks p.2 ++ .zeichen "}" :: R) hp.1.1 (by
        intro r e
        unfold argToks at e; split at e <;> simp only [List.nil_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, List.cons_append, List.append_assoc] at e)
      have hA := argToks_rund p.2 hp.2 (.zeichen "}" :: R) F' (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by
        have := druckToksListe_le_argToks p.2
        simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.map_nil, kommaToks, List.length_append, Nat.reduceLeDiff] at hF; omega)
      simp only [List.map_cons, List.map_nil, kommaToks, List.append_assoc] at hP hA ⊢
      unfold parsePfadFolge
      simp only [hP]
      rw [hA]
      simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, fordereZeichen, strEq_self, ↓reduceIte]
    | cons q qs =>
      have hq := hg q (by simp only [List.mem_cons, true_or, or_true])
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons, List.map_cons, kommaToks, List.append_assoc, List.cons_append, List.nil_append, List.length_append, Nat.reduceLeDiff] at hF ⊢; omega)
      obtain ⟨a, us, hq1⟩ : ∃ a us, pfadToks q.1 = nameTok a :: us := by
        match q.1, hq.1.1 with
        | [a], _ => exact ⟨a, [], rfl⟩
        | a :: b :: cs, _ => exact ⟨a, _, rfl⟩
      have hk : kommaToks ((q :: qs).map fun p => pfadToks p.1 ++ argToks p.2) =
          nameTok a :: (kommaToks ((q :: qs).map fun p => pfadToks p.1 ++ argToks p.2)).tail := by
        cases qs <;> simp only [List.map_cons, hq1, List.cons_append, List.map_nil, kommaToks, List.tail_cons, List.append_assoc, List.nil_append]
      have hd : kommaToks ((p :: q :: qs).map fun p => pfadToks p.1 ++ argToks p.2) = pfadToks p.1 ++
          (argToks p.2 ++ .zeichen "," :: kommaToks ((q :: qs).map fun p => pfadToks p.1 ++ argToks p.2)) := by
        simp only [List.map_cons, kommaToks, List.append_assoc, List.cons_append, List.nil_append]
      have hP := nimmPfad_pfad p.1 (argToks p.2 ++ .zeichen "," ::
        (kommaToks ((q :: qs).map fun p => pfadToks p.1 ++ argToks p.2) ++ .zeichen "}" :: R)) hp.1.1 (by
          intro r e
          unfold argToks at e; split at e <;> simp only [List.isEmpty_iff, List.cons_append, List.nil_append, List.map_cons, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, List.append_assoc] at e)
      have hA := argToks_rund p.2 hp.2 (.zeichen "," ::
        (kommaToks ((q :: qs).map fun p => pfadToks p.1 ++ argToks p.2) ++ .zeichen "}" :: R)) F'
        (by intro r e; simp only [List.map_cons, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by
          have := druckToksListe_le_argToks p.2
          rw [hd] at hF; simp only [List.length_cons, List.map_cons, List.length_append, Nat.reduceLeDiff] at hF; omega)
      rw [hd]
      simp only [List.append_assoc, List.cons_append] at hP hA ⊢
      unfold parsePfadFolge
      simp only [hP]
      rw [hA]
      rw [hk] at hR ⊢
      simp only [List.cons_append] at hR ⊢
      simp only [hR]
      rcases nameTok_cases a with h | h <;> rw [h] <;> rfl

theorem item_conc (ps : List (List String × List SExpr)) (hps : ∀ p ∈ ps, PfadGut p.1 ∧ ∀ x ∈ p.2, gut x = true) :
    ItemBein (.concT ps) := by
  intro rest F hF
  have hW := druckStarts_eq ps (fun p hp => (hps p hp).1)
  have hlen : ps.length ≤ (kommaToks (ps.map fun p => pfadToks p.1 ++ argToks p.2)).length := by
    clear hF hW
    induction ps with
    | nil => simp only [List.length_nil, List.map_nil, Nat.zero_le]
    | cons p ps ih =>
      have hp := hps p (by simp only [List.mem_cons, true_or])
      have ih' := ih (fun x hx => hps x (List.mem_cons_of_mem _ hx))
      have h1 : 1 ≤ (pfadToks p.1).length := by
        match p.1, hp.1.1 with
        | [a], _ => simp only [pfadToks, List.length_cons, List.length_nil, Nat.zero_add, Std.le_refl]
        | a :: b :: cs, _ => simp only [pfadToks, List.cons_append, List.nil_append, List.length_cons, Nat.le_add_left]
      cases ps with
      | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_cons, List.map_nil, kommaToks, List.length_append, ge_iff_le]; omega
      | cons q qs => simp only [List.length_cons, List.map_cons, kommaToks, List.append_assoc, List.cons_append, List.nil_append, List.length_append, ge_iff_le] at ih' ⊢; omega
  simp only [fbI, druckItem, hW, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckItem (.concT ps) ++ rest = .wort "concurrent" :: .zeichen "{" ::
      (kommaToks (ps.map fun p => pfadToks p.1 ++ argToks p.2) ++ .zeichen "}" :: .zeichen ";" :: rest) := by
    simp only [druckItem, hW, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_concurrent]
  cases ps with
  | nil => simp only [parseNebenTief, nimmWort, strEq_self, ↓reduceIte, List.map_nil, kommaToks, List.nil_append, parsePfadListe, fordereZeichen]
  | cons p ps' =>
    have hp := hps p (by simp only [List.mem_cons, true_or])
    have hF' := startFolge_rund (p :: ps') (.zeichen ";" :: rest) F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hps (by omega)
    obtain ⟨a, us, hq1⟩ : ∃ a us, pfadToks p.1 = nameTok a :: us := by
      match p.1, hp.1.1 with
      | [a], _ => exact ⟨a, [], rfl⟩
      | a :: b :: cs, _ => exact ⟨a, _, rfl⟩
    have hk : kommaToks ((p :: ps').map fun p => pfadToks p.1 ++ argToks p.2) =
        nameTok a :: (kommaToks ((p :: ps').map fun p => pfadToks p.1 ++ argToks p.2)).tail := by
      cases ps' <;> simp only [List.map_cons, hq1, List.cons_append, List.map_nil, kommaToks, List.tail_cons, List.append_assoc, List.nil_append]
    rw [hk] at hF' ⊢
    simp only [List.cons_append, List.map_cons] at hF' ⊢
    simp only [parseNebenTief, nimmWort, strEq_self, ↓reduceIte, parsePfadListe, fordereZeichen, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hF']


theorem item_mod (segs : List String) (its : List SItemTief) (hs : PfadGut segs)
    (hits : ∀ it ∈ its, ItemBein it ∧ ItemKopf it) : ItemBein (.modT ("::".intercalate segs) its) := by
  intro rest F hF
  have hr := rohToks_pfad segs hs.1 hs.2
  have hd : druckItem (.modT ("::".intercalate segs) its) ++ rest = .wort "module" :: (pfadToks segs ++
      .zeichen "{" :: (druckItems its ++ .zeichen "}" :: rest)) := by
    simp only [druckItem, hr, List.cons_append, List.nil_append, List.append_assoc]
  simp only [fbI, druckItem, hr, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hP := nimmPfad_pfad segs (.zeichen "{" :: (druckItems its ++ .zeichen "}" :: rest)) hs.1
    (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
  have hI := items_rund its (.zeichen "}" :: rest) F' hits (Or.inr (Or.inl ⟨rest, rfl⟩)) (by omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_module]
  simp only [parseModulTief, nimmWort, strEq_self, ↓reduceIte, hP, fordereZeichen, hI]

/-! ### `atomic` -/

theorem platzListe_rund (ps : List SExpr) (hps : ∀ p ∈ ps, gut p = true) (R : List Token) (F : Nat)
    (hF : 8 * (druckPlaetze ps).length + 48 ≤ F) :
    parsePlatzListe F (.zeichen "{" :: (druckPlaetze ps ++ .zeichen "}" :: R)) = .ok (ps, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases ps with
  | nil => simp only [parsePlatzListe, fordereZeichen, strEq_self, ↓reduceIte, druckPlaetze, List.nil_append]
  | cons p ps' =>
    rw [druckPlaetze_eq] at hF ⊢
    have hL := predListe_rund (p :: ps') (.zeichen "}" :: R) F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hps
      ⟨rfl, rfl, rfl, (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩
      (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by omega)
    obtain ⟨t, ts, hd, -, -⟩ := druck_kopf_pred p (hps p (by simp only [List.mem_cons, true_or]))
    have hne : ∀ r, druckPredListe (p :: ps') ++ .zeichen "}" :: R ≠ .zeichen "}" :: r := by
      intro r e
      have : druckPredListe (p :: ps') = druckToks p ++ (druckPredListe (p :: ps')).drop (druckToks p).length := by
        cases ps' <;> simp only [druckPredListe, List.drop_length, List.append_nil, List.append_assoc, List.cons_append, List.nil_append, List.drop_left']
      rw [this, hd] at e
      simp only [List.length_cons, List.cons_append, List.append_assoc, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      have := druck_kopf p (hps p (by simp only [List.mem_cons, true_or]))
      obtain ⟨t', ts', hd', hk'⟩ := this
      rw [hd] at hd'; injection hd' with e1; subst e1; simp only [KopfGut, String.reduceEq, or_self] at hk'
    simp only [parsePlatzListe, fordereZeichen, strEq_self, ite_true]
    simp only [hne, hL]
    simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, strEq_self, ↓reduceIte]

/-- The order words of an atomic. -/
def istOrdnung (o : String) : Bool :=
  strEq o "acquire" || strEq o "release" || strEq o "seq" || strEq o "relaxed"

/-- A printable `atomic` tail. -/
def AtomGut (pub : Option (List SExpr)) (ord : Option String) : Prop :=
  (∀ ps, pub = some ps → ∀ p ∈ ps, gut p = true) ∧ (∀ o, ord = some o → istOrdnung o = true)

def atomTail (pub : Option (List SExpr)) (ord : Option String) (obs : Option String) : List Token :=
  (match pub with
    | some [] => [.wort "publishes", .wort "nothing"]
    | some ps => [.wort "publishes", .zeichen "{"] ++ druckPlaetze ps ++ [.zeichen "}"]
    | none => []) ++
  (match ord with
    | some o => [.wort o]
    | none => []) ++
  (match obs with
    | some o => [.wort "observed", .wort "by", nameTok o]
    | none => []) ++ [.zeichen ";"]

theorem atomRest_ende (f : Nat) (acc : String × STyp × Option (List SExpr) × Option String × Option String)
    (R : List Token) : parseAtomarRest (f + 1) acc (.zeichen ";" :: R) = .ok (acc, R) := by
  simp only [parseAtomarRest, fordereZeichen, strEq_self, ↓reduceIte]

theorem atomRest_obs (f : Nat) (a : String) (b : STyp) (c : Option (List SExpr)) (d : Option String)
    (e : Option String) (o : String) (R : List Token) :
    parseAtomarRest (f + 1) (a, b, c, d, e) (.wort "observed" :: .wort "by" :: nameTok o :: R) =
      parseAtomarRest f (a, b, c, d, some o) R := by
  simp [parseAtomarRest, nimmWort, strEq_self, nimmName, (by decide : strEq "observed" "publishes" = false), (by decide : strEq "observed" "acquire" = false), (by decide : strEq "observed" "release" = false), (by decide : strEq "observed" "seq" = false), (by decide : strEq "observed" "relaxed" = false)]

theorem atomRest_ord (f : Nat) (a : String) (b : STyp) (c : Option (List SExpr)) (d : Option String)
    (e : Option String) (o : String) (ho : istOrdnung o = true) (R : List Token) :
    parseAtomarRest (f + 1) (a, b, c, d, e) (.wort o :: R) = parseAtomarRest f (a, b, c, some o, e) R := by
  simp only [istOrdnung, Bool.or_eq_true, strEq_eq] at ho
  rcases ho with ((h | h) | h) | h <;> subst h
  · simp [parseAtomarRest, strEq_self, (by decide : strEq "acquire" "publishes" = false)]
  · simp [parseAtomarRest, strEq_self, (by decide : strEq "release" "publishes" = false),
      (by decide : strEq "release" "acquire" = false)]
  · simp [parseAtomarRest, strEq_self, (by decide : strEq "seq" "publishes" = false),
      (by decide : strEq "seq" "acquire" = false), (by decide : strEq "seq" "release" = false)]
  · simp [parseAtomarRest, strEq_self, (by decide : strEq "relaxed" "publishes" = false),
      (by decide : strEq "relaxed" "acquire" = false), (by decide : strEq "relaxed" "release" = false),
      (by decide : strEq "relaxed" "seq" = false)]

theorem atomRest_nichts (f : Nat) (a : String) (b : STyp) (c : Option (List SExpr)) (d : Option String)
    (e : Option String) (R : List Token) :
    parseAtomarRest (f + 1) (a, b, c, d, e) (.wort "publishes" :: .wort "nothing" :: R) =
      parseAtomarRest f (a, b, some [], d, e) R := by
  simp only [parseAtomarRest, strEq_self, ↓reduceIte]

theorem atomRest_liste (f : Nat) (a : String) (b : STyp) (c : Option (List SExpr)) (d : Option String)
    (e : Option String) (ps : List SExpr) (hps : ∀ p ∈ ps, gut p = true) (R : List Token)
    (hF : 8 * (druckPlaetze ps).length + 48 ≤ f) :
    parseAtomarRest (f + 1) (a, b, c, d, e) (.wort "publishes" :: .zeichen "{" ::
      (druckPlaetze ps ++ .zeichen "}" :: R)) = parseAtomarRest f (a, b, some ps, d, e) R := by
  have hL := platzListe_rund ps hps R f hF
  simp only [parseAtomarRest, strEq_self, ↓reduceIte, hL]

theorem item_atom (n : String) (t : STyp) (pub : Option (List SExpr)) (ord obs : Option String)
    (ht : TypGut t) (hg : AtomGut pub ord) : ItemBein (.atomT n t pub ord obs) := by
  intro rest F hF
  obtain ⟨hpub, hord⟩ := hg
  have hd : druckItem (.atomT n t pub ord obs) ++ rest = .wort "atomic" :: nameTok n :: .zeichen ":" ::
      (druckTyp t ++ (atomTail pub ord obs ++ rest)) := by
    simp only [druckItem, atomTail]
    rcases pub with _ | _ | ⟨p, ps⟩ <;> cases ord <;> cases obs <;> simp only [List.cons_append, List.nil_append, List.append_nil, List.append_assoc]
  have hlen : (druckItem (.atomT n t pub ord obs)).length = 3 + (druckTyp t).length +
      (atomTail pub ord obs).length := by
    simp only [druckItem, atomTail]
    rcases pub with _ | _ | ⟨p, ps⟩ <;> cases ord <;> cases obs <;> simp only [List.cons_append, List.nil_append, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.add_right_cancel_iff, List.append_assoc, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
  simp only [fbI, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hTF : TypFolge (atomTail pub ord obs ++ rest) := by
    have gen : ∀ (w : String) (X : List Token), w ≠ "in" → w ≠ "wrapping" → w ≠ "embeds" →
        w ≠ "rounded" → TypFolge (.wort w :: X) := by
      intro w X h1 h2 h3 h4
      have : strEq w "rounded" = false := by
        cases h : strEq w "rounded"
        · rfl
        · exact absurd ((strEq_eq _ _).mp h) h4
      refine ⟨?_, ?_, ?_, ?_, rfl, rfl, by simp only [ruhigGleit, this, Bool.not_false]⟩ <;> intro r e <;> simp only [List.cons.injEq, Token.wort.injEq, reduceCtorEq, false_and] at e <;> simp_all
    rcases pub with _ | _ | ⟨p, ps⟩
    · rcases ord with _ | o
      · cases obs
        · exact ⟨(by intro r e; simp only [atomTail, List.append_nil, List.nil_append, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [atomTail, List.append_nil, List.nil_append, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at e),
            (by intro r e; simp only [atomTail, List.append_nil, List.nil_append, List.cons_append, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [atomTail, List.append_nil, List.nil_append, List.cons_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩
        · exact gen "observed" _ (by decide) (by decide) (by decide) (by decide)
      · have ho := hord o rfl
        simp only [istOrdnung, Bool.or_eq_true, strEq_eq] at ho
        simp only [atomTail, List.nil_append, List.singleton_append, List.cons_append]
        rcases ho with ((h | h) | h) | h <;> subst h <;>
          exact gen _ _ (by decide) (by decide) (by decide) (by decide)
    · exact gen "publishes" _ (by decide) (by decide) (by decide) (by decide)
    · exact gen "publishes" _ (by decide) (by decide) (by decide) (by decide)
  have hT := parse_druckTyp t ht _ F' hTF (by simp only [fbT]; omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_atomic]
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [parseAtomarTief, nimmWort, strEq_self, ite_true, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende, fordereZeichen, hT]
  have hR : parseAtomarRest (F'' + 1) (n, t, none, none, none) (atomTail pub ord obs ++ rest) =
      .ok ((n, t, pub, ord, obs), rest) := by
    have stepE : ∀ (G : Nat) acc, 1 ≤ G → parseAtomarRest G acc (.zeichen ";" :: rest) = .ok (acc, rest) := by
      intro G acc hG; obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩; exact atomRest_ende G' acc rest
    have stepO : ∀ (G : Nat) (c : Option (List SExpr)) (d : Option String) (o : String) (R : List Token),
        1 ≤ G → parseAtomarRest G (n, t, c, d, none) (.wort "observed" :: .wort "by" :: nameTok o :: R) =
          parseAtomarRest (G - 1) (n, t, c, d, some o) R := by
      intro G c d o R hG; obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      exact atomRest_obs G' n t c d none o R
    have stepD : ∀ (G : Nat) (c : Option (List SExpr)) (o : String) (R : List Token), istOrdnung o = true →
        1 ≤ G → parseAtomarRest G (n, t, c, none, none) (.wort o :: R) =
          parseAtomarRest (G - 1) (n, t, c, some o, none) R := by
      intro G c o R ho hG; obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      exact atomRest_ord G' n t c none none o ho R
    have hlenT := hlen
    rcases pub with _ | _ | ⟨p, ps⟩
    · rcases ord with _ | o <;> rcases obs with _ | ob
      · simp only [atomTail, List.nil_append, List.cons_append]
        exact stepE _ _ (by omega)
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append]
        rw [stepO _ _ _ _ _ (by omega), stepE _ _ (by omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append]
        rw [stepD _ _ _ _ (hord o rfl) (by omega), stepE _ _ (by omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append]
        rw [stepD _ _ _ _ (hord o rfl) (by omega), stepO _ _ _ _ _ (by omega), stepE _ _ (by omega)]
    · rcases ord with _ | o <;> rcases obs with _ | ob
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_nichts, stepE _ _ (by simp only [atomTail, List.append_nil, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_nichts, stepO _ _ _ _ _ (by simp only [atomTail, List.append_nil, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepE _ _ (by simp only [atomTail, List.append_nil, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_nichts, stepD _ _ _ _ (hord o rfl) (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_nichts, stepD _ _ _ _ (hord o rfl) (by simp only [atomTail, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepO _ _ _ _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega), stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
    · have hps := hpub (p :: ps) rfl
      rcases ord with _ | o <;> rcases obs with _ | ob
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepO _ _ _ _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega), stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_nil, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepD _ _ _ _ (hord o rfl) (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepD _ _ _ _ (hord o rfl) (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega),
          stepO _ _ _ _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega), stepE _ _ (by simp only [atomTail, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega)]
  simp only [hR]

/-! ### `lock` -/

/-- The clauses of a lock behind its rank. -/
def lockTail (h sh : Option SExpr) (m : Option String) (inv : Option SExpr) : List Token :=
  (match h with
    | some e => [.wort "held", .zeichen "<="] ++ druckToks e ++ [.wort "ops"]
    | none => []) ++
  (match sh with
    | some e => [.wort "shared", .wort "held", .zeichen "<="] ++ druckToks e ++ [.wort "ops"]
    | none => []) ++
  (match m with
    | some w => [.wort "masks", nameTok w]
    | none => []) ++
  (match inv with
    | some p => [.wort "invariant"] ++ druckToks p
    | none => []) ++ [.zeichen ";"]

theorem lockTail_ruhig (h sh : Option SExpr) (m : Option String) (inv : Option SExpr) (rest : List Token) :
    ruhig (lockTail h sh m inv ++ rest) = true ∧ ruhigSuff (lockTail h sh m inv ++ rest) = true ∧
      ruhigGleit (lockTail h sh m inv ++ rest) = true := by
  cases h <;> cases sh <;> cases m <;> cases inv <;> exact ⟨rfl, rfl, rfl⟩

theorem item_lock (n : String) (ps : List SExpr) (rk : SExpr) (h sh : Option SExpr) (m : Option String)
    (inv : Option SExpr) (hps : ∀ p ∈ ps, gut p = true) (hrk : gut rk = true)
    (hh : ∀ e, h = some e → gut e = true) (hs : ∀ e, sh = some e → gut e = true)
    (hi : ∀ e, inv = some e → gut e = true) : ItemBein (.lockT n ps rk h sh m inv) := by
  intro rest F hF
  have hd : druckItem (.lockT n ps rk h sh m inv) ++ rest = .wort "lock" :: nameTok n :: .wort "protects" ::
      .zeichen "{" :: (druckPlaetze ps ++ .zeichen "}" :: .wort "rank" ::
        (druckToks rk ++ (lockTail h sh m inv ++ rest))) := by
    cases h <;> cases sh <;> cases m <;> cases inv <;> simp only [druckItem, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, lockTail]
  have hlen : (druckItem (.lockT n ps rk h sh m inv)).length = 6 + (druckPlaetze ps).length +
      (druckToks rk).length + (lockTail h sh m inv).length := by
    cases h <;> cases sh <;> cases m <;> cases inv <;> simp only [druckItem, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, lockTail, Nat.add_right_cancel_iff, Nat.reduceAdd] <;> omega
  simp only [fbI, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  obtain ⟨h1, h2, h3⟩ := lockTail_ruhig h sh m inv rest
  have hRk := ausdruck rk hrk (lockTail h sh m inv ++ rest) F' h1 h2 h3 (by omega)
  have hPL := platzListe_rund ps hps (.wort "rank" :: (druckToks rk ++ (lockTail h sh m inv ++ rest))) F'
    (by omega)
  have hE : ∀ e, gut e = true → (druckToks e).length ≤ (lockTail h sh m inv).length →
      ∀ X, parseOr F' (druckToks e ++ .wort "ops" :: X) = .ok (e, .wort "ops" :: X) :=
    fun e he hl X => ausdruck e he _ F' rfl rfl rfl (by omega)
  have hI : ∀ p, gut p = true → (druckToks p).length ≤ (lockTail h sh m inv).length →
      parsePred F' (druckToks p ++ .zeichen ";" :: rest) = .ok (p, .zeichen ";" :: rest) :=
    fun p hp hl => pred_druck p hp _ ⟨rfl, rfl, rfl, (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
      (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩ F' (by simp only [fb]; omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_lock]
  rcases h with _ | eh <;> rcases sh with _ | es <;> rcases m with _ | w <;> rcases inv with _ | ip
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, pure, Except.pure, fordereZeichen]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, (hI ip (hi ip rfl) (by simp [lockTail]; omega)), fordereZeichen]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, (hI ip (hi ip rfl) (by simp [lockTail]; omega)), fordereZeichen]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen, (hE es (hs es rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen, (hE es (hs es rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen, (hE es (hs es rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen, (hE es (hs es rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, (hI ip (hi ip rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, (hI ip (hi ip rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, (hE es (hs es rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, (hE es (hs es rfl) (by simp [lockTail]; omega)), List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, imp_self, implies_true, (hI ip (hi ip rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, (hE es (hs es rfl) (by simp [lockTail]; omega))]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp only [parseSperreTief, bind, Except.bind, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hPL, hRk, fordereZeichen, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), pure, Except.pure, (hE es (hs es rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega))]

/-! ### `table`: numbers as text, fields, edges, group invariants, parts -/

theorem lex_zahl_allein (n : Nat) : lex (toString n) = .ok [.num n, .ende] := by
  unfold lex
  rw [show (toString n).toList = Nat.toDigits 10 n by rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]]
  have hd := toDigits_ziffern n
  have hne : Nat.toDigits 10 n ≠ [] := Nat.toDigits_ne_nil
  obtain ⟨c, cs, hcs⟩ : ∃ c cs, Nat.toDigits 10 n = c :: cs := by
    cases h : Nat.toDigits 10 n with
    | nil => exact absurd h hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hc : istZiffer c = true := by rw [hcs] at hd; simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hd; exact hd.1
  have hlen : (toString n).length = cs.length + 1 := by
    rw [← String.length_toList, Nat.toString_eq_ofList_toDigits, String.toList_ofList, hcs]; rfl
  rw [hlen, hcs, scan_ziffer_kopf false c cs _ hc]
  have hk : scanZahlKopf (c :: cs) = zahlBasis 10 (c :: cs) := by
    cases cs with
    | nil => exact scanZahlKopf_eins c
    | cons d ds =>
      have : istZiffer d = true := by rw [hcs] at hd; simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hd; exact hd.2.1
      exact scanZahlKopf_dez c d ds (ziffer_kein_praefix this)
  rw [hk]
  have hz : nimmZiffern (c :: cs) 10 = (n, true, []) := by
    unfold nimmZiffern
    have := nimmZiffern_go (c :: cs) [] 0 false (by rw [← hcs]; exact hd)
    simp only [List.append_nil] at this
    rw [this, ← hcs, Nat.ofDigitChars_ten_toDigits]
    simp only [nimmZiffern.go, Bool.false_or, Prod.mk.injEq, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff, ne_eq, Nat.toDigits_ne_nil, not_false_eq_true, and_self]
  simp only [zahlBasis, hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte, BEq.rfl, zahlWeiter, Except.map, scan]

theorem rohToks_zahl (n : Nat) : rohToks (toString n) = [.num n] := by
  unfold rohToks; rw [lex_zahl_allein]; rfl

/-- A bit position as the printer writes it: one number or one name. -/
def PosGut (s : String) : Prop := (∃ n : Nat, s = toString n) ∨ nameForm s = true

theorem bitpos_rund (p : String) (h : PosGut p) (R : List Token) :
    parseBitpos (rohToks p ++ R) = .ok (p, R) := by
  rcases h with ⟨n, rfl⟩ | h
  · rw [rohToks_zahl]; rfl
  · rw [rohToks_name p h]
    unfold nameTok
    split <;> simp only [parseBitpos, List.cons_append, List.nil_append, nameText_wort, zeigeTok, nameText_ident]

/-- A printable field. -/
def FeldGut (f : SFeld) : Prop :=
  TypGut f.ftyp ∧ (∀ p, f.pos = some p → PosGut p) ∧ (∀ e, f.wo = some e → gut e = true)

/-- The options of a field behind its type. -/
def feldRestToks (f : SFeld) : List Token :=
  (match f.pos with
    | some p => [.zeichen "@"] ++ rohToks p
    | none => []) ++
  (match f.bezug with
    | some n => [.wort "offset_into", nameTok n]
    | none => []) ++
  (match f.wo with
    | some p => [.wort "where"] ++ druckToks p
    | none => []) ++
  (if f.reserviert then [.wort "reserved"] else []) ++
  (if f.byOps then [.wort "by", .wort "ops"] else [])

theorem druckFeld_eq (f : SFeld) :
    druckFeld f = [nameTok f.fname, .zeichen ":"] ++ druckTyp f.ftyp ++ feldRestToks f := by
  simp only [druckFeld, List.cons_append, List.nil_append, List.append_assoc, feldRestToks, List.cons.injEq, List.append_cancel_left_eq, true_and]; rfl


/-- What follows a field: `,` or `}`. -/
def FeldEnde (R : List Token) : Prop := (∃ r, R = .zeichen "," :: r) ∨ (∃ r, R = .zeichen "}" :: r)

theorem feldRest_ende (f : Nat) (R : List Token) (hR : FeldEnde R) :
    parseFeldRest (f + 1) R = .ok ((none, none, none, false, false), R) := by
  rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp only [parseFeldRest, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]

theorem feldRest_by (f : Nat) (R X : List Token) (p b : Option String) (w : Option SExpr) (r y : Bool)
    (h : parseFeldRest f R = .ok ((p, b, w, r, y), X)) :
    parseFeldRest (f + 1) (.wort "by" :: .wort "ops" :: R) = .ok ((p, b, w, r, true), X) := by
  simp [parseFeldRest, h, strEq_self, (by decide : strEq "by" "offset_into" = false),
    (by decide : strEq "by" "where" = false), (by decide : strEq "by" "reserved" = false),
    (by decide : strEq "ops" "ops" = true)]

theorem feldRest_res (f : Nat) (R X : List Token) (p b : Option String) (w : Option SExpr) (r y : Bool)
    (h : parseFeldRest f R = .ok ((p, b, w, r, y), X)) :
    parseFeldRest (f + 1) (.wort "reserved" :: R) = .ok ((p, b, w, true, y), X) := by
  simp [parseFeldRest, h, strEq_self, (by decide : strEq "reserved" "offset_into" = false),
    (by decide : strEq "reserved" "where" = false)]

theorem feldRest_wo (f : Nat) (e : SExpr) (R X : List Token) (p b : Option String) (w : Option SExpr)
    (r y : Bool) (hP : parsePred f (druckToks e ++ R) = .ok (e, R))
    (h : parseFeldRest f R = .ok ((p, b, w, r, y), X)) :
    parseFeldRest (f + 1) (.wort "where" :: (druckToks e ++ R)) = .ok ((p, b, some e, r, y), X) := by
  simp [parseFeldRest, h, hP, strEq_self, (by decide : strEq "where" "offset_into" = false)]

theorem feldRest_bezug (f : Nat) (n : String) (R X : List Token) (p b : Option String) (w : Option SExpr)
    (r y : Bool) (h : parseFeldRest f R = .ok ((p, b, w, r, y), X)) :
    parseFeldRest (f + 1) (.wort "offset_into" :: nameTok n :: R) = .ok ((p, some n, w, r, y), X) := by
  by_cases hn : n = "Self"
  · subst hn
    have e : nameTok "Self" = .wort "Self" := by decide
    rw [e]; simp only [parseFeldRest, strEq_self, ↓reduceIte, zeigeTok, h]
  · have : strEq n "Self" = false := strEq_ne hn
    rcases nameTok_cases n with hh | hh <;> rw [hh] <;> simp only [parseFeldRest, strEq_self, ↓reduceIte, zeigeTok, this, Bool.false_eq_true, nameText_wort, h, nameText_ident]

theorem feldRest_pos (f : Nat) (q : String) (hq : PosGut q) (R X : List Token) (p b : Option String)
    (w : Option SExpr) (r y : Bool) (h : parseFeldRest f R = .ok ((p, b, w, r, y), X)) :
    parseFeldRest (f + 1) (.zeichen "@" :: (rohToks q ++ R)) = .ok ((some q, b, w, r, y), X) := by
  simp only [parseFeldRest, bitpos_rund q hq R, h]

theorem feldRest_rund (fd : SFeld) (hfd : FeldGut fd) (R : List Token) (hR : FeldEnde R) (F : Nat)
    (hF : 8 * (feldRestToks fd).length + 60 ≤ F) :
    parseFeldRest F (feldRestToks fd ++ R) = .ok ((fd.pos, fd.bezug, fd.wo, fd.reserviert, fd.byOps), R) := by
  obtain ⟨-, hpos, hwo⟩ := hfd
  obtain ⟨name, typ, pos, bezug, wo, res, byo⟩ := fd
  simp only at hpos hwo ⊢
  have hPF : PredFolge R ∧ (∀ r, R ≠ .zeichen "," :: r → True) := by
    refine ⟨?_, fun _ _ => trivial⟩
    rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
      exact ⟨rfl, rfl, rfl, (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩
  -- layer by layer, from the end
  have L5 : ∀ G, 2 ≤ G → parseFeldRest G ((if byo then [Token.wort "by", .wort "ops"] else []) ++ R) =
      .ok ((none, none, none, false, byo), R) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    cases byo
    · simpa using feldRest_ende (G' + 1) R hR
    · simpa using feldRest_by (G' + 1) R R none none none false false (feldRest_ende G' R hR)
  have L4 : ∀ G, 3 ≤ G → parseFeldRest G ((if res then [Token.wort "reserved"] else []) ++
      ((if byo then [Token.wort "by", .wort "ops"] else []) ++ R)) = .ok ((none, none, none, res, byo), R) := by
    intro G hG
    cases res
    · simpa using L5 G (by omega)
    · obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      simpa using feldRest_res G' _ R none none none false byo (L5 G' (by omega))
  have hPF4 : PredFolge ((if res then [Token.wort "reserved"] else []) ++
      ((if byo then [Token.wort "by", .wort "ops"] else []) ++ R)) := by
    cases res <;> cases byo <;> simp only [ite_true, Bool.false_eq_true, ite_false, List.nil_append,
      List.singleton_append, List.cons_append]
    · exact hPF.1
    all_goals exact ⟨rfl, rfl, rfl, (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and] at e)⟩
  have hlen45 : ((if res then [Token.wort "reserved"] else []) ++
      ((if byo then [Token.wort "by", .wort "ops"] else []) ++ R)).length ≤ 3 + R.length := by
    cases res <;> cases byo <;> simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, Nat.le_add_left, List.cons_append, List.length_cons] <;> omega
  rcases pos with _ | q <;> rcases bezug with _ | n <;> rcases wo with _ | e
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    have := L4 F (by omega)
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
    have he := hwo e rfl
    have hPe := pred_druck e he _ hPF4 (G + 0) (by simp only [fb]; omega)
    have := feldRest_wo (G + 0) e _ _ none none none res byo hPe (L4 G (by omega))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
    have := feldRest_bezug (G + 0) n _ _ none none none res byo (L4 G (by omega))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 2 := ⟨F - 2, by omega⟩
    have he := hwo e rfl
    have hPe := pred_druck e he _ hPF4 (G + 0) (by simp only [fb]; omega)
    have := feldRest_bezug (G + 1) n _ _ none none (some e) res byo (feldRest_wo (G + 0) e _ _ none none none res byo hPe (L4 G (by omega)))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 1 := ⟨F - 1, by omega⟩
    have := feldRest_pos (G + 0) q (hpos q rfl) _ _ none none none res byo (L4 G (by omega))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 2 := ⟨F - 2, by omega⟩
    have he := hwo e rfl
    have hPe := pred_druck e he _ hPF4 (G + 0) (by simp only [fb]; omega)
    have := feldRest_pos (G + 1) q (hpos q rfl) _ _ none none (some e) res byo (feldRest_wo (G + 0) e _ _ none none none res byo hPe (L4 G (by omega)))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 2 := ⟨F - 2, by omega⟩
    have := feldRest_pos (G + 1) q (hpos q rfl) _ _ none (some n) none res byo (feldRest_bezug (G + 0) n _ _ none none none res byo (L4 G (by omega)))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this
  · simp only [feldRestToks, List.nil_append, List.singleton_append, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.length_nil] at hF ⊢
    obtain ⟨G, rfl⟩ : ∃ G, F = G + 3 := ⟨F - 3, by omega⟩
    have he := hwo e rfl
    have hPe := pred_druck e he _ hPF4 (G + 0) (by simp only [fb]; omega)
    have := feldRest_pos (G + 2) q (hpos q rfl) _ _ none (some n) (some e) res byo (feldRest_bezug (G + 1) n _ _ none none (some e) res byo (feldRest_wo (G + 0) e _ _ none none none res byo hPe (L4 G (by omega))))
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, Nat.add_zero] using this


theorem feldRest_typFolge (fd : SFeld) (R : List Token) (hR : FeldEnde R) :
    TypFolge (feldRestToks fd ++ R) := by
  have gen : ∀ (w : String) (X : List Token), w ≠ "in" → w ≠ "wrapping" → w ≠ "embeds" →
      w ≠ "rounded" → TypFolge (.wort w :: X) := by
    intro w X h1 h2 h3 h4
    have : strEq w "rounded" = false := by
      cases h : strEq w "rounded"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) h4
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, by simp only [ruhigGleit, this, Bool.not_false]⟩ <;> intro r e <;> simp only [List.cons.injEq, Token.wort.injEq, reduceCtorEq, false_and] at e <;> simp_all
  obtain ⟨name, typ, pos, bezug, wo, res, byo⟩ := fd
  rcases pos with _ | q
  · rcases bezug with _ | n
    · rcases wo with _ | e
      · cases res
        · cases byo
          · simp only [feldRestToks, ite_false, Bool.false_eq_true, List.nil_append]
            rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
              exact ⟨(by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
                (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩
          · exact gen "by" _ (by decide) (by decide) (by decide) (by decide)
        · exact gen "reserved" _ (by decide) (by decide) (by decide) (by decide)
      · exact gen "where" _ (by decide) (by decide) (by decide) (by decide)
    · exact gen "offset_into" _ (by decide) (by decide) (by decide) (by decide)
  · exact ⟨(by intro x e; simp only [feldRestToks, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [feldRestToks, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, reduceCtorEq, false_and] at e),
      (by intro x e; simp only [feldRestToks, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, reduceCtorEq, false_and] at e), (by intro x e; simp only [feldRestToks, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩

theorem feld_rund (fd : SFeld) (hfd : FeldGut fd) (R : List Token) (hR : FeldEnde R) (F : Nat)
    (hF : 8 * (druckFeld fd).length + 61 ≤ F) : parseFeld F (druckFeld fd ++ R) = .ok (fd, R) := by
  rw [druckFeld_eq] at hF ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hT := parse_druckTyp fd.ftyp hfd.1 (feldRestToks fd ++ R) F' (feldRest_typFolge fd R hR)
    (by simp only [fbT]; omega)
  have hRe := feldRest_rund fd hfd R hR F' (by omega)
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  simp only [parseFeld, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hT, hRe]

theorem feldKopf (fd : SFeld) (X : List Token) : ∃ ts, druckFeld fd ++ X = nameTok fd.fname :: ts := by
  rw [druckFeld_eq]; exact ⟨_, rfl⟩

theorem felder_rund : ∀ (fs : List SFeld) (R : List Token) (F : Nat), fs ≠ [] → (∀ fd ∈ fs, FeldGut fd) →
    8 * (druckFelder fs).length + 62 ≤ F →
    parseFeldFolge F (druckFelder fs ++ .zeichen "}" :: R) = .ok (fs, R) := by
  intro fs
  induction fs with
  | nil => intro _ _ h; exact absurd rfl h
  | cons fd fs ih =>
    intro R F _ hg hF
    have hfd := hg fd (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases fs with
    | nil =>
      simp only [druckFelder] at hF ⊢
      have hP := feld_rund fd hfd (.zeichen "}" :: R) (Or.inr ⟨R, rfl⟩) F' (by omega)
      simp only [parseFeldFolge, hP, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, fordereZeichen, strEq_self, ↓reduceIte]
    | cons fd2 fs2 =>
      have hd : druckFelder (fd :: fd2 :: fs2) = druckFeld fd ++ .zeichen "," :: druckFelder (fd2 :: fs2) := by
        simp only [druckFelder, List.append_assoc, List.cons_append, List.nil_append]
      rw [hd] at hF ⊢
      simp only [List.length_append, List.length_cons] at hF
      have hP := feld_rund fd hfd (.zeichen "," :: (druckFelder (fd2 :: fs2) ++ .zeichen "}" :: R))
        (Or.inl ⟨_, rfl⟩) F' (by omega)
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
      obtain ⟨ts, hts⟩ : ∃ ts, druckFelder (fd2 :: fs2) ++ .zeichen "}" :: R = nameTok fd2.fname :: ts := by
        cases fs2 with
        | nil => simpa [druckFelder] using feldKopf fd2 (.zeichen "}" :: R)
        | cons x xs =>
          obtain ⟨ts, h⟩ := feldKopf fd2 (.zeichen "," :: (druckFelder (x :: xs) ++ .zeichen "}" :: R))
          exact ⟨ts, by simp only [druckFelder, List.append_assoc, List.cons_append, List.nil_append] at h ⊢; exact h⟩
      simp only [List.append_assoc, List.cons_append] at hP ⊢
      rw [hts] at hP hR ⊢
      unfold parseFeldFolge
      simp only [hP, hR]
      rcases nameTok_cases fd2.fname with h | h <;> rw [h] <;> rfl

theorem feldListe_rund (fs : List SFeld) (hg : ∀ fd ∈ fs, FeldGut fd) (R : List Token) (F : Nat)
    (hF : 8 * (druckFelder fs).length + 63 ≤ F) :
    parseFeldListe F (.zeichen "{" :: (druckFelder fs ++ .zeichen "}" :: R)) = .ok (fs, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases fs with
  | nil => simp only [parseFeldListe, fordereZeichen, strEq_self, ↓reduceIte, druckFelder, List.nil_append]
  | cons fd fs' =>
    have hFF := felder_rund (fd :: fs') R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hg (by omega)
    obtain ⟨ts, hts⟩ : ∃ ts, druckFelder (fd :: fs') ++ .zeichen "}" :: R = nameTok fd.fname :: ts := by
      cases fs' with
      | nil => simpa [druckFelder] using feldKopf fd (.zeichen "}" :: R)
      | cons x xs =>
        obtain ⟨ts, h⟩ := feldKopf fd (.zeichen "," :: (druckFelder (x :: xs) ++ .zeichen "}" :: R))
        exact ⟨ts, by simp only [druckFelder, List.append_assoc, List.cons_append, List.nil_append] at h ⊢; exact h⟩
    rw [hts] at hFF ⊢
    simp only [parseFeldListe, fordereZeichen, strEq_self, ↓reduceIte, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hFF]

/-- An edge kind of a `tree`. -/
def KanteGut (k : String × String) : Prop :=
  k.1 = "parent" ∨ k.1 = "child" ∨ k.1 = "sibling"

theorem kante_rund (a b : String) (h : KanteGut (a, b)) (R : List Token) :
    parseKante (.wort a :: nameTok b :: R) = .ok ((a, b), R) := by
  rcases h with h | h | h <;> simp only at h <;> subst h <;> simp only [parseKante, strEq_self, Bool.true_or, ↓reduceIte, nimmName, nameText_nameTok, Bool.or_true]

theorem kanten_rund : ∀ (ks : List (String × String)) (R : List Token) (F : Nat), ks ≠ [] →
    (∀ k ∈ ks, KanteGut k) → ks.length ≤ F →
    parseKanten F (druckKanten ks ++ .zeichen "}" :: R) = .ok (ks, .zeichen "}" :: R) := by
  intro ks
  induction ks with
  | nil => intro _ _ h; exact absurd rfl h
  | cons k ks ih =>
    intro R F _ hg hF
    obtain ⟨a, b⟩ := k
    have hk := kante_rund a b (hg (a, b) (by simp only [List.mem_cons, true_or]))
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    cases ks with
    | nil => simp only [parseKanten, druckKanten, List.cons_append, List.nil_append, hk, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]
    | cons k2 ks2 =>
      obtain ⟨a2, b2⟩ := k2
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      obtain ⟨ts, hts⟩ : ∃ ts, druckKanten ((a2, b2) :: ks2) ++ .zeichen "}" :: R = .wort a2 :: ts := by
        cases ks2 <;> exact ⟨_, by simp only [druckKanten, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl⟩
      have hd : druckKanten ((a, b) :: (a2, b2) :: ks2) = [.wort a, nameTok b, .zeichen ","] ++
          druckKanten ((a2, b2) :: ks2) := by simp only [druckKanten, List.cons_append, List.nil_append]
      rw [hd]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [hts] at hR ⊢
      unfold parseKanten
      simp only [hk, hR]

theorem baum_rund (ks : List (String × String)) (hne : ks ≠ []) (hg : ∀ k ∈ ks, KanteGut k)
    (R : List Token) (F : Nat) (hF : ks.length + 1 ≤ F) :
    parseBaum F (.zeichen "{" :: (druckKanten ks ++ .zeichen "}" :: R)) = .ok (ks, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hK := kanten_rund ks R F' hne hg (by omega)
  simp only [parseBaum, fordereZeichen, strEq_self, ↓reduceIte, hK]


/-- A printable group invariant: printable cost and predicate, a raw proof text without `:` and
    braces. -/
def InvGut (i : SGruppenInv) : Prop :=
  gut i.kosten = true ∧ PredGut i.pred ∧
    ∀ h, i.proof = some h → RohText (fun t => t = .zeichen ":" ∨ t = .zeichen "{" ∨ t = .zeichen "}") h

theorem gruppenInv_rund (i : SGruppenInv) (hi : InvGut i) (R : List Token) (F : Nat)
    (hF : 8 * (druckGruppenInv i).length + 60 ≤ F) :
    parseGruppenInv F (druckGruppenInv i ++ R) = .ok (i, R) := by
  obtain ⟨hk, hp, hpr⟩ := hi
  obtain ⟨name, kosten, online, proof, pred⟩ := i
  simp only at hk hp hpr ⊢
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by simp only [druckGruppenInv, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add] at hF; omega⟩
  have hon : ∀ X, (Token.wort (if online then "online" else "offline") :: X) =
      .wort (if online then "online" else "offline") :: X := fun _ => rfl
  have hm : (strEq (if online then "online" else "offline") "online" ||
      strEq (if online then "online" else "offline") "offline") = true := by cases online <;> decide
  have hmo : strEq (if online then "online" else "offline") "online" = online := by cases online <;> decide
  have hoff : online = false → strEq (if online then "online" else "offline") "offline" = true := by
    intro h; subst h; decide
  cases proof with
  | none =>
    simp only [druckGruppenInv, List.length_append, List.length_cons, List.length_nil] at hF
    have hK := ausdruck kosten hk (.zeichen ")" :: .wort "runs" ::
      .wort (if online then "online" else "offline") :: .zeichen ":" :: (druckToks pred ++ .zeichen ";" :: R))
      (F' + 1) rfl rfl rfl (by omega)
    have hP := pred_voll pred hp (.zeichen ";" :: R) ⟨rfl, rfl, rfl, (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e),
      (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩ F' (by simp only [bP]; omega)
    simp only [druckGruppenInv, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    simp only [parseGruppenInv, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, nimmKostenO, nameText_ident, fordereZeichen, hK, hmo, Bool.or_eq_true, parseInvRest, hP, ite_eq_left_iff, not_or, Bool.not_eq_true, reduceCtorEq, imp_false, not_and, Bool.not_eq_false]
    all_goals exact hoff
  | some h =>
    obtain ⟨ts, rfl, hts⟩ := hpr _ rfl
    have hroh := rohToks_render ts (fun t ht => (hts t ht).1)
    simp only [druckGruppenInv, hroh, List.length_append, List.length_cons, List.length_nil] at hF
    have hK := ausdruck kosten hk (.zeichen ")" :: .wort "runs" ::
      .wort (if online then "online" else "offline") :: .wort "by" ::
        (ts ++ .zeichen ":" :: (druckToks pred ++ .zeichen ";" :: R)))
      (F' + 1) rfl rfl rfl (by omega)
    have hP := pred_voll pred hp (.zeichen ";" :: R) ⟨rfl, rfl, rfl, (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e),
      (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e)⟩ F' (by simp only [bP]; omega)
    have hN := nimmBisZeichen_roh ":" ts (druckToks pred ++ .zeichen ";" :: R)
      (fun t ht => ⟨(hts t ht).1, fun e => (hts t ht).2 (Or.inr (Or.inl e)),
        fun e => (hts t ht).2 (Or.inr (Or.inr e)), fun e => (hts t ht).2 (Or.inl e)⟩)
    simp only [druckGruppenInv, hroh, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append]
    simp only [parseGruppenInv, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, nimmKostenO, nameText_ident, fordereZeichen, hK, hmo, Bool.or_eq_true, parseInvRest, hN, hP, ite_eq_left_iff, not_or, Bool.not_eq_true, reduceCtorEq, imp_false, not_and, Bool.not_eq_false]
    all_goals exact hoff

/-- A printable part of a table. -/
def TeilGut : STabTeil → Prop
  | .tConst _ t v => TypGut t ∧ KonstGut v
  | .tSlot fs => ∀ fd ∈ fs, FeldGut fd
  | .tInv i => InvGut i
  | .tOps ns => ns ≠ []
  | .tTree ks => ks ≠ [] ∧ ∀ k ∈ ks, KanteGut k
  | .tBusy _ => True

theorem tabTeile_ende (f : Nat) (R : List Token) :
    parseTabTeile (f + 1) (.zeichen "}" :: R) = .ok ([], .zeichen "}" :: R) := by
  simp only [parseTabTeile]

theorem tabTeil_rund (t : STabTeil) (ht : TeilGut t) (R X : List Token) (ps : List STabTeil) (f : Nat)
    (hR : parseTabTeile f R = .ok (ps, X)) (hf : 8 * (druckTabTeil t).length + 63 ≤ f) :
    parseTabTeile (f + 1) (druckTabTeil t ++ R) = .ok (t :: ps, X) := by
  cases t with
  | tConst n ty v =>
    obtain ⟨hty, hv⟩ := ht
    simp only [druckTabTeil, List.length_append, List.length_cons, List.length_nil] at hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    have hT := typ_gleich ty hty (druckKonstWert v ++ .zeichen ";" :: R) f' (by simp only [fbT]; omega)
    have hV := konst_rund v hv (.zeichen ";" :: R) f' rfl rfl rfl (by simp only [fbK]; omega)
    have hK : parseKonstNach (f' + 1) (nameTok n :: .zeichen ":" :: (druckTyp ty ++ .zeichen "=" ::
        (druckKonstWert v ++ .zeichen ";" :: R))) = .ok (.constT n ty v, R) := by
      simp only [parseKonstNach, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hT, hV]
    simp only [druckTabTeil, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    unfold parseTabTeile
    simp only [(by decide : strEq "const" "const" = true), ite_true, hK, hR]
  | tSlot fs =>
    simp only [druckTabTeil, List.length_append, List.length_cons, List.length_nil] at hf
    have hL := feldListe_rund fs ht R f (by omega)
    simp only [druckTabTeil, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    unfold parseTabTeile
    simp only [(by decide : strEq "slot" "const" = false), (by decide : strEq "slot" "slot" = true),
      Bool.false_eq_true, ite_false, ite_true, hL, hR]
  | tInv i =>
    simp only [druckTabTeil] at hf
    have hI := gruppenInv_rund i ht R f (by omega)
    obtain ⟨ts, hts⟩ : ∃ ts, druckGruppenInv i = .wort "invariant" :: ts := ⟨_, rfl⟩
    simp only [druckTabTeil]
    rw [hts] at hI ⊢
    simp only [List.cons_append] at hI ⊢
    unfold parseTabTeile
    simp only [(by decide : strEq "invariant" "const" = false),
      (by decide : strEq "invariant" "slot" = false), (by decide : strEq "invariant" "invariant" = true),
      Bool.false_eq_true, ite_false, ite_true, hI, hR]
  | tOps ns =>
    have hlen : ns.length ≤ (druckNamen ns).length := by
      clear hf ht hR
      induction ns with
      | nil => simp only [List.length_nil, Nat.zero_le]
      | cons n ns ih => cases ns with
        | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckNamen, Std.le_refl]
        | cons m ms => simp only [List.length_cons, druckNamen, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega
    simp only [druckTabTeil, List.length_append, List.length_cons, List.length_nil] at hf
    have hN := namen_rund ns (.zeichen ";" :: R) f ht (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by omega)
    simp only [druckTabTeil, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    unfold parseTabTeile
    simp only [(by decide : strEq "ops" "const" = false), (by decide : strEq "ops" "slot" = false),
      (by decide : strEq "ops" "invariant" = false), (by decide : strEq "ops" "ops" = true),
      Bool.false_eq_true, ite_false, ite_true, hN, fordereZeichen, strEq_self, hR]
  | tTree ks =>
    obtain ⟨hne, hg⟩ := ht
    have hlen : ks.length ≤ (druckKanten ks).length := by
      clear hf hne hg hR
      induction ks with
      | nil => simp only [List.length_nil, Nat.zero_le]
      | cons k ks ih => cases ks with
        | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckKanten, Nat.reduceAdd, Nat.reduceLeDiff]
        | cons k2 ks2 => simp only [List.length_cons, druckKanten, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega
    simp only [druckTabTeil, List.length_append, List.length_cons, List.length_nil] at hf
    have hB := baum_rund ks hne hg R f (by omega)
    simp only [druckTabTeil, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    unfold parseTabTeile
    simp only [(by decide : strEq "tree" "const" = false), (by decide : strEq "tree" "slot" = false),
      (by decide : strEq "tree" "invariant" = false), (by decide : strEq "tree" "ops" = false),
      (by decide : strEq "tree" "tree" = true), Bool.false_eq_true, ite_false, ite_true, hB, hR]
  | tBusy n =>
    simp only [druckTabTeil, List.cons_append, List.nil_append]
    unfold parseTabTeile
    simp only [(by decide : strEq "occupied" "const" = false), (by decide : strEq "occupied" "slot" = false), (by decide : strEq "occupied" "invariant" = false), (by decide : strEq "occupied" "ops" = false), (by decide : strEq "occupied" "tree" = false), (by decide : strEq "occupied" "occupied" = true), Bool.false_eq_true, ite_false, ite_true, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende, fordereZeichen, strEq_self, hR]

theorem tabTeile_rund : ∀ (ps : List STabTeil) (R : List Token) (F : Nat), (∀ t ∈ ps, TeilGut t) →
    8 * (druckTabTeile ps).length + 64 ≤ F →
    parseTabTeile F (druckTabTeile ps ++ .zeichen "}" :: R) = .ok (ps, .zeichen "}" :: R) := by
  intro ps
  induction ps with
  | nil =>
    intro R F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    exact tabTeile_ende F' R
  | cons t ps ih =>
    intro R F hg hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckTabTeile, List.length_append] at hF ⊢
    have h1 : 1 ≤ (druckTabTeil t).length := by cases t <;> simp only [druckTabTeil, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.le_add_left, druckGruppenInv, Nat.reduceAdd, Nat.reduceLeDiff]
    have hR := ih R F' (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
    rw [List.append_assoc]
    exact tabTeil_rund t (hg t (by simp only [List.mem_cons, true_or])) _ _ ps F' hR (by omega)


/-! ### The table head -/

def cntToks : Option SExpr → List Token
  | some e => [.wort "count"] ++ druckToks e
  | none => []

def nameOptToks (w : String) : Option String → List Token
  | some b => [.wort w, nameTok b]
  | none => []

def shToks (sh : Bool) : List Token := if sh then [.wort "shared"] else []

theorem tabKopf_ende (f : Nat) (R : List Token) :
    parseTabellenKopf (f + 1) (.zeichen "{" :: R) = .ok ((none, none, none, none, false), .zeichen "{" :: R) := by
  simp only [parseTabellenKopf]

theorem tabKopf_shared (f : Nat) (R X : List Token) (c : Option SExpr) (v b o : Option String) (g : Bool)
    (h : parseTabellenKopf f R = .ok ((c, v, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "shared" :: R) = .ok ((c, v, b, o, true), X) := by
  simp [parseTabellenKopf, h, strEq_self, (by decide : strEq "shared" "count" = false),
    (by decide : strEq "shared" "from" = false),
    (by decide : strEq "shared" "backed" = false), (by decide : strEq "shared" "owner" = false)]

theorem tabKopf_owner (f : Nat) (n : String) (R X : List Token) (c : Option SExpr) (v b o : Option String)
    (g : Bool) (h : parseTabellenKopf f R = .ok ((c, v, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "owner" :: nameTok n :: R) = .ok ((c, v, b, some n, g), X) := by
  simp [parseTabellenKopf, h, strEq_self, nimmName, (by decide : strEq "owner" "count" = false),
    (by decide : strEq "owner" "from" = false), (by decide : strEq "owner" "backed" = false)]

theorem tabKopf_backed (f : Nat) (n : String) (R X : List Token) (c : Option SExpr) (v b o : Option String)
    (g : Bool) (h : parseTabellenKopf f R = .ok ((c, v, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "backed" :: nameTok n :: R) = .ok ((c, v, some n, o, g), X) := by
  simp [parseTabellenKopf, h, strEq_self, nimmName, (by decide : strEq "backed" "count" = false),
    (by decide : strEq "backed" "from" = false)]

theorem tabKopf_from (f : Nat) (n : String) (R X : List Token) (c : Option SExpr) (v b o : Option String)
    (g : Bool) (h : parseTabellenKopf f R = .ok ((c, v, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "from" :: nameTok n :: R) = .ok ((c, some n, b, o, g), X) := by
  simp [parseTabellenKopf, h, strEq_self, nimmName, (by decide : strEq "from" "count" = false)]

theorem tabKopf_count (f : Nat) (e : SExpr) (R X : List Token) (c : Option SExpr) (v b o : Option String)
    (g : Bool) (hO : parseOr f (druckToks e ++ R) = .ok (e, R))
    (h : parseTabellenKopf f R = .ok ((c, v, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "count" :: (druckToks e ++ R)) = .ok ((some e, v, b, o, g), X) := by
  simp only [parseTabellenKopf, strEq_self, ↓reduceIte, hO, h]

theorem tabKopf_rund (cnt : Option SExpr) (von backed owner : Option String) (sh : Bool)
    (hc : ∀ e, cnt = some e → gut e = true) (R : List Token) (F : Nat)
    (hF : 8 * (cntToks cnt ++ nameOptToks "from" von ++ nameOptToks "backed" backed ++ nameOptToks "owner" owner ++
      shToks sh).length + 40 ≤ F) :
    parseTabellenKopf F (cntToks cnt ++ nameOptToks "from" von ++ nameOptToks "backed" backed ++
      nameOptToks "owner" owner ++ shToks sh ++ .zeichen "{" :: R) =
      .ok ((cnt, von, backed, owner, sh), .zeichen "{" :: R) := by
  have L1 : ∀ G, 2 ≤ G → parseTabellenKopf G (shToks sh ++ .zeichen "{" :: R) =
      .ok ((none, none, none, none, sh), .zeichen "{" :: R) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    cases sh
    · simpa [shToks] using tabKopf_ende (G' + 1) R
    · simpa [shToks] using tabKopf_shared (G' + 1) _ _ none none none none false (tabKopf_ende G' R)
  have L2 : ∀ G, 3 ≤ G → parseTabellenKopf G (nameOptToks "owner" owner ++ (shToks sh ++ .zeichen "{" :: R)) =
      .ok ((none, none, none, owner, sh), .zeichen "{" :: R) := by
    intro G hG
    cases owner with
    | none => simpa [nameOptToks] using L1 G (by omega)
    | some o =>
      obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      simpa [nameOptToks] using tabKopf_owner G' o _ _ none none none none sh (L1 G' (by omega))
  have L3 : ∀ G, 4 ≤ G → parseTabellenKopf G (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++
      (shToks sh ++ .zeichen "{" :: R))) = .ok ((none, none, backed, owner, sh), .zeichen "{" :: R) := by
    intro G hG
    cases backed with
    | none => simpa [nameOptToks] using L2 G (by omega)
    | some b =>
      obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      simpa [nameOptToks] using tabKopf_backed G' b _ _ none none none owner sh (L2 G' (by omega))
  have L4 : ∀ G, 5 ≤ G → parseTabellenKopf G (nameOptToks "from" von ++ (nameOptToks "backed" backed ++
      (nameOptToks "owner" owner ++ (shToks sh ++ .zeichen "{" :: R)))) =
      .ok ((none, von, backed, owner, sh), .zeichen "{" :: R) := by
    intro G hG
    cases von with
    | none => simpa [nameOptToks] using L3 G (by omega)
    | some p =>
      obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      simpa [nameOptToks] using tabKopf_from G' p _ _ none none backed owner sh (L3 G' (by omega))
  simp only [List.append_assoc] at hF ⊢
  cases cnt with
  | none => simpa [cntToks] using L4 F (by simp only [cntToks, List.nil_append, List.length_append] at hF; omega)
  | some e =>
    have he := hc e rfl
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [cntToks, List.cons_append, List.nil_append, List.length_cons, List.length_append] at hF; omega⟩
    have hrX : ruhig (nameOptToks "from" von ++ (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++
          (shToks sh ++ .zeichen "{" :: R)))) = true ∧
        ruhigSuff (nameOptToks "from" von ++ (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++
          (shToks sh ++ .zeichen "{" :: R)))) = true ∧
        ruhigGleit (nameOptToks "from" von ++ (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++
          (shToks sh ++ .zeichen "{" :: R)))) = true := by
      cases von <;> cases backed <;> cases owner <;> cases sh <;> exact ⟨rfl, rfl, rfl⟩
    have hO := ausdruck e he _ F' hrX.1 hrX.2.1 hrX.2.2 (by simp only [cntToks, List.cons_append, List.nil_append, List.length_cons, List.length_append, Nat.reduceLeDiff] at hF; omega)
    have := tabKopf_count F' e _ _ none von backed owner sh hO (L4 F' (by simp only [cntToks, List.cons_append, List.nil_append, List.length_cons, List.length_append, Nat.reduceLeDiff] at hF; omega))
    simpa [cntToks] using this

theorem item_table (n : String) (von : Option String) (cnt : Option SExpr) (backed owner : Option String)
    (sh : Bool) (parts : List STabTeil) (hc : ∀ e, cnt = some e → gut e = true) (hp : ∀ t ∈ parts, TeilGut t) :
    ItemBein (.tableT n von cnt backed owner sh parts) := by
  intro rest F hF
  have hd : druckItem (.tableT n von cnt backed owner sh parts) ++ rest = .wort "table" :: nameTok n ::
      (cntToks cnt ++ nameOptToks "from" von ++ nameOptToks "backed" backed ++ nameOptToks "owner" owner ++
        shToks sh ++ .zeichen "{" :: (druckTabTeile parts ++ .zeichen "}" :: rest)) := by
    cases cnt <;> cases von <;> cases backed <;> cases owner <;> cases sh <;>
      simp only [druckItem, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, List.append_assoc, cntToks, nameOptToks, shToks]
  have hlen : (druckItem (.tableT n von cnt backed owner sh parts)).length = 2 +
      (cntToks cnt ++ nameOptToks "from" von ++ nameOptToks "backed" backed ++ nameOptToks "owner" owner ++
        shToks sh).length + 1 + (druckTabTeile parts).length + 1 := by
    cases cnt <;> cases von <;> cases backed <;> cases owner <;> cases sh <;>
      simp only [druckItem, List.append_nil, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, cntToks, nameOptToks, shToks, Nat.add_zero, Nat.reduceAdd, Nat.add_right_cancel_iff, List.append_assoc] <;> omega
  simp only [fbI, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hK := tabKopf_rund cnt von backed owner sh hc (druckTabTeile parts ++ .zeichen "}" :: rest) F' (by omega)
  have hT := tabTeile_rund parts rest F' hp (by omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_table]
  simp only [List.append_assoc] at hK
  simp only [parseTabellenTief, nimmWort, strEq_self, ↓reduceIte, List.append_assoc, nimmName, nameText_nameTok, hK, fordereZeichen, hT]


/-! ### `entry` -/

/-- What follows a register binding: `,` or `}`. -/
def BindEnde (R : List Token) : Prop := (∃ r, R = .zeichen "," :: r) ∨ (∃ r, R = .zeichen "}" :: r)

theorem regBind_rund (b : SRegBind) (R : List Token) (hR : BindEnde R) :
    parseRegBind (druckRegBind b ++ R) = .ok (b, R) := by
  cases b with
  | reg a =>
    rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
      simp [druckRegBind, parseRegBind, nimmName, (by decide : strEq "," "=" = false), (by decide : strEq "," ":" = false), (by decide : strEq "}" "=" = false), (by decide : strEq "}" ":" = false)]
  | binds a c => simp only [parseRegBind, nimmName, druckRegBind, List.cons_append, List.nil_append, nameText_nameTok, strEq_self, Bool.true_or, ↓reduceIte]

theorem regBindFolge_rund : ∀ (bs : List SRegBind) (R : List Token) (F : Nat), bs ≠ [] → bs.length ≤ F →
    parseRegBindFolge F (druckRegBinds bs ++ .zeichen "}" :: R) = .ok (bs, R) := by
  intro bs
  induction bs with
  | nil => intro _ _ h; exact absurd rfl h
  | cons b bs ih =>
    intro R F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    cases bs with
    | nil =>
      have hB := regBind_rund b (.zeichen "}" :: R) (Or.inr ⟨R, rfl⟩)
      simp only [druckRegBinds]
      simp only [parseRegBindFolge, hB, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, fordereZeichen, strEq_self, ↓reduceIte]
    | cons c cs =>
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      have hd : druckRegBinds (b :: c :: cs) = druckRegBind b ++ .zeichen "," :: druckRegBinds (c :: cs) := by
        simp only [druckRegBinds, List.append_assoc, List.cons_append, List.nil_append]
      rw [hd, List.append_assoc]
      have hB := regBind_rund b (.zeichen "," :: (druckRegBinds (c :: cs) ++ .zeichen "}" :: R)) (Or.inl ⟨_, rfl⟩)
      obtain ⟨a, ts, hts⟩ : ∃ a ts, druckRegBinds (c :: cs) ++ .zeichen "}" :: R = nameTok a :: ts := by
        cases c with
        | reg x => exact ⟨x, (druckRegBinds (.reg x :: cs) ++ .zeichen "}" :: R).tail,
            by cases cs <;> simp only [druckRegBinds, druckRegBind, List.cons_append, List.nil_append, List.tail_cons]⟩
        | binds x y => exact ⟨x, (druckRegBinds (.binds x y :: cs) ++ .zeichen "}" :: R).tail,
            by cases cs <;> simp only [druckRegBinds, druckRegBind, List.cons_append, List.nil_append, List.tail_cons]⟩
      try simp only [List.cons_append] at hB
      simp only [List.append_assoc, List.cons_append]
      rw [hts] at hB hR ⊢
      unfold parseRegBindFolge
      simp only [hB, hR]
      rcases nameTok_cases a with h | h <;> rw [h] <;> rfl

theorem regBindListe_rund (bs : List SRegBind) (R : List Token) (F : Nat) (hF : bs.length + 2 ≤ F) :
    parseRegBindListe F (.zeichen "{" :: (druckRegBinds bs ++ .zeichen "}" :: R)) = .ok (bs, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases bs with
  | nil => simp only [parseRegBindListe, fordereZeichen, strEq_self, ↓reduceIte, druckRegBinds, List.nil_append]
  | cons b bs' =>
    have hR := regBindFolge_rund (b :: bs') R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (by omega)
    obtain ⟨a, ts, hts⟩ : ∃ a ts, druckRegBinds (b :: bs') ++ .zeichen "}" :: R = nameTok a :: ts := by
      cases b with
      | reg x => exact ⟨x, (druckRegBinds (.reg x :: bs') ++ .zeichen "}" :: R).tail,
          by cases bs' <;> simp only [druckRegBinds, druckRegBind, List.cons_append, List.nil_append, List.tail_cons]⟩
      | binds x y => exact ⟨x, (druckRegBinds (.binds x y :: bs') ++ .zeichen "}" :: R).tail,
          by cases bs' <;> simp only [druckRegBinds, druckRegBind, List.cons_append, List.nil_append, List.tail_cons]⟩
    rw [hts] at hR ⊢
    simp only [parseRegBindListe, fordereZeichen, strEq_self, ↓reduceIte, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hR]

theorem namenKlammer_rund (ns : List String) (R : List Token) (F : Nat) (hF : ns.length + 2 ≤ F) :
    parseNamenEingeklammert F (druckNamenKlammer ns ++ R) = .ok (ns, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases ns with
  | nil => simp only [parseNamenEingeklammert, fordereZeichen, druckNamenKlammer, druckNamen, List.append_nil, List.cons_append, List.nil_append, strEq_self, ↓reduceIte]
  | cons n ns' =>
    have hN := namen_rund (n :: ns') (.zeichen "}" :: R) F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by omega)
    obtain ⟨ts, hts⟩ : ∃ ts, druckNamen (n :: ns') ++ .zeichen "}" :: R = nameTok n :: ts := by
      cases ns' <;> exact ⟨_, by simp only [druckNamen, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl⟩
    simp only [druckNamenKlammer, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    rw [hts] at hN ⊢
    simp only [parseNamenEingeklammert, fordereZeichen, strEq_self, ↓reduceIte, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hN, Token.zeichen.injEq, String.reduceEq]

/-- A printable entry: printable vector and stack-index expressions, a `nested` mode of one word,
    a dispatch path. -/
def EingangGut (e : SEingang) : Prop :=
  (∀ v, e.vektor = some v → gut v = true) ∧ (∀ x, e.ist = some x → gut x = true) ∧
    (e.nest = none ∨ e.nest = some "never" ∨ e.nest = some "masked") ∧ e.dispatch ≠ []

def vekToks : Option SExpr → List Token
  | some v => [.wort "vector"] ++ druckToks v
  | none => []

def istToks : Option SExpr → List Token
  | some x => [.wort "ist"] ++ druckToks x
  | none => []

def nestToks : Option String → List Token
  | some n => [.wort "nested"] ++ rohToks n
  | none => []

def cpuToks (b : Bool) : List Token := if b then [.wort "per", .wort "cpu"] else []

theorem druckEingang_eq (e : SEingang) : druckEingang e = [.wort "entry", nameTok e.name] ++ vekToks e.vektor ++
    nameOptToks "via" e.via ++ [.wort "arch", nameTok e.arch, .zeichen "{", .wort "regs", .wort "in", .zeichen "{"] ++
    druckRegBinds e.regIn ++ [.zeichen "}", .wort "regs", .wort "out", .zeichen "{"] ++ druckRegBinds e.regOut ++
    [.zeichen "}", .wort "preserves"] ++ druckNamenKlammer e.erhaelt ++ [.wort "clobbers"] ++
    druckNamenKlammer e.kills ++ [.wort "stack", nameTok e.stapel] ++ cpuToks e.perCpu ++ istToks e.ist ++
    nestToks e.nest ++ [.wort "dispatch"] ++ pfadToks e.dispatch ++ [.zeichen ";", .zeichen "}"] := by
  simp only [druckEingang, List.cons_append, List.nil_append, List.append_assoc, vekToks, nameOptToks, cpuToks, istToks, nestToks, List.cons.injEq, true_and]; rfl

theorem eingangKopf_arch (f : Nat) (a : String) (R : List Token) :
    parseEingangKopf (f + 1) (.wort "arch" :: nameTok a :: R) = .ok ((none, none, a), R) := by
  simp [parseEingangKopf, nimmName, strEq_self, (by decide : strEq "arch" "vector" = false), (by decide : strEq "arch" "via" = false)]

theorem eingangKopf_via (f : Nat) (m : String) (X R : List Token) (v : Option SExpr) (w : Option String)
    (a : String) (h : parseEingangKopf f X = .ok ((v, w, a), R)) :
    parseEingangKopf (f + 1) (.wort "via" :: nameTok m :: X) = .ok ((v, some m, a), R) := by
  simp [parseEingangKopf, nimmName, strEq_self, h, (by decide : strEq "via" "vector" = false)]

theorem eingangKopf_vector (f : Nat) (e : SExpr) (X R : List Token) (v : Option SExpr) (w : Option String)
    (a : String) (hO : parseOr f (druckToks e ++ X) = .ok (e, X)) (h : parseEingangKopf f X = .ok ((v, w, a), R)) :
    parseEingangKopf (f + 1) (.wort "vector" :: (druckToks e ++ X)) = .ok ((some e, w, a), R) := by
  simp only [parseEingangKopf, strEq_self, ↓reduceIte, hO, h]

theorem eingangKopf_rund (vek : Option SExpr) (via : Option String) (a : String) (hv : ∀ v, vek = some v → gut v = true)
    (R : List Token) (F : Nat) (hF : 8 * (vekToks vek).length + 40 ≤ F) :
    parseEingangKopf F (vekToks vek ++ (nameOptToks "via" via ++ (.wort "arch" :: nameTok a :: R))) =
      .ok ((vek, via, a), R) := by
  have L1 : ∀ G, 2 ≤ G → parseEingangKopf G (nameOptToks "via" via ++ (.wort "arch" :: nameTok a :: R)) =
      .ok ((none, via, a), R) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    cases via with
    | none => simpa [nameOptToks] using eingangKopf_arch (G' + 1) a R
    | some m => simpa [nameOptToks] using eingangKopf_via (G' + 1) m _ R none none a (eingangKopf_arch G' a R)
  cases vek with
  | none => simpa [vekToks] using L1 F (by simp only [vekToks, List.length_nil, Nat.mul_zero, Nat.zero_add] at hF; omega)
  | some v =>
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [vekToks, List.cons_append, List.nil_append, List.length_cons] at hF; omega⟩
    have hrX : ruhig (nameOptToks "via" via ++ (.wort "arch" :: nameTok a :: R)) = true ∧
        ruhigSuff (nameOptToks "via" via ++ (.wort "arch" :: nameTok a :: R)) = true ∧
        ruhigGleit (nameOptToks "via" via ++ (.wort "arch" :: nameTok a :: R)) = true := by
      cases via <;> exact ⟨rfl, rfl, rfl⟩
    have hO := ausdruck v (hv v rfl) _ F' hrX.1 hrX.2.1 hrX.2.2 (by simp only [vekToks, List.cons_append, List.nil_append, List.length_cons, Nat.reduceLeDiff] at hF; omega)
    simpa [vekToks] using eingangKopf_vector F' v _ R none via a hO (L1 F' (by simp only [vekToks, List.cons_append, List.nil_append, List.length_cons, Nat.reduceLeDiff] at hF; omega))

theorem dispatch_rund (f : Nat) (dp : List String) (hdp : dp ≠ []) (R : List Token) :
    parseEingangDispatch (f + 1) (.wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) = .ok (dp, R) := by
  have hP := nimmPfad_pfad dp (.zeichen ";" :: R) hdp (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
  simp only [parseEingangDispatch, nimmWort, strEq_self, ↓reduceIte, hP, fordereZeichen]

theorem rohToks_never : rohToks "never" = [.wort "never"] := by
  rw [rohToks_name "never" (by decide)]; simp only [nameTok, List.cons.injEq, ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false, and_true]; decide

theorem rohToks_masked : rohToks "masked" = [.wort "masked"] := by
  rw [rohToks_name "masked" (by decide)]; simp only [nameTok, List.cons.injEq, ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false, and_true]; decide

theorem nestOpt_rund (f : Nat) (nest : Option String) (hn : nest = none ∨ nest = some "never" ∨ nest = some "masked")
    (X : List Token) :
    parseEingangNestedOpt (f + 1) (nestToks nest ++ .wort "dispatch" :: X) = .ok (nest, .wort "dispatch" :: X) := by
  rcases hn with rfl | rfl | rfl
  · simp [nestToks, parseEingangNestedOpt, (by decide : strEq "dispatch" "nested" = false)]
  · have : rohToks "never" = [.wort "never"] := by rw [rohToks_name "never" (by decide)]; simp only [nameTok, List.cons.injEq, ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false, and_true]; decide
    simp only [parseEingangNestedOpt, nestToks, this, List.cons_append, List.nil_append, strEq_self, ↓reduceIte, Bool.true_or]
  · have : rohToks "masked" = [.wort "masked"] := by rw [rohToks_name "masked" (by decide)]; simp only [nameTok, List.cons.injEq, ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false, and_true]; decide
    simp [nestToks, this, parseEingangNestedOpt, strEq_self, (by decide : strEq "masked" "never" = false)]

theorem nested_rund (f : Nat) (nest : Option String) (hn : nest = none ∨ nest = some "never" ∨ nest = some "masked")
    (dp : List String) (hdp : dp ≠ []) (R : List Token) :
    parseEingangNested (f + 2) (nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) =
      .ok ((nest, dp), R) := by
  simp only [parseEingangNested, nestOpt_rund f nest hn, dispatch_rund f dp hdp R]

theorem restNach_rund (f : Nat) (ist : Option SExpr) (hi : ∀ x, ist = some x → gut x = true) (nest : Option String)
    (hn : nest = none ∨ nest = some "never" ∨ nest = some "masked") (dp : List String) (hdp : dp ≠ [])
    (R : List Token) (hF : 8 * (istToks ist).length + 40 ≤ f) :
    parseEingangRestNach (f + 3) (istToks ist ++ (nestToks nest ++ .wort "dispatch" ::
      (pfadToks dp ++ .zeichen ";" :: R))) = .ok ((ist, nest, dp), R) := by
  have hN := nested_rund f nest hn dp hdp R
  have hN1 := nested_rund (f + 1) nest hn dp hdp R
  have hkopf : ∃ w X, nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R) = .wort w :: X ∧
      w ≠ "ist" := by
    rcases hn with rfl | rfl | rfl
    · exact ⟨"dispatch", _, rfl, by decide⟩
    · exact ⟨"nested", _, by simp only [nestToks, rohToks_never, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl, by decide⟩
    · exact ⟨"nested", _, by simp only [nestToks, rohToks_masked, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl, by decide⟩
  cases ist with
  | none =>
    obtain ⟨w, X, hw, hne⟩ := hkopf
    have : strEq w "ist" = false := by
      cases h : strEq w "ist"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) hne
    simp only [istToks, List.nil_append]
    rw [hw] at hN ⊢
    simp only [parseEingangRestNach, this, Bool.false_eq_true, ↓reduceIte, hN]
  | some x =>
    have hx := hi x rfl
    have hrX : ruhig (nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) = true ∧
        ruhigSuff (nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) = true ∧
        ruhigGleit (nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) = true := by
      rcases hn with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
    have hO := ausdruck x hx _ (f + 2) hrX.1 hrX.2.1 hrX.2.2 (by simp only [istToks, List.cons_append, List.nil_append, List.length_cons] at hF; omega)
    simp only [istToks, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    simp only [parseEingangRestNach, strEq_self, ↓reduceIte, hO, hN]


theorem rest_rund (f : Nat) (st : String) (cpu : Bool) (ist : Option SExpr) (hi : ∀ x, ist = some x → gut x = true)
    (nest : Option String) (hn : nest = none ∨ nest = some "never" ∨ nest = some "masked") (dp : List String)
    (hdp : dp ≠ []) (R : List Token) (hF : 8 * (istToks ist).length + 40 ≤ f) :
    parseEingangRest (f + 4) (.wort "stack" :: nameTok st :: (cpuToks cpu ++ (istToks ist ++ (nestToks nest ++
      .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R))))) = .ok ((st, cpu, ist, nest, dp), R) := by
  have hRN := restNach_rund f ist hi nest hn dp hdp R hF
  cases cpu with
  | true =>
    simp only [cpuToks, ite_true, List.cons_append, List.nil_append]
    simp only [parseEingangRest, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hRN]
  | false =>
    simp only [cpuToks, Bool.false_eq_true, ite_false, List.nil_append]
    have hkopf : ∃ w X, istToks ist ++ (nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) =
        .wort w :: X ∧ w ≠ "per" := by
      cases ist with
      | some x => exact ⟨"ist", _, rfl, by decide⟩
      | none =>
        rcases hn with rfl | rfl | rfl
        · exact ⟨"dispatch", _, rfl, by decide⟩
        · exact ⟨"nested", _, by simp only [istToks, nestToks, rohToks_never, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl, by decide⟩
        · exact ⟨"nested", _, by simp only [istToks, nestToks, rohToks_masked, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl, by decide⟩
    obtain ⟨w, X, hw, hne⟩ := hkopf
    have : strEq w "per" = false := by
      cases h : strEq w "per"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) hne
    rw [hw] at hRN ⊢
    simp only [parseEingangRest, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, this, Bool.false_eq_true, hRN]

theorem druckRegBinds_len (bs : List SRegBind) : bs.length ≤ (druckRegBinds bs).length := by
  induction bs with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons b bs ih =>
    cases bs with
    | nil => cases b <;> simp only [List.length_cons, List.length_nil, Nat.zero_add, druckRegBinds, druckRegBind, Nat.reduceAdd, Nat.reduceLeDiff, Std.le_refl]
    | cons c cs =>
      simp only [druckRegBinds, List.length_append, List.length_cons] at ih ⊢
      cases b <;> simp only [druckRegBind, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] <;> omega

theorem druckNamen_len (ns : List String) : ns.length ≤ (druckNamen ns).length := by
  induction ns with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons n ns ih => cases ns with
    | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckNamen, Std.le_refl]
    | cons m ms => simp only [List.length_cons, druckNamen, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega

theorem item_entry (e : SEingang) (he : EingangGut e) : ItemBein (.entryT e) := by
  intro rest F hF
  obtain ⟨hv, hi, hn, hdp⟩ := he
  have hlenRI := druckRegBinds_len e.regIn
  have hlenRO := druckRegBinds_len e.regOut
  have hlenE := druckNamen_len e.erhaelt
  have hlenK := druckNamen_len e.kills
  simp only [fbI, druckItem, druckEingang_eq, druckNamenKlammer, List.length_append, List.length_cons,
    List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 7 := ⟨F - 7, by omega⟩
  have hK := eingangKopf_rund e.vektor e.via e.arch hv (.zeichen "{" :: .wort "regs" :: .wort "in" :: .zeichen "{" ::
    (druckRegBinds e.regIn ++ .zeichen "}" :: .wort "regs" :: .wort "out" :: .zeichen "{" :: (druckRegBinds e.regOut ++
      .zeichen "}" :: .wort "preserves" :: (druckNamenKlammer e.erhaelt ++ .wort "clobbers" ::
        (druckNamenKlammer e.kills ++ .wort "stack" :: nameTok e.stapel :: (cpuToks e.perCpu ++ (istToks e.ist ++
          (nestToks e.nest ++ .wort "dispatch" :: (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest)))))))))
    (F' + 4) (by omega)
  have hRI := regBindListe_rund e.regIn (.wort "regs" :: .wort "out" :: .zeichen "{" :: (druckRegBinds e.regOut ++
      .zeichen "}" :: .wort "preserves" :: (druckNamenKlammer e.erhaelt ++ .wort "clobbers" ::
        (druckNamenKlammer e.kills ++ .wort "stack" :: nameTok e.stapel :: (cpuToks e.perCpu ++ (istToks e.ist ++
          (nestToks e.nest ++ .wort "dispatch" :: (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest))))))))
    (F' + 4) (by omega)
  have hRO := regBindListe_rund e.regOut (.wort "preserves" :: (druckNamenKlammer e.erhaelt ++ .wort "clobbers" ::
        (druckNamenKlammer e.kills ++ .wort "stack" :: nameTok e.stapel :: (cpuToks e.perCpu ++ (istToks e.ist ++
          (nestToks e.nest ++ .wort "dispatch" :: (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest)))))))
    (F' + 4) (by omega)
  have hE := namenKlammer_rund e.erhaelt (.wort "clobbers" ::
        (druckNamenKlammer e.kills ++ .wort "stack" :: nameTok e.stapel :: (cpuToks e.perCpu ++ (istToks e.ist ++
          (nestToks e.nest ++ .wort "dispatch" :: (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest))))))
    (F' + 4) (by omega)
  have hKi := namenKlammer_rund e.kills (.wort "stack" :: nameTok e.stapel :: (cpuToks e.perCpu ++ (istToks e.ist ++
          (nestToks e.nest ++ .wort "dispatch" :: (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest)))))
    (F' + 4) (by omega)
  have hR := rest_rund F' e.stapel e.perCpu e.ist hi e.nest hn e.dispatch hdp (.zeichen "}" :: rest)
    (by omega)
  have hd : druckItem (.entryT e) ++ rest = .wort "entry" :: nameTok e.name :: (vekToks e.vektor ++
      (nameOptToks "via" e.via ++ (.wort "arch" :: nameTok e.arch :: (.zeichen "{" :: .wort "regs" :: .wort "in" ::
        .zeichen "{" :: (druckRegBinds e.regIn ++ .zeichen "}" :: .wort "regs" :: .wort "out" :: .zeichen "{" ::
          (druckRegBinds e.regOut ++ .zeichen "}" :: .wort "preserves" :: (druckNamenKlammer e.erhaelt ++
            .wort "clobbers" :: (druckNamenKlammer e.kills ++ .wort "stack" :: nameTok e.stapel ::
              (cpuToks e.perCpu ++ (istToks e.ist ++ (nestToks e.nest ++ .wort "dispatch" ::
                (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest)))))))))))) := by
    simp only [druckItem, druckEingang_eq, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_entry]
  simp only [druckNamenKlammer, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    at hRI hRO hE hKi hK ⊢
  simp only [parseEingangTief, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hK, fordereZeichen, hRI, hRO, hE, hKi, hR]



/-! ### `group` -/

theorem gruppenInvs_rund : ∀ (ivs : List SGruppenInv), (∀ i ∈ ivs, InvGut i) → ∀ (R : List Token) (F : Nat),
    8 * (druckGruppenInvs ivs).length + 61 ≤ F →
    parseGruppenInvListe F (druckGruppenInvs ivs ++ .zeichen "}" :: R) = .ok (ivs, .zeichen "}" :: R) := by
  intro ivs
  induction ivs with
  | nil =>
    intro _ R F hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseGruppenInvListe, druckGruppenInvs, List.nil_append]
  | cons i ivs ih =>
    intro hg R F hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckGruppenInvs, List.length_append] at hF
    have h1 : 1 ≤ (druckGruppenInv i).length := by simp only [druckGruppenInv, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.le_add_left]
    have hI := gruppenInv_rund i (hg i (by simp only [List.mem_cons, true_or])) (druckGruppenInvs ivs ++ .zeichen "}" :: R) F' (by omega)
    have hR := ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) R F' (by omega)
    have hd : druckGruppenInv i = .wort "invariant" :: (druckGruppenInv i).tail := rfl
    simp only [druckGruppenInvs, List.append_assoc]
    rw [hd] at hI ⊢
    simp only [List.cons_append] at hI ⊢
    simp only [parseGruppenInvListe, strEq_self, ↓reduceIte, hI, hR]

/-- The tail of a group: `;` without invariants, the invariants in braces otherwise. -/
def gruppeRestToks : List SGruppenInv → List Token
  | [] => [.zeichen ";"]
  | ivs => [.zeichen "{"] ++ druckGruppenInvs ivs ++ [.zeichen "}"]

theorem item_group (n : String) (ms : List String) (ivs : List SGruppenInv) (hms : ms ≠ [])
    (hivs : ∀ i ∈ ivs, InvGut i) : ItemBein (.groupT n ms ivs) := by
  intro rest F hF
  have hd : druckItem (.groupT n ms ivs) ++ rest = .wort "group" :: nameTok n :: .wort "over" :: .zeichen "{" ::
      (druckNamen ms ++ .zeichen "}" :: (gruppeRestToks ivs ++ rest)) := by
    cases ivs <;> simp only [druckItem, druckNamenKlammer, List.cons_append, List.nil_append, List.append_assoc, gruppeRestToks]
  have hlen : (druckItem (.groupT n ms ivs)).length = 5 + (druckNamen ms).length + (gruppeRestToks ivs).length := by
    cases ivs <;> simp only [druckItem, druckNamenKlammer, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, gruppeRestToks, Nat.add_right_cancel_iff] <;> omega
  have hms' : ms.length ≤ (druckNamen ms).length := by
    clear hF hd hlen hms
    induction ms with
    | nil => simp only [List.length_nil, Nat.zero_le]
    | cons m ms ih => cases ms with
      | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckNamen, Std.le_refl]
      | cons a as => simp only [List.length_cons, druckNamen, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega
  simp only [fbI, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hN := namen_rund ms (.zeichen "}" :: (gruppeRestToks ivs ++ rest)) F' hms (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
    (by omega)
  have hRest : parseGruppeRest F' (gruppeRestToks ivs ++ rest) = .ok (ivs, rest) := by
    obtain ⟨G, rfl⟩ : ∃ G, F' = G + 1 := ⟨F' - 1, by omega⟩
    cases ivs with
    | nil => simp only [parseGruppeRest, gruppeRestToks, List.cons_append, List.nil_append]
    | cons i is =>
      simp only [gruppeRestToks, List.length_append, List.length_cons, List.length_nil] at hF
      have hL := gruppenInvs_rund (i :: is) hivs rest G (by omega)
      simp only [gruppeRestToks, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
      simp only [parseGruppeRest, hL, fordereZeichen, strEq_self, ↓reduceIte]
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_group]
  simp only [parseGruppeTief, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, fordereZeichen, hN, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, hRest]

end Gabbro.Grammatik.Parser
