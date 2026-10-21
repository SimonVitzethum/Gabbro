/-
  File:      Grammatik/Parser/Round/RundlaufItem.lean
  Subject:   Layer L2c: items read back -- `parseItemsTief`/`parseTopTief` of the item printer's tokens
             (`druckItem`, Print/Item.lean) return the items -- and the composition of all layers:
             `parseTopTief` of the lexed rendered text of printable items is `.ok items`.

  The class `ItemGut` (stated in full below) covers: `module` (a `::` path of name-shaped non-table
  words, nested items), `use`, `const` (expression or nested array values), `static` (with
  `aligned`, `section`, `shared`), `table` (count/backed/owner/shared head; `const`, `slot` fields
  with bit position, `offset_into`, `where`, `reserved`, `by ops`; group invariants; `ops`; `tree`;
  `occupied`), `fn` with its whole head (modifier, parameters, result, `or`
  channel, the clauses `requires`, `ensures`, `maintains`, `refines`, `effects`, `costs`,
  `decreases`, `payload`, `section`, `arch`, `advances`) and a block body or `;`, `lock` (with
  `held`, `shared held`, `masks`, `invariant`), `atomic` (with `publishes`, an order, `observed
  by`), `reason`, `concurrent`. Every expression is `gut`, every type `TypGut`, every body
  `AnwGut .block`, predicates (`requires`/`ensures`/`invariant`, place lists) ride `pred_druck`.

  Main statements: `rundlauf_items` (`parseItemsTief` before `}`, the end marker or nothing),
  `parseTopTief_druck` (the whole program reader, fuel `8 * length + 32`), and
  `rundlauf_programm` -- for printable items whose print is lexically clean,
  `parseTopTief` of `lex (renderText (druckItems its))` is `.ok its`.
-/
import Grammatik.Parser.Round.RundlaufPred

namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

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
  simp [parseItemTief, e1, e2]

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

theorem parseItemKopf_const (f : Nat) (n : String) (rest : List Token) :
    parseItemKopfTief (f + 1) (.wort "const" :: .ident n :: rest) =
      parseKonstNach f (.ident n :: rest) := by
  have hm : istMod "const" = false := by decide
  simp only [parseItemKopfTief, sammleModifikatoren, hm, Bool.false_eq_true, ite_false, ite_true,
    (by decide : strEq "const" "module" = false), (by decide : strEq "const" "use" = false),
    (by decide : strEq "const" "fn" = false), (by decide : strEq "const" "translator" = false),
    (by decide : strEq "const" "profile" = false), (by decide : strEq "const" "requires" = false),
    (by decide : strEq "const" "concurrent" = false), (by decide : strEq "const" "type" = false),
    (by decide : strEq "const" "const" = true), nimmWort, strEq_self]

/-! ### Paths, constant values -/

theorem nimmPfad_pfad (p : List String) (R : List Token) (hp : p ≠ []) (hR : ∀ r, R ≠ .zeichen "::" :: r) :
    nimmPfad (pfadToks p ++ R) = .ok (p, R) := by
  match p, hp with
  | [a], _ => simp [pfadToks, nimmPfad, nameText, sammleSeg_stop2 [a] R hR]
  | a :: b :: cs, _ =>
    have := sammleSeg_pfad (b :: cs) [a] R (by simp) hR
    simp only [pfadToks, List.cons_append, List.nil_append, List.singleton_append] at this ⊢
    simp [nimmPfad, nameText, this]

/-- A printable constant value: an expression, or an array literal of printable values. -/
inductive KonstGut : SKonstWert → Prop
  | one (e : SExpr) : gut e = true → KonstGut (.one e)
  | rows (xs : List SKonstWert) : (∀ x ∈ xs, KonstGut x) → KonstGut (.rows xs)

def fbK (v : SKonstWert) : Nat := 8 * (druckKonstWert v).length + 40

theorem druckKonstWerte_cons (x : SKonstWert) (xs : List SKonstWert) (h : xs ≠ []) :
    druckKonstWert.druckKonstWerte (x :: xs) =
      druckKonstWert x ++ .zeichen "," :: druckKonstWert.druckKonstWerte xs := by
  match xs, h with
  | y :: ys, _ => simp [druckKonstWert.druckKonstWerte]

theorem konst_kopf (v : SKonstWert) (hv : KonstGut v) :
    ∃ t ts, druckKonstWert v = t :: ts ∧ t ≠ .zeichen "]" ∧ t ≠ .zeichen "}" := by
  cases hv with
  | one e he =>
    obtain ⟨t, ts, hd, hk⟩ := druck_kopf e he
    refine ⟨t, ts, by simp [druckKonstWert, hd], ?_, ?_⟩ <;> intro e' <;> subst e' <;> simp [KopfGut] at hk
  | rows xs _ => exact ⟨.zeichen "[", _, by simp [druckKonstWert]; rfl, by simp, by simp⟩

theorem konst_len (v : SKonstWert) (hv : KonstGut v) : 1 ≤ (druckKonstWert v).length := by
  obtain ⟨t, ts, hd, -⟩ := konst_kopf v hv
  rw [hd]; simp

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
      simp [KopfGut] at hk
    simp only [druckKonstWert]
    rw [parseKonstWert.eq_def]
    simp only [hnb]
    simp [hO, bind, Except.bind, pure, Except.pure]
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
        simp [druckKonstWert.druckKonstWerte, parseConstRows]
      | cons y ys ihy =>
        intro hsub G hG
        have hyx := hsub y (by simp)
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
          simp [hV, bind, Except.bind, pure, Except.pure]
        | cons z zs =>
          rw [druckKonstWerte_cons y (z :: zs) (by simp)] at hG ⊢
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
          simp [hV, hR, bind, Except.bind, pure, Except.pure]
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbK] at hF; omega⟩
    have hH := hrows xs (fun x hx => hx) F' (by simp only [fbK, druckKonstWert] at hF; simp at hF; omega)
    simp only [druckKonstWert, List.cons_append, List.append_assoc, List.singleton_append]
    simp [parseKonstWert, hH, bind, Except.bind, pure, Except.pure]

/-! ### Effects -/

/-- The table words an expression print can start with. -/
def exprWortKopf (w : String) : Bool :=
  strEq w "true" || strEq w "false" || strEq w "sizeof" || strEq w "lenof" || strEq w "aligned" ||
    strEq w "old" || strEq w "result"

theorem druck_wortkopf (e : SExpr) (hg : gut e = true) (w : String) (ts : List Token)
    (h : druckToks e = .wort w :: ts) : exprWortKopf w = true := by
  have platz : ∀ p, gutPlatz p = true → druckToks p = .wort w :: ts → exprWortKopf w = true := by
    intro p hp hd
    obtain ⟨a, us, hu⟩ := platz_kopf p hp
    rw [hu] at hd; cases hd
  cases e with
  | lit n => simp [druckToks] at h
  | float s => simp [druckToks] at h
  | tru => simp [druckToks] at h; obtain ⟨rfl, -⟩ := h; decide
  | fls => simp [druckToks] at h; obtain ⟨rfl, -⟩ := h; decide
  | «variable» s => simp [druckToks] at h
  | field x f => exact platz (.field x f) (by simpa [gut, gutPlatz] using hg) h
  | index x i => exact platz (.index x i) (by simpa [gut, gutPlatz] using hg) h
  | arrow x f => exact platz (.arrow x f) (by simpa [gut, gutPlatz] using hg) h
  | un o x => simp [druckToks] at h
  | bin o l r => simp [druckToks] at h
  | call f xs => simp [druckToks] at h
  | fnref p => simp [druckToks] at h
  | built f xs =>
    rcases gut_built_faelle f xs hg with ⟨x, hw, rfl, -, -⟩ | ⟨a, b, rfl, rfl, -, -⟩
    · simp [druckToks] at h; obtain ⟨rfl, -⟩ := h; rcases hw with rfl | rfl <;> decide
    · simp [druckToks] at h; obtain ⟨rfl, -⟩ := h; decide
  | old x => simp [druckToks] at h; obtain ⟨rfl, -⟩ := h; decide
  | res => simp [druckToks] at h; obtain ⟨rfl, -⟩ := h; decide
  | why g f => simp [druckToks] at h
  | ext k ns xs => simp [gut] at hg

/-- A printable effect arm. -/
def EffGut : SEffekt → Prop
  | .reads p => gut p = true
  | .writes p => gut p = true
  | .locks _ p => gut p = true
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
    have hO := ausdruck p he R F' h1 h2 h3 (by
      simp only [druckEffekt, List.length_append, List.length_singleton] at hF; split at hF <;> simp at hF <;> omega)
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
            exact absurd (druck_wortkopf p he _ _ hd) (by decide)
        simp only [parseEffekt, (by decide : strEq "locks" "reads" = false), (by decide : strEq "locks" "writes" = false), (by decide : strEq "locks" "locks" = true), Bool.false_eq_true, ite_false, ite_true, hw, hO]
      | _ => simp only [parseEffekt, (by decide : strEq "locks" "reads" = false), (by decide : strEq "locks" "writes" = false), (by decide : strEq "locks" "locks" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hO]
    · simp only [druckEffekt, ite_true, List.singleton_append, List.cons_append, List.append_assoc,
        List.nil_append]
      simp only [parseEffekt, (by decide : strEq "locks" "reads" = false), (by decide : strEq "locks" "writes" = false), (by decide : strEq "locks" "locks" = true), Bool.false_eq_true, ite_false, ite_true,
        (by decide : strEq "shared" "shared" = true), hO]
  | masks n =>
    simp only [druckEffekt, List.cons_append, List.nil_append]
    simp only [parseEffekt, (by decide : strEq "masks" "reads" = false), (by decide : strEq "masks" "writes" = false), (by decide : strEq "masks" "locks" = false), (by decide : strEq "masks" "masks" = true), Bool.false_eq_true, ite_false, ite_true, nimmName,
      nameText]
  | allocs n =>
    simp only [druckEffekt, List.cons_append, List.nil_append]
    simp only [parseEffekt, (by decide : strEq "allocs" "reads" = false), (by decide : strEq "allocs" "writes" = false), (by decide : strEq "allocs" "locks" = false), (by decide : strEq "allocs" "masks" = false), (by decide : strEq "allocs" "allocs" = true), Bool.false_eq_true, ite_false, ite_true, nimmName,
      nameText]
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
    have he := hg e (by simp)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases es with
    | nil =>
      simp only [druckEffekte] at hF ⊢
      have hE := effekt_rund e he (.zeichen "}" :: R) (Or.inr ⟨R, rfl⟩) F' (by omega)
      simp [parseEffektListe, hE]
    | cons e2 es2 =>
      have hd : druckEffekte (e :: e2 :: es2) = druckEffekt e ++ .zeichen "," :: druckEffekte (e2 :: es2) := by
        simp [druckEffekte]
      rw [hd] at hF ⊢
      simp only [List.length_append, List.length_cons] at hF
      have hE := effekt_rund e he (.zeichen "," :: (druckEffekte (e2 :: es2) ++ .zeichen "}" :: R))
        (Or.inl ⟨_, rfl⟩) F' (by omega)
      have hR := ih R F' (by simp) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
      have hk : istZeichenZ "}" (druckEffekte (e2 :: es2) ++ .zeichen "}" :: R) = false := by
        cases e2 <;> cases es2 <;> simp [druckEffekte, druckEffekt, istZeichenZ] <;> (try split) <;> rfl
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
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp at hF; omega⟩
    cases ns with
    | nil =>
      simp only [druckNamen, List.cons_append, List.nil_append]
      simp only [parseNamenListe, nimmName, nameText, hR]
    | cons m ms =>
      have hq := ih R F' (by simp) hR (by simp at hF ⊢; omega)
      have hlook : ∃ v, nimmName (druckNamen (m :: ms) ++ R) = .ok v := by
        cases ms <;> simp [druckNamen, nimmName, nameText]
      obtain ⟨v, hv⟩ := hlook
      have hd : druckNamen (n :: m :: ms) ++ R = .ident n :: .zeichen "," :: (druckNamen (m :: ms) ++ R) := by
        simp [druckNamen]
      rw [hd]
      have h0 : nimmName (.ident n :: .zeichen "," :: (druckNamen (m :: ms) ++ R)) =
          .ok (n, .zeichen "," :: (druckNamen (m :: ms) ++ R)) := rfl
      simp only [parseNamenListe, h0, hv, hq]

/-! ### Clauses -/

/-- The printable clauses (`by`, `retires`, `deadline` ride as reconstructed text: excluded). -/
def KlauselGut : SKlausel → Prop
  | .needs p => gut p = true
  | .gives p => gut p = true
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
  · exact ⟨⟨rfl, rfl, rfl, (by intro x e; simp at e), (by intro x e; simp at e), (by intro x e; simp at e)⟩,
      (by intro x e; simp at e), (by intro x e; simp at e)⟩
  · exact ⟨⟨rfl, rfl, rfl, (by intro x e; simp at e), (by intro x e; simp at e), (by intro x e; simp at e)⟩,
      (by intro x e; simp at e), (by intro x e; simp at e)⟩
  · have hr : w ≠ "rounded" := by intro e; subst e; exact absurd hw (by decide)
    have hi : w ≠ "in" := by intro e; subst e; exact absurd hw (by decide)
    have hre : w ≠ "reaches" := by intro e; subst e; exact absurd hw (by decide)
    have hrs : strEq w "rounded" = false := by
      cases h : strEq w "rounded"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) hr
    refine ⟨⟨rfl, rfl, by simp [ruhigGleit, hrs], (by intro x e; simp at e), ?_, ?_⟩,
      (by intro x e; simp at e), (by intro x e; simp at e)⟩
    · intro x e; simp at e; exact hi e.1
    · intro x e; simp at e; exact hre e.1

theorem klausel_rund (k : SKlausel) (hk : KlauselGut k) (R : List Token) (hR : KlauselFolge R) (F : Nat)
    (hF : 8 * (druckKlausel k).length + 41 ≤ F) :
    parseKlausel F (druckKlausel k ++ R) = .ok ([k], R) := by
  obtain ⟨hp, hkomma, hdd⟩ := klauselFolge_pred R hR
  obtain ⟨h1, h2, h3, -⟩ := id hp
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases k with
  | needs p =>
    simp only [druckKlausel, List.length_append, List.length_singleton] at hF ⊢
    have hL := predListe_rund [p] R F' (by simp) (by simpa [KlauselGut] using hk) hp hkomma
      (by simp [druckPredListe]; omega)
    simp only [druckPredListe] at hL
    simp only [List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "requires" "requires" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hL, List.map]
  | gives p =>
    simp only [druckKlausel, List.length_append, List.length_singleton] at hF ⊢
    have hL := predListe_rund [p] R F' (by simp) (by simpa [KlauselGut] using hk) hp hkomma
      (by simp [druckPredListe]; omega)
    simp only [druckPredListe] at hL
    simp only [List.singleton_append, List.cons_append]
    simp only [parseKlausel, (by decide : strEq "ensures" "requires" = false), (by decide : strEq "ensures" "ensures" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, hL, List.map]
  | keeps ns =>
    have hlen : ns.length ≤ (druckNamen ns).length := by
      clear hF hk
      induction ns with
      | nil => simp
      | cons n ns ih => cases ns with
        | nil => simp [druckNamen]
        | cons m ms => simp [druckNamen] at ih ⊢; omega
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
      have hE := effekte_rund (e :: es') R F' (by simp) hk (by omega)
      have hne : ∀ r, druckEffekte (e :: es') ++ .zeichen "}" :: R ≠ .zeichen "}" :: r := by
        intro r e'
        cases e <;> cases es' <;> simp [druckEffekte, druckEffekt] at e' <;> (try split at e') <;> simp_all
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
    simp only [parseKlausel, (by decide : strEq "arch" "requires" = false), (by decide : strEq "arch" "ensures" = false), (by decide : strEq "arch" "maintains" = false), (by decide : strEq "arch" "refines" = false), (by decide : strEq "arch" "effects" = false), (by decide : strEq "arch" "costs" = false), (by decide : strEq "arch" "deadline" = false), (by decide : strEq "arch" "decreases" = false), (by decide : strEq "arch" "by" = false), (by decide : strEq "arch" "section" = false), (by decide : strEq "arch" "arch" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, nimmName, nameText]
  | moves a b =>
    simp only [druckKlausel, List.cons_append, List.nil_append]
    simp only [parseKlausel, (by decide : strEq "advances" "requires" = false), (by decide : strEq "advances" "ensures" = false), (by decide : strEq "advances" "maintains" = false), (by decide : strEq "advances" "refines" = false), (by decide : strEq "advances" "effects" = false), (by decide : strEq "advances" "costs" = false), (by decide : strEq "advances" "deadline" = false), (by decide : strEq "advances" "decreases" = false), (by decide : strEq "advances" "by" = false), (by decide : strEq "advances" "section" = false), (by decide : strEq "advances" "arch" = false), (by decide : strEq "advances" "payload" = false), (by decide : strEq "advances" "advances" = true), Bool.false_eq_true, ite_false, ite_true, List.nil_append, nimmName, nameText, fordereZeichen, strEq_self]
  | induc h => simp [KlauselGut] at hk
  | quits s => simp [KlauselGut] at hk
  | limit s => simp [KlauselGut] at hk

theorem klausel_kopf (k : SKlausel) (hk : KlauselGut k) :
    ∃ w ts, druckKlausel k = .wort w :: ts ∧ istKlauselKopf w = true := by
  cases k <;> simp [KlauselGut] at hk <;> exact ⟨_, _, rfl, by decide⟩

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
    rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp [druckKlauseln, parseKlauseln]
  | cons k ks ih =>
    intro R F hg hR hF
    have hk := hg k (by simp)
    obtain ⟨w, ts, hd, hw⟩ := klausel_kopf k hk
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckKlauseln, List.length_append] at hF ⊢
    have hfolge : KlauselFolge (druckKlauseln ks ++ R) := by
      cases ks with
      | nil => rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩
               · exact Or.inl ⟨r, by simp [druckKlauseln]⟩
               · exact Or.inr (Or.inl ⟨r, by simp [druckKlauseln]⟩)
      | cons k2 ks2 =>
        obtain ⟨w2, ts2, hd2, hw2⟩ := klausel_kopf k2 (hg k2 (by simp))
        exact Or.inr (Or.inr ⟨w2, ts2 ++ druckKlauseln ks2 ++ R, by simp [druckKlauseln, hd2], hw2⟩)
    have hl1 : 1 ≤ (druckKlausel k).length := by rw [hd]; simp
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
    have ht : TypGut t := hg (n, t) (by simp)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases ps with
    | nil =>
      obtain ⟨r, rfl⟩ := hR
      simp only [druckParams, druckParam, List.length_append, List.length_cons, List.length_nil] at hF ⊢
      have hT := parse_druckTyp t ht (.zeichen ")" :: r) F'
        ⟨(by intro x e; simp at e), (by intro x e; simp at e), (by intro x e; simp at e),
          (by intro x e; simp at e), rfl, rfl, rfl⟩ (by simp only [fbT]; omega)
      simp only [List.cons_append, List.nil_append, List.append_assoc]
      simp [parseParamListe, nimmName, nameText, fordereZeichen, strEq_self, hT]
    | cons q qs =>
      obtain ⟨m, u⟩ := q
      obtain ⟨Z, hZ⟩ : ∃ Z, druckParams ((m, u) :: qs) = .ident m :: Z := by
        cases qs <;> exact ⟨_, rfl⟩
      have hd : druckParams ((n, t) :: (m, u) :: qs) ++ R = .ident n :: .zeichen ":" ::
          (druckTyp t ++ .zeichen "," :: .ident m :: (Z ++ R)) := by
        have : druckParams ((n, t) :: (m, u) :: qs) = druckParam (n, t) ++ [.zeichen ","] ++
            druckParams ((m, u) :: qs) := rfl
        rw [this, hZ]; simp [druckParam]
      have hlen : (druckParams ((n, t) :: (m, u) :: qs)).length =
          (druckTyp t).length + 3 + (druckParams ((m, u) :: qs)).length := by
        have : druckParams ((n, t) :: (m, u) :: qs) = druckParam (n, t) ++ [.zeichen ","] ++
            druckParams ((m, u) :: qs) := rfl
        rw [this]; simp [druckParam]; omega
      rw [hlen] at hF
      have hR' := ih R F' (by simp) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) hR (by omega)
      rw [hZ] at hR' hF
      have hT := parse_druckTyp t ht (.zeichen "," :: .ident m :: (Z ++ R)) F'
        ⟨(by intro x e; simp at e), (by intro x e; simp at e), (by intro x e; simp at e),
          (by intro x e; simp at e), rfl, rfl, rfl⟩ (by simp only [fbT]; simp at hF; omega)
      rw [hd]
      simp only [List.cons_append] at hR'
      simp [parseParamListe, nimmName, nameText, fordereZeichen, strEq_self, hT, hR']

theorem params_rund (ps : List (String × STyp)) (hg : ∀ p ∈ ps, TypGut p.2) (R : List Token) (F : Nat)
    (hF : 8 * (druckParams ps).length + 32 ≤ F) :
    parseParams F (.zeichen "(" :: (druckParams ps ++ .zeichen ")" :: R)) = .ok (ps, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases ps with
  | nil => simp [druckParams, parseParams, fordereZeichen, strEq_self]
  | cons p ps =>
    obtain ⟨n, t⟩ := p
    obtain ⟨Z, hZ⟩ : ∃ Z, druckParams ((n, t) :: ps) = .ident n :: Z := by
      cases ps <;> exact ⟨_, rfl⟩
    have hL := paramListe_rund ((n, t) :: ps) (.zeichen ")" :: R) F' (by simp) hg ⟨R, rfl⟩ (by omega)
    rw [hZ] at hL ⊢
    simp only [List.cons_append] at hL ⊢
    simp [parseParams, fordereZeichen, strEq_self, hL]

/-- A printable function head. -/
def SigGut (s : FnSig) : Prop :=
  (s.art = "" ∨ s.art = "const" ∨ istMod s.art = true) ∧ (∀ p ∈ s.params, TypGut p.2) ∧
    TypOptGut s.res ∧ (∀ k ∈ s.klauseln, KlauselGut k)

/-- The function head behind its modifier, up to the body. -/
def sigToks (s : FnSig) : List Token :=
  [.wort "fn", .ident s.name, .zeichen "("] ++ druckParams s.params ++ [.zeichen ")"] ++
    (match s.res with
      | some t => [.zeichen "->"] ++ druckTyp t
      | none => []) ++
    (match s.fehler with
      | some n => [.wort "or", .ident n]
      | none => []) ++
    druckKlauseln s.klauseln

theorem druckFnSig_eq (s : FnSig) :
    druckFnSig s = (if strEq s.art "" then [] else [.wort s.art]) ++ sigToks s := by
  simp [druckFnSig, sigToks]; rfl

/-- The result tokens of a head. -/
def resToks : Option STyp → List Token
  | some t => [.zeichen "->"] ++ druckTyp t
  | none => []

/-- The `or` channel tokens of a head. -/
def fehlerToks : Option String → List Token
  | some n => [.wort "or", .ident n]
  | none => []

theorem sigToks_eq (s : FnSig) : sigToks s = [.wort "fn", .ident s.name, .zeichen "("] ++
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
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, by simp [ruhigGleit, this]⟩ <;> intro r e <;> simp at e <;> simp_all
  cases fehler with
  | some n => exact gen "or" _ (by decide) (by decide) (by decide) (by decide)
  | none =>
    simp only [fehlerToks, List.nil_append]
    cases ks with
    | nil =>
      rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
        exact ⟨(by intro x e; simp [druckKlauseln] at e), (by intro x e; simp [druckKlauseln] at e),
          (by intro x e; simp [druckKlauseln] at e), (by intro x e; simp [druckKlauseln] at e), rfl, rfl, rfl⟩
    | cons k ks' =>
      obtain ⟨w, ts, hd, hw⟩ := klausel_kopf k (hk k (by simp))
      have : druckKlauseln (k :: ks') ++ R = .wort w :: (ts ++ druckKlauseln ks' ++ R) := by
        simp [druckKlauseln, hd]
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
  have hlenF : (fehlerToks fehler).length ≤ 2 := by cases fehler <;> simp [fehlerToks]
  simp only [List.length_append, List.length_cons, List.length_nil] at hF
  have hK := klauseln_rund klauseln R F' hk hR (by omega)
  have hFe : parseFehler (fehlerToks fehler ++ druckKlauseln klauseln ++ R) =
      .ok (fehler, druckKlauseln klauseln ++ R) := by
    cases fehler with
    | some n => simp [fehlerToks, parseFehler, strEq_self, nimmName, nameText]
    | none =>
      simp only [fehlerToks, List.nil_append]
      cases klauseln with
      | nil =>
        rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp [druckKlauseln, parseFehler]
      | cons k ks =>
        obtain ⟨w, ts, hd, hw⟩ := klausel_kopf k (hk k (by simp))
        have hwo : strEq w "or" = false := by
          cases h : strEq w "or"
          · rfl
          · have := (strEq_eq _ _).mp h; subst this; exact absurd hw (by decide)
        simp [druckKlauseln, hd, parseFehler, hwo]
  have hTF := kopfRest_typFolge fehler klauseln hk R hR
  have hErg : parseErgebnis F' (resToks res ++ (fehlerToks fehler ++ druckKlauseln klauseln ++ R)) =
      .ok (res, fehler, druckKlauseln klauseln ++ R) := by
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    cases res with
    | some t =>
      have hT := parse_druckTyp t hres _ F'' hTF (by simp only [fbT]; simp [resToks] at hF; omega)
      simp only [resToks, List.singleton_append, List.cons_append, List.append_assoc] at hT hFe ⊢
      simp [parseErgebnis, hT, hFe]
    | none =>
      simp only [resToks, List.nil_append]
      have hne : ∀ r, fehlerToks fehler ++ druckKlauseln klauseln ++ R ≠ .zeichen "->" :: r := by
        intro r e
        cases fehler with
        | some n => simp [fehlerToks] at e
        | none =>
          cases klauseln with
          | nil => rcases hR with ⟨r', rfl⟩ | ⟨r', rfl⟩ <;> simp [fehlerToks, druckKlauseln] at e
          | cons k ks =>
            obtain ⟨w, ts, hd, -⟩ := klausel_kopf k (hk k (by simp))
            simp [fehlerToks, druckKlauseln, hd] at e
      rw [parseErgebnis.eq_def]
      simp only [hne]
      simp only [List.append_assoc] at hFe
      simp [hFe]
  have hP := params_rund params hp (resToks res ++ (fehlerToks fehler ++ druckKlauseln klauseln ++ R)) F'
    (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] at hP hErg hK ⊢
  simp [parseFnSig, nimmWort, strEq_self, nimmName, nameText, hP, hErg, hK]

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
    rcases hR with rfl | ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp [druckItems, parseItemsTief]
  | cons it its ih =>
    intro R F h hR hF
    obtain ⟨hB, w, ts, hd, -, -⟩ := h it (by simp)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckItems, List.length_append] at hF ⊢
    have hl : 1 ≤ (druckItem it).length := by rw [hd]; simp
    have hI := hB (druckItems its ++ R) F' (by simp only [fbI]; omega)
    have hR' := ih R F' (fun x hx => h x (List.mem_cons_of_mem _ hx)) hR (by omega)
    rw [List.append_assoc, hd]
    rw [hd] at hI
    simp only [List.cons_append] at hI ⊢
    simp [parseItemsTief, hI, hR']

theorem item_use (p : List String) (hp : p ≠ []) : ItemBein (.useT p) := by
  intro rest F hF
  simp only [fbI] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hd : druckItem (.useT p) ++ rest = .wort "use" :: (pfadToks p ++ .zeichen ";" :: rest) := by
    simp [druckItem]
  have hP := nimmPfad_pfad p (.zeichen ";" :: rest) hp
    (by intro r e; injection e with e1; injection e1 with e2; exact absurd e2 (by decide))
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_use]
  simp [parseUseTief, nimmWort, strEq_self, hP, fordereZeichen]

/-- `= v ;` behind a type: the initialiser follow. -/
theorem typ_gleich (t : STyp) (ht : TypGut t) (X : List Token) (F : Nat) (hF : fbT t ≤ F) :
    parseTyp F (druckTyp t ++ .zeichen "=" :: X) = .ok (t, .zeichen "=" :: X) :=
  parse_druckTyp t ht _ F ⟨(by intro r e; simp at e), (by intro r e; simp at e),
    (by intro r e; simp at e), (by intro r e; simp at e), rfl, rfl, rfl⟩ hF

theorem item_const (n : String) (t : STyp) (v : SKonstWert) (ht : TypGut t) (hv : KonstGut v) :
    ItemBein (.constT n t v) := by
  intro rest F hF
  simp only [fbI, druckItem, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckItem (.constT n t v) ++ rest = .wort "const" :: .ident n :: .zeichen ":" ::
      (druckTyp t ++ .zeichen "=" :: (druckKonstWert v ++ .zeichen ";" :: rest)) := by
    simp [druckItem]
  have hT := typ_gleich t ht (druckKonstWert v ++ .zeichen ";" :: rest) F' (by simp only [fbT]; omega)
  have hV := konst_rund v hv (.zeichen ";" :: rest) F' rfl rfl rfl (by simp only [fbK]; omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_const]
  simp [parseKonstNach, nimmName, nameText, fordereZeichen, strEq_self, hT, hV]

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
      simp [globTailToks, parseGlobTail, nimmTextTok, fordereZeichen, strEq_self, bind, Except.bind,
        pure, Except.pure]
  | some e =>
    have he := hal e rfl
    cases s with
    | none =>
      cases sh with
      | false =>
        have hO := ausdruck e he (.zeichen ";" :: rest) F' rfl rfl rfl (by
          simp [globTailToks] at hF; omega)
        simp [globTailToks, parseGlobTail, hO, fordereZeichen, strEq_self, bind, Except.bind, pure,
          Except.pure]
      | true =>
        have hO := ausdruck e he (.wort "shared" :: .zeichen ";" :: rest) F' rfl rfl rfl (by
          simp [globTailToks] at hF; omega)
        simp [globTailToks, parseGlobTail, hO, fordereZeichen, strEq_self, bind, Except.bind, pure,
          Except.pure]
    | some x =>
      cases sh with
      | false =>
        have hO := ausdruck e he (.wort "section" :: .text x :: .zeichen ";" :: rest) F' rfl rfl rfl (by
          simp [globTailToks] at hF; omega)
        simp [globTailToks, parseGlobTail, hO, nimmTextTok, fordereZeichen, strEq_self, bind,
          Except.bind, pure, Except.pure]
      | true =>
        have hO := ausdruck e he (.wort "section" :: .text x :: .wort "shared" :: .zeichen ";" :: rest) F'
          rfl rfl rfl (by simp [globTailToks] at hF; omega)
        simp [globTailToks, parseGlobTail, hO, nimmTextTok, fordereZeichen, strEq_self, bind,
          Except.bind, pure, Except.pure]

theorem globTail_ruhig (al : Option SExpr) (s : Option String) (sh : Bool) (rest : List Token) :
    ruhig (globTailToks al s sh ++ rest) = true ∧ ruhigSuff (globTailToks al s sh ++ rest) = true ∧
      ruhigGleit (globTailToks al s sh ++ rest) = true := by
  cases al <;> cases s <;> cases sh <;> exact ⟨rfl, rfl, rfl⟩

theorem item_static (m : Bool) (n : String) (t : STyp) (v : SKonstWert) (al : Option SExpr)
    (s : Option String) (sh : Bool) (ht : TypGut t) (hv : KonstGut v) (hal : ∀ e, al = some e → gut e = true) :
    ItemBein (.globT m n t v al s sh) := by
  intro rest F hF
  have hd : druckItem (.globT m n t v al s sh) ++ rest = .wort "static" :: ((if m then [.wort "mut"] else []) ++
      .ident n :: .zeichen ":" :: (druckTyp t ++ .zeichen "=" :: (druckKonstWert v ++
        (globTailToks al s sh ++ rest)))) := by
    cases al <;> cases s <;> cases sh <;> simp [druckItem, globTailToks]
  have hlen : (druckItem (.globT m n t v al s sh)).length = 1 + (if m then 1 else 0) + 2 +
      (druckTyp t).length + 1 + (druckKonstWert v).length + (globTailToks al s sh).length := by
    cases m <;> cases al <;> cases s <;> cases sh <;> simp [druckItem, globTailToks] <;> omega
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
  · simp [parseGlobTief, nimmWort, strEq_self, parseGlobAfter, nimmName, nameText, fordereZeichen, hT,
      hV, hG, bind, Except.bind, pure, Except.pure]
  · simp [parseGlobTief, nimmWort, strEq_self, parseGlobAfter, nimmName, nameText, fordereZeichen, hT,
      hV, hG, bind, Except.bind, pure, Except.pure]


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
  rw [druckFnSig_eq]; simp

theorem item_fn (sig : FnSig) (b : SAnw) (hs : SigGut sig) (hb : BlockBein b) (hk : BlockKopf b) :
    ItemBein (.fnT sig b) := by
  intro rest F hF
  obtain ⟨us, hus⟩ := hk
  have hlen := druckFnSig_len sig
  have hbl : 1 ≤ (druckAnw b).length := by rw [hus]; simp
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
  simp [parseFnRest, hB]

theorem item_proto (sig : FnSig) (hs : SigGut sig) : ItemBein (.protoT sig) := by
  intro rest F hF
  have hlen := druckFnSig_len sig
  simp only [fbI, druckItem, List.length_append, List.length_singleton] at hF
  obtain ⟨G, hG, hI⟩ := item_fnkopf sig hs (.zeichen ";" :: rest) (Or.inr ⟨rest, rfl⟩) F (by omega)
  simp only [druckItem, List.append_assoc, List.singleton_append]
  rw [hI]
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  simp [parseFnRest]

/-! ### `reason`, `concurrent`, `module` -/

/-- A printable reason case: its number is printable. -/
def FallGut (c : String × SExpr × String) : Prop := gut c.2.1 = true

theorem grundFaelle_rund : ∀ (cs : List (String × SExpr × String)) (ex : Bool) (R : List Token) (F : Nat),
    (∀ c ∈ cs, FallGut c) → 8 * (druckGrundFaelle cs).length + 42 ≤ F →
    parseGrundFaelle F (druckGrundFaelle cs ++ ((if ex then [.wort "exhaustive"] else []) ++
      .zeichen "}" :: R)) = .ok ((cs, ex), R) := by
  intro cs
  induction cs with
  | nil =>
    intro ex R F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases ex <;> simp [druckGrundFaelle, parseGrundFaelle, fordereZeichen, strEq_self]
  | cons c cs ih =>
    intro ex R F hg hF
    obtain ⟨n, num, t⟩ := c
    have hnum : gut num = true := hg (n, num, t) (by simp)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckGrundFaelle, List.length_append, List.length_cons, List.length_nil] at hF
    have hR := ih ex R F' (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
    obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
    have hO := ausdruck num hnum (.text t :: .zeichen "," :: (druckGrundFaelle cs ++
      ((if ex then [.wort "exhaustive"] else []) ++ .zeichen "}" :: R))) F'' rfl rfl rfl (by omega)
    simp only [druckGrundFaelle, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append]
    unfold parseGrundFaelle
    simp [parseGrundFall, nimmName, nameText, fordereZeichen, strEq_self, hO, nimmTextTok, hR]

theorem item_why (n : String) (cs : List (String × SExpr × String)) (ex : Bool) (hg : ∀ c ∈ cs, FallGut c) :
    ItemBein (.whyT n cs ex) := by
  intro rest F hF
  have hd : druckItem (.whyT n cs ex) ++ rest = .wort "reason" :: .ident n :: .zeichen "{" ::
      (druckGrundFaelle cs ++ ((if ex then [.wort "exhaustive"] else []) ++ .zeichen "}" :: rest)) := by
    cases ex <;> simp [druckItem]
  have hlen : (druckGrundFaelle cs).length + 3 ≤ (druckItem (.whyT n cs ex)).length := by
    cases ex <;> simp [druckItem] <;> omega
  simp only [fbI] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hG := grundFaelle_rund cs ex rest F' hg (by omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_reason]
  simp [parseGrundTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hG]

/-- A path printed as text: segments name-shaped, no table words. -/
def PfadGut (segs : List String) : Prop :=
  segs ≠ [] ∧ ∀ a ∈ segs, nameForm a = true ∧ istSchluessel a = false

theorem druckWurzeln_pfade : ∀ (ps : List (List String)), (∀ p ∈ ps, PfadGut p) →
    druckWurzeln (ps.map (fun p => "::".intercalate p)) =
      kommaToks (ps.map pfadToks) := by
  intro ps hps
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := hps p (by simp)
    have ih' := ih (fun x hx => hps x (List.mem_cons_of_mem _ hx))
    cases ps with
    | nil => simp [druckWurzeln, kommaToks, rohToks_pfad p hp.1 hp.2]
    | cons q qs =>
      simp only [List.map_cons] at ih' ⊢
      simp only [druckWurzeln, kommaToks, rohToks_pfad p hp.1 hp.2] at ih' ⊢
      rw [ih']

theorem pfadFolge_rund : ∀ (ps : List (List String)) (R : List Token) (F : Nat), ps ≠ [] →
    (∀ p ∈ ps, p ≠ []) → (ps.map pfadToks).length ≤ F →
    parsePfadFolge F (kommaToks (ps.map pfadToks) ++ .zeichen "}" :: R) = .ok (ps, R) := by
  intro ps
  induction ps with
  | nil => intro _ _ h; exact absurd rfl h
  | cons p ps ih =>
    intro R F _ hg hF
    have hp := hg p (by simp)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp at hF; omega⟩
    cases ps with
    | nil =>
      have hP := nimmPfad_pfad p (.zeichen "}" :: R) hp (by intro r e; simp at e)
      simp only [List.map_cons, List.map_nil, kommaToks]
      simp [parsePfadFolge, hP, fordereZeichen, strEq_self]
    | cons q qs =>
      have hq := hg q (by simp)
      have hR := ih R F' (by simp) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by simp at hF ⊢; omega)
      have hP := nimmPfad_pfad p (.zeichen "," :: (kommaToks ((q :: qs).map pfadToks) ++ .zeichen "}" :: R))
        hp (by intro r e; simp at e)
      obtain ⟨a, us, hq1⟩ : ∃ a us, pfadToks q = .ident a :: us := by
        match q, hq with
        | [a], _ => exact ⟨a, [], rfl⟩
        | a :: b :: cs, _ => exact ⟨a, _, rfl⟩
      have hk : kommaToks ((q :: qs).map pfadToks) = .ident a :: (kommaToks ((q :: qs).map pfadToks)).tail := by
        cases qs <;> simp [kommaToks, hq1]
      have hd : kommaToks ((p :: q :: qs).map pfadToks) = pfadToks p ++ .zeichen "," ::
          kommaToks ((q :: qs).map pfadToks) := by
        simp [kommaToks]
      rw [hd]
      simp only [List.append_assoc, List.cons_append] at hP ⊢
      rw [hk] at hP hR ⊢
      simp only [List.cons_append] at hP hR ⊢
      unfold parsePfadFolge
      simp only [hP, hR]

theorem item_conc (ps : List (List String)) (hps : ∀ p ∈ ps, PfadGut p) : ItemBein (.concT ps) := by
  intro rest F hF
  have hW := druckWurzeln_pfade ps hps
  have hlen : (ps.map pfadToks).length ≤ (kommaToks (ps.map pfadToks)).length := by
    clear hF hW
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have hp := hps p (by simp)
      have ih' := ih (fun x hx => hps x (List.mem_cons_of_mem _ hx))
      have h1 : 1 ≤ (pfadToks p).length := by
        match p, hp.1 with
        | [a], _ => simp [pfadToks]
        | a :: b :: cs, _ => simp [pfadToks]
      cases ps with
      | nil => simp [kommaToks]; omega
      | cons q qs => simp [kommaToks] at ih' ⊢; omega
  simp only [fbI, druckItem, hW, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckItem (.concT ps) ++ rest = .wort "concurrent" :: .zeichen "{" ::
      (kommaToks (ps.map pfadToks) ++ .zeichen "}" :: .zeichen ";" :: rest) := by
    simp [druckItem, hW]
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_concurrent]
  cases ps with
  | nil => simp [kommaToks, parseNebenTief, nimmWort, strEq_self, parsePfadListe, fordereZeichen]
  | cons p ps' =>
    have hp := hps p (by simp)
    have hF' := pfadFolge_rund (p :: ps') (.zeichen ";" :: rest) F' (by simp) (fun x hx => (hps x hx).1)
      (by omega)
    obtain ⟨a, us, hq1⟩ : ∃ a us, pfadToks p = .ident a :: us := by
      match p, hp.1 with
      | [a], _ => exact ⟨a, [], rfl⟩
      | a :: b :: cs, _ => exact ⟨a, _, rfl⟩
    have hk : kommaToks ((p :: ps').map pfadToks) = .ident a :: (kommaToks ((p :: ps').map pfadToks)).tail := by
      cases ps' <;> simp [kommaToks, hq1]
    rw [hk] at hF' ⊢
    simp only [List.cons_append, List.map_cons] at hF' ⊢
    simp [parseNebenTief, nimmWort, strEq_self, parsePfadListe, fordereZeichen, hF']


theorem item_mod (segs : List String) (its : List SItemTief) (hs : PfadGut segs)
    (hits : ∀ it ∈ its, ItemBein it ∧ ItemKopf it) : ItemBein (.modT ("::".intercalate segs) its) := by
  intro rest F hF
  have hr := rohToks_pfad segs hs.1 hs.2
  have hd : druckItem (.modT ("::".intercalate segs) its) ++ rest = .wort "module" :: (pfadToks segs ++
      .zeichen "{" :: (druckItems its ++ .zeichen "}" :: rest)) := by
    simp [druckItem, hr]
  simp only [fbI, druckItem, hr, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hP := nimmPfad_pfad segs (.zeichen "{" :: (druckItems its ++ .zeichen "}" :: rest)) hs.1
    (by intro r e; simp at e)
  have hI := items_rund its (.zeichen "}" :: rest) F' hits (Or.inr (Or.inl ⟨rest, rfl⟩)) (by omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_module]
  simp [parseModulTief, nimmWort, strEq_self, hP, fordereZeichen, hI]

/-! ### `atomic` -/

theorem platzListe_rund (ps : List SExpr) (hps : ∀ p ∈ ps, gut p = true) (R : List Token) (F : Nat)
    (hF : 8 * (druckPlaetze ps).length + 48 ≤ F) :
    parsePlatzListe F (.zeichen "{" :: (druckPlaetze ps ++ .zeichen "}" :: R)) = .ok (ps, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases ps with
  | nil => simp [druckPlaetze, parsePlatzListe, fordereZeichen, strEq_self]
  | cons p ps' =>
    rw [druckPlaetze_eq] at hF ⊢
    have hL := predListe_rund (p :: ps') (.zeichen "}" :: R) F' (by simp) hps
      ⟨rfl, rfl, rfl, (by intro r e; simp at e), (by intro r e; simp at e), (by intro r e; simp at e)⟩
      (by intro r e; simp at e) (by omega)
    obtain ⟨t, ts, hd, -, -⟩ := druck_kopf_pred p (hps p (by simp))
    have hne : ∀ r, druckPredListe (p :: ps') ++ .zeichen "}" :: R ≠ .zeichen "}" :: r := by
      intro r e
      have : druckPredListe (p :: ps') = druckToks p ++ (druckPredListe (p :: ps')).drop (druckToks p).length := by
        cases ps' <;> simp [druckPredListe]
      rw [this, hd] at e
      simp at e
      obtain ⟨rfl, -⟩ := e
      have := druck_kopf p (hps p (by simp))
      obtain ⟨t', ts', hd', hk'⟩ := this
      rw [hd] at hd'; injection hd' with e1; subst e1; simp [KopfGut] at hk'
    simp only [parsePlatzListe, fordereZeichen, strEq_self, ite_true]
    simp only [hne, hL]
    simp [fordereZeichen, strEq_self]

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
    | some o => [.wort "observed", .wort "by", .ident o]
    | none => []) ++ [.zeichen ";"]

theorem atomRest_ende (f : Nat) (acc : String × STyp × Option (List SExpr) × Option String × Option String)
    (R : List Token) : parseAtomarRest (f + 1) acc (.zeichen ";" :: R) = .ok (acc, R) := by
  simp [parseAtomarRest, fordereZeichen, strEq_self]

theorem atomRest_obs (f : Nat) (a : String) (b : STyp) (c : Option (List SExpr)) (d : Option String)
    (e : Option String) (o : String) (R : List Token) :
    parseAtomarRest (f + 1) (a, b, c, d, e) (.wort "observed" :: .wort "by" :: .ident o :: R) =
      parseAtomarRest f (a, b, c, d, some o) R := by
  simp [parseAtomarRest, nimmWort, strEq_self, nimmName, nameText,
    (by decide : strEq "observed" "publishes" = false), (by decide : strEq "observed" "acquire" = false),
    (by decide : strEq "observed" "release" = false), (by decide : strEq "observed" "seq" = false),
    (by decide : strEq "observed" "relaxed" = false)]

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
  simp [parseAtomarRest, strEq_self]

theorem atomRest_liste (f : Nat) (a : String) (b : STyp) (c : Option (List SExpr)) (d : Option String)
    (e : Option String) (ps : List SExpr) (hps : ∀ p ∈ ps, gut p = true) (R : List Token)
    (hF : 8 * (druckPlaetze ps).length + 48 ≤ f) :
    parseAtomarRest (f + 1) (a, b, c, d, e) (.wort "publishes" :: .zeichen "{" ::
      (druckPlaetze ps ++ .zeichen "}" :: R)) = parseAtomarRest f (a, b, some ps, d, e) R := by
  have hL := platzListe_rund ps hps R f hF
  simp [parseAtomarRest, strEq_self, hL]

theorem item_atom (n : String) (t : STyp) (pub : Option (List SExpr)) (ord obs : Option String)
    (ht : TypGut t) (hg : AtomGut pub ord) : ItemBein (.atomT n t pub ord obs) := by
  intro rest F hF
  obtain ⟨hpub, hord⟩ := hg
  have hd : druckItem (.atomT n t pub ord obs) ++ rest = .wort "atomic" :: .ident n :: .zeichen ":" ::
      (druckTyp t ++ (atomTail pub ord obs ++ rest)) := by
    simp only [druckItem, atomTail]
    rcases pub with _ | _ | ⟨p, ps⟩ <;> cases ord <;> cases obs <;> simp
  have hlen : (druckItem (.atomT n t pub ord obs)).length = 3 + (druckTyp t).length +
      (atomTail pub ord obs).length := by
    simp only [druckItem, atomTail]
    rcases pub with _ | _ | ⟨p, ps⟩ <;> cases ord <;> cases obs <;> simp <;> omega
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
      refine ⟨?_, ?_, ?_, ?_, rfl, rfl, by simp [ruhigGleit, this]⟩ <;> intro r e <;> simp at e <;> simp_all
    rcases pub with _ | _ | ⟨p, ps⟩
    · rcases ord with _ | o
      · cases obs
        · exact ⟨(by intro r e; simp [atomTail] at e), (by intro r e; simp [atomTail] at e),
            (by intro r e; simp [atomTail] at e), (by intro r e; simp [atomTail] at e), rfl, rfl, rfl⟩
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
  simp only [parseAtomarTief, nimmWort, strEq_self, ite_true, nimmName, nameText, fordereZeichen, hT]
  have hR : parseAtomarRest (F'' + 1) (n, t, none, none, none) (atomTail pub ord obs ++ rest) =
      .ok ((n, t, pub, ord, obs), rest) := by
    have stepE : ∀ (G : Nat) acc, 1 ≤ G → parseAtomarRest G acc (.zeichen ";" :: rest) = .ok (acc, rest) := by
      intro G acc hG; obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩; exact atomRest_ende G' acc rest
    have stepO : ∀ (G : Nat) (c : Option (List SExpr)) (d : Option String) (o : String) (R : List Token),
        1 ≤ G → parseAtomarRest G (n, t, c, d, none) (.wort "observed" :: .wort "by" :: .ident o :: R) =
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
        rw [atomRest_nichts, stepE _ _ (by simp [atomTail] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_nichts, stepO _ _ _ _ _ (by simp [atomTail] at hF; omega),
          stepE _ _ (by simp [atomTail] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_nichts, stepD _ _ _ _ (hord o rfl) (by simp [atomTail] at hF; omega),
          stepE _ _ (by simp [atomTail] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_nichts, stepD _ _ _ _ (hord o rfl) (by simp [atomTail] at hF; omega),
          stepO _ _ _ _ _ (by simp [atomTail] at hF; omega), stepE _ _ (by simp [atomTail] at hF; omega)]
    · have hps := hpub (p :: ps) rfl
      rcases ord with _ | o <;> rcases obs with _ | ob
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp [atomTail] at hF; omega),
          stepE _ _ (by simp [atomTail] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp [atomTail] at hF; omega),
          stepO _ _ _ _ _ (by simp [atomTail] at hF; omega), stepE _ _ (by simp [atomTail] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp [atomTail] at hF; omega),
          stepD _ _ _ _ (hord o rfl) (by simp [atomTail] at hF; omega),
          stepE _ _ (by simp [atomTail] at hF; omega)]
      · simp only [atomTail, List.nil_append, List.cons_append, List.singleton_append, List.append_assoc]
        rw [atomRest_liste _ _ _ _ _ _ _ hps _ (by simp [atomTail] at hF; omega),
          stepD _ _ _ _ (hord o rfl) (by simp [atomTail] at hF; omega),
          stepO _ _ _ _ _ (by simp [atomTail] at hF; omega), stepE _ _ (by simp [atomTail] at hF; omega)]
  simp [hR]

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
    | some w => [.wort "masks", .ident w]
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
  have hd : druckItem (.lockT n ps rk h sh m inv) ++ rest = .wort "lock" :: .ident n :: .wort "protects" ::
      .zeichen "{" :: (druckPlaetze ps ++ .zeichen "}" :: .wort "rank" ::
        (druckToks rk ++ (lockTail h sh m inv ++ rest))) := by
    cases h <;> cases sh <;> cases m <;> cases inv <;> simp [druckItem, lockTail]
  have hlen : (druckItem (.lockT n ps rk h sh m inv)).length = 6 + (druckPlaetze ps).length +
      (druckToks rk).length + (lockTail h sh m inv).length := by
    cases h <;> cases sh <;> cases m <;> cases inv <;> simp [druckItem, lockTail] <;> omega
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
    fun p hp hl => pred_druck p hp _ ⟨rfl, rfl, rfl, (by intro r e; simp at e), (by intro r e; simp at e),
      (by intro r e; simp at e)⟩ F' (by simp only [fb]; omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_lock]
  rcases h with _ | eh <;> rcases sh with _ | es <;> rcases m with _ | w <;> rcases inv with _ | ip
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk,
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hI ip (hi ip rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk,
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hI ip (hi ip rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE es (hs es rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE es (hs es rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE es (hs es rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE es (hs es rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE eh (hh eh rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE eh (hh eh rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), (hE es (hs es rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), (hE es (hs es rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), (hE es (hs es rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]
  · simp only [lockTail, List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hRk hPL ⊢
    simp [parseSperreTief, nimmWort, strEq_self, nimmName, nameText, fordereZeichen, hPL, hRk, (hE eh (hh eh rfl) (by simp [lockTail]; omega)), (hE es (hs es rfl) (by simp [lockTail]; omega)), (hI ip (hi ip rfl) (by simp [lockTail]; omega)),
      bind, Except.bind, pure, Except.pure]

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
  have hc : istZiffer c = true := by rw [hcs] at hd; simp at hd; exact hd.1
  have hlen : (toString n).length = cs.length + 1 := by
    rw [← String.length_toList, Nat.toString_eq_ofList_toDigits, String.toList_ofList, hcs]; rfl
  rw [hlen, hcs, scan_ziffer_kopf false c cs _ hc]
  have hk : scanZahlKopf (c :: cs) = zahlBasis 10 (c :: cs) := by
    cases cs with
    | nil => exact scanZahlKopf_eins c
    | cons d ds =>
      have : istZiffer d = true := by rw [hcs] at hd; simp at hd; exact hd.2.1
      exact scanZahlKopf_dez c d ds (ziffer_kein_praefix this)
  rw [hk]
  have hz : nimmZiffern (c :: cs) 10 = (n, true, []) := by
    unfold nimmZiffern
    have := nimmZiffern_go (c :: cs) [] 0 false (by rw [← hcs]; exact hd)
    simp only [List.append_nil] at this
    rw [this, ← hcs, Nat.ofDigitChars_ten_toDigits]
    simp [nimmZiffern.go]
  simp [zahlBasis, hz, zahlWeiter, scan, Except.map]

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
    split <;> simp [parseBitpos, nameText, zeigeTok]

/-- A printable field. -/
def FeldGut (f : SFeld) : Prop :=
  TypGut f.ftyp ∧ (∀ p, f.pos = some p → PosGut p) ∧ (∀ e, f.wo = some e → gut e = true)

/-- The options of a field behind its type. -/
def feldRestToks (f : SFeld) : List Token :=
  (match f.pos with
    | some p => [.zeichen "@"] ++ rohToks p
    | none => []) ++
  (match f.bezug with
    | some n => [.wort "offset_into", .ident n]
    | none => []) ++
  (match f.wo with
    | some p => [.wort "where"] ++ druckToks p
    | none => []) ++
  (if f.reserviert then [.wort "reserved"] else []) ++
  (if f.byOps then [.wort "by", .wort "ops"] else [])

theorem druckFeld_eq (f : SFeld) :
    druckFeld f = [.ident f.fname, .zeichen ":"] ++ druckTyp f.ftyp ++ feldRestToks f := by
  simp [druckFeld, feldRestToks]; rfl


/-- What follows a field: `,` or `}`. -/
def FeldEnde (R : List Token) : Prop := (∃ r, R = .zeichen "," :: r) ∨ (∃ r, R = .zeichen "}" :: r)

theorem feldRest_ende (f : Nat) (R : List Token) (hR : FeldEnde R) :
    parseFeldRest (f + 1) R = .ok ((none, none, none, false, false), R) := by
  rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp [parseFeldRest]

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
    parseFeldRest (f + 1) (.wort "offset_into" :: .ident n :: R) = .ok ((p, some n, w, r, y), X) := by
  by_cases hn : n = "Self"
  · subst hn; simp [parseFeldRest, h, strEq_self, zeigeTok]
  · have : strEq n "Self" = false := by
      cases e : strEq n "Self"
      · rfl
      · exact absurd ((strEq_eq _ _).mp e) hn
    simp [parseFeldRest, h, strEq_self, zeigeTok, this, nameText]

theorem feldRest_pos (f : Nat) (q : String) (hq : PosGut q) (R X : List Token) (p b : Option String)
    (w : Option SExpr) (r y : Bool) (h : parseFeldRest f R = .ok ((p, b, w, r, y), X)) :
    parseFeldRest (f + 1) (.zeichen "@" :: (rohToks q ++ R)) = .ok ((some q, b, w, r, y), X) := by
  simp [parseFeldRest, h, bitpos_rund q hq R]

theorem feldRest_rund (fd : SFeld) (hfd : FeldGut fd) (R : List Token) (hR : FeldEnde R) (F : Nat)
    (hF : 8 * (feldRestToks fd).length + 60 ≤ F) :
    parseFeldRest F (feldRestToks fd ++ R) = .ok ((fd.pos, fd.bezug, fd.wo, fd.reserviert, fd.byOps), R) := by
  obtain ⟨-, hpos, hwo⟩ := hfd
  obtain ⟨name, typ, pos, bezug, wo, res, byo⟩ := fd
  simp only at hpos hwo ⊢
  have hPF : PredFolge R ∧ (∀ r, R ≠ .zeichen "," :: r → True) := by
    refine ⟨?_, fun _ _ => trivial⟩
    rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
      exact ⟨rfl, rfl, rfl, (by intro x e; simp at e), (by intro x e; simp at e), (by intro x e; simp at e)⟩
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
    all_goals exact ⟨rfl, rfl, rfl, (by intro x e; simp at e), (by intro x e; simp at e), (by intro x e; simp at e)⟩
  have hlen45 : ((if res then [Token.wort "reserved"] else []) ++
      ((if byo then [Token.wort "by", .wort "ops"] else []) ++ R)).length ≤ 3 + R.length := by
    cases res <;> cases byo <;> simp <;> omega
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
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, by simp [ruhigGleit, this]⟩ <;> intro r e <;> simp at e <;> simp_all
  obtain ⟨name, typ, pos, bezug, wo, res, byo⟩ := fd
  rcases pos with _ | q
  · rcases bezug with _ | n
    · rcases wo with _ | e
      · cases res
        · cases byo
          · simp only [feldRestToks, ite_false, Bool.false_eq_true, List.nil_append]
            rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
              exact ⟨(by intro x e; simp at e), (by intro x e; simp at e), (by intro x e; simp at e),
                (by intro x e; simp at e), rfl, rfl, rfl⟩
          · exact gen "by" _ (by decide) (by decide) (by decide) (by decide)
        · exact gen "reserved" _ (by decide) (by decide) (by decide) (by decide)
      · exact gen "where" _ (by decide) (by decide) (by decide) (by decide)
    · exact gen "offset_into" _ (by decide) (by decide) (by decide) (by decide)
  · exact ⟨(by intro x e; simp [feldRestToks] at e), (by intro x e; simp [feldRestToks] at e),
      (by intro x e; simp [feldRestToks] at e), (by intro x e; simp [feldRestToks] at e), rfl, rfl, rfl⟩

theorem feld_rund (fd : SFeld) (hfd : FeldGut fd) (R : List Token) (hR : FeldEnde R) (F : Nat)
    (hF : 8 * (druckFeld fd).length + 61 ≤ F) : parseFeld F (druckFeld fd ++ R) = .ok (fd, R) := by
  rw [druckFeld_eq] at hF ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hT := parse_druckTyp fd.ftyp hfd.1 (feldRestToks fd ++ R) F' (feldRest_typFolge fd R hR)
    (by simp only [fbT]; omega)
  have hRe := feldRest_rund fd hfd R hR F' (by omega)
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  simp [parseFeld, nimmName, nameText, fordereZeichen, strEq_self, hT, hRe]

theorem feldKopf (fd : SFeld) (X : List Token) : ∃ ts, druckFeld fd ++ X = .ident fd.fname :: ts := by
  rw [druckFeld_eq]; exact ⟨_, rfl⟩

theorem felder_rund : ∀ (fs : List SFeld) (R : List Token) (F : Nat), fs ≠ [] → (∀ fd ∈ fs, FeldGut fd) →
    8 * (druckFelder fs).length + 62 ≤ F →
    parseFeldFolge F (druckFelder fs ++ .zeichen "}" :: R) = .ok (fs, R) := by
  intro fs
  induction fs with
  | nil => intro _ _ h; exact absurd rfl h
  | cons fd fs ih =>
    intro R F _ hg hF
    have hfd := hg fd (by simp)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases fs with
    | nil =>
      simp only [druckFelder] at hF ⊢
      have hP := feld_rund fd hfd (.zeichen "}" :: R) (Or.inr ⟨R, rfl⟩) F' (by omega)
      simp [parseFeldFolge, hP, fordereZeichen, strEq_self]
    | cons fd2 fs2 =>
      have hd : druckFelder (fd :: fd2 :: fs2) = druckFeld fd ++ .zeichen "," :: druckFelder (fd2 :: fs2) := by
        simp [druckFelder]
      rw [hd] at hF ⊢
      simp only [List.length_append, List.length_cons] at hF
      have hP := feld_rund fd hfd (.zeichen "," :: (druckFelder (fd2 :: fs2) ++ .zeichen "}" :: R))
        (Or.inl ⟨_, rfl⟩) F' (by omega)
      have hR := ih R F' (by simp) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
      obtain ⟨ts, hts⟩ : ∃ ts, druckFelder (fd2 :: fs2) ++ .zeichen "}" :: R = .ident fd2.fname :: ts := by
        cases fs2 with
        | nil => simpa [druckFelder] using feldKopf fd2 (.zeichen "}" :: R)
        | cons x xs =>
          obtain ⟨ts, h⟩ := feldKopf fd2 (.zeichen "," :: (druckFelder (x :: xs) ++ .zeichen "}" :: R))
          exact ⟨ts, by simp [druckFelder] at h ⊢; exact h⟩
      simp only [List.append_assoc, List.cons_append] at hP ⊢
      rw [hts] at hP hR ⊢
      unfold parseFeldFolge
      simp only [hP, hR]

theorem feldListe_rund (fs : List SFeld) (hg : ∀ fd ∈ fs, FeldGut fd) (R : List Token) (F : Nat)
    (hF : 8 * (druckFelder fs).length + 63 ≤ F) :
    parseFeldListe F (.zeichen "{" :: (druckFelder fs ++ .zeichen "}" :: R)) = .ok (fs, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases fs with
  | nil => simp [druckFelder, parseFeldListe, fordereZeichen, strEq_self]
  | cons fd fs' =>
    have hFF := felder_rund (fd :: fs') R F' (by simp) hg (by omega)
    obtain ⟨ts, hts⟩ : ∃ ts, druckFelder (fd :: fs') ++ .zeichen "}" :: R = .ident fd.fname :: ts := by
      cases fs' with
      | nil => simpa [druckFelder] using feldKopf fd (.zeichen "}" :: R)
      | cons x xs =>
        obtain ⟨ts, h⟩ := feldKopf fd (.zeichen "," :: (druckFelder (x :: xs) ++ .zeichen "}" :: R))
        exact ⟨ts, by simp [druckFelder] at h ⊢; exact h⟩
    rw [hts] at hFF ⊢
    simp [parseFeldListe, fordereZeichen, strEq_self, hFF]

/-- An edge kind of a `tree`. -/
def KanteGut (k : String × String) : Prop :=
  k.1 = "parent" ∨ k.1 = "child" ∨ k.1 = "sibling"

theorem kante_rund (a b : String) (h : KanteGut (a, b)) (R : List Token) :
    parseKante (.wort a :: .ident b :: R) = .ok ((a, b), R) := by
  rcases h with h | h | h <;> simp only at h <;> subst h <;> simp [parseKante, nimmName, nameText, strEq_self]

theorem kanten_rund : ∀ (ks : List (String × String)) (R : List Token) (F : Nat), ks ≠ [] →
    (∀ k ∈ ks, KanteGut k) → ks.length ≤ F →
    parseKanten F (druckKanten ks ++ .zeichen "}" :: R) = .ok (ks, .zeichen "}" :: R) := by
  intro ks
  induction ks with
  | nil => intro _ _ h; exact absurd rfl h
  | cons k ks ih =>
    intro R F _ hg hF
    obtain ⟨a, b⟩ := k
    have hk := kante_rund a b (hg (a, b) (by simp))
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp at hF; omega⟩
    cases ks with
    | nil => simp [druckKanten, parseKanten, hk]
    | cons k2 ks2 =>
      obtain ⟨a2, b2⟩ := k2
      have hR := ih R F' (by simp) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by simp at hF ⊢; omega)
      obtain ⟨ts, hts⟩ : ∃ ts, druckKanten ((a2, b2) :: ks2) ++ .zeichen "}" :: R = .wort a2 :: ts := by
        cases ks2 <;> exact ⟨_, by simp [druckKanten]; rfl⟩
      have hd : druckKanten ((a, b) :: (a2, b2) :: ks2) = [.wort a, .ident b, .zeichen ","] ++
          druckKanten ((a2, b2) :: ks2) := by simp [druckKanten]
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
  simp [parseBaum, fordereZeichen, strEq_self, hK]


/-- A printable group invariant: printable cost and predicate, a raw proof text without `:` and
    braces. -/
def InvGut (i : SGruppenInv) : Prop :=
  gut i.kosten = true ∧ gut i.pred = true ∧
    ∀ h, i.proof = some h → RohText (fun t => t = .zeichen ":" ∨ t = .zeichen "{" ∨ t = .zeichen "}") h

theorem gruppenInv_rund (i : SGruppenInv) (hi : InvGut i) (R : List Token) (F : Nat)
    (hF : 8 * (druckGruppenInv i).length + 60 ≤ F) :
    parseGruppenInv F (druckGruppenInv i ++ R) = .ok (i, R) := by
  obtain ⟨hk, hp, hpr⟩ := hi
  obtain ⟨name, kosten, online, proof, pred⟩ := i
  simp only at hk hp hpr ⊢
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by simp [druckGruppenInv] at hF; omega⟩
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
    have hP := pred_druck pred hp (.zeichen ";" :: R) ⟨rfl, rfl, rfl, (by intro r e; simp at e),
      (by intro r e; simp at e), (by intro r e; simp at e)⟩ F' (by simp only [fb]; omega)
    simp only [druckGruppenInv, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    simp [parseGruppenInv, nimmWort, strEq_self, nimmName, nameText, nimmKostenO, fordereZeichen, hK, hm,
      hmo, hoff, parseInvRest, hP]
    all_goals exact hoff
  | some h =>
    obtain ⟨ts, rfl, hts⟩ := hpr _ rfl
    have hroh := rohToks_render ts (fun t ht => (hts t ht).1)
    simp only [druckGruppenInv, hroh, List.length_append, List.length_cons, List.length_nil] at hF
    have hK := ausdruck kosten hk (.zeichen ")" :: .wort "runs" ::
      .wort (if online then "online" else "offline") :: .wort "by" ::
        (ts ++ .zeichen ":" :: (druckToks pred ++ .zeichen ";" :: R)))
      (F' + 1) rfl rfl rfl (by omega)
    have hP := pred_druck pred hp (.zeichen ";" :: R) ⟨rfl, rfl, rfl, (by intro r e; simp at e),
      (by intro r e; simp at e), (by intro r e; simp at e)⟩ F' (by simp only [fb]; omega)
    have hN := nimmBisZeichen_roh ":" ts (druckToks pred ++ .zeichen ";" :: R)
      (fun t ht => ⟨(hts t ht).1, fun e => (hts t ht).2 (Or.inr (Or.inl e)),
        fun e => (hts t ht).2 (Or.inr (Or.inr e)), fun e => (hts t ht).2 (Or.inl e)⟩)
    simp only [druckGruppenInv, hroh, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append]
    simp [parseGruppenInv, nimmWort, strEq_self, nimmName, nameText, nimmKostenO, fordereZeichen, hK, hm,
      hmo, hoff, parseInvRest, hP, hN]
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
  simp [parseTabTeile]

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
    have hK : parseKonstNach (f' + 1) (.ident n :: .zeichen ":" :: (druckTyp ty ++ .zeichen "=" ::
        (druckKonstWert v ++ .zeichen ";" :: R))) = .ok (.constT n ty v, R) := by
      simp [parseKonstNach, nimmName, nameText, fordereZeichen, strEq_self, hT, hV]
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
      | nil => simp
      | cons n ns ih => cases ns with
        | nil => simp [druckNamen]
        | cons m ms => simp [druckNamen] at ih ⊢; omega
    simp only [druckTabTeil, List.length_append, List.length_cons, List.length_nil] at hf
    have hN := namen_rund ns (.zeichen ";" :: R) f ht (by intro r e; simp at e) (by omega)
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
      | nil => simp
      | cons k ks ih => cases ks with
        | nil => simp [druckKanten]
        | cons k2 ks2 => simp [druckKanten] at ih ⊢; omega
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
    simp only [(by decide : strEq "occupied" "const" = false),
      (by decide : strEq "occupied" "slot" = false), (by decide : strEq "occupied" "invariant" = false),
      (by decide : strEq "occupied" "ops" = false), (by decide : strEq "occupied" "tree" = false),
      (by decide : strEq "occupied" "occupied" = true), Bool.false_eq_true, ite_false, ite_true,
      nimmName, nameText, fordereZeichen, strEq_self, hR]

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
    have h1 : 1 ≤ (druckTabTeil t).length := by cases t <;> simp [druckTabTeil, druckGruppenInv]
    have hR := ih R F' (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by omega)
    rw [List.append_assoc]
    exact tabTeil_rund t (hg t (by simp)) _ _ ps F' hR (by omega)


/-! ### The table head -/

def cntToks : Option SExpr → List Token
  | some e => [.wort "count"] ++ druckToks e
  | none => []

def nameOptToks (w : String) : Option String → List Token
  | some b => [.wort w, .ident b]
  | none => []

def shToks (sh : Bool) : List Token := if sh then [.wort "shared"] else []

theorem tabKopf_ende (f : Nat) (R : List Token) :
    parseTabellenKopf (f + 1) (.zeichen "{" :: R) = .ok ((none, none, none, false), .zeichen "{" :: R) := by
  simp [parseTabellenKopf]

theorem tabKopf_shared (f : Nat) (R X : List Token) (c : Option SExpr) (b o : Option String) (g : Bool)
    (h : parseTabellenKopf f R = .ok ((c, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "shared" :: R) = .ok ((c, b, o, true), X) := by
  simp [parseTabellenKopf, h, strEq_self, (by decide : strEq "shared" "count" = false),
    (by decide : strEq "shared" "backed" = false), (by decide : strEq "shared" "owner" = false)]

theorem tabKopf_owner (f : Nat) (n : String) (R X : List Token) (c : Option SExpr) (b o : Option String)
    (g : Bool) (h : parseTabellenKopf f R = .ok ((c, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "owner" :: .ident n :: R) = .ok ((c, b, some n, g), X) := by
  simp [parseTabellenKopf, h, strEq_self, nimmName, nameText, (by decide : strEq "owner" "count" = false),
    (by decide : strEq "owner" "backed" = false)]

theorem tabKopf_backed (f : Nat) (n : String) (R X : List Token) (c : Option SExpr) (b o : Option String)
    (g : Bool) (h : parseTabellenKopf f R = .ok ((c, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "backed" :: .ident n :: R) = .ok ((c, some n, o, g), X) := by
  simp [parseTabellenKopf, h, strEq_self, nimmName, nameText, (by decide : strEq "backed" "count" = false)]

theorem tabKopf_count (f : Nat) (e : SExpr) (R X : List Token) (c : Option SExpr) (b o : Option String)
    (g : Bool) (hO : parseOr f (druckToks e ++ R) = .ok (e, R))
    (h : parseTabellenKopf f R = .ok ((c, b, o, g), X)) :
    parseTabellenKopf (f + 1) (.wort "count" :: (druckToks e ++ R)) = .ok ((some e, b, o, g), X) := by
  simp [parseTabellenKopf, h, hO, strEq_self]

theorem tabKopf_rund (cnt : Option SExpr) (backed owner : Option String) (sh : Bool)
    (hc : ∀ e, cnt = some e → gut e = true) (R : List Token) (F : Nat)
    (hF : 8 * (cntToks cnt ++ nameOptToks "backed" backed ++ nameOptToks "owner" owner ++ shToks sh).length + 40 ≤ F) :
    parseTabellenKopf F (cntToks cnt ++ nameOptToks "backed" backed ++ nameOptToks "owner" owner ++ shToks sh ++
      .zeichen "{" :: R) = .ok ((cnt, backed, owner, sh), .zeichen "{" :: R) := by
  have L1 : ∀ G, 2 ≤ G → parseTabellenKopf G (shToks sh ++ .zeichen "{" :: R) =
      .ok ((none, none, none, sh), .zeichen "{" :: R) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    cases sh
    · simpa [shToks] using tabKopf_ende (G' + 1) R
    · simpa [shToks] using tabKopf_shared (G' + 1) _ _ none none none false (tabKopf_ende G' R)
  have L2 : ∀ G, 3 ≤ G → parseTabellenKopf G (nameOptToks "owner" owner ++ (shToks sh ++ .zeichen "{" :: R)) =
      .ok ((none, none, owner, sh), .zeichen "{" :: R) := by
    intro G hG
    cases owner with
    | none => simpa [nameOptToks] using L1 G (by omega)
    | some o =>
      obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      simpa [nameOptToks] using tabKopf_owner G' o _ _ none none none sh (L1 G' (by omega))
  have L3 : ∀ G, 4 ≤ G → parseTabellenKopf G (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++
      (shToks sh ++ .zeichen "{" :: R))) = .ok ((none, backed, owner, sh), .zeichen "{" :: R) := by
    intro G hG
    cases backed with
    | none => simpa [nameOptToks] using L2 G (by omega)
    | some b =>
      obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
      simpa [nameOptToks] using tabKopf_backed G' b _ _ none none owner sh (L2 G' (by omega))
  simp only [List.append_assoc] at hF ⊢
  cases cnt with
  | none => simpa [cntToks] using L3 F (by simp [cntToks] at hF; omega)
  | some e =>
    have he := hc e rfl
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp [cntToks] at hF; omega⟩
    have hrX : ruhig (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++ (shToks sh ++ .zeichen "{" :: R))) = true ∧
        ruhigSuff (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++ (shToks sh ++ .zeichen "{" :: R))) = true ∧
        ruhigGleit (nameOptToks "backed" backed ++ (nameOptToks "owner" owner ++ (shToks sh ++ .zeichen "{" :: R))) = true := by
      cases backed <;> cases owner <;> cases sh <;> exact ⟨rfl, rfl, rfl⟩
    have hO := ausdruck e he _ F' hrX.1 hrX.2.1 hrX.2.2 (by simp [cntToks] at hF; omega)
    have := tabKopf_count F' e _ _ none backed owner sh hO (L3 F' (by simp [cntToks] at hF; omega))
    simpa [cntToks] using this

theorem item_table (n : String) (cnt : Option SExpr) (backed owner : Option String) (sh : Bool)
    (parts : List STabTeil) (hc : ∀ e, cnt = some e → gut e = true) (hp : ∀ t ∈ parts, TeilGut t) :
    ItemBein (.tableT n cnt backed owner sh parts) := by
  intro rest F hF
  have hd : druckItem (.tableT n cnt backed owner sh parts) ++ rest = .wort "table" :: .ident n ::
      (cntToks cnt ++ nameOptToks "backed" backed ++ nameOptToks "owner" owner ++ shToks sh ++
        .zeichen "{" :: (druckTabTeile parts ++ .zeichen "}" :: rest)) := by
    cases cnt <;> cases backed <;> cases owner <;> cases sh <;>
      simp [druckItem, cntToks, nameOptToks, shToks]
  have hlen : (druckItem (.tableT n cnt backed owner sh parts)).length = 2 +
      (cntToks cnt ++ nameOptToks "backed" backed ++ nameOptToks "owner" owner ++ shToks sh).length + 1 +
      (druckTabTeile parts).length + 1 := by
    cases cnt <;> cases backed <;> cases owner <;> cases sh <;>
      simp [druckItem, cntToks, nameOptToks, shToks] <;> omega
  simp only [fbI, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hK := tabKopf_rund cnt backed owner sh hc (druckTabTeile parts ++ .zeichen "}" :: rest) F' (by omega)
  have hT := tabTeile_rund parts rest F' hp (by omega)
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_table]
  simp only [List.append_assoc] at hK
  simp [parseTabellenTief, nimmWort, strEq_self, nimmName, nameText, hK, fordereZeichen, hT]


/-! ### The printability class of items and the induction -/

/-- **The printability class of items** (see the header). -/
inductive ItemGut : SItemTief → Prop
  | modT (segs : List String) (its : List SItemTief) :
      PfadGut segs → (∀ it ∈ its, ItemGut it) → ItemGut (.modT ("::".intercalate segs) its)
  | useT (p : List String) : p ≠ [] → ItemGut (.useT p)
  | constT (n : String) (t : STyp) (v : SKonstWert) : TypGut t → KonstGut v → ItemGut (.constT n t v)
  | globT (m : Bool) (n : String) (t : STyp) (v : SKonstWert) (al : Option SExpr) (s : Option String)
      (sh : Bool) : TypGut t → KonstGut v → (∀ e, al = some e → gut e = true) →
      ItemGut (.globT m n t v al s sh)
  | fnT (sig : FnSig) (b : SAnw) : SigGut sig → AnwGut .block b → ItemGut (.fnT sig b)
  | protoT (sig : FnSig) : SigGut sig → ItemGut (.protoT sig)
  | lockT (n : String) (ps : List SExpr) (rk : SExpr) (h sh : Option SExpr) (m : Option String)
      (inv : Option SExpr) : (∀ p ∈ ps, gut p = true) → gut rk = true → (∀ e, h = some e → gut e = true) →
      (∀ e, sh = some e → gut e = true) → (∀ e, inv = some e → gut e = true) →
      ItemGut (.lockT n ps rk h sh m inv)
  | atomT (n : String) (t : STyp) (pub : Option (List SExpr)) (ord obs : Option String) :
      TypGut t → AtomGut pub ord → ItemGut (.atomT n t pub ord obs)
  | whyT (n : String) (cs : List (String × SExpr × String)) (ex : Bool) :
      (∀ c ∈ cs, FallGut c) → ItemGut (.whyT n cs ex)
  | concT (ps : List (List String)) : (∀ p ∈ ps, PfadGut p) → ItemGut (.concT ps)
  | tableT (n : String) (cnt : Option SExpr) (backed owner : Option String) (sh : Bool)
      (parts : List STabTeil) : (∀ e, cnt = some e → gut e = true) → (∀ t ∈ parts, TeilGut t) →
      ItemGut (.tableT n cnt backed owner sh parts)

theorem itemKopf_wort (it : SItemTief) (w : String) (h1 : w ≠ "when") (h2 : w ≠ "pub")
    (h : ∃ ts, druckItem it = .wort w :: ts) : ItemKopf it := by
  obtain ⟨ts, h⟩ := h; exact ⟨w, ts, h, h1, h2⟩

theorem fn_kopf (sig : FnSig) (hs : SigGut sig) (X : List Token) :
    ∃ w ts, druckFnSig sig ++ X = .wort w :: ts ∧ w ≠ "when" ∧ w ≠ "pub" := by
  obtain ⟨hart, -⟩ := hs
  obtain ⟨ts, hts⟩ := sigToks_kopf sig
  rw [druckFnSig_eq]
  rcases hart with h | h | h
  · refine ⟨"fn", ts ++ X, ?_, by decide, by decide⟩
    simp [h, strEq_self, hts]
  · refine ⟨"const", sigToks sig ++ X, ?_, by decide, by decide⟩
    simp [h, (by decide : strEq "const" "" = false)]
  · have hne : strEq sig.art "" = false := by
      cases e : strEq sig.art ""
      · rfl
      · have := (strEq_eq _ _).mp e; rw [this] at h; exact absurd h (by decide)
    refine ⟨sig.art, sigToks sig ++ X, ?_, ?_, ?_⟩
    · simp [hne]
    · intro e; rw [e] at h; exact absurd h (by decide)
    · intro e; rw [e] at h; exact absurd h (by decide)

/-- **The induction over items.** -/
theorem item_bein : ∀ (it : SItemTief), ItemGut it → ItemBein it ∧ ItemKopf it := by
  intro it h
  induction h with
  | modT segs its hs _ ih =>
    exact ⟨item_mod segs its hs ih, itemKopf_wort _ "module" (by decide) (by decide) ⟨_, rfl⟩⟩
  | useT p hp => exact ⟨item_use p hp, itemKopf_wort _ "use" (by decide) (by decide) ⟨_, rfl⟩⟩
  | constT n t v ht hv =>
    exact ⟨item_const n t v ht hv, itemKopf_wort _ "const" (by decide) (by decide) ⟨_, rfl⟩⟩
  | globT m n t v al s sh ht hv hal =>
    exact ⟨item_static m n t v al s sh ht hv hal, itemKopf_wort _ "static" (by decide) (by decide) ⟨_, rfl⟩⟩
  | fnT sig b hs hb =>
    obtain ⟨hbb, hbk⟩ := bein_gut .block b hb
    refine ⟨item_fn sig b hs hbb hbk, ?_⟩
    obtain ⟨w, ts, hd, h1, h2⟩ := fn_kopf sig hs (druckAnw b)
    exact ⟨w, ts, by simpa [druckItem] using hd, h1, h2⟩
  | protoT sig hs =>
    refine ⟨item_proto sig hs, ?_⟩
    obtain ⟨w, ts, hd, h1, h2⟩ := fn_kopf sig hs [.zeichen ";"]
    exact ⟨w, ts, by simpa [druckItem] using hd, h1, h2⟩
  | lockT n ps rk h sh m inv hps hrk hh hs hi =>
    exact ⟨item_lock n ps rk h sh m inv hps hrk hh hs hi,
      itemKopf_wort _ "lock" (by decide) (by decide) ⟨_, rfl⟩⟩
  | atomT n t pub ord obs ht hg =>
    exact ⟨item_atom n t pub ord obs ht hg, itemKopf_wort _ "atomic" (by decide) (by decide) ⟨_, rfl⟩⟩
  | whyT n cs ex hg => exact ⟨item_why n cs ex hg, itemKopf_wort _ "reason" (by decide) (by decide) ⟨_, rfl⟩⟩
  | concT ps hps =>
    exact ⟨item_conc ps hps, itemKopf_wort _ "concurrent" (by decide) (by decide) ⟨_, rfl⟩⟩
  | tableT n cnt backed owner sh parts hc hp =>
    exact ⟨item_table n cnt backed owner sh parts hc hp,
      itemKopf_wort _ "table" (by decide) (by decide) ⟨_, rfl⟩⟩

/-- **L2c: printable items read back** through `parseItemsTief`, before `}`, the end marker or
    nothing. -/
theorem rundlauf_items (its : List SItemTief) (h : ∀ it ∈ its, ItemGut it) (R : List Token)
    (hR : ItemsEnde R) (F : Nat) (hF : 8 * (druckItems its).length + 39 ≤ F) :
    parseItemsTief F (druckItems its ++ R) = .ok (its, R) :=
  items_rund its R F (fun it hit => item_bein it (h it hit)) hR hF

/-- **The whole program reader** (`parseTopTief`, fuel `8 * length + 32`) returns every list of
    printable items. -/
theorem parseTopTief_druck (its : List SItemTief) (h : ∀ it ∈ its, ItemGut it) :
    parseTopTief (druckItems its ++ [.ende]) = .ok its := by
  unfold parseTopTief
  rw [rundlauf_items its h [.ende] (Or.inr (Or.inr ⟨[], rfl⟩)) _
    (by simp only [List.length_append, List.length_singleton]; omega)]

/-- **The composition of all layers**: printable items whose print is lexically clean read back
    from their rendered source text -- lexer (L1), then the program reader (L2c over L2b over
    L2a). -/
theorem rundlauf_programm (its : List SItemTief) (h : ∀ it ∈ its, ItemGut it)
    (ht : ∀ t ∈ druckItems its, TokGut t) :
    (match lex (renderText (druckItems its)) with
      | .ok toks => parseTopTief toks
      | .error _ => .error "lex") = .ok its := by
  rw [lex_render _ ht]
  exact parseTopTief_druck its h


/-! ### Witnesses -/

/-- A program with every covered item kind: `use`, `const` with an array value, `static mut ...
    shared`, a `lock` with `held`, an `atomic` with `publishes nothing` and an order, a `reason`, a
    `module` holding a function with a contract (`requires`, `effects`, `costs`), a result type and
    a body, `concurrent` over a two-segment path, and a `table` with a count, `shared`, a slot field
    with `where` and `by ops`, `ops`, `tree`, `occupied` and a group invariant. -/
def zeugeProgramm : List SItemTief := [
  .useT ["io", "konsole"],
  .constT "N" (.atom "u32") (.rows [.one (.lit 1), .one (.lit 2)]),
  .globT true "zaehler" (.atom "u64") (.one (.lit 0)) none none true,
  .lockT "L" [.variable "zaehler"] (.lit 1) (some (.lit 10)) none none none,
  .atomT "flag" (.atom "bool") (some []) (some "release") none,
  .whyT "Fehler" [("Voll", .lit 1, "voll")] true,
  .modT ("::".intercalate ["kern"]) [
    .fnT { art := "", name := "erhoehe", params := [("wert", .atom "u64")], res := some (.atom "u64"),
           fehler := none,
           klauseln := [.needs (.bin "<" (.variable "wert") (.lit 100)),
                        .effs [.writes (.variable "zaehler")], .cost (.lit 5)] }
      (.block [.set (.variable "zaehler") "+=" (.variable "wert")] (some (.ret (some (.variable "wert")))))],
  .concT [["kern", "erhoehe"]],
  .tableT "Knoten" (some (.lit 64)) none none true [
    .tSlot [{ fname := "wert", ftyp := .atom "u32", pos := none, bezug := none,
              wo := some (.bin "<" (.variable "wert") (.lit 10)), reserviert := false, byOps := true }],
    .tOps ["einfuegen", "loeschen"],
    .tTree [("parent", "eltern")],
    .tBusy "belegt",
    .tInv { name := "klein", kosten := .lit 1, online := true, proof := none,
            pred := .bin "<" (.variable "n") (.lit 64) }]]

theorem zeugeProgramm_gut : ∀ it ∈ zeugeProgramm, ItemGut it := by
  have atom : ∀ a, typKopf a = false → TypGut (.atom a) := fun a h => by
    have := TypGut.kette (.atom a) [] (.atom a h) (by simp [TsGut]); simpa [applyTS] using this
  intro it hit
  simp only [zeugeProgramm, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .useT _ (by simp)
  · refine .constT _ _ _ (atom _ (by decide)) (.rows _ ?_)
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> exact .one _ (by decide)
  · exact .globT _ _ _ _ _ _ _ (atom _ (by decide)) (.one _ (by decide)) (by simp)
  · refine .lockT _ _ _ _ _ _ _ (by simp; decide) (by decide) ?_ (by simp) (by simp)
    intro e he; cases he; decide
  · exact .atomT _ _ _ _ _ (atom _ (by decide)) ⟨by intro ps h p hp; cases h; simp at hp,
      by intro o h; cases h; decide⟩
  · exact .whyT _ _ _ (by intro c hc; simp at hc; subst hc; show gut (.lit 1) = true; decide)
  · refine .modT ["kern"] _ ⟨by simp, by intro a ha; simp at ha; subst ha; exact ⟨by decide, by decide⟩⟩ ?_
    intro it hit; simp at hit; subst hit
    refine .fnT _ _ ⟨Or.inl rfl, ?_, atom _ (by decide), ?_⟩ ?_
    · intro p hp; simp at hp; subst hp; exact atom _ (by decide)
    · intro k hk; simp at hk
      rcases hk with rfl | rfl | rfl
      · show gut _ = true; decide
      · intro e he; simp at he; subst he; show gut _ = true; decide
      · show gut _ = true; decide
    · refine .block _ _ ?_ (by show gut _ = true; decide) (by intro h; cases h)
      intro s hs; simp at hs; subst hs
      exact .set _ _ _ (by decide) (by decide) (by decide)
  · exact .concT _ (by
      intro p hp; simp at hp; subst hp
      exact ⟨by simp, by intro a ha; simp at ha; rcases ha with rfl | rfl <;> exact ⟨by decide, by decide⟩⟩)
  · refine .tableT _ _ _ _ _ _ (by intro e he; cases he; decide) ?_
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · intro fd hfd; simp at hfd; subst hfd
      exact ⟨atom _ (by decide), by simp, by intro e he; cases he; decide⟩
    · show _ ≠ []; simp
    · exact ⟨by simp, by intro k hk; simp at hk; subst hk; exact Or.inl rfl⟩
    · trivial
    · exact ⟨by decide, by decide, by simp⟩

/-- The witness program reads back through the whole program reader. -/
theorem zeugeProgramm_rund : parseTopTief (druckItems zeugeProgramm ++ [.ende]) = .ok zeugeProgramm :=
  parseTopTief_druck zeugeProgramm zeugeProgramm_gut

/-- The witness program from its rendered source text: lexer, then the program reader. -/
theorem zeugeProgramm_text :
    (match lex (renderText (druckItems zeugeProgramm)) with
      | .ok toks => parseTopTief toks
      | .error _ => .error "lex") = .ok zeugeProgramm :=
  rundlauf_programm zeugeProgramm zeugeProgramm_gut (tokGut_of_all _ (by decide))


end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.rundlauf_items
#print axioms Gabbro.Grammatik.Parser.parseTopTief_druck
#print axioms Gabbro.Grammatik.Parser.rundlauf_programm
#print axioms Gabbro.Grammatik.Parser.zeugeProgramm_rund
#print axioms Gabbro.Grammatik.Parser.zeugeProgramm_text

/-
  CUTS: what the item round trip does not cover yet, and why.

  * Item kinds not in `ItemGut`: `type`, `format`, `arena`, `state`, `device`, `assume`,
    `axiom`, `check`, `rcu`, `group`, `accumulates`, `walk`, `entry`, `entrust`, `boot`, `syscall`,
    `target`, `translator`, `profile`, the spec/asm function bodies (`= pred ;`, `= asm {..} ;`) and
    the `when TESTBUILD` gate; slot bit positions as a `[hi:lo]` group. Each is one more constructor of `ItemGut` with its reader lemma in
    the pattern of `item_lock`/`item_atom` (a named recursive tail reader is a step lemma per
    clause; a `do` block is a case split over its optional clauses). `device` and `entry` are the
    largest (register maps, banks, transitions).
  * Clauses riding as reconstructed text (`by`, `retires`, `deadline`): the reader rebuilds a
    string from tokens (`druck e`, `nimmBisKopf`), the printer re-lexes it; excluded from
    `KlauselGut`.
  * Paths printed as text (`module`, `concurrent`) need name-shaped non-table segments
    (`PfadGut`): the printer re-lexes the joined text.
  * As everywhere, the text-level theorem (`rundlauf_programm`) needs every identifier token of the
    print to be a non-table word (`TokGut`); type atoms print as `nameTok` and are covered.
-/
