/-
  File:      Grammatik/Parser/Round/RundlaufAnwVoll.lean
  Subject:   Layer L2b: every printable statement and block reads back -- `parseStmt`/`parseBlock` of
             the statement printer's tokens (`druckAnw`, Print/Stmt.lean) return the tree.

  `rundlauf_anw`: for every statement in the printability class `AnwGut .anw` and every follow that
  does not start with `else` (`KE`), `parseStmt F (druckAnw s ++ rest) = .ok (s, rest)` with fuel
  `fbA s = 8 * #tokens + 30` or more; `rundlauf_block`: the same for blocks through `parseBlock`,
  whatever follows. The proof is one induction over the printability derivation (`AnwGut`, indexed
  by the position: statement, block, `else if` branch, `match` arm), one lemma per statement form.

  The class `AnwGut` (stated in full below) is what the reader forces, form by form:
  - expressions are `gut` (L2a), places are `gutPlatz`, types `TypGut` (RundlaufTyp);
  - every body is a block (`AnwGut .block`), `else if` branches and `match` arms are `elsif`/`arm`
    nodes in their lists; a block without an ender does not end in `return`/`leave`/`next`
    (`EndeGut`: the reader would take it for the ender);
  - raw header texts are rendered token lists without the collector's stop tokens (`RohText`);
  - names print as `nameTok`, the lexer's token (a table word is a `wort`): a `let` binder is no
    `mut`, a place head no `transition` and none of the primary words (`istKopfWort`), a call head
    no statement head word (`istAnwWort`), the place of a plain `locks` no `shared`;
  - a call head and a `start` root are a single name-shaped word (the printer re-lexes the
    text); `breaking` and `start` carry at least one name; `narrow ... to` is `finite` or a raw text
    that does not start with `finite`; a `publishes` payload other than `nothing` is a raw text.
  Excluded, with the reason (recorded in the CUTS at the end): `.other` (never read), a bare block
  as a statement (the reader has no such statement), calls through a `::` path or a place
  (`a::f(x)`, `p->f(x)`: the printer prints the text of the callee), `let ... else` with `mut`
  (the form has no `mut`), raw texts with braces, `;`, or stop words inside.
-/
module

public import Grammatik.Parser.Round.RundlaufQuant.Teil2

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ### Shapes of a follow, legs, fuel -/

/-- The follow does not start with `else` (a statement list never does). -/
def KE (rest : List Token) : Prop := ∀ r, rest ≠ .wort "else" :: r

/-- The fuel bound of a statement or block: eight per printed token, thirty spare. -/
def fbA (s : SAnw) : Nat := 8 * (druckAnw s).length + 30

/-- A statement reads back before every `else`-free follow. -/
def AnwBein (s : SAnw) : Prop :=
  ∀ (rest : List Token) (F : Nat), KE rest → fbA s ≤ F → parseStmt F (druckAnw s ++ rest) = .ok (s, rest)

/-- A block reads back before every follow. -/
def BlockBein (b : SAnw) : Prop :=
  ∀ (rest : List Token) (F : Nat), fbA b ≤ F → parseBlock F (druckAnw b ++ rest) = .ok (b, rest)

/-- The first token of a statement print: no `}`, no `else`, no end marker. -/
def AnwKopf (s : SAnw) : Prop :=
  ∃ t ts, druckAnw s = t :: ts ∧ t ≠ .zeichen "}" ∧ t ≠ .wort "else" ∧ t ≠ .ende

/-- A raw text: a rendered token list with none of the stop tokens. -/
def RohText (stop : Token → Prop) (s : String) : Prop :=
  ∃ ts, s = renderText ts ∧ ∀ t ∈ ts, TokGut t ∧ ¬ stop t

/-- The name token opens no place continuation. -/
theorem ortsFort_nameTok (s : String) (r : List Token) : istOrtsFort (nameTok s :: r) = false := by
  unfold nameTok; split <;> rfl

theorem ke_zeichen (z : String) (r : List Token) : KE (.zeichen z :: r) := by
  intro r' e; cases e

/-- The head variable of a place. -/
def kopfName : SExpr → String
  | .variable s => s
  | .field x _ => kopfName x
  | .index x _ => kopfName x
  | .arrow x _ => kopfName x
  | _ => ""

theorem platz_kopfName_aux : ∀ (n : Nat) (p : SExpr), groesse p ≤ n → gutPlatz p = true →
    ∃ ts, druckToks p = nameTok (kopfName p) :: ts := by
  intro n
  induction n with
  | zero => intro p hs _; have := groesse_pos p; omega
  | succ n ih =>
    intro p hs hg
    cases p with
    | «variable» s => exact ⟨[], by simp only [druckToks, kopfName]⟩
    | field y f =>
      obtain ⟨ts, h⟩ := ih y (by simp only [groesse] at hs; omega) (by simpa [gutPlatz] using hg)
      exact ⟨ts ++ [.zeichen ".", nameTok f], by simp only [druckToks, h, List.cons_append, kopfName]⟩
    | index y i =>
      obtain ⟨ts, h⟩ := ih y (by simp only [groesse] at hs; omega)
        (by simp only [gutPlatz, Bool.and_eq_true] at hg; exact hg.1)
      exact ⟨ts ++ ([.zeichen "["] ++ druckToks i ++ [.zeichen "]"]), by simp only [druckToks, h, List.cons_append, List.append_assoc, List.nil_append, kopfName]⟩
    | arrow y f =>
      obtain ⟨ts, h⟩ := ih y (by simp only [groesse] at hs; omega) (by simpa [gutPlatz] using hg)
      exact ⟨ts ++ [.zeichen "->", nameTok f], by simp only [druckToks, h, List.cons_append, kopfName]⟩
    | _ => simp only [gutPlatz, Bool.false_eq_true] at hg

/-- A place prints with its head variable's name token. -/
theorem platz_kopfName (p : SExpr) (hp : gutPlatz p = true) :
    ∃ ts, druckToks p = nameTok (kopfName p) :: ts :=
  platz_kopfName_aux (groesse p) p (Nat.le_refl _) hp

theorem nameTok_inj {a b : String} (h : nameTok a = nameTok b) : a = b := by
  have := congrArg nameText h; simpa using this

/-! ### Statement dispatch on the head word -/

theorem parseStmt_let (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "let" :: rest) = parseLet f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "let" "let" = true)]

theorem parseStmt_if (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "if" :: rest) = parseWenn f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "if" "let" = false), (by decide : strEq "if" "if" = true)]

theorem parseStmt_match (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "match" :: rest) = parseMatchS f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "match" "let" = false), (by decide : strEq "match" "if" = false), (by decide : strEq "match" "match" = true)]

theorem parseStmt_traverse (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "traverse" :: rest) = parseTraverse f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "traverse" "let" = false), (by decide : strEq "traverse" "if" = false), (by decide : strEq "traverse" "match" = false), (by decide : strEq "traverse" "traverse" = true)]

theorem parseStmt_retry (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "retry" :: rest) = parseSchleife f rest 1 := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "retry" "let" = false), (by decide : strEq "retry" "if" = false), (by decide : strEq "retry" "match" = false), (by decide : strEq "retry" "traverse" = false), (by decide : strEq "retry" "retry" = true)]

theorem parseStmt_forever (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "forever" :: rest) = parseSchleife f rest 2 := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "forever" "let" = false), (by decide : strEq "forever" "if" = false), (by decide : strEq "forever" "match" = false), (by decide : strEq "forever" "traverse" = false), (by decide : strEq "forever" "retry" = false), (by decide : strEq "forever" "forever" = true)]

theorem parseStmt_breaking (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "breaking" :: rest) = parseBricht f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "breaking" "let" = false), (by decide : strEq "breaking" "if" = false), (by decide : strEq "breaking" "match" = false), (by decide : strEq "breaking" "traverse" = false), (by decide : strEq "breaking" "retry" = false), (by decide : strEq "breaking" "forever" = false), (by decide : strEq "breaking" "breaking" = true)]

theorem parseStmt_narrow (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "narrow" :: rest) = parseNarrow f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "narrow" "let" = false), (by decide : strEq "narrow" "if" = false), (by decide : strEq "narrow" "match" = false), (by decide : strEq "narrow" "traverse" = false), (by decide : strEq "narrow" "retry" = false), (by decide : strEq "narrow" "forever" = false), (by decide : strEq "narrow" "breaking" = false), (by decide : strEq "narrow" "narrow" = true)]

theorem parseStmt_locks (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "locks" :: rest) = parseSperrt f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "locks" "let" = false), (by decide : strEq "locks" "if" = false), (by decide : strEq "locks" "match" = false), (by decide : strEq "locks" "traverse" = false), (by decide : strEq "locks" "retry" = false), (by decide : strEq "locks" "forever" = false), (by decide : strEq "locks" "breaking" = false), (by decide : strEq "locks" "narrow" = false), (by decide : strEq "locks" "locks" = true)]

theorem parseStmt_observes (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "observes" :: rest) = parseBeobachtet f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "observes" "let" = false), (by decide : strEq "observes" "if" = false), (by decide : strEq "observes" "match" = false), (by decide : strEq "observes" "traverse" = false), (by decide : strEq "observes" "retry" = false), (by decide : strEq "observes" "forever" = false), (by decide : strEq "observes" "breaking" = false), (by decide : strEq "observes" "narrow" = false), (by decide : strEq "observes" "locks" = false), (by decide : strEq "observes" "observes" = true)]

theorem parseStmt_leave (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "leave" :: rest) = parseVerlasse f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "leave" "let" = false), (by decide : strEq "leave" "if" = false), (by decide : strEq "leave" "match" = false), (by decide : strEq "leave" "traverse" = false), (by decide : strEq "leave" "retry" = false), (by decide : strEq "leave" "forever" = false), (by decide : strEq "leave" "breaking" = false), (by decide : strEq "leave" "narrow" = false), (by decide : strEq "leave" "locks" = false), (by decide : strEq "leave" "observes" = false), (by decide : strEq "leave" "leave" = true)]

theorem parseStmt_next (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "next" :: rest) = parseWeiter f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "next" "let" = false), (by decide : strEq "next" "if" = false), (by decide : strEq "next" "match" = false), (by decide : strEq "next" "traverse" = false), (by decide : strEq "next" "retry" = false), (by decide : strEq "next" "forever" = false), (by decide : strEq "next" "breaking" = false), (by decide : strEq "next" "narrow" = false), (by decide : strEq "next" "locks" = false), (by decide : strEq "next" "observes" = false), (by decide : strEq "next" "leave" = false), (by decide : strEq "next" "next" = true)]

theorem parseStmt_return (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "return" :: rest) = parseRueck f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "return" "let" = false), (by decide : strEq "return" "if" = false), (by decide : strEq "return" "match" = false), (by decide : strEq "return" "traverse" = false), (by decide : strEq "return" "retry" = false), (by decide : strEq "return" "forever" = false), (by decide : strEq "return" "breaking" = false), (by decide : strEq "return" "narrow" = false), (by decide : strEq "return" "locks" = false), (by decide : strEq "return" "observes" = false), (by decide : strEq "return" "leave" = false), (by decide : strEq "return" "next" = false), (by decide : strEq "return" "return" = true)]

theorem parseStmt_reset (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "reset" :: rest) = parseReset f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "reset" "let" = false), (by decide : strEq "reset" "if" = false), (by decide : strEq "reset" "match" = false), (by decide : strEq "reset" "traverse" = false), (by decide : strEq "reset" "retry" = false), (by decide : strEq "reset" "forever" = false), (by decide : strEq "reset" "breaking" = false), (by decide : strEq "reset" "narrow" = false), (by decide : strEq "reset" "locks" = false), (by decide : strEq "reset" "observes" = false), (by decide : strEq "reset" "leave" = false), (by decide : strEq "reset" "next" = false), (by decide : strEq "reset" "return" = false), (by decide : strEq "reset" "reset" = true)]

theorem parseStmt_grow (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "grow" :: rest) = parseGrow f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "grow" "let" = false), (by decide : strEq "grow" "if" = false), (by decide : strEq "grow" "match" = false), (by decide : strEq "grow" "traverse" = false), (by decide : strEq "grow" "retry" = false), (by decide : strEq "grow" "forever" = false), (by decide : strEq "grow" "breaking" = false), (by decide : strEq "grow" "narrow" = false), (by decide : strEq "grow" "locks" = false), (by decide : strEq "grow" "observes" = false), (by decide : strEq "grow" "leave" = false), (by decide : strEq "grow" "next" = false), (by decide : strEq "grow" "return" = false), (by decide : strEq "grow" "reset" = false), (by decide : strEq "grow" "grow" = true)]

theorem parseStmt_free (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "free" :: rest) = parseFree f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "free" "let" = false), (by decide : strEq "free" "if" = false), (by decide : strEq "free" "match" = false), (by decide : strEq "free" "traverse" = false), (by decide : strEq "free" "retry" = false), (by decide : strEq "free" "forever" = false), (by decide : strEq "free" "breaking" = false), (by decide : strEq "free" "narrow" = false), (by decide : strEq "free" "locks" = false), (by decide : strEq "free" "observes" = false), (by decide : strEq "free" "leave" = false), (by decide : strEq "free" "next" = false), (by decide : strEq "free" "return" = false), (by decide : strEq "free" "reset" = false), (by decide : strEq "free" "grow" = false), (by decide : strEq "free" "free" = true)]

theorem parseStmt_child (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "child" :: rest) = parseChild f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "child" "let" = false), (by decide : strEq "child" "if" = false), (by decide : strEq "child" "match" = false), (by decide : strEq "child" "traverse" = false), (by decide : strEq "child" "retry" = false), (by decide : strEq "child" "forever" = false), (by decide : strEq "child" "breaking" = false), (by decide : strEq "child" "narrow" = false), (by decide : strEq "child" "locks" = false), (by decide : strEq "child" "observes" = false), (by decide : strEq "child" "leave" = false), (by decide : strEq "child" "next" = false), (by decide : strEq "child" "return" = false), (by decide : strEq "child" "reset" = false), (by decide : strEq "child" "grow" = false), (by decide : strEq "child" "free" = false), (by decide : strEq "child" "child" = true)]

theorem parseStmt_transition (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "transition" :: rest) = parseUebergang f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "transition" "let" = false), (by decide : strEq "transition" "if" = false), (by decide : strEq "transition" "match" = false), (by decide : strEq "transition" "traverse" = false), (by decide : strEq "transition" "retry" = false), (by decide : strEq "transition" "forever" = false), (by decide : strEq "transition" "breaking" = false), (by decide : strEq "transition" "narrow" = false), (by decide : strEq "transition" "locks" = false), (by decide : strEq "transition" "observes" = false), (by decide : strEq "transition" "leave" = false), (by decide : strEq "transition" "next" = false), (by decide : strEq "transition" "return" = false), (by decide : strEq "transition" "reset" = false), (by decide : strEq "transition" "grow" = false), (by decide : strEq "transition" "free" = false), (by decide : strEq "transition" "child" = false), (by decide : strEq "transition" "transition" = true)]

theorem parseStmt_advances (f : Nat) (rest : List Token) (h : istOrtsFort rest = false) :
    parseStmt (f + 1) (.wort "advances" :: rest) = parseSchreitet f rest := by
  simp only [parseStmt, h, Bool.false_eq_true, ite_false, ite_true, (by decide : strEq "advances" "let" = false), (by decide : strEq "advances" "if" = false), (by decide : strEq "advances" "match" = false), (by decide : strEq "advances" "traverse" = false), (by decide : strEq "advances" "retry" = false), (by decide : strEq "advances" "forever" = false), (by decide : strEq "advances" "breaking" = false), (by decide : strEq "advances" "narrow" = false), (by decide : strEq "advances" "locks" = false), (by decide : strEq "advances" "observes" = false), (by decide : strEq "advances" "leave" = false), (by decide : strEq "advances" "next" = false), (by decide : strEq "advances" "return" = false), (by decide : strEq "advances" "reset" = false), (by decide : strEq "advances" "grow" = false), (by decide : strEq "advances" "free" = false), (by decide : strEq "advances" "child" = false), (by decide : strEq "advances" "transition" = false), (by decide : strEq "advances" "advances" = true)]

/-! ### Lists and blocks -/

/-- A statement list up to the closing brace. -/
theorem parseStmts_rund : ∀ (ss : List SAnw) (rest : List Token) (F : Nat),
    (∀ s ∈ ss, AnwBein s ∧ AnwKopf s) → 8 * (druckAnwListe ss).length + 31 ≤ F →
    parseStmts F (druckAnwListe ss ++ .zeichen "}" :: rest) = .ok (ss, .zeichen "}" :: rest) := by
  intro ss
  induction ss with
  | nil =>
    intro rest F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseStmts, druckAnwListe, List.nil_append]
  | cons s ss ih =>
    intro rest F h hF
    obtain ⟨hB, t, ts, hd, h1, h2, h3⟩ := h s (by simp only [List.mem_cons, true_or])
    have hss := fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckAnwListe, List.length_append] at hF
    have hl : 1 ≤ (druckAnw s).length := by rw [hd]; simp only [List.length_cons, Nat.le_add_left]
    have hK : KE (druckAnwListe ss ++ .zeichen "}" :: rest) := by
      intro r e
      cases ss with
      | nil => simp only [druckAnwListe, List.nil_append, List.cons.injEq, reduceCtorEq, false_and] at e
      | cons s2 ss2 =>
        obtain ⟨-, t2, ts2, hd2, -, h22, -⟩ := hss s2 (by simp only [List.mem_cons, true_or])
        simp only [druckAnwListe, hd2, List.cons_append, List.append_assoc] at e
        injection e with e1; exact h22 e1
    have hS := hB (druckAnwListe ss ++ .zeichen "}" :: rest) F' hK (by simp only [fbA]; omega)
    have hR := ih rest F' hss (by omega)
    have hm : ∀ r, t :: (ts ++ (druckAnwListe ss ++ .zeichen "}" :: rest)) ≠ .zeichen "}" :: r := by
      intro r e; injection e with e1; exact h1 e1
    have hm2 : ∀ r, t :: (ts ++ (druckAnwListe ss ++ .zeichen "}" :: rest)) ≠ .ende :: r := by
      intro r e; injection e with e1; exact h3 e1
    simp only [druckAnwListe, List.append_assoc]
    rw [hd] at hS ⊢
    simp only [List.cons_append, List.append_assoc] at hS ⊢
    rw [parseStmts.eq_def]
    simp only [hS, hR]

/-- The ender, as the statements a block prints. -/
theorem schliesse_rund (ss : List SAnw) (e : Option SEnde) (hw : EndeGut ss e) :
    schliesseBlock (ss ++ endeAnw e) = .block ss e := by
  cases e with
  | none =>
    simp only [endeAnw, List.append_nil]
    cases ss with
    | nil => rfl
    | cons s ss' =>
      have hl := hw rfl
      simp only [schliesseBlock]
      cases hg : (s :: ss').getLast? with
      | none => rfl
      | some x =>
        have hx := hl x hg
        cases x <;> simp_all [istEnder]
  | some e' =>
    cases e' with
    | ret x => simp only [schliesseBlock, endeAnw, List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self,
  List.getLast?_append, List.getLast?_singleton, Option.some_or, ne_eq, not_false_eq_true,
  List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]
    | leave l => simp only [schliesseBlock, endeAnw, List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self,
  List.getLast?_append, List.getLast?_singleton, Option.some_or, ne_eq, not_false_eq_true,
  List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]
    | next l => simp only [schliesseBlock, endeAnw, List.append_eq_nil_iff, List.cons_ne_self, and_false, imp_self,
  List.getLast?_append, List.getLast?_singleton, Option.some_or, ne_eq, not_false_eq_true,
  List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]

/-- A block from the legs of its statements and its ender. -/
theorem block_rund (ss : List SAnw) (e : Option SEnde)
    (h : ∀ s ∈ ss ++ endeAnw e, AnwBein s ∧ AnwKopf s) (hw : EndeGut ss e) :
    BlockBein (.block ss e) := by
  intro rest F hF
  have hd : druckAnw (.block ss e) ++ rest =
      .zeichen "{" :: (druckAnwListe (ss ++ endeAnw e) ++ .zeichen "}" :: rest) := by
    simp only [druckAnw, List.cons_append, List.nil_append, druckEnde_eq, List.append_assoc, druckAnwListe_append]
  have hlen : (druckAnw (.block ss e)).length = (druckAnwListe (ss ++ endeAnw e)).length + 2 := by
    simp only [druckAnw, List.cons_append, List.nil_append, druckEnde_eq, List.append_assoc, List.length_cons,
  List.length_append, List.length_nil, Nat.zero_add, druckAnwListe_append, Nat.add_right_cancel_iff]; omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [fbA] at hF; omega⟩
  have hP := parseStmts_rund (ss ++ endeAnw e) rest F' h (by simp only [fbA] at hF; omega)
  rw [hd]
  simp only [parseBlock, fordereZeichen, strEq_self, ite_true, hP]
  simp only [schliesse_rund ss e hw]


/-! ### Small statements -/

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
    cases m <;> (try rw [hm]) <;> simp only [parseLet, bind, Except.bind, nimmName, nameText_ident, druckTypOpt, List.nil_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, pure, Except.pure, fordereZeichen, strEq_self, ↓reduceIte, parseLetNach, List.cons_append, nameText_nameTok] <;> rfl
  | some t =>
    have hT : parseTyp f (druckTyp t ++ .zeichen "=" :: nach) = .ok (t, .zeichen "=" :: nach) :=
      parse_druckTyp t hty _ f
        ⟨(by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e), (by intro r e; simp only [List.cons.injEq, reduceCtorEq, false_and] at e),
          (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e), rfl, rfl, rfl⟩ (hf t rfl)
    cases m <;> (try rw [hm]) <;> simp only [parseLet, bind, Except.bind, nimmName, nameText_ident, druckTypOpt, List.cons_append, List.nil_append, hT, pure, Except.pure, fordereZeichen, strEq_self, ↓reduceIte, parseLetNach, nameText_nameTok] <;> rfl

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
  simp only [parseLetExpr, bind, Except.bind, hO, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]


/-! ### Statements headed by a place or a call -/

/-- The head words `parseStmt` opens a form with (unless a place continuation follows),
    `transition`, which `parsePlatzStmt` opens whatever follows, and `else`, which ends a statement
    list's follow (`KE`). -/
def anwWortTafel : List (List Char) :=
  ["else", "let", "if", "match", "traverse", "retry", "forever", "breaking", "narrow", "locks", "observes",
   "leave", "next", "return", "reset", "grow", "free", "child", "transition", "advances"].map
    String.toList

/-- A statement head word (see `anwWortTafel`). -/
def istAnwWort (s : String) : Bool := anwWortTafel.contains s.toList

theorem anwWort_strEq {a : String} (h : istAnwWort a = false) (w : String)
    (hw : istAnwWort w = true) : strEq a w = false := by
  cases hc : strEq a w
  · rfl
  · have := (strEq_eq _ _).mp hc; subst this; rw [h] at hw; exact absurd hw (by decide)

/-- A statement headed by a printed name goes to the place reader: the name is no head word, or a
    place continuation follows; and it is not `transition`; and it is not `start {`. -/
theorem parseStmt_ident (f : Nat) (a : String) (r : List Token) (h : ∀ r', r ≠ .zeichen "{" :: r')
    (hw : istOrtsFort r = true ∨ istAnwWort a = false) :
    parseStmt (f + 1) (nameTok a :: r) = parsePlatzStmt f (nameTok a :: r) := by
  unfold nameTok
  split
  · rcases hw with hw | hw
    · simp only [parseStmt, hw, ↓reduceIte]
    · have e := fun w (hw' : istAnwWort w = true) => anwWort_strEq hw w hw'
      simp only [parseStmt, e "let" rfl, Bool.false_eq_true, ↓reduceIte, e "if" rfl, e "match" rfl,
  e "traverse" rfl, e "retry" rfl, e "forever" rfl, e "breaking" rfl, e "narrow" rfl, e "locks" rfl, e "observes" rfl,
  e "leave" rfl, e "next" rfl, e "return" rfl, e "reset" rfl, e "grow" rfl, e "free" rfl, e "child" rfl,
  e "transition" rfl, e "advances" rfl, ite_self]
  · rw [parseStmt.eq_def]
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
