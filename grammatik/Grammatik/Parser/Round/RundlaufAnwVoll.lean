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
import Grammatik.Parser.Round.RundlaufQuant

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

/-- A place head never opens `start {`. -/
theorem platz_nicht_start (z : SExpr) (hz : gutPlatz z = true) (X : List Token)
    (hX : ∀ r', X ≠ .zeichen "{" :: r') (hXo : istOrtsFort X = true) :
    ∃ a r, druckToks z ++ X = nameTok a :: r ∧ (∀ r', r ≠ .zeichen "{" :: r') ∧
      istOrtsFort r = true ∧ a ≠ "transition" := by
  obtain ⟨a, suff, rfl, hka, _, _⟩ := zerlege (groesse z) z (Nat.le_refl _) hz
  rw [druckToks_applySuff]
  refine ⟨a, suffToks suff ++ X, by simp only [druckToks, List.cons_append, List.nil_append], ?_, ?_, ?_⟩
  · intro r' e
    cases suff with
    | nil => exact hX r' (by simpa [suffToks] using e)
    | cons s _ => cases s <;> simp only [suffToks, List.cons_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, List.append_assoc, List.nil_append] at e
  · cases suff with
    | nil => simpa [suffToks] using hXo
    | cons s _ => cases s <;> rfl
  · intro e; subst e; revert hka; decide

theorem anw_set (z : SExpr) (o : String) (w : SExpr) (hz : gutPlatz z = true)
    (ho : istZuweis o = true) (hw : gut w = true) : AnwBein (.set z o w) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_singleton] at hF
  have hd : druckAnw (.set z o w) ++ rest = druckToks z ++ .zeichen o :: (druckToks w ++ .zeichen ";" :: rest) := by
    simp only [druckAnw, List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨a, r, hzr, hr, hro, hrt⟩ := platz_nicht_start z hz
    (.zeichen o :: (druckToks w ++ .zeichen ";" :: rest))
    (by intro r' e; injection e with e1; injection e1 with e1; subst e1
        rcases zuweis_is "{" ho with h | h | h | h | h <;> exact absurd h (by decide))
    (by rcases zuweis_is o ho with h | h | h | h | h <;> subst h <;> rfl)
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  rw [hd, hzr, parseStmt_ident _ _ _ hr (Or.inl hro), parsePlatzStmt_ident _ _ _ hrt, ← hzr]
  have hK := kopfP z hz (.zeichen o :: (druckToks w ++ .zeichen ";" :: rest)) F'
    (by rcases zuweis_is o ho with h | h | h | h | h <;> subst h <;> rfl) (by omega)
  have hO := ausdruck w hw (.zeichen ";" :: rest) F' rfl rfl rfl (by omega)
  simp only [parseKopfStmt, hK]
  split
  · simp only [gutPlatz, Bool.false_eq_true] at hz
  · simp only [gutPlatz, Bool.false_eq_true] at hz
  · rcases zuweis_is o ho with h | h | h | h | h <;> subst h <;>
      simp only [String.reduceEq, imp_self, strEq_self, Bool.true_or, ↓reduceIte, List.tail_cons, hO, fordereZeichen, Bool.or_true]

theorem anw_shift (z : SExpr) (a b : String) (hz : gutPlatz z = true) : AnwBein (.shift z a b) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_singleton, List.length_cons,
    List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨c, ts, hc, ck⟩ := platz_kopf z hz
  have hd : druckAnw (.shift z a b) ++ rest = .wort "transition" :: (druckToks z ++
      (.zeichen ":" :: nameTok a :: .zeichen "->" :: nameTok b :: .zeichen ";" :: rest)) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseStmt_transition _ _ (by rw [hc]; first | rfl | exact ortsFort_nameTok _ _)]
  have hO := ortP z hz (.zeichen ":" :: nameTok a :: .zeichen "->" :: nameTok b :: .zeichen ";" :: rest)
    F' rfl (by omega)
  simp only [parseUebergang, hO, fordereZeichen, strEq_self, ↓reduceIte, nimmName, nameText_nameTok]

theorem anw_free (z : SExpr) (hz : gutPlatz z = true) : AnwBein (.free z) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_singleton, List.length_cons,
    List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨c, ts, hc, ck⟩ := platz_kopf z hz
  have hd : druckAnw (.free z) ++ rest = .wort "free" :: (druckToks z ++ .zeichen ";" :: rest) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseStmt_free _ _ (by rw [hc]; first | rfl | exact ortsFort_nameTok _ _)]
  have hO := ortP z hz (.zeichen ";" :: rest) F' rfl (by omega)
  simp only [parseFree, bind, Except.bind, hO, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]

/-- A name-shaped call head (or `start` root) re-lexes to its name token. -/
def NameGut (f : String) : Prop := nameForm f = true

theorem rohToks_nameGut (f : String) (h : NameGut f) : rohToks f = [nameTok f] :=
  rohToks_name f h

/-- Argument legs from printability. -/
theorem args_gut (xs : List SExpr) (h : gutListe xs = true) :
    ∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true := by
  intro x hx
  have := gutListe_mem xs x hx h
  exact ⟨legs_tok x this, this⟩

theorem anw_call (f : String) (xs : List SExpr) (hf : NameGut f) (hw : istAnwWort f = false)
    (hxs : gutListe xs = true) : AnwBein (.call f xs) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, rohToks_nameGut f hf, List.length_append, List.length_singleton,
    List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckAnw (.call f xs) ++ rest = nameTok f :: .zeichen "(" ::
      (druckToksListe xs ++ [.zeichen ")"] ++ (.zeichen ";" :: rest)) := by
    simp only [druckAnw, rohToks_nameGut f hf, List.cons_append, List.nil_append, List.append_assoc]
  have ht : f ≠ "transition" := by intro e; subst e; revert hw; decide
  rw [hd, parseStmt_ident _ _ _ (by intro r e; simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq, Token.zeichen.injEq,
  String.reduceEq, false_and] at e) (Or.inr hw), parsePlatzStmt_ident _ _ _ ht]
  have hA := argsM xs (.zeichen ";" :: rest) F' (args_gut xs hxs) (by omega)
  simp only [parseKopfStmt]
  rw [show F' + 1 = F' + 1 from rfl, kopf_ruf_head, hA]
  simp only [fordereZeichen, strEq_self, ↓reduceIte]

/-! ### Statements with a block -/

/-- A block prints with its opening brace first. -/
def BlockKopf (b : SAnw) : Prop := ∃ ts, druckAnw b = .zeichen "{" :: ts

theorem blockKopf_block (ss : List SAnw) (e : Option SEnde) : BlockKopf (.block ss e) :=
  ⟨druckAnwListe ss ++ druckEnde e ++ [.zeichen "}"], by simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]⟩

theorem ortsfort_block (b : SAnw) (hk : BlockKopf b) (rest : List Token) :
    istOrtsFort (druckAnw b ++ rest) = false := by
  obtain ⟨ts, h⟩ := hk; rw [h]; rfl

theorem block_len (b : SAnw) (hk : BlockKopf b) : 1 ≤ (druckAnw b).length := by
  obtain ⟨ts, h⟩ := hk; rw [h]; simp only [List.length_cons, Nat.le_add_left]

theorem anw_child (b : SAnw) (hb : BlockBein b) (hk : BlockKopf b) : AnwBein (.child b) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_singleton] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckAnw (.child b) ++ rest = .wort "child" :: (druckAnw b ++ rest) := by
    simp only [druckAnw, List.cons_append, List.nil_append]
  have hB := hb rest (F' + 1) (by simp only [fbA]; omega)
  rw [hd, parseStmt_child _ _ (ortsfort_block b hk rest)]
  simp only [parseChild, bind, Except.bind, hB, pure, Except.pure]

theorem anw_watch (d : String) (b : SAnw) (hb : BlockBein b) (hk : BlockKopf b) :
    AnwBein (.watch d b) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckAnw (.watch d b) ++ rest = .wort "observes" :: nameTok d :: (druckAnw b ++ rest) := by
    simp only [druckAnw, List.cons_append, List.nil_append]
  have hB := hb rest (F' + 1) (by simp only [fbA]; omega)
  rw [hd, parseStmt_observes _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  simp only [parseBeobachtet, nimmName, nameText_nameTok, hB]

/-- `locks` before a place whose head is no `shared`: the place reader sees the head name. -/
theorem parseSperrt_nameTok (f : Nat) (c : String) (hc : c ≠ "shared") (R : List Token) :
    parseSperrt (f + 1) (nameTok c :: R) = (match parseOrt f (nameTok c :: R) with
      | .error e => .error e
      | .ok (o, rest) => match parseBlock f rest with
        | .error e => .error e
        | .ok (b, rest') => .ok (.locks false o b, rest')) := by
  have hs : strEq c "shared" = false := by
    cases h : strEq c "shared"
    · rfl
    · exact absurd ((strEq_eq _ _).mp h) hc
  unfold nameTok; split
  · simp only [parseSperrt, hs, Bool.false_eq_true, ↓reduceIte] <;> rfl
  · rfl

theorem anw_locks (g : Bool) (o : SExpr) (b : SAnw) (ho : gutPlatz o = true)
    (hsh : g = false → kopfName o ≠ "shared") (hb : BlockBein b)
    (hk : BlockKopf b) : AnwBein (.locks g o b) := by
  intro rest F _ hF
  obtain ⟨ts, hts⟩ := hk
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_zero] at hF <;> omega⟩
  obtain ⟨c, cs, hc, ck⟩ := platz_kopf o ho
  have hO := ortP o ho (druckAnw b ++ rest) (F' + 1) (by rw [hts]; rfl)
    (by split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
  have hB := hb rest (F' + 1) (by simp only [fbA]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
  cases g
  · have hd : druckAnw (.locks false o b) ++ rest = .wort "locks" :: (druckToks o ++ (druckAnw b ++ rest)) := by
      simp only [druckAnw, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append,
  List.append_assoc]
    rw [hd, parseStmt_locks _ _ (by rw [hc]; first | rfl | exact ortsFort_nameTok _ _)]
    have hcn : c = kopfName o := by
      obtain ⟨us, hu⟩ := platz_kopfName o ho
      rw [hc] at hu; injection hu with hu; exact nameTok_inj hu
    simp only [hc, List.cons_append] at hO ⊢
    rw [show F' + 2 = (F' + 1) + 1 from rfl, parseSperrt_nameTok _ c (hcn ▸ hsh rfl)]
    simp only [hO, hB]
  · have hd : druckAnw (.locks true o b) ++ rest =
        .wort "locks" :: .wort "shared" :: (druckToks o ++ (druckAnw b ++ rest)) := by
      simp only [druckAnw, ↓reduceIte, List.cons_append, List.nil_append, List.append_assoc]
    rw [hd, parseStmt_locks _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
    simp only [parseSperrt, strEq_self, ↓reduceIte, hO, hB]

theorem anw_grow (a : String) (e : SExpr) (b : SAnw) (he : gut e = true) (hb : BlockBein b)
    (hk : BlockKopf b) : AnwBein (.grow a e b) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil,
    List.length_singleton] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hd : druckAnw (.grow a e b) ++ rest = .wort "grow" :: nameTok a :: .wort "by" ::
      (druckToks e ++ .wort "else" :: (druckAnw b ++ .zeichen ";" :: rest)) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  have hB := hb (.zeichen ";" :: rest) F' (by simp only [fbA]; omega)
  have hE := ausdruck e he (.wort "else" :: (druckAnw b ++ .zeichen ";" :: rest)) F' rfl rfl rfl
    (by omega)
  rw [hd, parseStmt_grow _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  simp only [parseGrow, bind, Except.bind, nimmName, nameText_nameTok, nimmWort, strEq_self, ↓reduceIte, hE, hB,
  fordereZeichen, pure, Except.pure]


/-! ### More statement forms -/

theorem anw_reset (a : String) (rg : Option (SExpr × SExpr))
    (hrg : ∀ i n, rg = some (i, n) → gut i = true ∧ gut n = true) : AnwBein (.reset a rg) := by
  intro rest F _ hF
  cases rg with
  | none =>
    simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hd : druckAnw (.reset a none) ++ rest = .wort "reset" :: nameTok a :: .zeichen ";" :: rest := by
      simp only [druckAnw, List.append_nil, List.cons_append, List.nil_append]
    rw [hd, parseStmt_reset _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
    simp only [parseReset, bind, Except.bind, nimmName, nameText_nameTok, pure, Except.pure, fordereZeichen,
  strEq_self, ↓reduceIte]
  | some p =>
    obtain ⟨i, n⟩ := p
    obtain ⟨hi, hn⟩ := hrg i n rfl
    simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hd : druckAnw (.reset a (some (i, n))) ++ rest = .wort "reset" :: nameTok a :: .wort "at" ::
        (druckToks i ++ .wort "count" :: (druckToks n ++ .zeichen ";" :: rest)) := by
      simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
    have hI := ausdruck i hi (.wort "count" :: (druckToks n ++ .zeichen ";" :: rest)) F' rfl rfl rfl
      (by omega)
    have hN := ausdruck n hn (.zeichen ";" :: rest) F' rfl rfl rfl (by omega)
    rw [hd, parseStmt_reset _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
    simp only [parseReset, bind, Except.bind, nimmName, nameText_nameTok, hI, nimmWort, strEq_self, ↓reduceIte,
  hN, pure, Except.pure, fordereZeichen]

theorem parseStmt_at (f : Nat) (r : List Token) :
    parseStmt (f + 1) (.zeichen "@" :: r) = parseLibStmt f (.zeichen "@" :: r) := by
  simp only [parseStmt]

theorem komma_null : ∀ (n : Nat),
    kommaToks (List.replicate n [Token.num 0]) = druckToksListe (List.replicate n (.lit 0)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ m =>
      simp only [List.replicate_succ] at ih ⊢
      simp only [kommaToks, druckToksListe] at ih ⊢
      rw [ih]
      rfl

theorem druckToksListe_null_len (n : Nat) :
    (druckToksListe (List.replicate n (.lit 0))).length ≤ 2 * n := by
  induction n with
  | zero => simp only [List.replicate_zero, druckToksListe, List.length_nil, Nat.mul_zero, Std.le_refl]
  | succ n ih =>
    cases n with
    | zero => simp only [Nat.zero_add, List.replicate_one, druckToksListe, druckToks, List.length_cons, List.length_nil,
  Nat.mul_one, Nat.reduceLeDiff]
    | succ m =>
      simp only [List.replicate_succ] at ih ⊢
      simp only [druckToksListe, List.length_append, List.length_cons, List.length_nil] at ih ⊢
      simp only [druckToks, List.length_cons, List.length_nil]
      omega

/-- The library call head: `@ l # f ( args ) { }`. -/
theorem libRuf_rund (l g : String) (xs : List SExpr) (hxs : ∀ x ∈ xs, LegsB (fb x) x ∧ gut x = true)
    (rest : List Token) (F : Nat) (hF : 6 * (druckToksListe xs).length + 37 ≤ F) :
    parseLibRuf F (.zeichen "@" :: nameTok l :: .zeichen "#" :: nameTok g :: .zeichen "(" ::
      (druckToksListe xs ++ [.zeichen ")"] ++ (.zeichen "{" :: .zeichen "}" :: rest))) =
      .ok ((l, g, xs.length), rest) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hA := argsM xs (.zeichen "{" :: .zeichen "}" :: rest) F' hxs (by omega)
  simp only [List.append_assoc, List.singleton_append] at hA
  simp only [parseLibRuf, List.append_assoc, List.cons_append, List.nil_append, nimmName, nameText_nameTok,
  fordereZeichen, strEq_self, ↓reduceIte, hA, nimmBereich]

theorem anw_lcall (l g : String) (n : Nat) : AnwBein (.lcall l g n) := by
  intro rest F _ hF
  have hlen := druckToksListe_null_len n
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil, komma_null] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hd : druckAnw (.lcall l g n) ++ rest = .zeichen "@" :: nameTok l :: .zeichen "#" :: nameTok g ::
      .zeichen "(" :: (druckToksListe (List.replicate n (.lit 0)) ++ [.zeichen ")"] ++
        (.zeichen "{" :: .zeichen "}" :: .zeichen ";" :: rest)) := by
    simp only [druckAnw, komma_null, List.cons_append, List.nil_append, List.append_assoc]
  have hxs : ∀ x ∈ List.replicate n (SExpr.lit 0), LegsB (fb x) x ∧ gut x = true := by
    intro x hx
    rw [List.eq_of_mem_replicate hx]
    exact ⟨legs_tok _ rfl, rfl⟩
  have hL := libRuf_rund l g _ hxs (.zeichen ";" :: rest) F' (by omega)
  rw [hd, parseStmt_at]
  simp only [List.append_assoc, List.singleton_append] at hL
  simp only [parseLibStmt, List.append_assoc, List.cons_append, List.nil_append, hL, List.length_replicate,
  fordereZeichen, strEq_self, ↓reduceIte]

theorem anw_bindLib (m : Bool) (x : String) (hx : x ≠ "mut") (ty : Option STyp) (l g : String)
    (hty : TypOptGut ty) :
    AnwBein (.bindLib m x ty l g) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_cons, List.length_nil, List.length_append] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckAnw (.bindLib m x ty l g) ++ rest = .wort "let" :: ((if m then [.wort "mut"] else []) ++
      nameTok x :: (druckTypOpt ty ++ .zeichen "=" :: (.zeichen "@" :: nameTok l :: .zeichen "#" ::
        nameTok g :: .zeichen "(" :: (druckToksListe [] ++ [.zeichen ")"] ++
          (.zeichen "{" :: .zeichen "}" :: .zeichen ";" :: rest))))) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, druckToksListe]
  rw [hd, parseStmt_let _ _ (by cases m <;> first | rfl | (simp only [Bool.false_eq_true, ite_false, List.nil_append]; exact ortsFort_nameTok _ _))]
  rw [parseLet_kopf (F' + 1) m x hx ty _ hty (by
      intro t ht; have := fbT_of ty t ht; simp only [fbT]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)]
  obtain ⟨F'', hF''⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega⟩
  have hL := libRuf_rund l g [] (by simp only [List.not_mem_nil, false_implies, implies_true]) (.zeichen ";" :: rest) F' (by simp only [druckToksListe, List.length_nil, Nat.mul_zero, Nat.zero_add]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
  subst hF''
  simp only [List.append_assoc, List.singleton_append] at hL
  simp only [parseLetNach, List.append_assoc, List.cons_append, List.nil_append, parseLetLib, bind, Except.bind,
  hL, List.length_nil, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]


/-! ### `let` forms with a tail -/

theorem anw_alloc (m : Bool) (n : String) (hx : n ≠ "mut") (ty : Option STyp) (t : String) (w : SExpr) (s : Option SAnw)
    (hty : TypOptGut ty) (hw : gut w = true) (hs : ∀ b, s = some b → BlockBein b) :
    AnwBein (.alloc m n ty t w s) := by
  intro rest F _ hF
  have he : strEq "alloc" "alloc" = true := by decide
  cases s with
  | none =>
    simp only [fbA, druckAnw, List.length_cons, List.length_nil, List.length_append] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
    have hd : druckAnw (.alloc m n ty t w none) ++ rest = .wort "let" :: ((if m then [.wort "mut"] else []) ++
        nameTok n :: (druckTypOpt ty ++ .zeichen "=" :: (.wort "alloc" :: nameTok t :: .zeichen "(" ::
          (druckToks w ++ .zeichen ")" :: .zeichen ";" :: rest)))) := by
      simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, List.append_nil]
    rw [hd, parseStmt_let _ _ (by cases m <;> first | rfl | (simp only [Bool.false_eq_true, ite_false, List.nil_append]; exact ortsFort_nameTok _ _))]
    rw [show F' + 3 = (F' + 2) + 1 from rfl,
      parseLet_kopf (F' + 2) m n hx ty _ hty (by
        intro t ht; have := fbT_of ty t ht; simp only [fbT]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_zero, Nat.reduceLeDiff] at hF <;> omega)]
    have hW := ausdruck w hw (.zeichen ")" :: .zeichen ";" :: rest) (F' + 1) rfl rfl rfl
      (by split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_zero, Nat.reduceLeDiff] at hF <;> omega)
    simp only [parseLetNach, he, ite_true, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
    simp only [parseLetAlloc, bind, Except.bind, nimmName, nameText_nameTok, fordereZeichen, strEq_self,
  ↓reduceIte, hW, pure, Except.pure]
  | some b =>
    simp only [fbA, druckAnw, List.length_cons, List.length_nil, List.length_append] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
    have hd : druckAnw (.alloc m n ty t w (some b)) ++ rest = .wort "let" ::
        ((if m then [.wort "mut"] else []) ++
        nameTok n :: (druckTypOpt ty ++ .zeichen "=" :: (.wort "alloc" :: nameTok t :: .zeichen "(" ::
          (druckToks w ++ .zeichen ")" :: .wort "else" :: (druckAnw b ++ .zeichen ";" :: rest))))) := by
      simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
    rw [hd, parseStmt_let _ _ (by cases m <;> first | rfl | (simp only [Bool.false_eq_true, ite_false, List.nil_append]; exact ortsFort_nameTok _ _))]
    rw [show F' + 3 = (F' + 2) + 1 from rfl,
      parseLet_kopf (F' + 2) m n hx ty _ hty (by
        intro t ht; have := fbT_of ty t ht; simp only [fbT]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)]
    have hW := ausdruck w hw (.zeichen ")" :: .wort "else" :: (druckAnw b ++ .zeichen ";" :: rest))
      (F' + 1) rfl rfl rfl (by split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
    have hB := hs b rfl (.zeichen ";" :: rest) (F' + 1) (by
      simp only [fbA]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)
    simp only [parseLetNach, he, ite_true, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
    simp only [parseLetAlloc, bind, Except.bind, nimmName, nameText_nameTok, fordereZeichen, strEq_self,
  ↓reduceIte, hW, hB, pure, Except.pure]

theorem anw_allocVon (m : Bool) (n : String) (hx : n ≠ "mut") (ty : Option STyp) (t : String)
    (hty : TypOptGut ty) : AnwBein (.allocVon m n ty t) := by
  intro rest F _ hF
  have he : strEq "alloc" "alloc" = true := by decide
  simp only [fbA, druckAnw, List.length_cons, List.length_nil, List.length_append] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckAnw (.allocVon m n ty t) ++ rest = .wort "let" :: ((if m then [.wort "mut"] else []) ++
      nameTok n :: (druckTypOpt ty ++ .zeichen "=" :: (.wort "alloc" :: nameTok t :: .zeichen ";" :: rest))) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseStmt_let _ _ (by cases m <;> first | rfl | (simp only [Bool.false_eq_true, ite_false, List.nil_append]; exact ortsFort_nameTok _ _))]
  rw [show F' + 3 = (F' + 2) + 1 from rfl,
    parseLet_kopf (F' + 2) m n hx ty _ hty (by
      intro t ht; have := fbT_of ty t ht; simp only [fbT]; split at hF <;> simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, Nat.add_zero] at hF <;> omega)]
  simp only [parseLetNach, he, ite_true, nameText_nameTok]

theorem anw_bindElse (x : String) (hx : x ≠ "mut") (ty : Option STyp) (e : SExpr) (f : String) (b : SAnw)
    (hty : TypOptGut ty) (he : gut e = true) (hb : BlockBein b) :
    AnwBein (.bindElse x ty e f b) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_cons, List.length_nil, List.length_append] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckAnw (.bindElse x ty e f b) ++ rest = .wort "let" :: ((if false then [.wort "mut"] else []) ++
      nameTok x :: (druckTypOpt ty ++ .zeichen "=" :: (druckToks e ++ .wort "else" :: .zeichen "(" ::
        nameTok f :: .zeichen ")" :: (druckAnw b ++ rest)))) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, Bool.false_eq_true, ↓reduceIte]
  rw [hd, parseStmt_let _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  rw [show F' + 3 = (F' + 2) + 1 from rfl,
    parseLet_kopf (F' + 2) false x hx ty _ hty (by
      intro t ht; have := fbT_of ty t ht; simp only [fbT]; omega),
    parseLetNach_expr _ _ _ _ e he]
  have hE := ausdruck e he (.wort "else" :: .zeichen "(" :: nameTok f :: .zeichen ")" :: (druckAnw b ++ rest))
    (F' + 1) rfl rfl rfl (by omega)
  have hB := hb rest (F' + 1) (by simp only [fbA]; omega)
  simp only [parseLetExpr, bind, Except.bind, hE, nimmName, nameText_nameTok, fordereZeichen, strEq_self,
  ↓reduceIte, hB, pure, Except.pure]

/-- A raw text inside braces (`awaits`/`publishes` payloads). -/
def RohZu (s : String) : Prop :=
  RohText (fun t => t = .zeichen "{" ∨ t = .zeichen "}") s

/-- A raw text up to `;` (the `exchange` tail). -/
def RohSemi (s : String) : Prop :=
  RohText (fun t => t = .zeichen "{" ∨ t = .zeichen "}" ∨ t = .zeichen ";") s

theorem anw_await (n : String) (hx : n ≠ "mut") (ty : Option STyp) (q : SExpr) (p : String) (hty : TypOptGut ty)
    (hq : gut q = true) (hp : RohZu p) :
    AnwBein (.await n ty q p) := by
  intro rest F _ hF
  obtain ⟨ts, rfl, hts⟩ := hp
  have hroh := rohToks_render ts (fun t ht => (hts t ht).1)
  simp only [fbA, druckAnw, hroh, List.length_cons, List.length_nil, List.length_append] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckAnw (.await n ty q (renderText ts)) ++ rest = .wort "let" :: ((if false then [.wort "mut"] else []) ++
      nameTok n :: (druckTypOpt ty ++ .zeichen "=" :: (druckToks q ++ .wort "awaits" :: .zeichen "{" ::
        (ts ++ .zeichen "}" :: .zeichen ";" :: rest)))) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, hroh, Bool.false_eq_true,
  ↓reduceIte]
  rw [hd, parseStmt_let _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  rw [show F' + 3 = (F' + 2) + 1 from rfl,
    parseLet_kopf (F' + 2) false n hx ty _ hty (by
      intro t ht; have := fbT_of ty t ht; simp only [fbT]; omega),
    parseLetNach_expr _ _ _ _ q hq]
  have hQ := ausdruck q hq (.wort "awaits" :: .zeichen "{" :: (ts ++ .zeichen "}" :: .zeichen ";" :: rest))
    (F' + 1) rfl rfl rfl (by omega)
  have hN := nimmBisZeichen_roh "}" ts (.zeichen ";" :: rest)
    (fun t ht => ⟨(hts t ht).1, fun e => (hts t ht).2 (Or.inl e), fun e => (hts t ht).2 (Or.inr e),
      fun e => (hts t ht).2 (Or.inr e)⟩)
  simp only [parseLetExpr, bind, Except.bind, hQ, hN, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]

theorem anw_swap (n : String) (hx : n ≠ "mut") (ty : Option STyp) (o : SExpr) (k : String)
    (hty : TypOptGut ty) (ho : gut o = true) (hk : RohSemi k) :
    AnwBein (.swap n ty o k) := by
  intro rest F _ hF
  obtain ⟨ts, rfl, hts⟩ := hk
  have hroh := rohToks_render ts (fun t ht => (hts t ht).1)
  simp only [fbA, druckAnw, hroh, List.length_cons, List.length_nil, List.length_append] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  have hd : druckAnw (.swap n ty o (renderText ts)) ++ rest = .wort "let" :: ((if false then [.wort "mut"] else []) ++
      nameTok n :: (druckTypOpt ty ++ .zeichen "=" :: (druckToks o ++ .wort "exchange" ::
        (ts ++ .zeichen ";" :: rest)))) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, hroh, Bool.false_eq_true,
  ↓reduceIte]
  rw [hd, parseStmt_let _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
  rw [show F' + 3 = (F' + 2) + 1 from rfl,
    parseLet_kopf (F' + 2) false n hx ty _ hty (by
      intro t ht; have := fbT_of ty t ht; simp only [fbT]; omega),
    parseLetNach_expr _ _ _ _ o ho]
  have hO := ausdruck o ho (.wort "exchange" :: (ts ++ .zeichen ";" :: rest)) (F' + 1) rfl rfl rfl
    (by omega)
  have hN := nimmBisZeichen_roh ";" ts rest
    (fun t ht => ⟨(hts t ht).1, fun e => (hts t ht).2 (Or.inl e),
      fun e => (hts t ht).2 (Or.inr (Or.inl e)), fun e => (hts t ht).2 (Or.inr (Or.inr e))⟩)
  simp only [parseLetExpr, bind, Except.bind, hO, hN, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]

/-- The payload of a publication: `nothing`, or a raw text in braces. -/
def PubGut (p : String) : Prop := p = "nothing" ∨ (RohZu p ∧ p ≠ "nothing")

theorem anw_emit (z w : SExpr) (p : String) (hz : gutPlatz z = true) (hw : gut w = true)
    (hp : PubGut p) : AnwBein (.emit z w p) := by
  intro rest F _ hF
  -- the payload tokens
  obtain ⟨P, hP, hPk⟩ : ∃ P : List Token, (if strEq p "nothing" then [Token.wort "nothing"]
      else [Token.zeichen "{"] ++ rohToks p ++ [Token.zeichen "}"]) = P ∧
      ∀ r, (match P ++ .zeichen ";" :: r with
        | .wort q :: rest'' =>
          if strEq q "nothing" then match fordereZeichen ";" rest'' with
            | .ok rest3 => (Except.ok (SAnw.emit z w "nothing", rest3) : Except String (SAnw × List Token))
            | .error e => .error e
          else .error "publishes without payload"
        | .zeichen "{" :: rest'' => match nimmBisZeichen "}" rest'' 0 with
          | .ok (pl, rest3) => match fordereZeichen "}" rest3 with
            | .ok rest4 => match fordereZeichen ";" rest4 with
              | .ok rest5 => .ok (.emit z w pl, rest5)
              | .error e => .error e
            | .error e => .error e
          | .error e => .error e
        | _ => .error "publishes without payload") = .ok (.emit z w p, r) := by
    rcases hp with rfl | ⟨⟨ts, rfl, hts⟩, hne⟩
    · refine ⟨[.wort "nothing"], by simp only [strEq_self, ↓reduceIte], ?_⟩
      intro r; simp only [List.cons_append, List.nil_append, strEq_self, ↓reduceIte, fordereZeichen]
    · have hroh := rohToks_render ts (fun t ht => (hts t ht).1)
      have hs : strEq (renderText ts) "nothing" = false := by
        cases h : strEq (renderText ts) "nothing"
        · rfl
        · exact absurd ((strEq_eq _ _).mp h) hne
      refine ⟨[.zeichen "{"] ++ ts ++ [.zeichen "}"], by simp only [hs, Bool.false_eq_true, ↓reduceIte, hroh, List.cons_append, List.nil_append], ?_⟩
      intro r
      have hN := nimmBisZeichen_roh "}" ts (.zeichen ";" :: r)
        (fun t ht => ⟨(hts t ht).1, fun e => (hts t ht).2 (Or.inl e), fun e => (hts t ht).2 (Or.inr e),
          fun e => (hts t ht).2 (Or.inr e)⟩)
      simp only [List.cons_append, List.nil_append, List.append_assoc, hN, fordereZeichen, strEq_self, ↓reduceIte]
  have hlenP : P.length ≤ (druckAnw (.emit z w p)).length := by
    rw [← hP]; simp only [List.cons_append, List.nil_append, druckAnw, List.append_assoc, List.length_append,
  List.length_cons, List.length_nil, Nat.zero_add]; omega
  simp only [fbA] at hF
  have hd : druckAnw (.emit z w p) ++ rest = druckToks z ++ .zeichen "=" :: (druckToks w ++
      .wort "publishes" :: (P ++ .zeichen ";" :: rest)) := by
    rw [← hP]; simp only [druckAnw, List.append_assoc, List.cons_append, List.nil_append]
  have hlz : (druckAnw (.emit z w p)).length = (druckToks z).length + 1 + (druckToks w).length + 1 +
      P.length + 1 := by
    rw [← hP]; simp only [druckAnw, List.append_assoc, List.cons_append, List.nil_append, List.length_append,
  List.length_cons, List.length_nil, Nat.zero_add]; omega
  have := platz_nicht_start z hz (.zeichen "=" :: (druckToks w ++
      .wort "publishes" :: (P ++ .zeichen ";" :: rest))) (by intro r' e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) rfl
  obtain ⟨a, r, hzr, hr, hro, hrt⟩ := this
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  rw [hd, hzr, parseStmt_ident _ _ _ hr (Or.inl hro), parsePlatzStmt_ident _ _ _ hrt, ← hzr]
  have hK := kopfP z hz (.zeichen "=" :: (druckToks w ++ .wort "publishes" :: (P ++ .zeichen ";" :: rest)))
    F' rfl (by omega)
  have hO := ausdruck w hw (.wort "publishes" :: (P ++ .zeichen ";" :: rest)) F' rfl rfl rfl (by omega)
  simp only [parseKopfStmt, hK]
  split
  · simp only [gutPlatz, Bool.false_eq_true] at hz
  · simp only [gutPlatz, Bool.false_eq_true] at hz
  · simp only [String.reduceEq, imp_self, strEq_self, Bool.true_or, ↓reduceIte, List.tail_cons, hO]
    exact hPk rest


/-! ### `start`, `breaking`, loops, `narrow`, `traverse` -/

theorem parseStmt_start (f : Nat) (r : List Token) :
    parseStmt (f + 1) (.ident "start" :: .zeichen "{" :: r) = parseStart f r := by
  simp only [parseStmt]

theorem startRoots_rund : ∀ (ps : List String) (rest : List Token) (F : Nat), ps ≠ [] →
    (∀ p ∈ ps, NameGut p) → ps.length + 1 ≤ F →
    parseStartRoots F (druckWurzeln ps ++ .zeichen "}" :: rest) = .ok (ps, rest) := by
  intro ps
  induction ps with
  | nil => intro _ _ h; exact absurd rfl h
  | cons p ps ih =>
    intro rest F _ hp hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    have hp1 := rohToks_nameGut p (hp p (by simp only [List.mem_cons, true_or]))
    cases ps with
    | nil =>
      have hs := sammleSeg_stop2 [p] (.zeichen "}" :: rest) (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
      simp only [parseStartRoots, bind, Except.bind, nimmName, druckWurzeln, hp1, List.cons_append, List.nil_append,
  nameText_nameTok, hs, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true,
  fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure, String.intercalate_singleton]
    | cons q qs =>
      have hq := ih rest F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hp x (List.mem_cons_of_mem _ hx))
        (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      have hq1 := rohToks_nameGut q (hp q (by simp only [List.mem_cons, true_or, or_true]))
      have hs := sammleSeg_stop2 [p] (.zeichen "," :: (druckWurzeln (q :: qs) ++ .zeichen "}" :: rest))
        (by intro x e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
      have hw : druckWurzeln (q :: qs) = nameTok q :: (druckWurzeln (q :: qs)).tail := by
        cases qs <;> simp only [druckWurzeln, hq1, List.tail_cons, List.cons_append, List.nil_append]
      have hd : druckWurzeln (p :: q :: qs) ++ .zeichen "}" :: rest =
          nameTok p :: .zeichen "," :: (druckWurzeln (q :: qs) ++ .zeichen "}" :: rest) := by
        simp only [druckWurzeln, hp1, List.cons_append, List.nil_append]
      rw [hd]
      simp only [parseStartRoots, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende, hs, String.intercalate_singleton, bind, Except.bind, pure, Except.pure]
      rw [hw] at hq ⊢
      simp only [List.cons_append] at hq
      simp only [List.cons_append, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hq]

theorem anw_start (ps : List String) (hne : ps ≠ []) (hp : ∀ p ∈ ps, NameGut p) :
    AnwBein (.start ps) := by
  intro rest F _ hF
  have hlen : ps.length ≤ (druckWurzeln ps).length := by
    clear hF hne
    induction ps with
    | nil => simp only [List.length_nil, Nat.zero_le]
    | cons p ps ih =>
      have h1 := rohToks_nameGut p (hp p (by simp only [List.mem_cons, true_or]))
      have := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
      cases ps with
      | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckWurzeln, h1, Std.le_refl]
      | cons q qs => simp only [List.length_cons, druckWurzeln, h1, List.cons_append, List.nil_append, Nat.add_le_add_iff_right,
  ge_iff_le] at this ⊢; omega
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hd : druckAnw (.start ps) ++ rest = .ident "start" :: .zeichen "{" ::
      (druckWurzeln ps ++ .zeichen "}" :: .zeichen ";" :: rest) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  have hR := startRoots_rund ps (.zeichen ";" :: rest) F' hne hp (by omega)
  rw [hd, parseStmt_start]
  simp only [parseStart, bind, Except.bind, hR, fordereZeichen, strEq_self, ↓reduceIte, pure, Except.pure]

theorem identList_rund : ∀ (ns : List String) (X : List Token) (F : Nat), ns ≠ [] →
    (∀ r, X ≠ .zeichen "," :: r) → ns.length ≤ F →
    nimmIdentList F (druckNamen ns ++ X) = .ok (ns, X) := by
  intro ns
  induction ns with
  | nil => intro _ _ h; exact absurd rfl h
  | cons n ns ih =>
    intro X F _ hX hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    cases ns with
    | nil =>
      rcases X with _ | ⟨x, xs⟩
      · simp only [nimmIdentList, nimmName, druckNamen, List.append_nil, nameText_nameTok]
      · have : ∀ r, x :: xs ≠ .zeichen "," :: r := hX
        simp only [druckNamen, List.cons_append, List.nil_append, nimmIdentList, nimmName, nameText_nameTok, nameText_ident, nameText_wort, nameText_zeichen, nameText_num, nameText_ende]
        all_goals split
        all_goals first
          | rfl
          | (rename_i heq; simp at heq; exact absurd (by rw [heq.1, heq.2]) (hX _))
    | cons m ms =>
      have hq := ih X F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hX (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      simp only [druckNamen, List.cons_append, List.nil_append, List.singleton_append] at hq ⊢
      simp only [nimmIdentList, nimmName, nameText_nameTok, hq]

theorem anw_waive (ns : List String) (b : SAnw) (hne : ns ≠ []) (hb : BlockBein b) (hk : BlockKopf b) :
    AnwBein (.waive ns b) := by
  intro rest F _ hF
  have hlen : ns.length ≤ (druckNamen ns).length := by
    clear hF hne
    induction ns with
    | nil => simp only [List.length_nil, Nat.zero_le]
    | cons n ns ih => cases ns with
      | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckNamen, Std.le_refl]
      | cons m ms => simp only [List.length_cons, druckNamen, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega
  obtain ⟨ts, hts⟩ := hk
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hd : druckAnw (.waive ns b) ++ rest = .wort "breaking" :: (druckNamen ns ++ (druckAnw b ++ rest)) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  have hI := identList_rund ns (druckAnw b ++ rest) (F' + 1) hne (by rw [hts]; intro r e; simp only [List.cons_append, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
    (by omega)
  have hB := hb rest (F' + 1) (by simp only [fbA]; omega)
  have hof : istOrtsFort (druckNamen ns ++ (druckAnw b ++ rest)) = false := by
    cases ns with
    | nil => exact absurd rfl hne
    | cons n ns => cases ns <;> simp only [druckNamen, List.cons_append, List.nil_append, ortsFort_nameTok]
  rw [hd, parseStmt_breaking _ _ hof]
  simp only [parseBricht, hI, hB]

/-- A loop header: a raw text without a brace or `effects`, not starting with a place continuation. -/
def RohKopf (h : String) : Prop :=
  ∃ ts, h = renderText ts ∧ (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .wort "effects") ∧
    ∀ R, istOrtsFort (ts ++ .zeichen "{" :: R) = false

theorem anw_schleife (art : Nat) (h : String) (b : SAnw) (ha : art = 1 ∨ art = 2) (hh : RohKopf h)
    (hb : BlockBein b) (hk : BlockKopf b) :
    AnwBein (if art = 1 then .retry h b else .loop h b) := by
  intro rest F _ hF
  obtain ⟨ts, rfl, hts, hof⟩ := hh
  obtain ⟨us, hus⟩ := hk
  have hroh := rohToks_render ts (fun t ht => (hts t ht).1)
  have hd : druckAnw (if art = 1 then .retry (renderText ts) b else .loop (renderText ts) b) ++ rest =
      .wort (if art = 1 then "retry" else "forever") :: (ts ++ (druckAnw b ++ rest)) := by
    rcases ha with rfl | rfl <;> simp only [↓reduceIte, druckAnw, hroh, List.cons_append, List.nil_append, List.append_assoc, Nat.succ_ne_self]
  have hlen : (druckAnw (if art = 1 then .retry (renderText ts) b else .loop (renderText ts) b)).length =
      1 + ts.length + (druckAnw b).length := by
    rcases ha with rfl | rfl <;> simp only [↓reduceIte, druckAnw, hroh, List.cons_append, List.nil_append, List.length_cons, List.length_append, Nat.succ_ne_self] <;> omega
  simp only [fbA, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hK := schleifenKopf_roh ts (us ++ rest) F' (fun t ht => hts t ht) (by omega)
  have hB := hb rest F' (by simp only [fbA]; omega)
  have hof' : istOrtsFort (ts ++ (druckAnw b ++ rest)) = false := by
    rw [hus]; exact hof _
  rw [hd]
  rcases ha with rfl | rfl
  · simp only [ite_true]
    rw [parseStmt_retry _ _ hof']
    rw [hus] at hB ⊢
    simp only [List.cons_append] at hB
    simp only [parseSchleife, List.cons_append, hK, hB, BEq.rfl, ↓reduceIte]
  · simp only [show ¬((2 : Nat) = 1) from by decide, ite_false]
    rw [parseStmt_forever _ _ hof']
    rw [hus] at hB ⊢
    simp only [List.cons_append] at hB
    simp only [parseSchleife, List.cons_append, hK, hB, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]

/-- The range text of `narrow ... to`: `finite`, or a raw text without braces or `else` that does
    not start with `finite`. -/
def TrimGut (t : String) : Prop :=
  t = "finite" ∨ ∃ ts, t = renderText ts ∧
    (∀ x ∈ ts, TokGut x ∧ x ≠ .zeichen "{" ∧ x ≠ .zeichen "}" ∧ x ≠ .wort "else") ∧
    ∀ r, ts ≠ .wort "finite" :: r

theorem anw_trim (o : SExpr) (t : String) (b : SAnw) (ho : gutPlatz o = true) (ht : TrimGut t)
    (hb : BlockBein b) (hk : BlockKopf b) : AnwBein (.trim o t b) := by
  intro rest F _ hF
  obtain ⟨us, hus⟩ := hk
  obtain ⟨c, cs, hc, ck⟩ := platz_kopf o ho
  rcases ht with rfl | ⟨ts, rfl, hts, hfin⟩
  · have hroh : rohToks "finite" = [.wort "finite"] := by
      rw [rohToks_name "finite" (by decide)]; simp only [nameTok, List.cons.injEq, ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false,
  Bool.not_eq_false, and_true]; decide
    simp only [fbA, druckAnw, hroh, List.length_append, List.length_cons, List.length_nil] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hd : druckAnw (.trim o "finite" b) ++ rest = .wort "narrow" :: (druckToks o ++
        .wort "to" :: .wort "finite" :: .wort "else" :: (druckAnw b ++ rest)) := by
      simp only [druckAnw, List.cons_append, List.nil_append, hroh, List.append_assoc]
    have hO := ortP o ho (.wort "to" :: .wort "finite" :: .wort "else" :: (druckAnw b ++ rest)) F' rfl
      (by omega)
    have hB := hb rest F' (by simp only [fbA]; omega)
    rw [hd, parseStmt_narrow _ _ (by rw [hc]; first | rfl | exact ortsFort_nameTok _ _)]
    simp only [parseNarrow, hO, strEq_self, ↓reduceIte, hB]
  · have hroh := rohToks_render ts (fun x hx => (hts x hx).1)
    simp only [fbA, druckAnw, hroh, List.length_append, List.length_cons, List.length_nil] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
    have hd : druckAnw (.trim o (renderText ts) b) ++ rest = .wort "narrow" :: (druckToks o ++
        .wort "to" :: (ts ++ .wort "else" :: (druckAnw b ++ rest))) := by
      simp only [druckAnw, List.cons_append, List.nil_append, hroh, List.append_assoc]
    have hO := ortP o ho (.wort "to" :: (ts ++ .wort "else" :: (druckAnw b ++ rest))) F' rfl (by omega)
    have hB := hb rest F' (by simp only [fbA]; omega)
    have hN := nimmBisWort_roh "else" ts (druckAnw b ++ rest) hts
    rw [hd, parseStmt_narrow _ _ (by rw [hc]; first | rfl | exact ortsFort_nameTok _ _)]
    simp only [parseNarrow, hO, strEq_self, ite_true]
    split
    · rename_i z rest'' heq
      have hz : strEq z "finite" = false := by
        cases h : strEq z "finite"
        · rfl
        · have := (strEq_eq _ _).mp h
          subst this
          cases ts with
          | nil => simp only [List.nil_append, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and] at heq
          | cons x xs => simp only [List.cons_append, List.cons.injEq] at heq; exact absurd (by rw [heq.1]) (hfin xs)
      simp only [hz, Bool.false_eq_true, ite_false]
      rw [hN]
      simp only [nimmWort, strEq_self, ↓reduceIte, hB]
    · rw [hN]
      simp only [nimmWort, strEq_self, ↓reduceIte, hB]

/-- `traverseRest` stops at `invariant` too. -/
theorem traverseRest_roh2 : ∀ (ts rest : List Token) (x : Token),
    (x = .zeichen "{" ∨ x = .wort "invariant") →
    (∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .wort "invariant") →
    traverseRest (ts ++ x :: rest) = .ok (renderText ts, x :: rest) := by
  intro ts rest x hx
  rcases hx with rfl | rfl
  · exact traverseRest_roh ts rest
  · induction ts with
    | nil => intro _; simp only [List.nil_append, traverseRest, strEq_self, ↓reduceIte, renderText_nil]
    | cons t ts ih =>
      intro h
      obtain ⟨hg, h1, h2⟩ := h t (by simp only [List.mem_cons, true_or])
      have ih' := ih (fun x hx => h x (by simp only [List.mem_cons, hx, or_true]))
      rw [renderText_cons t ts hg]
      cases t with
      | wort s =>
        have hs : strEq s "invariant" = false := by
          cases e : strEq s "invariant"
          · rfl
          · exact absurd (by rw [(strEq_eq _ _).mp e]) h2
        simp only [List.cons_append, traverseRest, hs, Bool.false_eq_true, ↓reduceIte, ih', zeigeTok]
      | zeichen s =>
        have hs : s ≠ "{" := fun e => h1 (by rw [e])
        simp only [List.cons_append, traverseRest, ih', zeigeTok]
      | _ => simp only [List.cons_append, traverseRest, ih']

/-- The raw words of a `traverse` header: no brace, no `invariant`. -/
def RohTrav (r : String) : Prop :=
  ∃ ts, r = renderText ts ∧ ∀ t ∈ ts, TokGut t ∧ t ≠ .zeichen "{" ∧ t ≠ .wort "invariant"

/-- The tokens an optional `of e` / `invariant e` adds. -/
def optTokLen : Option SExpr → Nat
  | some x => 1 + (druckToks x).length
  | none => 0

theorem anw_each (b : String) (o : Option SExpr) (k : String) (s : SExpr) (m : String) (r : String)
    (i : Option SExpr) (body : SAnw) (ho : ∀ e, o = some e → gut e = true) (hs : gut s = true)
    (hr : RohTrav r) (hi : ∀ e, i = some e → PredGut e) (hb : BlockBein body)
    (hk : BlockKopf body) : AnwBein (.each b o k s m r i body) := by
  intro rest F _ hF
  obtain ⟨ts, rfl, hts⟩ := hr
  obtain ⟨us, hus⟩ := hk
  have hroh := rohToks_render ts (fun x hx => (hts x hx).1)
  have hd0 : ∀ (O I : List Token), [Token.wort "traverse", nameTok b] ++ O ++
      [.wort "over", nameTok k, .wort "of"] ++ druckToks s ++ [.wort "by", nameTok m] ++ ts ++ I ++
        druckAnw body ++ rest = .wort "traverse" :: nameTok b :: (O ++ (.wort "over" :: nameTok k ::
          .wort "of" :: (druckToks s ++ (.wort "by" :: nameTok m :: (ts ++ (I ++ (.zeichen "{" ::
            (us ++ rest)))))))) := by
    intro O I; rw [hus]; simp only [List.cons_append, List.nil_append, List.append_assoc]
  have hlen : ∀ (O I : List Token), (druckAnw (.each b o k s m (renderText ts) i body)).length =
      2 + optTokLen o + 3 + (druckToks s).length + 2 + ts.length + optTokLen i +
        (druckAnw body).length := by
    intro _ _
    cases o <;> cases i <;> simp only [druckAnw, List.append_nil, List.cons_append, List.nil_append, hroh, List.append_assoc, List.length_cons, List.length_append, optTokLen, Nat.add_zero, Nat.reduceAdd] <;> omega
  have hlen' := hlen [] []
  simp only [fbA, hlen'] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  have hS : ∀ (T : List Token), parseOr F' (druckToks s ++ .wort "by" :: T) = .ok (s, .wort "by" :: T) :=
    fun T => ausdruck s hs _ F' rfl rfl rfl (by omega)
  have hB : parseBlock F' (.zeichen "{" :: (us ++ rest)) = .ok (body, rest) := by
    have := hb rest F' (by simp only [fbA]; omega)
    rw [hus] at this; simpa using this
  have hT1 := traverseRest_roh2 ts (us ++ rest) (.zeichen "{") (Or.inl rfl) hts
  cases o with
  | none =>
    cases i with
    | none =>
      have hd : druckAnw (.each b none k s m (renderText ts) none body) ++ rest =
          [Token.wort "traverse", nameTok b] ++ [] ++ [.wort "over", nameTok k, .wort "of"] ++
          druckToks s ++ [.wort "by", nameTok m] ++ ts ++ [] ++ druckAnw body ++ rest := by
        simp only [druckAnw, List.append_nil, List.cons_append, List.nil_append, hroh, List.append_assoc]
      rw [hd, hd0, parseStmt_traverse _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
      simp only [List.nil_append] at hT1 ⊢
      simp only [parseTraverse, nimmName, nameText_nameTok, List.cons.injEq, Token.wort.injEq, String.reduceEq,
  false_and, imp_self, implies_true, nimmWort, strEq_self, ↓reduceIte, hS, hT1, hB]
    | some e =>
      have he := hi e rfl
      have hd : druckAnw (.each b none k s m (renderText ts) (some e) body) ++ rest =
          [Token.wort "traverse", nameTok b] ++ [] ++ [.wort "over", nameTok k, .wort "of"] ++
          druckToks s ++ [.wort "by", nameTok m] ++ ts ++ ([.wort "invariant"] ++ druckToks e) ++
            druckAnw body ++ rest := by
        simp only [druckAnw, List.append_nil, List.cons_append, List.nil_append, hroh, List.append_assoc]
      have hT := traverseRest_roh2 ts (druckToks e ++ (.zeichen "{" :: (us ++ rest))) (.wort "invariant")
        (Or.inr rfl) hts
      have hE := pred_voll e he (.zeichen "{" :: (us ++ rest)) ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩ F'
        (by simp only [bP]; simp only [optTokLen] at hF; omega)
      rw [hd, hd0, parseStmt_traverse _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
      simp only [List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hT ⊢
      simp only [parseTraverse, nimmName, nameText_nameTok, List.cons.injEq, Token.wort.injEq, String.reduceEq,
  false_and, imp_self, implies_true, nimmWort, strEq_self, ↓reduceIte, hS, hT, hE, hB]
  | some x =>
    have hx := ho x rfl
    have hX : ∀ (T : List Token), parseOr F' (druckToks x ++ .wort "over" :: T) = .ok (x, .wort "over" :: T) :=
      fun T => ausdruck x hx _ F' rfl rfl rfl (by simp only [optTokLen] at hF; omega)
    cases i with
    | none =>
      have hd : druckAnw (.each b (some x) k s m (renderText ts) none body) ++ rest =
          [Token.wort "traverse", nameTok b] ++ ([.wort "of"] ++ druckToks x) ++
          [.wort "over", nameTok k, .wort "of"] ++ druckToks s ++ [.wort "by", nameTok m] ++ ts ++ [] ++
            druckAnw body ++ rest := by
        simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, hroh, List.append_nil]
      rw [hd, hd0, parseStmt_traverse _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
      simp only [List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hT1 ⊢
      simp only [parseTraverse, nimmName, nameText_nameTok, hX, nimmWort, strEq_self, ↓reduceIte, hS, hT1, hB]
    | some e =>
      have he := hi e rfl
      have hd : druckAnw (.each b (some x) k s m (renderText ts) (some e) body) ++ rest =
          [Token.wort "traverse", nameTok b] ++ ([.wort "of"] ++ druckToks x) ++
          [.wort "over", nameTok k, .wort "of"] ++ druckToks s ++ [.wort "by", nameTok m] ++ ts ++
            ([.wort "invariant"] ++ druckToks e) ++ druckAnw body ++ rest := by
        simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, hroh]
      have hT := traverseRest_roh2 ts (druckToks e ++ (.zeichen "{" :: (us ++ rest))) (.wort "invariant")
        (Or.inr rfl) hts
      have hE := pred_voll e he (.zeichen "{" :: (us ++ rest)) ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩ F'
        (by simp only [bP]; simp only [optTokLen] at hF; omega)
      rw [hd, hd0, parseStmt_traverse _ _ (by first | rfl | exact ortsFort_nameTok _ _)]
      simp only [List.nil_append, List.cons_append, List.append_assoc, List.singleton_append] at hT ⊢
      simp only [parseTraverse, nimmName, nameText_nameTok, hX, nimmWort, strEq_self, ↓reduceIte, hS, hT, hE, hB]


/-! ### `if` with `else if` branches, `match` with arms -/

/-- The legs of an `else if` branch. -/
def ElsifBein (x : SAnw) : Prop :=
  ∃ c b, x = .elsif c b ∧ gut c = true ∧ BlockBein b ∧ BlockKopf b

/-- The tokens of an optional `else` block. -/
def druckSonst : Option SAnw → List Token
  | some b => [.wort "else"] ++ druckAnw b
  | none => []

theorem elseIfs_rund : ∀ (eis : List SAnw) (s : Option SAnw) (acc : List SAnw) (rest : List Token) (F : Nat),
    (∀ x ∈ eis, ElsifBein x) → (∀ b, s = some b → BlockBein b ∧ BlockKopf b) →
    (s = none → KE rest) → 8 * (druckAnwListe eis ++ druckSonst s).length + 31 ≤ F →
    parseElseIfs F (druckAnwListe eis ++ druckSonst s ++ rest) acc = .ok ((acc ++ eis, s), rest) := by
  intro eis
  induction eis with
  | nil =>
    intro s acc rest F _ hs hK hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases s with
    | none =>
      have hk := hK rfl
      simp only [druckAnwListe, druckSonst, List.nil_append, List.append_nil]
      rcases rest with _ | ⟨t, r⟩
      · simp only [parseElseIfs]
      · cases t with
        | wort w =>
          have : strEq w "else" = false := by
            cases h : strEq w "else"
            · rfl
            · exact absurd (by rw [(strEq_eq _ _).mp h]) (hk r)
          simp only [parseElseIfs, this, Bool.false_eq_true, ↓reduceIte]
        | _ => simp only [parseElseIfs]
    | some b =>
      obtain ⟨hb, us, hus⟩ := hs b rfl
      simp only [druckAnwListe, druckSonst, List.nil_append, List.length_append, List.length_cons,
        List.length_nil] at hF ⊢
      have hB := hb rest F' (by simp only [fbA]; omega)
      rw [hus] at hB ⊢
      simp only [List.cons_append, List.append_assoc] at hB ⊢
      simp only [parseElseIfs, strEq_self, ↓reduceIte, List.nil_append, hB, List.append_nil]
  | cons x eis ih =>
    intro s acc rest F hx hs hK hF
    obtain ⟨c, b, rfl, hc, hb, us, hus⟩ := hx x (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckAnwListe, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
    have hR := ih s (acc ++ [.elsif c b]) rest F' (fun y hy => hx y (List.mem_cons_of_mem _ hy)) hs hK
      (by simp only [List.length_append]; omega)
    have hB := hb (druckAnwListe eis ++ druckSonst s ++ rest) F' (by simp only [fbA]; omega)
    have hC := ausdruck c hc (druckAnw b ++ (druckAnwListe eis ++ druckSonst s ++ rest)) F'
      (by rw [hus]; rfl) (by rw [hus]; rfl) (by rw [hus]; rfl) (by omega)
    have hd : druckAnwListe (.elsif c b :: eis) ++ druckSonst s ++ rest = .wort "else" :: .wort "if" ::
        (druckToks c ++ (druckAnw b ++ (druckAnwListe eis ++ druckSonst s ++ rest))) := by
      simp only [druckAnwListe, druckAnw, List.cons_append, List.nil_append, List.append_assoc]
    rw [hd]
    simp only [List.append_assoc] at hR hB hC ⊢
    simp only [parseElseIfs, strEq_self, ↓reduceIte, List.tail_cons, hC, hB, hR, List.cons_append,
  List.nil_append]

theorem anw_cond (c : SExpr) (t : SAnw) (eis : List SAnw) (s : Option SAnw) (hc : gut c = true)
    (ht : BlockBein t) (htk : BlockKopf t) (heis : ∀ x ∈ eis, ElsifBein x)
    (hs : ∀ b, s = some b → BlockBein b ∧ BlockKopf b) : AnwBein (.cond c t eis s) := by
  intro rest F hK hF
  obtain ⟨us, hus⟩ := htk
  have hd : druckAnw (.cond c t eis s) ++ rest = .wort "if" :: (druckToks c ++ (druckAnw t ++
      (druckAnwListe eis ++ druckSonst s ++ rest))) := by
    cases s <;> simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, druckSonst]
  have hlen : (druckAnw (.cond c t eis s)).length = 1 + (druckToks c).length + (druckAnw t).length +
      (druckAnwListe eis ++ druckSonst s).length := by
    cases s <;> simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc, List.append_nil, List.length_cons, List.length_append, druckSonst] <;> omega
  simp only [fbA, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨k, ks, hk, hkg⟩ := druck_kopf c hc
  have hE := elseIfs_rund eis s [] rest F' heis hs (fun _ => hK) (by omega)
  have hT := ht (druckAnwListe eis ++ druckSonst s ++ rest) F' (by simp only [fbA]; omega)
  have hC := ausdruck c hc (druckAnw t ++ (druckAnwListe eis ++ druckSonst s ++ rest)) F'
    (by rw [hus]; rfl) (by rw [hus]; rfl) (by rw [hus]; rfl) (by omega)
  rw [hd, parseStmt_if _ _ (by rw [hk]; exact kopf_nicht_ortsfort k hkg _)]
  simp only [List.append_assoc] at hE hT hC ⊢
  simp only [parseWenn, hC, hT, hE, List.nil_append]

/-- The legs of a `match` arm. -/
def ArmBein (x : SAnw) : Prop :=
  ∃ v bi b, x = .arm v bi b ∧ BlockBein b ∧ BlockKopf b

theorem arme_rund : ∀ (arms : List SAnw) (rest : List Token) (F : Nat),
    (∀ x ∈ arms, ArmBein x) → 8 * (druckAnwListe arms).length + 31 ≤ F →
    parseArme F (druckAnwListe arms ++ .zeichen "}" :: rest) = .ok (arms, .zeichen "}" :: rest) := by
  intro arms
  induction arms with
  | nil =>
    intro rest F _ hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseArme, druckAnwListe, List.nil_append]
  | cons x arms ih =>
    intro rest F hx hF
    obtain ⟨v, bi, b, rfl, hb, us, hus⟩ := hx x (by simp only [List.mem_cons, true_or])
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    have hR := ih rest F' (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    have hB := hb (druckAnwListe arms ++ .zeichen "}" :: rest) F'
    cases bi with
    | none =>
      simp only [druckAnwListe, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
      have hd : druckAnwListe (.arm v none b :: arms) ++ .zeichen "}" :: rest = nameTok v :: .zeichen "=>" ::
          (druckAnw b ++ (druckAnwListe arms ++ .zeichen "}" :: rest)) := by
        simp only [druckAnwListe, druckAnw, List.append_nil, List.cons_append, List.nil_append, List.append_assoc]
      rw [hd]
      rw [hus] at hB ⊢
      simp only [List.cons_append] at hB
      simp only [parseArme, List.cons_append, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self,
  implies_true, nimmName, nameText_nameTok, fordereZeichen, Token.zeichen.injEq, String.reduceEq, strEq_self,
  ↓reduceIte, hB (by simp only [fbA]; omega), hR (by omega)]
    | some y =>
      simp only [druckAnwListe, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
      have hd : druckAnwListe (.arm v (some y) b :: arms) ++ .zeichen "}" :: rest = nameTok v ::
          .zeichen "(" :: nameTok y :: .zeichen ")" :: .zeichen "=>" ::
          (druckAnw b ++ (druckAnwListe arms ++ .zeichen "}" :: rest)) := by
        simp only [druckAnwListe, druckAnw, List.cons_append, List.nil_append, List.append_assoc]
      rw [hd]
      rw [hus] at hB ⊢
      simp only [List.cons_append] at hB
      simp only [parseArme, List.cons_append, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self,
  implies_true, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hB (by simp only [fbA]; omega),
  hR (by omega)]

theorem anw_cases (g : SExpr) (arms : List SAnw) (hg : gut g = true) (ha : ∀ x ∈ arms, ArmBein x) :
    AnwBein (.cases g arms) := by
  intro rest F _ hF
  simp only [fbA, druckAnw, List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 2 := ⟨F - 2, by omega⟩
  obtain ⟨k, ks, hk, hkg⟩ := druck_kopf g hg
  have hd : druckAnw (.cases g arms) ++ rest = .wort "match" :: (druckToks g ++ .zeichen "{" ::
      (druckAnwListe arms ++ .zeichen "}" :: rest)) := by
    simp only [druckAnw, List.cons_append, List.nil_append, List.append_assoc]
  have hG := ausdruck g hg (.zeichen "{" :: (druckAnwListe arms ++ .zeichen "}" :: rest)) F' rfl rfl rfl
    (by omega)
  have hA := arme_rund arms rest F' ha (by omega)
  rw [hd, parseStmt_match _ _ (by rw [hk]; exact kopf_nicht_ortsfort k hkg _)]
  simp only [parseMatchS, hG, fordereZeichen, strEq_self, ↓reduceIte, hA]


/-! ### The printability class and the induction -/

/-- The position of a statement tree: a statement, a block, an `else if` branch, a `match` arm. -/
inductive Rolle
  | anw | block | elsif | arm

/-- A printable ender: a valued `return` has a printable value. -/
def EndeOk : Option SEnde → Prop
  | some (.ret (some x)) => gut x = true
  | _ => True

/-- **The printability class of statements and blocks** (see the header). -/
inductive AnwGut : Rolle → SAnw → Prop
  | bind (m : Bool) (x : String) (ty : Option STyp) (e : SExpr) : x ≠ "mut" →
      TypOptGut ty → gut e = true → AnwGut .anw (.bind m x ty e)
  | bindElse (x : String) (ty : Option STyp) (e : SExpr) (f : String) (b : SAnw) : x ≠ "mut" →
      TypOptGut ty → gut e = true → AnwGut .block b → AnwGut .anw (.bindElse x ty e f b)
  | bindLib (m : Bool) (x : String) (ty : Option STyp) (l g : String) : x ≠ "mut" →
      TypOptGut ty → AnwGut .anw (.bindLib m x ty l g)
  | set (z : SExpr) (o : String) (w : SExpr) :
      gutPlatz z = true → istZuweis o = true → gut w = true → AnwGut .anw (.set z o w)
  | shift (z : SExpr) (a b : String) : gutPlatz z = true → AnwGut .anw (.shift z a b)
  | call (f : String) (xs : List SExpr) : NameGut f → istAnwWort f = false → gutListe xs = true →
      AnwGut .anw (.call f xs)
  | lcall (l g : String) (n : Nat) : AnwGut .anw (.lcall l g n)
  | cond (c : SExpr) (t : SAnw) (eis : List SAnw) (s : Option SAnw) :
      gut c = true → AnwGut .block t → (∀ x ∈ eis, AnwGut .elsif x) →
      (∀ b, s = some b → AnwGut .block b) → AnwGut .anw (.cond c t eis s)
  | elsif (c : SExpr) (b : SAnw) : gut c = true → AnwGut .block b → AnwGut .elsif (.elsif c b)
  | cases (g : SExpr) (arms : List SAnw) :
      gut g = true → (∀ x ∈ arms, AnwGut .arm x) → AnwGut .anw (.cases g arms)
  | arm (v : String) (bi : Option String) (b : SAnw) : AnwGut .block b → AnwGut .arm (.arm v bi b)
  | each (b : String) (o : Option SExpr) (k : String) (s : SExpr) (m r : String) (i : Option SExpr)
      (body : SAnw) : (∀ e, o = some e → gut e = true) → gut s = true → RohTrav r →
      (∀ e, i = some e → PredGut e) → AnwGut .block body → AnwGut .anw (.each b o k s m r i body)
  | retry (h : String) (b : SAnw) : RohKopf h → AnwGut .block b → AnwGut .anw (.retry h b)
  | loop (h : String) (b : SAnw) : RohKopf h → AnwGut .block b → AnwGut .anw (.loop h b)
  | waive (ns : List String) (b : SAnw) : ns ≠ [] → AnwGut .block b → AnwGut .anw (.waive ns b)
  | trim (o : SExpr) (t : String) (b : SAnw) :
      gutPlatz o = true → TrimGut t → AnwGut .block b → AnwGut .anw (.trim o t b)
  | locks (g : Bool) (o : SExpr) (b : SAnw) :
      gutPlatz o = true → (g = false → kopfName o ≠ "shared") → AnwGut .block b →
      AnwGut .anw (.locks g o b)
  | watch (d : String) (b : SAnw) : AnwGut .block b → AnwGut .anw (.watch d b)
  | leave (l : String) : AnwGut .anw (.leave l)
  | next (l : String) : AnwGut .anw (.next l)
  | emit (z w : SExpr) (p : String) :
      gutPlatz z = true → gut w = true → PubGut p → AnwGut .anw (.emit z w p)
  | await (n : String) (ty : Option STyp) (q : SExpr) (p : String) : n ≠ "mut" → TypOptGut ty → gut q = true →
      RohZu p → AnwGut .anw (.await n ty q p)
  | swap (n : String) (ty : Option STyp) (o : SExpr) (k : String) : n ≠ "mut" → TypOptGut ty → gut o = true →
      RohSemi k → AnwGut .anw (.swap n ty o k)
  | step (a b : String) : AnwGut .anw (.step a b)
  | retLeer : AnwGut .anw (.ret none)
  | ret (e : SExpr) : gut e = true → AnwGut .anw (.ret (some e))
  | alloc (m : Bool) (n : String) (ty : Option STyp) (t : String) (w : SExpr) (s : Option SAnw) :
      n ≠ "mut" → TypOptGut ty → gut w = true → (∀ b, s = some b → AnwGut .block b) →
      AnwGut .anw (.alloc m n ty t w s)
  | reset (a : String) (rg : Option (SExpr × SExpr)) :
      (∀ i n, rg = some (i, n) → gut i = true ∧ gut n = true) → AnwGut .anw (.reset a rg)
  | grow (a : String) (e : SExpr) (b : SAnw) : gut e = true → AnwGut .block b → AnwGut .anw (.grow a e b)
  | free (z : SExpr) : gutPlatz z = true → AnwGut .anw (.free z)
  | child (b : SAnw) : AnwGut .block b → AnwGut .anw (.child b)
  | start (ps : List String) : ps ≠ [] → (∀ p ∈ ps, NameGut p) → AnwGut .anw (.start ps)
  | block (ss : List SAnw) (e : Option SEnde) :
      (∀ s ∈ ss, AnwGut .anw s) → EndeOk e → EndeGut ss e → AnwGut .block (.block ss e)
  | allocVon (m : Bool) (n : String) (ty : Option STyp) (t : String) :
      n ≠ "mut" → TypOptGut ty → AnwGut .anw (.allocVon m n ty t)

/-- What the induction carries per position. -/
def Bein : Rolle → SAnw → Prop
  | .anw, s => AnwBein s ∧ AnwKopf s
  | .block, b => BlockBein b ∧ BlockKopf b
  | .elsif, x => ElsifBein x
  | .arm, x => ArmBein x

theorem anwKopf_wort (s : SAnw) (w : String) (hw : w ≠ "else") (h : ∃ ts, druckAnw s = .wort w :: ts) :
    AnwKopf s := by
  obtain ⟨ts, h⟩ := h
  exact ⟨_, ts, h, by simp only [ne_eq, reduceCtorEq, not_false_eq_true], by intro e; injection e with e; exact hw e, by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩

theorem nameTok_ne_else {a : String} (h : a ≠ "else") : nameTok a ≠ .wort "else" := by
  unfold nameTok; split
  · intro e; injection e with e; exact h e
  · simp only [ne_eq, reduceCtorEq, not_false_eq_true]

theorem anwKopf_ident (s : SAnw) (a : String) (ha : a ≠ "else")
    (h : ∃ ts, druckAnw s = nameTok a :: ts) : AnwKopf s := by
  obtain ⟨ts, h⟩ := h
  exact ⟨_, ts, h, by simp only [ne_eq, nameTok_ne_zeichen, not_false_eq_true], nameTok_ne_else ha, by simp only [ne_eq, nameTok_ne_ende, not_false_eq_true]⟩

theorem anwKopf_platz (s : SAnw) (z : SExpr) (hz : gutPlatz z = true)
    (h : ∃ ts, druckAnw s = druckToks z ++ ts) : AnwKopf s := by
  obtain ⟨ts, h⟩ := h
  obtain ⟨a, us, hu, ak⟩ := platz_kopf z hz
  exact anwKopf_ident s a (by intro e; subst e; revert ak; decide) ⟨us ++ ts, by rw [h, hu]; simp only [List.cons_append]⟩

theorem ende_bein (e : Option SEnde) (he : EndeOk e) : ∀ s ∈ endeAnw e, AnwBein s ∧ AnwKopf s := by
  intro s hs
  cases e with
  | none => simp only [endeAnw, List.not_mem_nil] at hs
  | some e' =>
    cases e' with
    | ret x =>
      cases x with
      | none =>
        simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
        exact ⟨anw_ret_leer, anwKopf_wort _ "return" (by decide) ⟨_, rfl⟩⟩
      | some y =>
        simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
        exact ⟨anw_ret y he, anwKopf_wort _ "return" (by decide) ⟨_, rfl⟩⟩
    | leave l =>
      simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
      exact ⟨anw_leave l, anwKopf_wort _ "leave" (by decide) ⟨_, rfl⟩⟩
    | next l =>
      simp only [endeAnw, List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
      exact ⟨anw_next l, anwKopf_wort _ "next" (by decide) ⟨_, rfl⟩⟩

/-- **The induction**: every printable tree has the legs of its position. -/
theorem bein_gut : ∀ (r : Rolle) (s : SAnw), AnwGut r s → Bein r s := by
  intro r s h
  induction h with
  | bind m x ty e hx hty he =>
    exact ⟨anw_bind m x hx ty e hty he, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | bindElse x ty e f b hx hty he _ ihb =>
    exact ⟨anw_bindElse x hx ty e f b hty he ihb.1, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | bindLib m x ty l g hx hty =>
    exact ⟨anw_bindLib m x hx ty l g hty, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | set z o w hz ho hw =>
    exact ⟨anw_set z o w hz ho hw, anwKopf_platz _ z hz ⟨_, by simp only [druckAnw, List.append_assoc, List.cons_append, List.nil_append, List.append_cancel_left_eq] <;> rfl⟩⟩
  | shift z a b hz =>
    exact ⟨anw_shift z a b hz, anwKopf_wort _ "transition" (by decide) ⟨_, rfl⟩⟩
  | call f xs hf hw hxs =>
    exact ⟨anw_call f xs hf hw hxs, anwKopf_ident _ f (by intro e; subst e; revert hw; decide)
      ⟨_, by simp only [druckAnw, rohToks_nameGut f hf, List.cons_append, List.nil_append, List.cons.injEq, true_and] <;> rfl⟩⟩
  | lcall l g n =>
    exact ⟨anw_lcall l g n, ⟨.zeichen "@", _, rfl, by simp only [ne_eq, Token.zeichen.injEq, String.reduceEq, not_false_eq_true], by simp only [ne_eq, reduceCtorEq, not_false_eq_true], by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩⟩
  | cond c t eis s hc _ _ _ iht iheis ihs =>
    exact ⟨anw_cond c t eis s hc iht.1 iht.2 iheis ihs, anwKopf_wort _ "if" (by decide)
      (by cases s <;> exact ⟨_, rfl⟩)⟩
  | elsif c b hc _ ihb => exact ⟨c, b, rfl, hc, ihb.1, ihb.2⟩
  | cases g arms hg _ iha =>
    exact ⟨anw_cases g arms hg iha, anwKopf_wort _ "match" (by decide) ⟨_, rfl⟩⟩
  | arm v bi b _ ihb => exact ⟨v, bi, b, rfl, ihb.1, ihb.2⟩
  | each b o k s m r i body ho hs hr hi _ ihb =>
    exact ⟨anw_each b o k s m r i body ho hs hr hi ihb.1 ihb.2,
      anwKopf_wort _ "traverse" (by decide) ⟨_, rfl⟩⟩
  | retry h b hh _ ihb =>
    exact ⟨by simpa using anw_schleife 1 h b (Or.inl rfl) hh ihb.1 ihb.2,
      anwKopf_wort _ "retry" (by decide) ⟨_, rfl⟩⟩
  | loop h b hh _ ihb =>
    exact ⟨by simpa using anw_schleife 2 h b (Or.inr rfl) hh ihb.1 ihb.2,
      anwKopf_wort _ "forever" (by decide) ⟨_, rfl⟩⟩
  | waive ns b hne _ ihb =>
    exact ⟨anw_waive ns b hne ihb.1 ihb.2, anwKopf_wort _ "breaking" (by decide) ⟨_, rfl⟩⟩
  | trim o t b ho ht _ ihb =>
    exact ⟨anw_trim o t b ho ht ihb.1 ihb.2, anwKopf_wort _ "narrow" (by decide) ⟨_, rfl⟩⟩
  | locks g o b ho hsh _ ihb =>
    exact ⟨anw_locks g o b ho hsh ihb.1 ihb.2, anwKopf_wort _ "locks" (by decide) ⟨_, rfl⟩⟩
  | watch d b _ ihb =>
    exact ⟨anw_watch d b ihb.1 ihb.2, anwKopf_wort _ "observes" (by decide) ⟨_, rfl⟩⟩
  | leave l => exact ⟨anw_leave l, anwKopf_wort _ "leave" (by decide) ⟨_, rfl⟩⟩
  | next l => exact ⟨anw_next l, anwKopf_wort _ "next" (by decide) ⟨_, rfl⟩⟩
  | emit z w p hz hw hp =>
    exact ⟨anw_emit z w p hz hw hp, anwKopf_platz _ z hz ⟨_, by simp only [druckAnw, List.append_assoc, List.cons_append, List.nil_append, List.append_cancel_left_eq] <;> rfl⟩⟩
  | await n ty q p hx hty hq hp =>
    exact ⟨anw_await n hx ty q p hty hq hp, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | swap n ty o k hx hty ho hk =>
    exact ⟨anw_swap n hx ty o k hty ho hk, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | step a b => exact ⟨anw_step a b, anwKopf_wort _ "advances" (by decide) ⟨_, rfl⟩⟩
  | retLeer => exact ⟨anw_ret_leer, anwKopf_wort _ "return" (by decide) ⟨_, rfl⟩⟩
  | ret e he => exact ⟨anw_ret e he, anwKopf_wort _ "return" (by decide) ⟨_, rfl⟩⟩
  | alloc m n ty t w s hx hty hw _ ihs =>
    exact ⟨anw_alloc m n hx ty t w s hty hw (fun b hb => (ihs b hb).1),
      anwKopf_wort _ "let" (by decide) (by cases s <;> exact ⟨_, rfl⟩)⟩
  | allocVon m n ty t hx hty =>
    exact ⟨anw_allocVon m n hx ty t hty, anwKopf_wort _ "let" (by decide) ⟨_, rfl⟩⟩
  | reset a rg hrg => exact ⟨anw_reset a rg hrg, anwKopf_wort _ "reset" (by decide) ⟨_, rfl⟩⟩
  | grow a e b he _ ihb =>
    exact ⟨anw_grow a e b he ihb.1 ihb.2, anwKopf_wort _ "grow" (by decide) ⟨_, rfl⟩⟩
  | free z hz => exact ⟨anw_free z hz, anwKopf_wort _ "free" (by decide) ⟨_, rfl⟩⟩
  | child b _ ihb =>
    exact ⟨anw_child b ihb.1 ihb.2, anwKopf_wort _ "child" (by decide) ⟨_, rfl⟩⟩
  | start ps hne hp => exact ⟨anw_start ps hne hp, anwKopf_ident _ "start" (by decide) ⟨_, rfl⟩⟩
  | block ss e _ he hw ihss =>
    refine ⟨block_rund ss e ?_ hw, blockKopf_block ss e⟩
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · exact ihss s h
    · exact ende_bein e he s h

/-- **L2b: every printable statement reads back** before an `else`-free follow. -/
theorem rundlauf_anw (s : SAnw) (h : AnwGut .anw s) (rest : List Token) (F : Nat) (hK : KE rest)
    (hF : fbA s ≤ F) : parseStmt F (druckAnw s ++ rest) = .ok (s, rest) :=
  (bein_gut .anw s h).1 rest F hK hF

/-- **L2b: every printable block reads back**, whatever follows. -/
theorem rundlauf_block (b : SAnw) (h : AnwGut .block b) (rest : List Token) (F : Nat)
    (hF : fbA b ≤ F) : parseBlock F (druckAnw b ++ rest) = .ok (b, rest) :=
  (bein_gut .block b h).1 rest F hF

/-- The whole block reader (`parseTopBlock`, fuel `8 * length + 32`). -/
theorem parseTopBlock_druck (b : SAnw) (h : AnwGut .block b) :
    parseTopBlock (druckAnw b ++ [.ende]) = .ok b := by
  unfold parseTopBlock
  rw [rundlauf_block b h [.ende] _ (by simp only [fbA, List.length_append, List.length_singleton]; omega)]

/-- **Composition with L1**: a printable block whose print is lexically clean reads back from its
    rendered source text. -/
theorem rundlauf_block_text (b : SAnw) (h : AnwGut .block b) (ht : ∀ t ∈ druckAnw b, TokGut t) :
    (match lex (renderText (druckAnw b)) with
      | .ok toks => parseTopBlock toks
      | .error _ => .error "lex") = .ok b := by
  rw [lex_render _ ht]
  exact parseTopBlock_druck b h


/-! ### Witnesses -/

/-- A block with a typed `let`, an indexed compound assignment, an `if` with an `else if` branch and
    an `else` block (holding a `child`), a `retry` with a raw header, a shared `locks`, a call, and a
    valued `return` as the ender. The binder `x`, the variable `x` and the call head `max` are table
    words: they print as `wort` and read back as names. -/
def zeugeBlock : SAnw :=
  .block [
    .bind false "x" (some (.atom "u32")) (.bin "+" (.variable "a") (.lit 1)),
    .set (.index (.variable "t") (.variable "x")) "+=" (.lit 2),
    .cond (.bin "<" (.variable "x") (.lit 10)) (.block [.call "max" [.variable "x"]] none)
      [.elsif (.bin "==" (.variable "x") (.lit 10)) (.block [] (some (.leave "l")))]
      (some (.block [.child (.block [] none)] none)),
    .retry (renderText [.wort "until", .ident "fertig"]) (.block [] none),
    .locks true (.variable "L") (.block [] none)]
    (some (.ret (some (.variable "x"))))

theorem zeugeBlock_gut : AnwGut .block zeugeBlock := by
  have leer : AnwGut .block (.block [] none) :=
    .block [] none (by simp only [List.not_mem_nil, false_implies, implies_true]) trivial (by intro _ s h; simp only [List.getLast?_nil, reduceCtorEq] at h)
  apply AnwGut.block _ _ _ (by show gut (.variable "x") = true; decide) (by intro h; cases h)
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact .bind _ _ _ _ (by decide) (.kette (.atom "u32") [] (.atom _ (by decide)) (by simp only [TsGut, List.not_mem_nil, false_implies, implies_true]))
      (by decide)
  · exact .set _ _ _ (by decide) (by decide) (by decide)
  · refine .cond _ _ _ _ (by decide) ?_ ?_ ?_
    · refine .block _ _ ?_ trivial (by intro _ s h; simp only [List.getLast?_singleton, Option.some.injEq] at h; subst h; rfl)
      intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
      exact .call _ _ (show nameForm _ = true by decide) (by decide) (by decide)
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx
      exact .elsif _ _ (by decide) (.block [] _ (by simp only [List.not_mem_nil, false_implies, implies_true]) trivial (by intro h; cases h))
    · intro b hb; cases hb
      refine .block _ _ ?_ trivial (by intro _ s h; simp only [List.getLast?_singleton, Option.some.injEq] at h; subst h; rfl)
      intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
      exact .child _ leer
  · refine .retry _ _ ⟨[.wort "until", .ident "fertig"], rfl, ?_, ?_⟩ leer
    · intro t ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact ⟨⟨by decide, by decide⟩, by simp only [ne_eq, reduceCtorEq, not_false_eq_true], by simp only [ne_eq, Token.wort.injEq, String.reduceEq, not_false_eq_true]⟩
      · exact ⟨⟨by decide, by decide⟩, by simp only [ne_eq, reduceCtorEq, not_false_eq_true], by simp only [ne_eq, reduceCtorEq, not_false_eq_true]⟩
    · intro R; rfl
  · exact .locks _ _ _ (by decide) (by intro h; cases h) leer

/-- The witness reads back through the whole block reader. -/
theorem zeugeBlock_rund : parseTopBlock (druckAnw zeugeBlock ++ [.ende]) = .ok zeugeBlock :=
  parseTopBlock_druck zeugeBlock zeugeBlock_gut

/-- The witness from its rendered source text (lexer, then the block reader). -/
theorem zeugeBlock_text :
    (match lex (renderText (druckAnw zeugeBlock)) with
      | .ok toks => parseTopBlock toks
      | .error _ => .error "lex") = .ok zeugeBlock :=
  rundlauf_block_text zeugeBlock zeugeBlock_gut (tokGut_of_all _ (by decide))

/-- **Planted defect** (the `EndeGut` hypothesis is needed): a block without an ender whose last
    statement is a `return` reads back with that statement as its ender. -/
theorem endeGut_noetig : ¬ EndeGut [.ret none] none := by
  intro h; exact absurd (h rfl (.ret none) rfl) (by decide)


end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.rundlauf_anw
#print axioms Gabbro.Grammatik.Parser.rundlauf_block
#print axioms Gabbro.Grammatik.Parser.parseTopBlock_druck
#print axioms Gabbro.Grammatik.Parser.rundlauf_block_text
#print axioms Gabbro.Grammatik.Parser.zeugeBlock_rund
#print axioms Gabbro.Grammatik.Parser.zeugeBlock_text

/-
  CUTS: what the statement round trip does not cover, and why.

  * `.other` (the reader never builds it) and a bare block in statement position (the reader has no
    such statement: `parseStmt` on `{` reads a place and fails).
  * A call through a `::` path or through a place (`a::f(x);`, `p->f(x);`): the printer prints the
    callee as text (`rohToks f`, `druck callee`); only a single name-shaped word re-lexes
    to one name token (`NameGut`). Paths would need the lexer over `a::f` without spaces.
  * Raw texts with braces, `;` or the collector's stop word inside (`publishes { a { b } }`, a
    `retry` header with an `effects { .. }` group, a `narrow` range with braces): the collectors track
    braces, but the class here is flat (`RohText` with the stop tokens excluded).
  * A `retry`/`forever` header that starts with a place continuation mark (`=`, `.`, `[`, ...):
    the dispatch would read the head word as a place.
  * Types: see `RundlaufTyp` (no `embeds`, raw groups, `entry fn`, rights lists).
  * Names print as `nameTok` (the lexer's token), so the TEXT level (`rundlauf_block_text`) needs
    only name-shaped names (`TokGut`). A name spelled like a word that opens a form where the name
    stands is outside the class: a `let` binder `mut`; a place head `transition` or a primary word
    (`true`, `false`, `Some`, `None`, `result`, `old`, `count`, `alloc`, and the refused heads of
    `istKeinPlatz`); a call statement head that is a statement word (`istAnwWort`, with `else`);
    the place of a plain `locks` headed `shared`. A variable `count` is excluded although the
    reader takes it unless `<name> in` follows (the `count` quantifier arm).
-/
