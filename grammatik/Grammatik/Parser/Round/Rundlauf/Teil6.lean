module

public import Grammatik.Parser.Expr.Ausdruck
public import Grammatik.Parser.Stmt.Anweisung
public import Grammatik.Parser.Lex.WortStellung
import all Init.Data.Repr
import all Init.Data.String.Defs
public import Grammatik.Parser.Round.Rundlauf.Teil5

@[expose] public section

namespace Gabbro.Grammatik.Parser

-- Whole argument lists through `parseArgs`: head by `toksKopf`
-- (never `)`, so the recursive arm is taken), element by
-- `arg_einzeln`, tail by list induction. Ends at `)`, which is
-- consumed (like every `parseArgs` arm).
theorem args_rund : ∀ (n : Nat) (Rn : R n)
    (xs : List SExpr) (rest : List Token) (F : Nat),
    groesseListe xs ≤ n → gutListe xs = true →
    12 * (groesseListe xs + 1) + groesseListe xs + 10 ≤ F →
    parseArgs F (druckToksListe xs ++ [.zeichen ")"] ++ rest) =
      .ok (xs, rest) := by
  intro n Rn xs
  induction xs with
  | nil =>
    intro rest F hs hg hF
    have hF1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseArgs, druckToksListe, List.nil_append,
      List.cons_append]
  | cons x zs ihzs =>
    intro rest F hs hg hF
    cases zs with
    | nil =>
      -- Singleton: `T(x)` then `)`. One `parseArg`, then close.
      have hx : groesse x ≤ n := by
        simp only [groesseListe] at hs
        omega
      have hxg : gut x = true := gutListe_Kopf x [] hg
      have hkop : ∀ (a : Token) (R : List Token),
          druckToks x = a :: R → a ≠ .zeichen ")" :=
        toksKopf n x hx hxg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [args_einzeln] at ⊢
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ")"] ++ rest ≠
            .zeichen ")" :: R2 := by
        intro R2 hcon
        have hne : druckToks x ≠ [] := by
          intro he
          have hlen := toksLang (groesse x) x (Nat.le_refl _)
          rw [he] at hlen
          simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
        obtain ⟨a, R3, hxb⟩ := List.exists_cons_of_ne_nil hne
        have ha := hkop a R3 hxb
        rw [hxb] at hcon
        simp only [List.cons_append] at hcon
        injection hcon with ha2 _
        exact ha ha2
      simp only [parseArgs, hmiss2] at ⊢
      have harg := arg_einzeln n Rn x (.zeichen ")") rest F' hx hxg
        (Or.inr rfl) (by simp only [groesseListe] at hF ⊢; omega)
      simp only [harg, List.cons_append] at ⊢
      rfl
    | cons y ys =>
      -- Cons: `T(x)` then `,`. Parse the head, step, recurse.
      have hx : groesse x ≤ n := by
        simp only [groesseListe] at hs
        omega
      have hxg : gut x = true := gutListe_Kopf x (y :: ys) hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      rw [args_cons] at ⊢
      have hmiss2 : ∀ (R2 : List Token),
          druckToks x ++ [.zeichen ","] ++ druckToksListe (y :: ys) ++
            [.zeichen ")"] ++ rest ≠
            .zeichen ")" :: R2 := by
        intro R2 hcon
        have hkop : ∀ (a : Token) (R : List Token),
            druckToks x = a :: R → a ≠ .zeichen ")" :=
          toksKopf n x hx hxg
        have hne : druckToks x ≠ [] := by
          intro he
          have hlen := toksLang (groesse x) x (Nat.le_refl _)
          rw [he] at hlen
          simp only [List.length_nil, Nat.le_zero_eq, Nat.succ_ne_self] at hlen
        obtain ⟨a, R3, hxb⟩ := List.exists_cons_of_ne_nil hne
        have ha := hkop a R3 hxb
        rw [hxb] at hcon
        simp only [List.cons_append] at hcon
        injection hcon with ha2 _
        exact ha ha2
      simp only [parseArgs, hmiss2] at ⊢
      have harg := arg_einzeln n Rn x (.zeichen ",")
        (druckToksListe (y :: ys) ++ [.zeichen ")"] ++ rest) F'
        hx hxg (Or.inl rfl) (by simp only [groesseListe] at hF ⊢; omega)
      -- ⊢ : match parseArgs F' (rest-args) ... — the `,` arm was taken;
      -- recurse on the tail.
      have hzs : groesseListe (y :: ys) ≤ n := by
        simp only [groesseListe] at hs ⊢
        omega
      have hxp := groesse_pos x
      have htail := ihzs rest F'
        hzs (gutListe_Schwanz x (y :: ys) hg)
        (by simp only [groesseListe] at hF ⊢; omega)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ harg htail
      simp only [harg, htail, List.cons_append, List.nil_append] at ⊢

-- Calls through `parsePrimary`: head word, then arguments.
theorem sammleSeg_paren : ∀ (f : String) (R : List Token),
    sammleSegmente (Token.zeichen "(" :: R) [f] =
      ([f], Token.zeichen "(" :: R) := by
  intro f R
  rfl
theorem kopf_ruf_head : ∀ (F : Nat) (f : String) (R : List Token),
    parseKopf (F + 1) (nameTok f :: Token.zeichen "(" :: R) =
      match parseArgs F R with
      | .ok (args, rest'') => .ok (.call f args, rest'')
      | .error e => .error e := by
  intro F f R
  simp only [parseKopf, nameText_nameTok]
  rfl
theorem prim_ruf : ∀ (n : Nat) (Rn : R n)
    (f : String) (xs : List SExpr) (rest : List Token) (F : Nat),
    groesse (.call f xs) ≤ n + 1 → gut (.call f xs) = true →
    ruhigSuff rest = true →
    12 * (groesse (.call f xs) + 1) + groesse (.call f xs) + 1 ≤ F →
    parsePrimary F (druckToks (.call f xs) ++ rest) =
      .ok (.call f xs, rest) := by
  intro n Rn f xs rest F hs hg hr hF
  simp only [gut, Bool.and_eq_true] at hg
  obtain ⟨hf, hxs⟩ := hg
  have hF1 : 1 ≤ F := by omega
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  simp only [druckToks, List.cons_append]
  rw [parsePrimary_nameTok _ _ _ (nichtWahr_falsch _ hf)]
  have hF2 : 1 ≤ F' := by omega
  obtain ⟨F'', rfl⟩ : ∃ F'', F' = F'' + 1 := ⟨F' - 1, by omega⟩
  simp only [List.cons_append, kopf_ruf_head] at ⊢
  -- ⊢ : ruf arm → `parseArgs`. Arguments close it.
  have hgl : groesseListe xs ≤ n := by
    simp only [groesse] at hs
    omega
  have hFa : 12 * (groesseListe xs + 1) + groesseListe xs + 10 ≤ F'' := by
    simp only [groesse] at hs hF ⊢
    omega
  have hA := args_rund n Rn xs rest F'' hgl hxs hFa
  simp only [List.cons_append, List.nil_append] at hA ⊢
  simp only [hA] at ⊢

-- Suffix fragments: one `.f`, `->f` or `[i]` step of a place
-- chain. Every `gutPlatz` tree is a head variable plus fragments
-- (`zerlege` below); the printer lays them end to end.
inductive SuffFrag
  | dot : String → SuffFrag
  | arrow : String → SuffFrag
  | idx : SExpr → SuffFrag
def suffToks : List SuffFrag → List Token
  | [] => []
  | .dot f :: s => .zeichen "." :: nameTok f :: suffToks s
  | .arrow f :: s => .zeichen "->" :: nameTok f :: suffToks s
  | .idx i :: s =>
    .zeichen "[" :: druckToks i ++ [.zeichen "]"] ++ suffToks s
def applySuff : SExpr → List SuffFrag → SExpr
  | e, [] => e
  | e, .dot f :: s => applySuff (.field e f) s
  | e, .arrow f :: s => applySuff (.arrow e f) s
  | e, .idx i :: s => applySuff (.index e i) s
def suffGroesse : List SuffFrag → Nat
  | [] => 0
  | .dot _ :: s => suffGroesse s + 1
  | .arrow _ :: s => suffGroesse s + 1
  | .idx i :: s => groesse i + suffGroesse s + 1

-- Which suffix fragments are printable (index payloads are).
def suffGut : List SuffFrag → Bool
  | [] => true
  | .dot _ :: s => suffGut s
  | .arrow _ :: s => suffGut s
  | .idx i :: s => gut i && suffGut s

-- Sizes commute with fragment application (for `omega`).
theorem groesse_applySuff : ∀ (base : SExpr) (suff : List SuffFrag),
    groesse (applySuff base suff) =
      groesse base + suffGroesse suff := by
  intro base suff
  induction suff generalizing base with
  | nil => simp only [applySuff, suffGroesse, Nat.add_zero]
  | cons f s ih =>
    cases f with
    | dot g => simp only [applySuff, ih, groesse, suffGroesse]; omega
    | arrow g => simp only [applySuff, ih, groesse, suffGroesse]; omega
    | idx i => simp only [applySuff, ih, groesse, suffGroesse]; omega
theorem applySuff_append : ∀ (base : SExpr) (s1 s2 : List SuffFrag),
    applySuff base (s1 ++ s2) =
      applySuff (applySuff base s1) s2 := by
  intro base s1
  induction s1 generalizing base with
  | nil => simp only [List.nil_append, applySuff, implies_true]
  | cons f s ih =>
    cases f with
    | dot g => simp only [List.cons_append, applySuff, ih, implies_true]
    | arrow g => simp only [List.cons_append, applySuff, ih, implies_true]
    | idx i => simp only [List.cons_append, applySuff, ih, implies_true]
theorem suffGroesse_append : ∀ (s1 s2 : List SuffFrag),
    suffGroesse (s1 ++ s2) = suffGroesse s1 + suffGroesse s2 := by
  intro s1
  induction s1 with
  | nil => simp only [List.nil_append, suffGroesse, Nat.zero_add, implies_true]
  | cons f s ih =>
    cases f with
    | dot g => simp only [List.cons_append, suffGroesse, ih]; omega
    | arrow g => simp only [List.cons_append, suffGroesse, ih]; omega
    | idx i => simp only [List.cons_append, suffGroesse, ih]; omega

-- `suffGut` splits over appends.
theorem suffGut_append : ∀ (s1 s2 : List SuffFrag),
    suffGut (s1 ++ s2) = (suffGut s1 && suffGut s2) := by
  intro s1
  induction s1 with
  | nil => simp only [List.nil_append, suffGut, Bool.true_and, implies_true]
  | cons f s ih =>
    cases f with
    | dot g => simp only [List.cons_append, suffGut, ih, implies_true]
    | arrow g => simp only [List.cons_append, suffGut, ih, implies_true]
    | idx i => simp only [List.cons_append, suffGut, ih, Bool.and_assoc, implies_true]

-- `sammleSegmente` never consumes a suffix chain (fragments start
-- with `.`, `->`, `[`, never `::`; the tail is benign).
theorem sammleSeg_suffToks : ∀ (suff : List SuffFrag) (segs : List String)
    (rest : List Token),
    ruhigSuff rest = true →
    sammleSegmente (suffToks suff ++ rest) segs =
      (segs, suffToks suff ++ rest) := by
  intro suff
  induction suff with
  | nil =>
    intro segs rest hr
    simp only [suffToks, List.nil_append] at ⊢
    exact sammleSeg_stop segs rest hr
  | cons frag suff ih =>
    cases frag with
    | dot f => intro segs rest hr; rfl
    | arrow f => intro segs rest hr; rfl
    | idx i => intro segs rest hr; rfl

-- A suffix chain followed by a benign tail never starts with `(`.
theorem suffToks_nopar : ∀ (suff : List SuffFrag) (rest R : List Token),
    ruhigSuff rest = true →
    suffToks suff ++ rest ≠ .zeichen "(" :: R := by
  intro suff
  induction suff with
  | nil =>
    intro rest R hr hcon
    simp only [suffToks, List.nil_append] at hcon
    exact ruhigSuff_nopar rest hr R hcon
  | cons frag suff ih =>
    cases frag with
    | dot f =>
      intro rest R hr hcon
      simp only [suffToks, List.cons_append] at hcon
      simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at hcon
    | arrow f =>
      intro rest R hr hcon
      simp only [suffToks, List.cons_append] at hcon
      simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at hcon
    | idx i =>
      intro rest R hr hcon
      simp only [suffToks, List.cons_append] at hcon
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.cons.injEq, Token.zeichen.injEq,
  String.reduceEq, false_and] at hcon

-- Every `gutPlatz` tree is a head variable plus fragments, with a
-- lawful head and lawful index payloads. By size induction.
theorem zerlege : ∀ (n : Nat) (p : SExpr), groesse p ≤ n →
    gutPlatz p = true →
    ∃ (a : String) (suff : List SuffFrag),
      p = applySuff (.variable a) suff ∧
      (!istKopfWort a) = true ∧
      suffGut suff = true ∧
      suffGroesse suff + 1 ≤ n := by
  intro n
  induction n with
  | zero =>
    intro p hs _
    have hp := groesse_pos p
    omega
  | succ n ih =>
    intro p hs hg
    cases p with
    | lit m => simp only [gutPlatz, Bool.false_eq_true] at hg
    | float s => simp only [gutPlatz, Bool.false_eq_true] at hg
    | tru => simp only [gutPlatz, Bool.false_eq_true] at hg
    | fls => simp only [gutPlatz, Bool.false_eq_true] at hg
    | «variable» a =>
      simp only [gutPlatz] at hg
      exact ⟨a, [], rfl, hg, rfl, by simp only [suffGroesse]; omega⟩
    | field x f =>
      simp only [gutPlatz] at hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hg
      refine ⟨a, suff ++ [.dot f], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hsg : suffGut (suff ++ [.dot f]) = suffGut suff := by
          simp only [suffGut_append, suffGut, Bool.and_true]
        rw [hsg]
        exact hgs
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        omega
    | index x i =>
      simp only [gutPlatz, Bool.and_eq_true] at hg
      obtain ⟨hpx, hi⟩ := hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hpx
      refine ⟨a, suff ++ [.idx i], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hgi : gut i = true := hi
        have hsg : suffGut (suff ++ [.idx i]) = (suffGut suff && gut i) := by
          simp only [suffGut_append, suffGut, Bool.and_true]
        rw [hsg]
        simp only [hgs, hgi, Bool.and_self]
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        simp only [groesse, groesse_applySuff] at hs
        omega
    | arrow x f =>
      simp only [gutPlatz] at hg
      have hx : groesse x ≤ n := by
        simp only [groesse] at hs
        omega
      obtain ⟨a, suff, rfl, hka, hgs, hsz⟩ := ih x hx hg
      refine ⟨a, suff ++ [.arrow f], ?_, hka, ?_, ?_⟩
      · rw [applySuff_append]
        rfl
      · have hsg : suffGut (suff ++ [.arrow f]) = suffGut suff := by
          simp only [suffGut_append, suffGut, Bool.and_true]
        rw [hsg]
        exact hgs
      · simp only [suffGroesse_append, suffGroesse] at ⊢
        omega
    | un o x => simp only [gutPlatz, Bool.false_eq_true] at hg
    | bin o l r => simp only [gutPlatz, Bool.false_eq_true] at hg
    | call f xs => simp only [gutPlatz, Bool.false_eq_true] at hg
    | fnref f => simp only [gutPlatz, Bool.false_eq_true] at hg
    | built f xs => simp only [gutPlatz, Bool.false_eq_true] at hg
    | old x => simp only [gutPlatz, Bool.false_eq_true] at hg
    | res => simp only [gutPlatz, Bool.false_eq_true] at hg
    | why g f => simp only [gutPlatz, Bool.false_eq_true] at hg
    | ext xk xn xs => simp only [gutPlatz, Bool.false_eq_true] at hg

-- Suffix chains through `parseSuffixe`, by list induction. Index
-- payloads parse via `R n` (smaller); fuel carries one spare per
-- fragment (`suff.length`) over the linear bound, so every strip
-- and every child is covered.
theorem suff_rund : ∀ (n : Nat) (Rn : R n)
    (suff : List SuffFrag) (base : SExpr) (rest : List Token) (F : Nat),
    suffGroesse suff + groesse base ≤ n + 1 →
    suffGut suff = true →
    ruhigSuff rest = true →
    12 * (suffGroesse suff + groesse base + 1) + suffGroesse suff ≤ F →
    parseSuffixe F base (suffToks suff ++ rest) =
      .ok (applySuff base suff, rest) := by
  intro n Rn suff
  induction suff with
  | nil =>
    intro base rest F hs hg hr hF
    have hF1 : 1 ≤ F := by omega
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [suffToks, List.nil_append] at ⊢
    exact stopSuffix F' base rest hr
  | cons frag suff ih =>
    cases frag with
    | dot f =>
      intro base rest F hs hg hr hF
      simp only [suffGut] at hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe, nameText_nameTok] at ⊢
      -- ⊢ : parseSuffixe F' (feld base f) (suffToks suff ++ rest) = ...
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.field base f) ≤ n + 1 := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.field base f) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.field base f) rest F' hs2 hg hr hF2
    | arrow f =>
      intro base rest F hs hg hr hF
      simp only [suffGut] at hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe, nameText_nameTok] at ⊢
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.arrow base f) ≤ n + 1 := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.arrow base f) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.arrow base f) rest F' hs2 hg hr hF2
    | idx i =>
      intro base rest F hs hg hr hF
      simp only [suffGut, Bool.and_eq_true] at hg
      obtain ⟨hi, hgs⟩ := hg
      have hF1 : 1 ≤ F := by omega
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      simp only [suffToks, List.cons_append] at ⊢
      simp only [parseSuffixe, nameText_nameTok] at ⊢
      -- ⊢ : parseOr F' (T(i) ++ ...) then `]` then recurse.
      have hii : groesse i ≤ n := by
        simp only [suffGroesse] at hs
        omega
      have hr1 : ruhig ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hr2 : ruhigSuff ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hr3 : ruhigGleit ([.zeichen "]"] ++ suffToks suff ++ rest) = true :=
        rfl
      have hFi : 12 * (groesse i + 1) + groesse i + 8 ≤ F' := by
        simp only [suffGroesse] at hs hF ⊢
        omega
      obtain ⟨hOr, -⟩ := Rn
      have hOi := hOr i ([.zeichen "]"] ++ suffToks suff ++ rest) F'
        hii hi hr1 hr2 hr3 hFi
      simp only [List.append_assoc, List.cons_append, List.nil_append] at ⊢ hOi
      simp only [hOi, List.cons_append] at ⊢
      simp only [applySuff] at ⊢
      have hs2 : suffGroesse suff + groesse (.index base i) ≤ n + 1 := by
        simp only [suffGroesse, groesse] at hs ⊢
        omega
      have hF2 : 12 * (suffGroesse suff + groesse (.index base i) + 1) +
          suffGroesse suff ≤ F' := by
        simp only [suffGroesse, groesse] at hs hF ⊢
        omega
      exact ih (SExpr.index base i) rest F' hs2 hgs hr hF2

end Gabbro.Grammatik.Parser
