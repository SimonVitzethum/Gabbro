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
  simp only [parseKopf, nameText_nameTok, sammleSeg_paren, rufKopf,
    strEq_paren_doppelpunkt, strEq_paren_paren, Bool.false_eq_true, ↓reduceIte] <;> rfl
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


end Gabbro.Grammatik.Parser
