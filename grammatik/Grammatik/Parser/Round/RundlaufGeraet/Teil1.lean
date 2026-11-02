/-
  File:      Grammatik/Parser/Round/RundlaufGeraet.lean
  Subject:   Layer L2c, devices: a `device` item (`druckItem (.devT n ps sp ms)`) reads back through
             `parseItemTief` -- `item_dev`.

  The printable devices (`GeraetGut`): parameters with printable types, any space name, and members
  that are `mirrors a from b;` (two printable expressions) or registers (`RegGut`): a printable
  type (a range type `u32 in 0 .. 9` among them), an address `@ e` or none, a class `class c` with
  its `in`-stage words (`in st, k in st', ...`) or none, `fields { n @ pos [class c], ... }` with
  bit positions that are numbers or names, `requires p` with an optional `else A::B`, and
  `depends { T, U.f }` with carriers of one or two segments.

  Excluded (recorded in the CUTS at the end): `bank` members (the reader keeps them as raw text and
  re-prints a reconstruction), `transition` members (their steps), register fields with a bit
  range `[hi:lo]`, a register named by nothing printable.

  The register reader is a loop over optional clauses (`parseRegRest`); the proof runs it clause by
  clause from the last to the first (`regRest_*` step lemmas), the record growing by one field per
  clause.
-/
module

public import Grammatik.Parser.Round.RundlaufItem.Teil6

@[expose] public section



namespace Gabbro.Grammatik.Parser

set_option maxRecDepth 100000

/-! ### What ends a register, carriers -/

/-- What follows a register: the next member (`reg`, `mirrors`) or the closing `}`. -/
def RegEnde (R : List Token) : Prop :=
  (∃ r, R = .zeichen "}" :: r) ∨ (∃ r, R = .wort "reg" :: r) ∨ (∃ r, R = .wort "mirrors" :: r)

theorem regRest_ende (f : Nat) (rg : SReg) (R : List Token) (hR : RegEnde R) :
    parseRegRest (f + 1) rg R = .ok (rg, R) := by
  rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · simp only [parseRegRest, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self,
  implies_true]
  · simp [parseRegRest, (by decide : strEq "reg" "class" = false), (by decide : strEq "reg" "fields" = false),
      (by decide : strEq "reg" "requires" = false), (by decide : strEq "reg" "depends" = false)]
  · simp [parseRegRest, (by decide : strEq "mirrors" "class" = false),
      (by decide : strEq "mirrors" "fields" = false), (by decide : strEq "mirrors" "requires" = false),
      (by decide : strEq "mirrors" "depends" = false)]

/-- A carrier: one or two segments. -/
def TraegerGut (c : List String) : Prop := c.length = 1 ∨ c.length = 2

/-- The print of one carrier (as `druckTraeger` prints it). -/
def traegerToks : List String → List Token
  | [a, b] => [nameTok a, .zeichen ".", nameTok b]
  | cs => druckNamen cs

theorem druckTraeger_eins (c : List String) : druckTraeger [c] = traegerToks c := by
  match c with
  | [a, b] => rfl
  | [] => rfl
  | [a] => rfl
  | a :: b :: d :: ds => rfl

theorem druckTraeger_cons (c d : List String) (cs : List (List String)) :
    druckTraeger (c :: d :: cs) = traegerToks c ++ .zeichen "," :: druckTraeger (d :: cs) := by
  match c with
  | [a, b] => simp only [druckTraeger, List.cons_append, List.nil_append, traegerToks]
  | [] => simp only [druckTraeger, List.append_assoc, List.cons_append, List.nil_append, traegerToks]
  | [a] => simp only [druckTraeger, List.append_assoc, List.cons_append, List.nil_append, traegerToks]
  | a :: b :: e :: es => simp only [druckTraeger, List.append_assoc, List.cons_append, List.nil_append, traegerToks]

/-- What follows a carrier: `,` or `}`. -/
def KommaZu (R : List Token) : Prop := (∃ r, R = .zeichen "," :: r) ∨ (∃ r, R = .zeichen "}" :: r)

theorem traeger_rund (c : List String) (hc : TraegerGut c) (R : List Token) (hR : KommaZu R) :
    parseTraeger (traegerToks c ++ R) = .ok (c, R) := by
  rcases hc with h | h
  · match c, h with
    | [a], _ =>
      rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> simp only [parseTraeger, nimmName, traegerToks, druckNamen, List.cons_append, List.nil_append,
  nameText_nameTok, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true]
  · match c, h with
    | [a, b], _ => simp only [parseTraeger, nimmName, traegerToks, List.cons_append, List.nil_append, nameText_nameTok]

theorem traeger_kopf (c : List String) (hc : TraegerGut c) (X : List Token) :
    ∃ a ts, traegerToks c ++ X = nameTok a :: ts := by
  rcases hc with h | h
  · match c, h with
    | [a], _ => exact ⟨a, X, by simp only [traegerToks, druckNamen, List.cons_append, List.nil_append]⟩
  · match c, h with
    | [a, b], _ => exact ⟨a, .zeichen "." :: nameTok b :: X, by simp only [traegerToks, List.cons_append, List.nil_append]⟩

theorem traegerFolge_rund : ∀ (cs : List (List String)) (R : List Token) (F : Nat), cs ≠ [] →
    (∀ c ∈ cs, TraegerGut c) → cs.length ≤ F →
    parseTraegerFolge F (druckTraeger cs ++ .zeichen "}" :: R) = .ok (cs, R) := by
  intro cs
  induction cs with
  | nil => intro _ _ h; exact absurd rfl h
  | cons c cs ih =>
    intro R F _ hg hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    have hc := hg c (by simp only [List.mem_cons, true_or])
    cases cs with
    | nil =>
      have hT := traeger_rund c hc (.zeichen "}" :: R) (Or.inr ⟨R, rfl⟩)
      rw [druckTraeger_eins]
      simp only [parseTraegerFolge, hT, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self,
  implies_true, fordereZeichen, strEq_self, ↓reduceIte]
    | cons d ds =>
      have hd := hg d (by simp only [List.mem_cons, true_or, or_true])
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      have hT := traeger_rund c hc (.zeichen "," :: (druckTraeger (d :: ds) ++ .zeichen "}" :: R))
        (Or.inl ⟨_, rfl⟩)
      obtain ⟨a, ts, hts⟩ : ∃ a ts, druckTraeger (d :: ds) ++ .zeichen "}" :: R = nameTok a :: ts := by
        cases ds with
        | nil => rw [druckTraeger_eins]; exact traeger_kopf d hd _
        | cons e es =>
          rw [druckTraeger_cons, List.append_assoc]; exact traeger_kopf d hd _
      rw [druckTraeger_cons, List.append_assoc]
      simp only [List.cons_append] at hT ⊢
      rw [hts] at hT hR ⊢
      unfold parseTraegerFolge
      simp only [hT, hR]
      rcases nameTok_cases a with h | h <;> rw [h] <;> rfl

theorem traegerListe_rund (cs : List (List String)) (hne : cs ≠ []) (hg : ∀ c ∈ cs, TraegerGut c)
    (R : List Token) (F : Nat) (hF : cs.length + 1 ≤ F) :
    parseTraegerListe F (.zeichen "{" :: (druckTraeger cs ++ .zeichen "}" :: R)) = .ok (cs, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hR := traegerFolge_rund cs R F' hne hg (by omega)
  obtain ⟨a, ts, hts⟩ : ∃ a ts, druckTraeger cs ++ .zeichen "}" :: R = nameTok a :: ts := by
    match cs, hne with
    | [c], _ => rw [druckTraeger_eins]; exact traeger_kopf c (hg c (by simp only [List.mem_cons, List.not_mem_nil, or_false])) _
    | c :: d :: ds, _ => rw [druckTraeger_cons, List.append_assoc]; exact traeger_kopf c (hg c (by simp only [List.mem_cons, true_or])) _
  rw [hts] at hR ⊢
  simp only [parseTraegerListe, fordereZeichen, strEq_self, ite_true]
  rcases nameTok_cases a with h | h <;> rw [h] at hR ⊢ <;> simp only [hR]

/-! ### Class stages -/

/-- The `, k in st` blocks behind the first stage; no name is `,`. -/
inductive PhRest : List String → Prop
  | nil : PhRest []
  | cons (k st : String) (ws : List String) : k ≠ "," → st ≠ "," → PhRest ws →
      PhRest ("," :: k :: "in" :: st :: ws)

/-- The `in`-stage words of a class: none, or `in st` and its blocks. -/
def PhasenGut (ws : List String) : Prop :=
  ws = [] ∨ ∃ st rest, ws = "in" :: st :: rest ∧ st ≠ "," ∧ PhRest rest

/-- A stage name prints as its name token. -/
theorem phase_name (w : String) (h : w ≠ ",") :
    (if strEq w "in" = true then [Token.wort "in"] else if strEq w "," = true then [Token.zeichen ","]
      else [nameTok w]) = [nameTok w] := by
  by_cases hi : w = "in"
  · subst hi; decide
  · simp only [strEq_ne hi, Bool.false_eq_true, ↓reduceIte, strEq_ne h]

theorem druckPhasen_block (k st : String) (ws : List String) (hk : k ≠ ",") (hs : st ≠ ",") :
    druckPhasen ("," :: k :: "in" :: st :: ws) =
      .zeichen "," :: nameTok k :: .wort "in" :: nameTok st :: druckPhasen ws := by
  simp only [druckPhasen]
  rw [phase_name k hk, phase_name st hs]
  simp [strEq_self, (by decide : strEq "," "in" = false), (by decide : strEq "in" "in" = true)]

theorem phasenRest_rund : ∀ (ws : List String), PhRest ws → ∀ (R : List Token) (F : Nat),
    (∀ r, R ≠ .zeichen "," :: r) → ws.length + 1 ≤ F →
    parsePhasenRest F (druckPhasen ws ++ R) = .ok (ws, R) := by
  intro ws h
  induction h with
  | nil =>
    intro R F hR hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_nil, Nat.zero_add] at hF; omega⟩
    simp only [druckPhasen, List.nil_append]
    cases R with
    | nil => simp only [parsePhasenRest]
    | cons t r =>
      cases t with
      | zeichen z =>
        have hz : z ≠ "," := fun e => hR r (by rw [e])
        simp only [parsePhasenRest]
      | _ => simp only [parsePhasenRest]
  | cons k st ws hk hs _ ih =>
    intro R F hR hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    rw [druckPhasen_block k st ws hk hs]
    have hW := ih R F' hR (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF; omega)
    simp only [List.cons_append, parsePhasenRest, nimmName, nameText_nameTok, nimmWort, strEq_self, ↓reduceIte,
  hW]

/-- What follows the stages of a class: no `in`, no `,`. -/
def PhFolge (R : List Token) : Prop := (∀ r, R ≠ .wort "in" :: r) ∧ (∀ r, R ≠ .zeichen "," :: r)

theorem phasen_rund (ws : List String) (h : PhasenGut ws) (R : List Token) (hR : PhFolge R) (F : Nat)
    (hF : ws.length + 2 ≤ F) : parsePhasen F (druckPhasen ws ++ R) = .ok (ws, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  rcases h with rfl | ⟨st, rest, rfl, hs, hr⟩
  · simp only [druckPhasen, List.nil_append]
    cases R with
    | nil => simp only [parsePhasen]
    | cons t r =>
      cases t with
      | wort w =>
        have hw : w ≠ "in" := fun e => hR.1 r (by rw [e])
        simp only [parsePhasen, strEq_ne hw, Bool.false_eq_true, ↓reduceIte]
      | _ => simp only [parsePhasen]
  · have hd : druckPhasen ("in" :: st :: rest) = .wort "in" :: nameTok st :: druckPhasen rest := by
      simp only [druckPhasen]; rw [phase_name st hs]; simp only [strEq_self, ↓reduceIte, List.cons_append, List.nil_append]
    rw [hd]
    have hW := phasenRest_rund rest hr R F' hR.2 (by simp only [List.length_cons, Nat.reduceLeDiff] at hF; omega)
    simp only [parsePhasen, List.cons_append, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hW]


end Gabbro.Grammatik.Parser
