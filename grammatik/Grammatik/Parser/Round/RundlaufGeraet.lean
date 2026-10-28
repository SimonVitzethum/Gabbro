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
import Grammatik.Parser.Round.RundlaufItem

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

/-! ### Register fields -/

/-- A printable register field: its bit position is a number or a name. -/
def RegFeldGut (f : SRegFeld) : Prop := PosGut f.pos

theorem regFeld_rund (fd : SRegFeld) (hf : RegFeldGut fd) (R : List Token) (hR : KommaZu R) (F : Nat) :
    parseRegFeld (F + 1) (druckRegFeld fd ++ R) = .ok (fd, R) := by
  obtain ⟨n, p, k⟩ := fd
  cases k with
  | none =>
    have hB := bitpos_rund p hf R
    rcases hR with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;>
      simp only [druckRegFeld, List.append_nil, List.cons_append, List.nil_append, List.append_assoc] at hB ⊢ <;>
      simp only [parseRegFeld, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hB]
  | some c =>
    have hB := bitpos_rund p hf (.wort "class" :: nameTok c :: R)
    simp only [druckRegFeld, List.cons_append, List.nil_append, List.append_assoc] at hB ⊢
    simp only [parseRegFeld, nimmName, nameText_nameTok, fordereZeichen, strEq_self, ↓reduceIte, hB]

theorem regFeld_kopf (fd : SRegFeld) (X : List Token) : ∃ ts, druckRegFeld fd ++ X = nameTok fd.name :: ts :=
  ⟨_, by simp only [druckRegFeld, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, true_and]; rfl⟩

theorem regFelder_rund : ∀ (fs : List SRegFeld) (R : List Token) (F : Nat), fs ≠ [] →
    (∀ fd ∈ fs, RegFeldGut fd) → fs.length + 1 ≤ F →
    parseRegFeldFolge F (druckRegFelder fs ++ .zeichen "}" :: R) = .ok (fs, R) := by
  intro fs
  induction fs with
  | nil => intro _ _ h; exact absurd rfl h
  | cons fd fs ih =>
    intro R F _ hg hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_cons] at hF; omega⟩
    have hfd := hg fd (by simp only [List.mem_cons, true_or])
    cases fs with
    | nil =>
      obtain ⟨G, rfl⟩ : ∃ G, F' = G + 1 := ⟨F' - 1, by simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff] at hF; omega⟩
      have hP := regFeld_rund fd hfd (.zeichen "}" :: R) (Or.inr ⟨R, rfl⟩) G
      simp only [druckRegFelder]
      simp only [parseRegFeldFolge, hP, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self,
  implies_true, fordereZeichen, strEq_self, ↓reduceIte]
    | cons fd2 fs2 =>
      have hR := ih R F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF ⊢; omega)
      obtain ⟨G, rfl⟩ : ∃ G, F' = G + 1 := ⟨F' - 1, by simp only [List.length_cons, Nat.add_le_add_iff_right] at hF; omega⟩
      have hd : druckRegFelder (fd :: fd2 :: fs2) = druckRegFeld fd ++ .zeichen "," :: druckRegFelder (fd2 :: fs2) := by
        simp only [druckRegFelder, List.append_assoc, List.cons_append, List.nil_append]
      rw [hd, List.append_assoc]
      have hP := regFeld_rund fd hfd (.zeichen "," :: (druckRegFelder (fd2 :: fs2) ++ .zeichen "}" :: R))
        (Or.inl ⟨_, rfl⟩) G
      obtain ⟨ts, hts⟩ : ∃ ts, druckRegFelder (fd2 :: fs2) ++ .zeichen "}" :: R = nameTok fd2.name :: ts := by
        cases fs2 with
        | nil => simpa [druckRegFelder] using regFeld_kopf fd2 (.zeichen "}" :: R)
        | cons x xs =>
          obtain ⟨ts, h⟩ := regFeld_kopf fd2 (.zeichen "," :: (druckRegFelder (x :: xs) ++ .zeichen "}" :: R))
          exact ⟨ts, by simp only [druckRegFelder, List.append_assoc, List.cons_append, List.nil_append] at h ⊢; exact h⟩
      simp only [List.cons_append] at hP ⊢
      rw [hts] at hP hR ⊢
      unfold parseRegFeldFolge
      simp only [hP, hR]
      rcases nameTok_cases fd2.name with h | h <;> rw [h] <;> rfl

theorem regFeldListe_rund (fs : List SRegFeld) (hne : fs ≠ []) (hg : ∀ fd ∈ fs, RegFeldGut fd)
    (R : List Token) (F : Nat) (hF : fs.length + 2 ≤ F) :
    parseRegFeldListe F (.zeichen "{" :: (druckRegFelder fs ++ .zeichen "}" :: R)) = .ok (fs, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hR := regFelder_rund fs R F' hne hg (by omega)
  obtain ⟨a, ts, hts⟩ : ∃ a ts, druckRegFelder fs ++ .zeichen "}" :: R = nameTok a :: ts := by
    match fs, hne with
    | [fd], _ => exact ⟨fd.name, _, by simpa [druckRegFelder] using (regFeld_kopf fd _).choose_spec⟩
    | fd :: fd2 :: fs2, _ =>
      obtain ⟨ts, h⟩ := regFeld_kopf fd (.zeichen "," :: (druckRegFelder (fd2 :: fs2) ++ .zeichen "}" :: R))
      exact ⟨fd.name, ts, by simp only [druckRegFelder, List.append_assoc, List.cons_append, List.nil_append] at h ⊢; exact h⟩
  rw [hts] at hR ⊢
  simp only [parseRegFeldListe, fordereZeichen, strEq_self, ite_true]
  rcases nameTok_cases a with h | h <;> rw [h] at hR ⊢ <;> simp only [hR]

/-! ### The clauses of a register -/

/-- The words that open a register clause or the next member. -/
def regWort (w : String) : Bool :=
  strEq w "class" || strEq w "fields" || strEq w "requires" || strEq w "depends" || strEq w "reg" ||
    strEq w "mirrors"

/-- What may follow a register clause: `}`, `@`, or a clause or member word. -/
def RegNach (X : List Token) : Prop :=
  (∃ r, X = .zeichen "}" :: r) ∨ (∃ r, X = .zeichen "@" :: r) ∨ (∃ w r, X = .wort w :: r ∧ regWort w = true)

theorem regNach_ende (R : List Token) (h : RegEnde R) : RegNach R := by
  rcases h with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exact Or.inl ⟨r, rfl⟩
  · exact Or.inr (Or.inr ⟨"reg", r, rfl, by decide⟩)
  · exact Or.inr (Or.inr ⟨"mirrors", r, rfl, by decide⟩)

/-- Everything a register clause's follow has to be. -/
structure RegFolge (X : List Token) : Prop where
  typ : TypFolge X
  pred : PredFolge X
  ph : PhFolge X
  sonst : ∀ r, X ≠ .wort "else" :: r
  dd : ∀ r, X ≠ .zeichen "::" :: r

theorem regNach_folge (X : List Token) (h : RegNach X) : RegFolge X := by
  rcases h with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨w, r, rfl, hw⟩
  · exact ⟨⟨by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩, ⟨by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true]⟩, by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true]⟩
  · exact ⟨⟨by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], rfl, rfl, rfl⟩,
      ⟨rfl, rfl, rfl, by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩, ⟨by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true]⟩, by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true]⟩
  · simp only [regWort, Bool.or_eq_true, strEq_eq] at hw
    rcases hw with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) <;>
      exact ⟨⟨by simp only [ne_eq, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], rfl, rfl, by simp only [ruhigGleit]; decide⟩,
        ⟨rfl, rfl, by simp only [ruhigGleit]; decide, by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true]⟩, ⟨by simp only [ne_eq, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩, by simp only [ne_eq, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true],
        by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true]⟩

/-- The pieces of a register's print (Print/Item.lean), by short names. -/
abbrev addrT := druckRegAdresse
abbrev klasseT := druckRegKlasse
abbrev felderT := druckRegFelderTeil
abbrev reqT := druckRegVoraus
abbrev depT := druckRegAbhaengt

/-- Everything behind the type of a register. -/
def regTail (r : SReg) : List Token :=
  addrT r.addr ++ klasseT r.klasse r.stage ++ felderT r.felder ++ reqT r.voraus r.elseF ++ depT r.abhaengt

theorem druckReg_eq (r : SReg) :
    druckReg r = [.wort "reg", nameTok r.name, .zeichen ":"] ++ druckTyp r.rtyp ++ regTail r := by
  simp only [druckReg, List.cons_append, List.nil_append, List.append_assoc, regTail]

theorem regNach_dep (cs : List (List String)) (X : List Token) (h : RegNach X) : RegNach (depT cs ++ X) := by
  cases cs with
  | nil => simpa [depT, druckRegAbhaengt] using h
  | cons c cs => exact Or.inr (Or.inr ⟨"depends", (depT (c :: cs) ++ X).tail, by simp only [depT, druckRegAbhaengt, List.cons_append, List.nil_append, List.append_assoc, List.tail_cons], by decide⟩)

theorem regNach_req (v : Option SExpr) (e : Option (String × String)) (X : List Token) (h : RegNach X) :
    RegNach (reqT v e ++ X) := by
  cases v with
  | none => simpa [reqT, druckRegVoraus] using h
  | some p =>
    cases e with
    | none => exact Or.inr (Or.inr ⟨"requires", (reqT (some p) none ++ X).tail, by simp only [reqT, druckRegVoraus, List.cons_append, List.nil_append, List.tail_cons], by decide⟩)
    | some ab =>
      obtain ⟨x, y⟩ := ab
      exact Or.inr (Or.inr ⟨"requires", (reqT (some p) (some (x, y)) ++ X).tail, by simp only [reqT, druckRegVoraus, List.cons_append, List.nil_append, List.append_assoc, List.tail_cons], by decide⟩)

theorem regNach_felder (fs : List SRegFeld) (X : List Token) (h : RegNach X) : RegNach (felderT fs ++ X) := by
  cases fs with
  | nil => simpa [felderT, druckRegFelderTeil] using h
  | cons f fs => exact Or.inr (Or.inr ⟨"fields", (felderT (f :: fs) ++ X).tail, by simp only [felderT, druckRegFelderTeil, List.cons_append, List.nil_append, List.append_assoc, List.tail_cons], by decide⟩)

theorem regNach_klasse (k : String) (st : List String) (X : List Token) (h : RegNach X) :
    RegNach (klasseT k st ++ X) := by
  unfold klasseT druckRegKlasse
  split
  · simpa using h
  · exact Or.inr (Or.inr ⟨"class", nameTok k :: (druckPhasen st ++ X), by simp only [List.cons_append, List.nil_append], by decide⟩)

theorem regNach_addr (a : SExpr) (X : List Token) (h : RegNach X) : RegNach (addrT a ++ X) := by
  unfold addrT druckRegAdresse
  split
  · simpa using h
  · exact Or.inr (Or.inl ⟨druckToks a ++ X, by simp only [List.cons_append, List.nil_append]⟩)

/-! ### One clause of a register at a time -/

theorem regRest_at (f : Nat) (rg : SReg) (e : SExpr) (R : List Token) (X)
    (hE : parseOr f (druckToks e ++ R) = .ok (e, R)) (hN : parseRegRest f { rg with addr := e } R = X) :
    parseRegRest (f + 1) rg (.zeichen "@" :: (druckToks e ++ R)) = X := by
  simp only [parseRegRest, hE, hN]

theorem regRest_class (f : Nat) (rg : SReg) (c : String) (st : List String) (R : List Token) (X)
    (hP : parsePhasen f (druckPhasen st ++ R) = .ok (st, R))
    (hN : parseRegRest f { rg with klasse := c, stage := st } R = X) :
    parseRegRest (f + 1) rg (.wort "class" :: nameTok c :: (druckPhasen st ++ R)) = X := by
  simp only [parseRegRest, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hP, hN]

theorem regRest_fields (f : Nat) (rg : SReg) (fs : List SRegFeld) (R : List Token) (X)
    (hL : parseRegFeldListe f (.zeichen "{" :: (druckRegFelder fs ++ .zeichen "}" :: R)) = .ok (fs, R))
    (hN : parseRegRest f { rg with felder := fs } R = X) :
    parseRegRest (f + 1) rg (.wort "fields" :: .zeichen "{" :: (druckRegFelder fs ++ .zeichen "}" :: R)) = X := by
  simp [parseRegRest, (by decide : strEq "fields" "class" = false), strEq_self, hL, hN]

theorem regRest_req (f : Nat) (rg : SReg) (p : SExpr) (R : List Token) (X)
    (hP : parsePred f (druckToks p ++ R) = .ok (p, R)) (hR : ∀ r, R ≠ .wort "else" :: r)
    (hN : parseRegRest f { rg with voraus := some p } R = X) :
    parseRegRest (f + 1) rg (.wort "requires" :: (druckToks p ++ R)) = X := by
  simp only [parseRegRest, (by decide : strEq "requires" "class" = false),
    (by decide : strEq "requires" "fields" = false), strEq_self, Bool.false_eq_true, ite_false, ite_true, hP]
  cases R with
  | nil => exact hN
  | cons t r =>
    cases t with
    | wort w =>
      have hw : w ≠ "else" := fun e => hR r (by rw [e])
      simp only [strEq_ne hw, Bool.false_eq_true, ↓reduceIte, hN]
    | _ => exact hN

theorem regRest_reqElse (f : Nat) (rg : SReg) (p : SExpr) (a b : String) (R : List Token) (X)
    (hP : parsePred f (druckToks p ++ (.wort "else" :: nameTok a :: .zeichen "::" :: nameTok b :: R)) =
      .ok (p, .wort "else" :: nameTok a :: .zeichen "::" :: nameTok b :: R))
    (hR : ∀ r, R ≠ .zeichen "::" :: r)
    (hN : parseRegRest f { rg with voraus := some p, elseF := some (a, b) } R = X) :
    parseRegRest (f + 1) rg (.wort "requires" :: (druckToks p ++
      (.wort "else" :: nameTok a :: .zeichen "::" :: nameTok b :: R))) = X := by
  have hPf := nimmPfad_pfad [a, b] R (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hR
  simp only [pfadToks, List.cons_append, List.nil_append] at hPf
  simp [parseRegRest, (by decide : strEq "requires" "class" = false),
    (by decide : strEq "requires" "fields" = false), strEq_self, hP, hPf, hN]

theorem regRest_dep (f : Nat) (rg : SReg) (cs : List (List String)) (R : List Token) (X)
    (hL : parseTraegerListe f (.zeichen "{" :: (druckTraeger cs ++ .zeichen "}" :: R)) = .ok (cs, R))
    (hN : parseRegRest f { rg with abhaengt := cs } R = X) :
    parseRegRest (f + 1) rg (.wort "depends" :: .zeichen "{" :: (druckTraeger cs ++ .zeichen "}" :: R)) = X := by
  simp [parseRegRest, (by decide : strEq "depends" "class" = false), (by decide : strEq "depends" "fields" = false),
    (by decide : strEq "depends" "requires" = false), strEq_self, hL, hN]

/-! ### A register, clause by clause from the last -/

/-- A printable register (see the header). -/
structure RegGut (r : SReg) : Prop where
  typ : TypGut r.rtyp
  addr : r.addr ≠ .variable "" → gut r.addr = true
  klasse : r.klasse = "" → r.stage = []
  stage : PhasenGut r.stage
  felder : ∀ fd ∈ r.felder, RegFeldGut fd
  voraus : ∀ p, r.voraus = some p → PredGut p
  sonst : r.voraus = none → r.elseF = none
  traeger : ∀ c ∈ r.abhaengt, TraegerGut c

theorem druckPhasen_len (st : List String) : (druckPhasen st).length = st.length := by
  induction st with
  | nil => rfl
  | cons w ws ih => simp only [druckPhasen]; split <;> (try split) <;> simp only [List.cons_append, List.nil_append, List.length_cons, ih, Nat.add_left_cancel_iff]

theorem druckRegFelder_len : ∀ (fs : List SRegFeld), fs.length ≤ (druckRegFelder fs).length := by
  intro fs
  induction fs with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons f fs ih =>
    cases fs with
    | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckRegFelder, druckRegFeld, List.cons_append,
  List.nil_append, List.length_append, Nat.le_add_left]
    | cons g gs => simp only [List.length_cons, druckRegFelder, List.append_assoc, List.cons_append, List.nil_append,
  List.length_append] at ih ⊢; omega

theorem druckTraeger_len : ∀ (cs : List (List String)), (∀ c ∈ cs, TraegerGut c) →
    cs.length ≤ (druckTraeger cs).length := by
  intro cs
  induction cs with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true, List.length_nil, Nat.zero_le, imp_self]
  | cons c cs ih =>
    intro hg
    have hc : 1 ≤ (traegerToks c).length := by
      rcases hg c (by simp only [List.mem_cons, true_or]) with h | h
      · match c, h with
        | [a], _ => simp only [traegerToks, druckNamen, List.length_cons, List.length_nil, Nat.zero_add, Std.le_refl]
      · match c, h with
        | [a, b], _ => simp only [traegerToks, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff]
    have := ih (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    cases cs with
    | nil => rw [druckTraeger_eins]; simpa using hc
    | cons d ds => rw [druckTraeger_cons]; simp only [List.length_cons, List.length_append, ge_iff_le] at this ⊢; omega

theorem dep_rund (cs : List (List String)) (hcs : ∀ c ∈ cs, TraegerGut c) (n : String) (t : STyp)
    (a : SExpr) (k : String) (st : List String) (fs : List SRegFeld) (v : Option SExpr)
    (e : Option (String × String)) (R : List Token) (hR : RegEnde R) (F : Nat)
    (hF : 8 * (depT cs).length + 40 ≤ F) :
    parseRegRest F ⟨n, t, a, k, st, fs, v, e, []⟩ (depT cs ++ R) = .ok (⟨n, t, a, k, st, fs, v, e, cs⟩, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases cs with
  | nil => simpa [depT, druckRegAbhaengt] using regRest_ende F' _ R hR
  | cons c cs' =>
    have hl := druckTraeger_len (c :: cs') hcs
    simp only [depT, druckRegAbhaengt, List.length_append, List.length_cons, List.length_nil] at hF
    obtain ⟨G, rfl⟩ : ∃ G, F' = G + 1 := ⟨F' - 1, by omega⟩
    simp only [depT, druckRegAbhaengt, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append]
    exact regRest_dep _ _ _ _ _ (traegerListe_rund _ (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hcs R _ (by omega)) (regRest_ende _ _ R hR)

theorem req_rund (v : Option SExpr) (e : Option (String × String)) (hv : ∀ p, v = some p → PredGut p)
    (he : v = none → e = none) (cs : List (List String)) (hcs : ∀ c ∈ cs, TraegerGut c) (n : String)
    (t : STyp) (a : SExpr) (k : String) (st : List String) (fs : List SRegFeld) (R : List Token)
    (hR : RegEnde R) (F : Nat) (hF : 8 * (reqT v e ++ depT cs).length + 40 ≤ F) :
    parseRegRest F ⟨n, t, a, k, st, fs, none, none, []⟩ (reqT v e ++ (depT cs ++ R)) =
      .ok (⟨n, t, a, k, st, fs, v, e, cs⟩, R) := by
  have hD := regNach_folge _ (regNach_dep cs R (regNach_ende R hR))
  cases v with
  | none =>
    rw [he rfl]
    simp only [reqT, druckRegVoraus, List.nil_append] at hF ⊢
    exact dep_rund cs hcs n t a k st fs none none R hR F hF
  | some p =>
    have hp := hv p rfl
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.length_append] at hF; omega⟩
    cases e with
    | none =>
      simp only [reqT, druckRegVoraus, List.length_append, List.length_cons, List.length_nil] at hF
      simp only [reqT, druckRegVoraus, List.cons_append, List.nil_append, List.append_assoc,
        List.singleton_append]
      exact regRest_req _ _ p _ _ (pred_voll p hp _ hD.pred F' (by simp only [bP]; omega)) hD.sonst
        (dep_rund cs hcs n t a k st fs (some p) none R hR F' (by omega))
    | some ab =>
      obtain ⟨x, y⟩ := ab
      simp only [reqT, druckRegVoraus, List.length_append, List.length_cons, List.length_nil] at hF
      simp only [reqT, druckRegVoraus, List.cons_append, List.nil_append, List.append_assoc,
        List.singleton_append]
      have hE : PredFolge (.wort "else" :: nameTok x :: .zeichen "::" :: nameTok y :: (depT cs ++ R)) :=
        ⟨rfl, rfl, by simp only [ruhigGleit]; decide, by simp only [ne_eq, List.cons.injEq, reduceCtorEq, false_and, not_false_eq_true, implies_true], by simp only [ne_eq, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true], by simp only [ne_eq, List.cons.injEq, Token.wort.injEq, String.reduceEq, false_and, not_false_eq_true,
  implies_true]⟩
      exact regRest_reqElse _ _ p x y _ _ (pred_voll p hp _ hE F' (by simp only [bP]; omega)) hD.dd
        (dep_rund cs hcs n t a k st fs (some p) (some (x, y)) R hR F' (by omega))

theorem fel_rund (fs : List SRegFeld) (hfs : ∀ fd ∈ fs, RegFeldGut fd) (v : Option SExpr)
    (e : Option (String × String)) (hv : ∀ p, v = some p → PredGut p) (he : v = none → e = none)
    (cs : List (List String)) (hcs : ∀ c ∈ cs, TraegerGut c) (n : String) (t : STyp) (a : SExpr)
    (k : String) (st : List String) (R : List Token) (hR : RegEnde R) (F : Nat)
    (hF : 8 * (felderT fs ++ reqT v e ++ depT cs).length + 40 ≤ F) :
    parseRegRest F ⟨n, t, a, k, st, [], none, none, []⟩ (felderT fs ++ (reqT v e ++ (depT cs ++ R))) =
      .ok (⟨n, t, a, k, st, fs, v, e, cs⟩, R) := by
  cases fs with
  | nil =>
    simp only [felderT, druckRegFelderTeil, List.nil_append] at hF ⊢
    exact req_rund v e hv he cs hcs n t a k st [] R hR F (by simpa using hF)
  | cons f fs' =>
    have hl := druckRegFelder_len (f :: fs')
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.append_assoc, List.length_append] at hF; omega⟩
    simp only [felderT, druckRegFelderTeil, List.length_append, List.length_cons, List.length_nil] at hF
    simp only [felderT, druckRegFelderTeil, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append]
    exact regRest_fields _ _ _ _ _ (regFeldListe_rund _ (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hfs _ F' (by simp only [List.length_cons] at hl ⊢; omega))
      (req_rund v e hv he cs hcs n t a k st (f :: fs') R hR F' (by simp only [List.length_append]; omega))

theorem kl_rund (k : String) (st : List String) (hk : k = "" → st = []) (hst : PhasenGut st)
    (fs : List SRegFeld) (hfs : ∀ fd ∈ fs, RegFeldGut fd) (v : Option SExpr)
    (e : Option (String × String)) (hv : ∀ p, v = some p → PredGut p) (he : v = none → e = none)
    (cs : List (List String)) (hcs : ∀ c ∈ cs, TraegerGut c) (n : String) (t : STyp) (a : SExpr)
    (R : List Token) (hR : RegEnde R) (F : Nat)
    (hF : 8 * (klasseT k st ++ felderT fs ++ reqT v e ++ depT cs).length + 40 ≤ F) :
    parseRegRest F ⟨n, t, a, "", [], [], none, none, []⟩
      (klasseT k st ++ (felderT fs ++ (reqT v e ++ (depT cs ++ R)))) =
      .ok (⟨n, t, a, k, st, fs, v, e, cs⟩, R) := by
  by_cases hk0 : k = ""
  · subst hk0
    rw [hk rfl]
    simp only [klasseT, druckRegKlasse, strEq_self, ite_true, List.nil_append] at hF ⊢
    exact fel_rund fs hfs v e hv he cs hcs n t a "" [] R hR F (by simpa using hF)
  · have hs : strEq k "" = false := strEq_ne hk0
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.append_assoc, List.length_append] at hF; omega⟩
    simp only [klasseT, druckRegKlasse, hs, Bool.false_eq_true, ite_false, List.length_append,
      List.length_cons, List.length_nil, druckPhasen_len] at hF
    simp only [klasseT, druckRegKlasse, hs, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append,
      List.append_assoc, List.singleton_append]
    have hX := regNach_folge _ (regNach_felder fs _ (regNach_req v e _ (regNach_dep cs R (regNach_ende R hR))))
    exact regRest_class _ _ k st _ _ (phasen_rund st hst _ hX.ph F' (by omega))
      (fel_rund fs hfs v e hv he cs hcs n t a k st R hR F' (by simp only [List.append_assoc, List.length_append]; omega))

theorem ad_rund (r : SReg) (hr : RegGut r) (R : List Token) (hR : RegEnde R) (F : Nat)
    (hF : 8 * (regTail r).length + 40 ≤ F) :
    parseRegRest F ⟨r.name, r.rtyp, .variable "", "", [], [], none, none, []⟩ (regTail r ++ R) = .ok (r, R) := by
  obtain ⟨n, t, a, k, st, fs, v, e, cs⟩ := r
  obtain ⟨-, ha, hk, hst, hfs, hv, he, hcs⟩ := hr
  simp only at ha hk hst hfs hv he hcs ⊢
  simp only [regTail, List.append_assoc] at hF ⊢
  by_cases ha0 : a = .variable ""
  · subst ha0
    simp only [addrT, druckRegAdresse, List.nil_append] at hF ⊢
    exact kl_rund k st hk hst fs hfs v e hv he cs hcs n t _ R hR F (by simpa [List.append_assoc] using hF)
  · have hd : addrT a = .zeichen "@" :: druckToks a := by
      unfold addrT druckRegAdresse; split
      · exact absurd rfl ha0
      · rfl
    rw [hd] at hF ⊢
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [List.cons_append, List.length_cons, List.length_append] at hF; omega⟩
    simp only [List.length_append, List.length_cons] at hF
    simp only [List.cons_append]
    have hX := regNach_folge _ (regNach_klasse k st _ (regNach_felder fs _ (regNach_req v e _
      (regNach_dep cs R (regNach_ende R hR)))))
    obtain ⟨h1, h2, h3⟩ := typFolge_ruhig hX.typ
    exact regRest_at _ _ a _ _ (ausdruck a (ha ha0) _ F' h1 h2 h3 (by omega))
      (kl_rund k st hk hst fs hfs v e hv he cs hcs n t a R hR F' (by simp only [List.append_assoc, List.length_append]; omega))

/-- **A register reads back** before the next member or `}`. -/
theorem reg_rund (r : SReg) (hr : RegGut r) (R : List Token) (hR : RegEnde R) (F : Nat)
    (hF : 8 * (druckReg r).length + 40 ≤ F) : parseReg F (druckReg r ++ R) = .ok (r, R) := by
  rw [druckReg_eq] at hF ⊢
  simp only [List.length_append, List.length_cons, List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hX := regNach_folge _ (regNach_addr r.addr _ (regNach_klasse r.klasse r.stage _
    (regNach_felder r.felder _ (regNach_req r.voraus r.elseF _ (regNach_dep r.abhaengt R (regNach_ende R hR))))))
  have hT := parse_druckTyp r.rtyp hr.typ (regTail r ++ R) F'
    (by simpa [regTail, List.append_assoc] using hX.typ) (by simp only [fbT]; omega)
  have hA := ad_rund r hr R hR F' (by omega)
  simp only [List.cons_append, List.nil_append, List.append_assoc] at hT ⊢
  simp only [parseReg, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, fordereZeichen, hT, hA]

/-! ### Members and the device -/

/-- A printable member: `mirrors a from b;` over printable expressions, or a printable register. -/
def GerGut : SGerTeil → Prop
  | .copy a b => gut a = true ∧ gut b = true
  | .reg r => RegGut r
  | _ => False

theorem gerTeile_kopf (ms : List SGerTeil) (hms : ∀ m ∈ ms, GerGut m) (R : List Token) :
    RegEnde (druckGerTeile ms ++ .zeichen "}" :: R) := by
  cases ms with
  | nil => exact Or.inl ⟨R, rfl⟩
  | cons m ms =>
    have hm := hms m (by simp only [List.mem_cons, true_or])
    cases m with
    | copy a b =>
      exact Or.inr (Or.inr ⟨(druckGerTeile (.copy a b :: ms) ++ .zeichen "}" :: R).tail,
        by simp only [druckGerTeile, druckGerTeil, List.cons_append, List.nil_append, List.append_assoc, List.tail_cons]⟩)
    | reg r =>
      exact Or.inr (Or.inl ⟨(druckGerTeile (.reg r :: ms) ++ .zeichen "}" :: R).tail,
        by simp only [druckGerTeile, druckGerTeil, druckReg, List.cons_append, List.nil_append, List.append_assoc,
  List.tail_cons]⟩)
    | bank _ => exact absurd hm id
    | trans _ => exact absurd hm id

theorem gerTeile_rund : ∀ (ms : List SGerTeil), (∀ m ∈ ms, GerGut m) → ∀ (R : List Token) (F : Nat),
    8 * (druckGerTeile ms).length + 41 ≤ F →
    parseGerTeile F (druckGerTeile ms ++ .zeichen "}" :: R) = .ok (ms, .zeichen "}" :: R) := by
  intro ms
  induction ms with
  | nil =>
    intro _ R F hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseGerTeile, druckGerTeile, List.nil_append]
  | cons m ms ih =>
    intro hms R F hF
    have hm := hms m (by simp only [List.mem_cons, true_or])
    have hrest := ih (fun x hx => hms x (List.mem_cons_of_mem _ hx)) R
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    cases m with
    | copy a b =>
      obtain ⟨ha, hb⟩ := hm
      simp only [druckGerTeile, druckGerTeil, List.length_append, List.length_cons, List.length_nil] at hF
      have hB := ausdruck b hb (.zeichen ";" :: (druckGerTeile ms ++ .zeichen "}" :: R)) F' rfl rfl rfl (by omega)
      have hA := ausdruck a ha (.wort "from" :: (druckToks b ++ .zeichen ";" ::
        (druckGerTeile ms ++ .zeichen "}" :: R))) F' rfl rfl rfl (by omega)
      have hM := hrest F' (by omega)
      simp only [druckGerTeile, druckGerTeil, List.cons_append, List.nil_append, List.append_assoc,
        List.singleton_append]
      simp only [parseGerTeile, strEq_self, ↓reduceIte, hA, nimmWort, hB, fordereZeichen, hM]
    | reg r =>
      simp only [druckGerTeile, druckGerTeil, List.length_append] at hF
      have h1 : 1 ≤ (druckReg r).length := by rw [druckReg_eq]; simp only [List.cons_append, List.nil_append, List.length_cons, List.length_append, Nat.le_add_left]
      have hReg := reg_rund r hm (druckGerTeile ms ++ .zeichen "}" :: R)
        (gerTeile_kopf ms (fun x hx => hms x (List.mem_cons_of_mem _ hx)) R) F' (by omega)
      have hM := hrest F' (by omega)
      have hd : druckReg r = .wort "reg" :: (druckReg r).tail := by rw [druckReg_eq]; rfl
      simp only [druckGerTeile, druckGerTeil, List.append_assoc]
      rw [hd] at hReg ⊢
      simp only [List.cons_append] at hReg ⊢
      simp [parseGerTeile, (by decide : strEq "reg" "mirrors" = false), strEq_self, hReg, hM]
    | bank _ => exact absurd hm id
    | trans _ => exact absurd hm id

/-- A printable device: printable parameter types and members. -/
def GeraetGut (ps : List (String × STyp)) (ms : List SGerTeil) : Prop :=
  (∀ p ∈ ps, TypGut p.2) ∧ ∀ m ∈ ms, GerGut m

/-- The parameters of a device as printed: none, or in parentheses. -/
def devParamT : List (String × STyp) → List Token
  | [] => []
  | ps => [.zeichen "("] ++ druckParams ps ++ [.zeichen ")"]

theorem druckDev_eq (n : String) (ps : List (String × STyp)) (sp : String) (ms : List SGerTeil) :
    druckItem (.devT n ps sp ms) = [.wort "device", nameTok n] ++ devParamT ps ++
      [.wort "at", nameTok sp, .zeichen "{"] ++ druckGerTeile ms ++ [.zeichen "}"] := by
  cases ps <;> rfl

theorem geraetNach_rund (f : Nat) (n : String) (ps : List (String × STyp)) (sp : String) (ms : List SGerTeil)
    (hms : ∀ m ∈ ms, GerGut m) (R : List Token) (hF : 8 * (druckGerTeile ms).length + 41 ≤ f) :
    parseGeraetNach (f + 1) n ps (.wort "at" :: nameTok sp :: .zeichen "{" ::
      (druckGerTeile ms ++ .zeichen "}" :: R)) = .ok (.devT n ps sp ms, R) := by
  have hG := gerTeile_rund ms hms R f hF
  simp only [parseGeraetNach, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, fordereZeichen, hG]

/-- **A device reads back** through the item reader. -/
theorem item_dev (n : String) (ps : List (String × STyp)) (sp : String) (ms : List SGerTeil)
    (h : GeraetGut ps ms) : ItemBein (.devT n ps sp ms) := by
  intro rest F hF
  obtain ⟨hps, hms⟩ := h
  simp only [fbI, druckDev_eq, List.length_append, List.length_cons, List.length_nil] at hF
  rw [druckDev_eq]
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 4 := ⟨F - 4, by omega⟩
  cases ps with
  | nil =>
    simp only [devParamT, List.length_nil] at hF
    simp only [devParamT, List.append_nil, List.cons_append, List.nil_append, List.append_assoc,
      List.singleton_append]
    rw [parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_device]
    simp only [parseGeraetTief, nimmWort, strEq_self, ite_true, nimmName_nameTok]
    rw [show F' + 1 = F' + 1 from rfl, geraetNach_rund F' n [] sp ms hms rest (by omega)]
  | cons p ps' =>
    simp only [devParamT, List.length_append, List.length_cons, List.length_nil] at hF
    have hP := params_rund (p :: ps') hps (.wort "at" :: nameTok sp :: .zeichen "{" ::
      (druckGerTeile ms ++ .zeichen "}" :: rest)) (F' + 1) (by omega)
    simp only [devParamT, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
      at hP ⊢
    rw [parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_device]
    simp only [parseGeraetTief, nimmWort, strEq_self, ite_true, nimmName_nameTok, hP]
    rw [geraetNach_rund F' n (p :: ps') sp ms hms rest (by omega)]

end Gabbro.Grammatik.Parser

#print axioms Gabbro.Grammatik.Parser.reg_rund
#print axioms Gabbro.Grammatik.Parser.gerTeile_rund
#print axioms Gabbro.Grammatik.Parser.item_dev

/-
  CUTS: what the device round trip does not cover, and why.

  * `bank` members: the reader keeps a bank as raw text rebuilt from its parts (`parseBank`:
    `druck` of the address, stride and count, the balanced body words), and the printer re-lexes
    that text; the round trip would need the rebuilt text to re-lex to the same parts. Excluded
    from `GerGut`.
  * `transition` members (`druckTrans`): steps, `requires` and `effects` of a transition. One more
    case of `GerGut` with a step-list reader lemma in the pattern of `kanten_rund`.
  * Register fields with a bit range `[hi:lo]` (`parseBitpos` keeps it as text): `RegFeldGut` takes
    a number or a name.
  * Stage names spelled `,` (`PhasenGut`); a class name `""` (it prints as no class).
-/
