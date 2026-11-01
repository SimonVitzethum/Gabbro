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

end Gabbro.Grammatik.Parser
