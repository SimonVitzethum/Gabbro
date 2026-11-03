module

public import Grammatik.Parser.Round.RundlaufItem.Teil2a
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil5
public import Grammatik.Parser.Round.RundlaufItem.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

/-- The ordinary printable core. Generic heads have separate source-path witnesses. -/
def SigGut (s : FnSig) : Prop :=
  (s.art = "" ∨ s.art = "const" ∨ istMod s.art = true) ∧ (∀ p ∈ s.params, TypGut p.2) ∧
    TypOptGut s.res ∧ (∀ k ∈ s.klauseln, KlauselGut k) ∧ s.generics = []

/-- The function head behind its modifier, up to the body. -/
def sigToks (s : FnSig) : List Token :=
  [.wort "fn", nameTok s.name] ++ druckGenericParams s.generics ++ [.zeichen "("] ++ druckParams s.params ++ [.zeichen ")"] ++
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

theorem sigToks_eq (s : FnSig) (hg : s.generics = []) : sigToks s = [.wort "fn", nameTok s.name, .zeichen "("] ++
    druckParams s.params ++ [.zeichen ")"] ++ resToks s.res ++ fehlerToks s.fehler ++ druckKlauseln s.klauseln := by
  simp only [sigToks, hg, druckGenericParams, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
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
  obtain ⟨-, hp, hres, hk, hgeneric⟩ := hs
  rw [sigToks_eq s hgeneric] at hF ⊢
  obtain ⟨art, name, params, res, fehler, klauseln, generics⟩ := s
  cases hgeneric
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
  simp only [parseFnSig, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok,
    bind, Except.bind, pure, Except.pure, parseGenericParams, List.any_nil, Bool.false_eq_true, hP, hErg, hK]

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

end Gabbro.Grammatik.Parser
