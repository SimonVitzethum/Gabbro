module

public import Grammatik.Parser.Round.RundlaufItem.Teil4a
public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil5
public import Grammatik.Parser.Round.RundlaufItem.Teil3

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

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

end Gabbro.Grammatik.Parser
