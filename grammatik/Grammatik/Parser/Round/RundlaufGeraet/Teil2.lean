module

public import Grammatik.Parser.Round.RundlaufItem.Teil6
public import Grammatik.Parser.Round.RundlaufGeraet.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

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
