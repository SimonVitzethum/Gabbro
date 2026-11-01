module

public import Grammatik.Parser.Round.RundlaufAnwVoll.Teil5
public import Grammatik.Parser.Round.RundlaufItem.Teil5

@[expose] public section

namespace Gabbro.Grammatik.Parser
set_option maxRecDepth 100000

theorem namenKlammer_rund (ns : List String) (R : List Token) (F : Nat) (hF : ns.length + 2 ≤ F) :
    parseNamenEingeklammert F (druckNamenKlammer ns ++ R) = .ok (ns, R) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  cases ns with
  | nil => simp only [parseNamenEingeklammert, fordereZeichen, druckNamenKlammer, druckNamen, List.append_nil, List.cons_append, List.nil_append, strEq_self, ↓reduceIte]
  | cons n ns' =>
    have hN := namen_rund (n :: ns') (.zeichen "}" :: R) F' (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e) (by omega)
    obtain ⟨ts, hts⟩ : ∃ ts, druckNamen (n :: ns') ++ .zeichen "}" :: R = nameTok n :: ts := by
      cases ns' <;> exact ⟨_, by simp only [druckNamen, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl⟩
    simp only [druckNamenKlammer, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    rw [hts] at hN ⊢
    simp only [parseNamenEingeklammert, fordereZeichen, strEq_self, ↓reduceIte, List.cons.injEq, nameTok_ne_zeichen, false_and, imp_self, implies_true, hN, Token.zeichen.injEq, String.reduceEq]

/-- A printable entry: printable vector and stack-index expressions, a `nested` mode of one word,
    a dispatch path. -/
def EingangGut (e : SEingang) : Prop :=
  (∀ v, e.vektor = some v → gut v = true) ∧ (∀ x, e.ist = some x → gut x = true) ∧
    (e.nest = none ∨ e.nest = some "never" ∨ e.nest = some "masked") ∧ e.dispatch ≠ []

def vekToks : Option SExpr → List Token
  | some v => [.wort "vector"] ++ druckToks v
  | none => []

def istToks : Option SExpr → List Token
  | some x => [.wort "ist"] ++ druckToks x
  | none => []

def nestToks : Option String → List Token
  | some n => [.wort "nested"] ++ rohToks n
  | none => []

def cpuToks (b : Bool) : List Token := if b then [.wort "per", .wort "cpu"] else []

theorem druckEingang_eq (e : SEingang) : druckEingang e = [.wort "entry", nameTok e.name] ++ vekToks e.vektor ++
    nameOptToks "via" e.via ++ [.wort "arch", nameTok e.arch, .zeichen "{", .wort "regs", .wort "in", .zeichen "{"] ++
    druckRegBinds e.regIn ++ [.zeichen "}", .wort "regs", .wort "out", .zeichen "{"] ++ druckRegBinds e.regOut ++
    [.zeichen "}", .wort "preserves"] ++ druckNamenKlammer e.erhaelt ++ [.wort "clobbers"] ++
    druckNamenKlammer e.kills ++ [.wort "stack", nameTok e.stapel] ++ cpuToks e.perCpu ++ istToks e.ist ++
    nestToks e.nest ++ [.wort "dispatch"] ++ pfadToks e.dispatch ++ [.zeichen ";", .zeichen "}"] := by
  simp only [druckEingang, List.cons_append, List.nil_append, List.append_assoc, vekToks, nameOptToks, cpuToks, istToks, nestToks, List.cons.injEq, true_and]; rfl

theorem eingangKopf_arch (f : Nat) (a : String) (R : List Token) :
    parseEingangKopf (f + 1) (.wort "arch" :: nameTok a :: R) = .ok ((none, none, a), R) := by
  simp [parseEingangKopf, nimmName, strEq_self, (by decide : strEq "arch" "vector" = false), (by decide : strEq "arch" "via" = false)]

theorem eingangKopf_via (f : Nat) (m : String) (X R : List Token) (v : Option SExpr) (w : Option String)
    (a : String) (h : parseEingangKopf f X = .ok ((v, w, a), R)) :
    parseEingangKopf (f + 1) (.wort "via" :: nameTok m :: X) = .ok ((v, some m, a), R) := by
  simp [parseEingangKopf, nimmName, strEq_self, h, (by decide : strEq "via" "vector" = false)]

theorem eingangKopf_vector (f : Nat) (e : SExpr) (X R : List Token) (v : Option SExpr) (w : Option String)
    (a : String) (hO : parseOr f (druckToks e ++ X) = .ok (e, X)) (h : parseEingangKopf f X = .ok ((v, w, a), R)) :
    parseEingangKopf (f + 1) (.wort "vector" :: (druckToks e ++ X)) = .ok ((some e, w, a), R) := by
  simp only [parseEingangKopf, strEq_self, ↓reduceIte, hO, h]

theorem eingangKopf_rund (vek : Option SExpr) (via : Option String) (a : String) (hv : ∀ v, vek = some v → gut v = true)
    (R : List Token) (F : Nat) (hF : 8 * (vekToks vek).length + 40 ≤ F) :
    parseEingangKopf F (vekToks vek ++ (nameOptToks "via" via ++ (.wort "arch" :: nameTok a :: R))) =
      .ok ((vek, via, a), R) := by
  have L1 : ∀ G, 2 ≤ G → parseEingangKopf G (nameOptToks "via" via ++ (.wort "arch" :: nameTok a :: R)) =
      .ok ((none, via, a), R) := by
    intro G hG
    obtain ⟨G', rfl⟩ : ∃ G', G = G' + 2 := ⟨G - 2, by omega⟩
    cases via with
    | none => simpa [nameOptToks] using eingangKopf_arch (G' + 1) a R
    | some m => simpa [nameOptToks] using eingangKopf_via (G' + 1) m _ R none none a (eingangKopf_arch G' a R)
  cases vek with
  | none => simpa [vekToks] using L1 F (by simp only [vekToks, List.length_nil, Nat.mul_zero, Nat.zero_add] at hF; omega)
  | some v =>
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by simp only [vekToks, List.cons_append, List.nil_append, List.length_cons] at hF; omega⟩
    have hrX : ruhig (nameOptToks "via" via ++ (.wort "arch" :: nameTok a :: R)) = true ∧
        ruhigSuff (nameOptToks "via" via ++ (.wort "arch" :: nameTok a :: R)) = true ∧
        ruhigGleit (nameOptToks "via" via ++ (.wort "arch" :: nameTok a :: R)) = true := by
      cases via <;> exact ⟨rfl, rfl, rfl⟩
    have hO := ausdruck v (hv v rfl) _ F' hrX.1 hrX.2.1 hrX.2.2 (by simp only [vekToks, List.cons_append, List.nil_append, List.length_cons, Nat.reduceLeDiff] at hF; omega)
    simpa [vekToks] using eingangKopf_vector F' v _ R none via a hO (L1 F' (by simp only [vekToks, List.cons_append, List.nil_append, List.length_cons, Nat.reduceLeDiff] at hF; omega))

theorem dispatch_rund (f : Nat) (dp : List String) (hdp : dp ≠ []) (R : List Token) :
    parseEingangDispatch (f + 1) (.wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) = .ok (dp, R) := by
  have hP := nimmPfad_pfad dp (.zeichen ";" :: R) hdp (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
  simp only [parseEingangDispatch, nimmWort, strEq_self, ↓reduceIte, hP, fordereZeichen]

theorem rohToks_never : rohToks "never" = [.wort "never"] := by
  rw [rohToks_name "never" (by decide)]; simp only [nameTok, List.cons.injEq, ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false, and_true]; decide

theorem rohToks_masked : rohToks "masked" = [.wort "masked"] := by
  rw [rohToks_name "masked" (by decide)]; simp only [nameTok, List.cons.injEq, ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false, and_true]; decide

theorem nestOpt_rund (f : Nat) (nest : Option String) (hn : nest = none ∨ nest = some "never" ∨ nest = some "masked")
    (X : List Token) :
    parseEingangNestedOpt (f + 1) (nestToks nest ++ .wort "dispatch" :: X) = .ok (nest, .wort "dispatch" :: X) := by
  rcases hn with rfl | rfl | rfl
  · simp [nestToks, parseEingangNestedOpt, (by decide : strEq "dispatch" "nested" = false)]
  · have : rohToks "never" = [.wort "never"] := by rw [rohToks_name "never" (by decide)]; simp only [nameTok, List.cons.injEq, ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false, and_true]; decide
    simp only [parseEingangNestedOpt, nestToks, this, List.cons_append, List.nil_append, strEq_self, ↓reduceIte, Bool.true_or]
  · have : rohToks "masked" = [.wort "masked"] := by rw [rohToks_name "masked" (by decide)]; simp only [nameTok, List.cons.injEq, ite_eq_left_iff, Bool.not_eq_true, reduceCtorEq, imp_false, Bool.not_eq_false, and_true]; decide
    simp [nestToks, this, parseEingangNestedOpt, strEq_self, (by decide : strEq "masked" "never" = false)]

theorem nested_rund (f : Nat) (nest : Option String) (hn : nest = none ∨ nest = some "never" ∨ nest = some "masked")
    (dp : List String) (hdp : dp ≠ []) (R : List Token) :
    parseEingangNested (f + 2) (nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) =
      .ok ((nest, dp), R) := by
  simp only [parseEingangNested, nestOpt_rund f nest hn, dispatch_rund f dp hdp R]

theorem restNach_rund (f : Nat) (ist : Option SExpr) (hi : ∀ x, ist = some x → gut x = true) (nest : Option String)
    (hn : nest = none ∨ nest = some "never" ∨ nest = some "masked") (dp : List String) (hdp : dp ≠ [])
    (R : List Token) (hF : 8 * (istToks ist).length + 40 ≤ f) :
    parseEingangRestNach (f + 3) (istToks ist ++ (nestToks nest ++ .wort "dispatch" ::
      (pfadToks dp ++ .zeichen ";" :: R))) = .ok ((ist, nest, dp), R) := by
  have hN := nested_rund f nest hn dp hdp R
  have hN1 := nested_rund (f + 1) nest hn dp hdp R
  have hkopf : ∃ w X, nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R) = .wort w :: X ∧
      w ≠ "ist" := by
    rcases hn with rfl | rfl | rfl
    · exact ⟨"dispatch", _, rfl, by decide⟩
    · exact ⟨"nested", _, by simp only [nestToks, rohToks_never, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl, by decide⟩
    · exact ⟨"nested", _, by simp only [nestToks, rohToks_masked, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl, by decide⟩
  cases ist with
  | none =>
    obtain ⟨w, X, hw, hne⟩ := hkopf
    have : strEq w "ist" = false := by
      cases h : strEq w "ist"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) hne
    simp only [istToks, List.nil_append]
    rw [hw] at hN ⊢
    simp only [parseEingangRestNach, this, Bool.false_eq_true, ↓reduceIte, hN]
  | some x =>
    have hx := hi x rfl
    have hrX : ruhig (nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) = true ∧
        ruhigSuff (nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) = true ∧
        ruhigGleit (nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) = true := by
      rcases hn with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
    have hO := ausdruck x hx _ (f + 2) hrX.1 hrX.2.1 hrX.2.2 (by simp only [istToks, List.cons_append, List.nil_append, List.length_cons] at hF; omega)
    simp only [istToks, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    simp only [parseEingangRestNach, strEq_self, ↓reduceIte, hO, hN]


theorem rest_rund (f : Nat) (st : String) (cpu : Bool) (ist : Option SExpr) (hi : ∀ x, ist = some x → gut x = true)
    (nest : Option String) (hn : nest = none ∨ nest = some "never" ∨ nest = some "masked") (dp : List String)
    (hdp : dp ≠ []) (R : List Token) (hF : 8 * (istToks ist).length + 40 ≤ f) :
    parseEingangRest (f + 4) (.wort "stack" :: nameTok st :: (cpuToks cpu ++ (istToks ist ++ (nestToks nest ++
      .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R))))) = .ok ((st, cpu, ist, nest, dp), R) := by
  have hRN := restNach_rund f ist hi nest hn dp hdp R hF
  cases cpu with
  | true =>
    simp only [cpuToks, ite_true, List.cons_append, List.nil_append]
    simp only [parseEingangRest, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hRN]
  | false =>
    simp only [cpuToks, Bool.false_eq_true, ite_false, List.nil_append]
    have hkopf : ∃ w X, istToks ist ++ (nestToks nest ++ .wort "dispatch" :: (pfadToks dp ++ .zeichen ";" :: R)) =
        .wort w :: X ∧ w ≠ "per" := by
      cases ist with
      | some x => exact ⟨"ist", _, rfl, by decide⟩
      | none =>
        rcases hn with rfl | rfl | rfl
        · exact ⟨"dispatch", _, rfl, by decide⟩
        · exact ⟨"nested", _, by simp only [istToks, nestToks, rohToks_never, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl, by decide⟩
        · exact ⟨"nested", _, by simp only [istToks, nestToks, rohToks_masked, List.cons_append, List.nil_append, List.cons.injEq, true_and]; rfl, by decide⟩
    obtain ⟨w, X, hw, hne⟩ := hkopf
    have : strEq w "per" = false := by
      cases h : strEq w "per"
      · rfl
      · exact absurd ((strEq_eq _ _).mp h) hne
    rw [hw] at hRN ⊢
    simp only [parseEingangRest, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, this, Bool.false_eq_true, hRN]

theorem druckRegBinds_len (bs : List SRegBind) : bs.length ≤ (druckRegBinds bs).length := by
  induction bs with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons b bs ih =>
    cases bs with
    | nil => cases b <;> simp only [List.length_cons, List.length_nil, Nat.zero_add, druckRegBinds, druckRegBind, Nat.reduceAdd, Nat.reduceLeDiff, Std.le_refl]
    | cons c cs =>
      simp only [druckRegBinds, List.length_append, List.length_cons] at ih ⊢
      cases b <;> simp only [druckRegBind, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd] <;> omega

theorem druckNamen_len (ns : List String) : ns.length ≤ (druckNamen ns).length := by
  induction ns with
  | nil => simp only [List.length_nil, Nat.zero_le]
  | cons n ns ih => cases ns with
    | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckNamen, Std.le_refl]
    | cons m ms => simp only [List.length_cons, druckNamen, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega

theorem item_entry (e : SEingang) (he : EingangGut e) : ItemBein (.entryT e) := by
  intro rest F hF
  obtain ⟨hv, hi, hn, hdp⟩ := he
  have hlenRI := druckRegBinds_len e.regIn
  have hlenRO := druckRegBinds_len e.regOut
  have hlenE := druckNamen_len e.erhaelt
  have hlenK := druckNamen_len e.kills
  simp only [fbI, druckItem, druckEingang_eq, druckNamenKlammer, List.length_append, List.length_cons,
    List.length_nil] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 7 := ⟨F - 7, by omega⟩
  have hK := eingangKopf_rund e.vektor e.via e.arch hv (.zeichen "{" :: .wort "regs" :: .wort "in" :: .zeichen "{" ::
    (druckRegBinds e.regIn ++ .zeichen "}" :: .wort "regs" :: .wort "out" :: .zeichen "{" :: (druckRegBinds e.regOut ++
      .zeichen "}" :: .wort "preserves" :: (druckNamenKlammer e.erhaelt ++ .wort "clobbers" ::
        (druckNamenKlammer e.kills ++ .wort "stack" :: nameTok e.stapel :: (cpuToks e.perCpu ++ (istToks e.ist ++
          (nestToks e.nest ++ .wort "dispatch" :: (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest)))))))))
    (F' + 4) (by omega)
  have hRI := regBindListe_rund e.regIn (.wort "regs" :: .wort "out" :: .zeichen "{" :: (druckRegBinds e.regOut ++
      .zeichen "}" :: .wort "preserves" :: (druckNamenKlammer e.erhaelt ++ .wort "clobbers" ::
        (druckNamenKlammer e.kills ++ .wort "stack" :: nameTok e.stapel :: (cpuToks e.perCpu ++ (istToks e.ist ++
          (nestToks e.nest ++ .wort "dispatch" :: (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest))))))))
    (F' + 4) (by omega)
  have hRO := regBindListe_rund e.regOut (.wort "preserves" :: (druckNamenKlammer e.erhaelt ++ .wort "clobbers" ::
        (druckNamenKlammer e.kills ++ .wort "stack" :: nameTok e.stapel :: (cpuToks e.perCpu ++ (istToks e.ist ++
          (nestToks e.nest ++ .wort "dispatch" :: (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest)))))))
    (F' + 4) (by omega)
  have hE := namenKlammer_rund e.erhaelt (.wort "clobbers" ::
        (druckNamenKlammer e.kills ++ .wort "stack" :: nameTok e.stapel :: (cpuToks e.perCpu ++ (istToks e.ist ++
          (nestToks e.nest ++ .wort "dispatch" :: (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest))))))
    (F' + 4) (by omega)
  have hKi := namenKlammer_rund e.kills (.wort "stack" :: nameTok e.stapel :: (cpuToks e.perCpu ++ (istToks e.ist ++
          (nestToks e.nest ++ .wort "dispatch" :: (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest)))))
    (F' + 4) (by omega)
  have hR := rest_rund F' e.stapel e.perCpu e.ist hi e.nest hn e.dispatch hdp (.zeichen "}" :: rest)
    (by omega)
  have hd : druckItem (.entryT e) ++ rest = .wort "entry" :: nameTok e.name :: (vekToks e.vektor ++
      (nameOptToks "via" e.via ++ (.wort "arch" :: nameTok e.arch :: (.zeichen "{" :: .wort "regs" :: .wort "in" ::
        .zeichen "{" :: (druckRegBinds e.regIn ++ .zeichen "}" :: .wort "regs" :: .wort "out" :: .zeichen "{" ::
          (druckRegBinds e.regOut ++ .zeichen "}" :: .wort "preserves" :: (druckNamenKlammer e.erhaelt ++
            .wort "clobbers" :: (druckNamenKlammer e.kills ++ .wort "stack" :: nameTok e.stapel ::
              (cpuToks e.perCpu ++ (istToks e.ist ++ (nestToks e.nest ++ .wort "dispatch" ::
                (pfadToks e.dispatch ++ .zeichen ";" :: .zeichen "}" :: rest)))))))))))) := by
    simp only [druckItem, druckEingang_eq, List.cons_append, List.nil_append, List.append_assoc]
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_entry]
  simp only [druckNamenKlammer, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
    at hRI hRO hE hKi hK ⊢
  simp only [parseEingangTief, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, hK, fordereZeichen, hRI, hRO, hE, hKi, hR]



/-! ### `group` -/

theorem gruppenInvs_rund : ∀ (ivs : List SGruppenInv), (∀ i ∈ ivs, InvGut i) → ∀ (R : List Token) (F : Nat),
    8 * (druckGruppenInvs ivs).length + 61 ≤ F →
    parseGruppenInvListe F (druckGruppenInvs ivs ++ .zeichen "}" :: R) = .ok (ivs, .zeichen "}" :: R) := by
  intro ivs
  induction ivs with
  | nil =>
    intro _ R F hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [parseGruppenInvListe, druckGruppenInvs, List.nil_append]
  | cons i ivs ih =>
    intro hg R F hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    simp only [druckGruppenInvs, List.length_append] at hF
    have h1 : 1 ≤ (druckGruppenInv i).length := by simp only [druckGruppenInv, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.le_add_left]
    have hI := gruppenInv_rund i (hg i (by simp only [List.mem_cons, true_or])) (druckGruppenInvs ivs ++ .zeichen "}" :: R) F' (by omega)
    have hR := ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) R F' (by omega)
    have hd : druckGruppenInv i = .wort "invariant" :: (druckGruppenInv i).tail := rfl
    simp only [druckGruppenInvs, List.append_assoc]
    rw [hd] at hI ⊢
    simp only [List.cons_append] at hI ⊢
    simp only [parseGruppenInvListe, strEq_self, ↓reduceIte, hI, hR]

/-- The tail of a group: `;` without invariants, the invariants in braces otherwise. -/
def gruppeRestToks : List SGruppenInv → List Token
  | [] => [.zeichen ";"]
  | ivs => [.zeichen "{"] ++ druckGruppenInvs ivs ++ [.zeichen "}"]

theorem item_group (n : String) (ms : List String) (ivs : List SGruppenInv) (hms : ms ≠ [])
    (hivs : ∀ i ∈ ivs, InvGut i) : ItemBein (.groupT n ms ivs) := by
  intro rest F hF
  have hd : druckItem (.groupT n ms ivs) ++ rest = .wort "group" :: nameTok n :: .wort "over" :: .zeichen "{" ::
      (druckNamen ms ++ .zeichen "}" :: (gruppeRestToks ivs ++ rest)) := by
    cases ivs <;> simp only [druckItem, druckNamenKlammer, List.cons_append, List.nil_append, List.append_assoc, gruppeRestToks]
  have hlen : (druckItem (.groupT n ms ivs)).length = 5 + (druckNamen ms).length + (gruppeRestToks ivs).length := by
    cases ivs <;> simp only [druckItem, druckNamenKlammer, List.cons_append, List.nil_append, List.append_assoc, List.length_cons, List.length_append, List.length_nil, Nat.zero_add, Nat.reduceAdd, gruppeRestToks, Nat.add_right_cancel_iff] <;> omega
  have hms' : ms.length ≤ (druckNamen ms).length := by
    clear hF hd hlen hms
    induction ms with
    | nil => simp only [List.length_nil, Nat.zero_le]
    | cons m ms ih => cases ms with
      | nil => simp only [List.length_cons, List.length_nil, Nat.zero_add, druckNamen, Std.le_refl]
      | cons a as => simp only [List.length_cons, druckNamen, List.cons_append, List.nil_append, Nat.add_le_add_iff_right] at ih ⊢; omega
  simp only [fbI, hlen] at hF
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 3 := ⟨F - 3, by omega⟩
  have hN := namen_rund ms (.zeichen "}" :: (gruppeRestToks ivs ++ rest)) F' hms (by intro r e; simp only [List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and] at e)
    (by omega)
  have hRest : parseGruppeRest F' (gruppeRestToks ivs ++ rest) = .ok (ivs, rest) := by
    obtain ⟨G, rfl⟩ : ∃ G, F' = G + 1 := ⟨F' - 1, by omega⟩
    cases ivs with
    | nil => simp only [parseGruppeRest, gruppeRestToks, List.cons_append, List.nil_append]
    | cons i is =>
      simp only [gruppeRestToks, List.length_append, List.length_cons, List.length_nil] at hF
      have hL := gruppenInvs_rund (i :: is) hivs rest G (by omega)
      simp only [gruppeRestToks, List.cons_append, List.nil_append, List.append_assoc, List.singleton_append]
      simp only [parseGruppeRest, hL, fordereZeichen, strEq_self, ↓reduceIte]
  rw [hd, parseItemTief_wort _ _ _ (by decide) (by decide), parseItemKopf_group]
  simp only [parseGruppeTief, nimmWort, strEq_self, ↓reduceIte, nimmName, nameText_nameTok, fordereZeichen, hN, List.cons.injEq, Token.zeichen.injEq, String.reduceEq, false_and, imp_self, implies_true, hRest]

end Gabbro.Grammatik.Parser
