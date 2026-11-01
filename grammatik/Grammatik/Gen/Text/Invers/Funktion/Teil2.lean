module

public import Grammatik.Gen.Text.Invers.Rumpf
public import Grammatik.Gen.Text.Invers.Funktion.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
section Kopf
variable (z : Spez)

theorem kopf_ok (gNr : Nat → Nat) (P : Programm z.deklaration) (f : z.deklaration.Fn) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (whys : List UWhy) (devs : List String) (mitGriff : Bool)
    (consts : List (String × Int)) (als : List (String × (Int × Int))) (sums : List USum)
    (zeiger : List String) (zb : Nat) (ps : List (String × STyp)) (ks : List UParamArt) (res : Option STyp) (req ens : List SKlausel)
    (hps : parListe (optTab z) (z.deklaration.signatur f).params.length 0 (z.deklaration.signatur f).params = .ok ps)
    (hks : (z.deklaration.signatur f).params.mapM artErg = some ks)
    (hres : delabRes z f = .ok res)
    (hV : KopfVor z gNr P f tabs locks globs whys devs mitGriff req ens) :
    elabKopf consts als tabs locks globs whys sums
      { art := "impl", name := nFn (fN z f), params := mitGriffPs ps mitGriff, res,
        fehler := if (z.deklaration.signatur f).gruende = 0 then none
          else some (nGrund (z.deklaration.signatur f).gruende),
        klauseln := klauselnVon z P f req ens } devs zeiger zb =
      .ok (kopfVon z gNr devs f ps ks mitGriff, uEindeutig ((tNamen z f).map nTab)) := by
  set S := z.deklaration.signatur f with hS
  set np := S.params.length with hnp
  obtain ⟨hfilt, hseq⟩ := parListe_ok (optTab z) np als tabs sums whys zeiger zb devs hV.devsOk S.params 0 ps ks hps hks
  have hlen := mapM_length artErg S.params ks hks
  obtain ⟨p1, p2, p3⟩ := tripel_proj ((List.range' 0 S.params.length).map fun i => nVar (np - 1 - i)) S.params ks
    (by simp only [List.length_map, List.length_range']) hlen
  -- the device handle is dropped
  have hog : uOhneGriffe devs (mitGriffPs ps mitGriff) = ps := by
    unfold mitGriffPs
    unfold uOhneGriffe at hfilt ⊢
    rw [List.filter_append, hfilt]
    cases mitGriff with
    | false => simp only [Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
    | true =>
      simp only [uGriffTyp, List.any_eq_true, ↓reduceIte, List.append_right_eq_self, List.filter_eq_nil_iff,
  List.mem_cons, List.not_mem_nil, or_false, Option.isNone_iff_eq_none, forall_eq, ite_eq_right_iff, reduceCtorEq,
  imp_false, not_exists, not_and, Bool.not_eq_true, not_forall, not_imp, Bool.not_eq_false]
      exact ⟨"Dev", hV.griff rfl, by decide⟩
  -- the clauses
  have hall : ∀ k ∈ klauselnVon z P f req ens, KlauselOk k := by
    intro k hk
    simp only [klauselnVon, List.mem_append] at hk
    rcases hk with ((hk | hk) | hk) | hk
    · unfold heldKlausel at hk; split at hk <;> simp_all [KlauselOk]
    · exact (hV.klauseln k (List.mem_append_left _ hk)).1
    · exact (hV.klauseln k (List.mem_append_right _ hk)).1
    · unfold effKlausel at hk; split at hk <;> simp_all [KlauselOk]
  have hok := ohneKlauselForm_ok _ hall
  have hrest : uGehalten locks (req ++ ens ++ effKlausel z P f) = .ok [] := by
    apply gehalten_ohne
    intro k hk args
    simp only [List.mem_append] at hk
    rcases hk with (hk | hk) | hk
    · exact (hV.klauseln k (List.mem_append_left _ hk)).2.1 args
    · exact (hV.klauseln k (List.mem_append_right _ hk)).2.1 args
    · unfold effKlausel at hk; split at hk <;> simp_all
  have hgeh : uGehalten locks (klauselnVon z P f req ens) = .ok (heldNamen z f) := by
    unfold klauselnVon heldKlausel
    by_cases he : (heldNamen z f).isEmpty
    · have : heldNamen z f = [] := by simpa using he
      simp only [he, ite_true, List.nil_append]
      rw [this]
      simpa [List.append_assoc] using hrest
    · simp only [he, Bool.false_eq_true, ite_false, List.cons_append, List.append_assoc, uGehalten]
      rw [gehaltenAux_ok locks _ hV.held]
      simp only [List.append_assoc] at hrest
      simp only [List.nil_append, hrest, List.append_nil]
  -- the reason channel
  have hkn : (match (if S.gruende = 0 then none else some (nGrund S.gruende)) with
      | .none => .ok none
      | .some r =>
        match whys.findIdx? (fun w => strEq w.name r) with
        | .none => .error ("reason unknown: " ++ r)
        | .some k =>
          match whys[k]? with
          | .some w => if w.cases.isEmpty then .error "reason without cases" else .ok (some (k, w.cases.length))
          | .none => .error ("reason unknown: " ++ r) : Except String (Option (Nat × Nat))) =
      .ok (kanalVon gNr S.gruende) := by
    by_cases hg : S.gruende = 0
    · simp only [hg, ↓reduceIte, kanalVon]
    · obtain ⟨w, hw1, hw2, hw3⟩ := hV.why hg
      rw [← hS] at hw1 hw2 hw3
      have hne : w.cases.isEmpty = false := by
        cases hc : w.cases with
        | nil => rw [hc] at hw3; simp only [List.length_nil] at hw3; exact absurd hw3.symm hg
        | cons _ _ => rfl
      simp only [hg, ite_false, hw1, hw2, hne, Bool.false_eq_true, kanalVon, hw3]
  -- the effects
  have hps_none : ∀ p ∈ ps, uGriffTyp devs p.2 = none := by
    intro p hp
    have := (List.filter_eq_self.1 hfilt) p hp
    simpa using this
  have heffOk : ∀ (kopf : UFnKopf), kopf.names = (List.range' 0 S.params.length).map (fun i => nVar (np - 1 - i)) →
      kopf.griffe = uGriffe devs 0 (mitGriffPs ps mitGriff) → EffOk kopf tabs globs := by
    intro kopf hn hg
    refine ⟨?_, ?_, hV.tabsOk⟩
    · intro n hm; rw [hn] at hm; simp only [List.mem_map] at hm
      obtain ⟨i, _, rfl⟩ := hm; exact Or.inl ⟨_, rfl⟩
    · intro g hm
      rw [hg] at hm
      unfold mitGriffPs at hm
      rw [griffe_append devs ps _ 0 hps_none] at hm
      exact (griffe_d devs _ mitGriff g hm).1
  have hwirk : uEffekte.uWirkungen (klauselnVon z P f req ens) = effListe z P f := by
    unfold klauselnVon
    rw [wirkungen_append, wirkungen_append, wirkungen_append]
    rw [wirkungen_ohne (heldKlausel z f) (by intro k hk es; unfold heldKlausel at hk; split at hk <;> simp_all),
      wirkungen_ohne req (fun k hk => (hV.klauseln k (List.mem_append_left _ hk)).2.2),
      wirkungen_ohne ens (fun k hk => (hV.klauseln k (List.mem_append_right _ hk)).2.2)]
    unfold effKlausel
    split
    · rename_i he; simp only [List.append_nil, uEffekte.uWirkungen, List.isEmpty_iff.1 he]
    · simp only [List.append_nil, uEffekte.uWirkungen, List.nil_append]
  have heff : ∀ (kopf : UFnKopf), EffOk kopf tabs globs →
      uEffekte kopf tabs locks globs (klauselnVon z P f req ens) =
        .ok { locks := lNamen z P f, puts := (tNamen z f).map nTab, gputs := (gNamen z f).map nGlob } := by
    intro kopf hE
    unfold uEffekte
    simp only [hwirk, effListe]
    exact eff_alle hE _ _ _ hV.tab hV.glob hV.sperren
  have himpl : strEq "impl" "impl" = true := by decide
  unfold elabKopf
  simp only [hog, himpl, Bool.true_or, Bool.not_true, Bool.false_eq_true, ite_false, hok, hseq, hgeh]
  have hkn' : ∀ x, (match (if S.gruende = 0 then none else some (nGrund S.gruende)) with
      | none => Except.ok none
      | some r =>
        match whys.findIdx? (fun w => strEq w.name r) with
        | none => Except.error ("reason unknown: " ++ r)
        | some k =>
          match whys[k]? with
          | some w => if w.cases.isEmpty = true then Except.error "reason without cases" else Except.ok (some (k, w.cases.length))
          | none => Except.error ("reason unknown: " ++ r) : Except String (Option (Nat × Nat))) = x →
      x = .ok (kanalVon gNr S.gruende) := by
    intro x hx; rw [← hx]; exact hkn
  split
  · rename_i e he; have := hkn' _ he; cases this
  · rename_i kn hk
    have hk2 := hkn' _ hk
    simp only [Except.ok.injEq] at hk2
    subst hk2
    rw [heff _ (heffOk _ (by simpa [hnp] using p1) rfl)]
    simp only
    unfold delabRes at hres
    simp only [← hS] at hres
    split at hres
    · rename_i hn
      simp only [pure, Except.pure, Except.ok.injEq] at hres; subst hres
      simp only [kopfVon, ← hS, hn, ergBereich, p1, p2, p3]
      simp only [hnp, reduceCtorEq, decide_false]
    · rename_i t ht
      cases t with
      | bool =>
        simp only [typS, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres; subst hres
        simp only [kopfVon, ← hS, ht, ergBereich, p1, p2, p3]
        simp only [hnp, decide_true]
      | int lo hi =>
        simp only [typS, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres; subst hres
        simp only [kopfVon, ← hS, ht, ergBereich, p1, p2, p3, uErgBereich, schranke_zahlE]
        simp only [hnp, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, reduceCtorEq, decide_false]
      | _ => have := hV.erg _ (by rw [← hS]; exact ht); simp only [artErg, Option.isSome_none, Bool.false_eq_true] at this

end Kopf

end Gabbro.Grammatik.Gen.Text
