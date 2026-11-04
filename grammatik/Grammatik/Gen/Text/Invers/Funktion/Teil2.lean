module

public import Grammatik.Gen.Text.Invers.Rumpf
public import Grammatik.Gen.Text.Invers.Funktion.Teil1
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-- Finish the actual head reader over plain data, before instantiating specification indices. -/
private theorem elabKopf_scalar
    (consts : List (String × Int)) (als : List (String × (Int × Int)))
    (tabs : List UTab) (locks : List ULock) (globs : List UGlob) (whys : List UWhy)
    (sums : List USum) (devs zeiger : List String) (zb : Nat) (otab : Int → Option Nat)
    (name : String) (params0 params : List (String × STyp))
    (parsed : List (String × Ty × UParamArt)) (names : List String) (types : List Ty)
    (kinds : List UParamArt) (erg : Option Ty) (res : Option STyp) (fehler : Option String)
    (klauseln : List SKlausel) (held : List String) (kn : Option (Nat × Nat))
    (eff : UEffekte) (out : UFnKopf)
    (hfilter : uOhneGriffe devs params0 = params)
    (hseq : uSeq (params.map (uParam als tabs sums whys zeiger zb [] [] [])) = .ok parsed)
    (hnames : parsed.map (·.1) = names) (htypes : parsed.map (·.2.1) = types)
    (hkinds : parsed.map (·.2.2) = kinds)
    (hmc : uMeasureClause als klauseln = .ok none)
    (hok : uOhneKlauselForm klauseln = .ok ())
    (hheld : uGehalten locks klauseln = .ok held)
    (hkn : (match fehler with
      | none => .ok none
      | some r =>
        match whys.findIdx? (fun w => strEq w.name r) with
        | none => .error ("reason unknown: " ++ r)
        | some k =>
          match whys[k]? with
          | some w => if w.cases.isEmpty then .error "reason without cases"
              else .ok (some (k, w.cases.length))
          | none => .error ("reason unknown: " ++ r) : Except String (Option (Nat × Nat))) = .ok kn)
    (heff : uEffekte
      { name, names, kinds, types, res := none, bits := params.map (fun p => uParamBreite p.2),
        held := uEindeutig held, kanal := kn, griffe := uGriffe devs 0 params0 }
      tabs locks globs klauseln = .ok eff)
    (herg : ∀ t, erg = some t → (artErg t).isSome)
    (hres : (match erg with
      | none => pure none
      | some t => do pure (some (← typS otab t)) : Except String (Option STyp)) = .ok res)
    (hout :
      { name, names, kinds, types, res := ergBereich erg, resBool := decide (erg = some .bool),
        bits := params.map (fun p => uParamBreite p.2), held := uEindeutig held, kanal := kn,
        griffe := uGriffe devs 0 params0, gputs := uEindeutig eff.gputs,
        nimmt := uEindeutig eff.nimmt, gibt := uEindeutig eff.gibt, leiht := uEindeutig eff.leiht,
        bewegt := uEindeutig eff.bewegt, praegt := uEindeutig eff.praegt } = out) :
    elabKopf consts als tabs locks globs whys sums
      { art := "impl", name, params := params0, res, fehler, klauseln }
      devs zeiger zb [] [] [] = .ok (out, uEindeutig eff.puts) := by
  rw [← hout]
  have himpl : strEq "impl" "impl" = true := by decide
  unfold elabKopf
  simp only [List.isEmpty_nil, himpl, Bool.true_or, Bool.not_true, Bool.false_eq_true,
    ite_false, hmc, hok, hfilter, hseq, hnames, htypes, hkinds, hheld, hkn, heff]
  cases erg with
  | none =>
    simp only [pure, Except.pure, Except.ok.injEq] at hres
    subst res
    simp only [ergBereich, reduceCtorEq, decide_false]
  | some t =>
    cases t with
    | bool =>
      simp only [typS, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres
      subst res
      simp only [ergBereich, decide_true]
    | int lo hi =>
      simp only [typS, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres
      subst res
      simp only [ergBereich, uErgBereich, schranke_zahlE, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq, reduceCtorEq, decide_false]
    | _ =>
      have impossible := herg _ rfl
      simp only [artErg, Option.isSome_none, Bool.false_eq_true] at impossible

section Kopf
variable (z : Spez)

/-- The clauses the generator writes carry no `decreases` measure in any alias scope. -/
theorem klauselnVon_measure (P : Programm z.deklaration) (f : Fin z.fns.length) (req ens : List SKlausel)
    (h : ∀ k ∈ req ++ ens, KlauselOk k) (als : List (String × (Int × Int))) :
    uMeasureClause als (klauselnVon z P f req ens) = .ok none := by
  have hall : ∀ k ∈ klauselnVon z P f req ens, dropsOf k = none := by
    intro k hk
    unfold klauselnVon at hk
    simp only [List.mem_append] at hk
    rcases hk with ((h1 | h2) | h3) | h4
    · unfold heldKlausel at h1; split at h1 <;> simp_all [dropsOf]
    · exact klauselOk_dropsOf (h k (List.mem_append_left _ h2))
    · exact klauselOk_dropsOf (h k (List.mem_append_right _ h3))
    · unfold effKlausel at h4; split at h4 <;> simp_all [dropsOf]
  have hnil : (klauselnVon z P f req ens).filterMap dropsOf = [] := List.filterMap_eq_nil_iff.mpr hall
  unfold uMeasureClause; rw [hnil]

/-- **The head read back.** -/
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
        klauseln := klauselnVon z P f req ens } devs zeiger zb [] [] [] =
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
  have hmc := klauselnVon_measure z P f req ens (fun k hk => (hV.klauseln k hk).1) als
  let base : UFnKopf :=
    { name := nFn (fN z f),
      names := (List.range' 0 S.params.length).map (fun i => nVar (np - 1 - i)),
      kinds := ks, types := S.params, res := none, bits := ps.map (fun p => uParamBreite p.2),
      held := uEindeutig (heldNamen z f), kanal := kanalVon gNr S.gruende,
      griffe := uGriffe devs 0 (mitGriffPs ps mitGriff) }
  have hbase : EffOk base tabs globs := heffOk base rfl rfl
  have hrun := heff base hbase
  exact elabKopf_scalar
    (otab := optTab z) (erg := S.erg)
    (names := (List.range' 0 S.params.length).map (fun i => nVar (np - 1 - i)))
    (types := S.params) (kinds := ks)
    (hfilter := hog) (hseq := hseq) (hnames := p1) (htypes := p2) (hkinds := p3)
    (hmc := hmc) (hok := hok) (hheld := hgeh) (hkn := hkn)
    (heff := hrun) (herg := hV.erg) (hres := hres) (hout := rfl)

end Kopf

end Gabbro.Grammatik.Gen.Text
