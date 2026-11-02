module

public import Grammatik.Gen.Text.Invers.Rumpf
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

/-! ### Parameters -/

theorem schranke_zahlE (als : List (String × (Int × Int))) (n : Int) : uSchranke als (zahlE n) = some n := by
  unfold zahlE
  split
  · rename_i h; simp only [uSchranke, Int.ofNat_eq_natCast, Int.toNat_of_nonneg h]
  · rename_i h; simp only [uSchranke, Int.ofNat_eq_natCast, Int.toNat_of_nonneg (show 0 ≤ -n by omega), Option.map_some,
  neg_neg]

theorem typS_art {otab : Int → Option Nat} {t : Ty} {st : STyp} {a : UParamArt} (ht : typS otab t = .ok st) (ha : artErg t = some a)
    (als : List (String × (Int × Int))) (tabs : List UTab) (sums : List USum) (whys : List UWhy)
    (zeiger : List String) (zb : Nat) (n : String) :
    uParam als tabs sums whys zeiger zb (n, st) = .ok (n, t, a) := by
  cases t with
  | int lo hi =>
    simp only [artErg, Option.some.injEq] at ha; subst ha
    simp only [typS, Except.ok.injEq] at ht; subst ht
    simp only [uParam, uTyp, schranke_zahlE, Bool.false_eq_true, ↓reduceIte, uArtVon]
  | bool =>
    simp only [artErg, Option.some.injEq] at ha; subst ha
    simp only [typS, Except.ok.injEq] at ht; subst ht
    rfl
  | _ => simp only [artErg, reduceCtorEq] at ha

theorem typS_griff {otab : Int → Option Nat} {t : Ty} {st : STyp} (ht : typS otab t = .ok st) (ha : (artErg t).isSome)
    (devs : List String) (hd : ∀ d ∈ devs, d = "Dev") : uGriffTyp devs st = none := by
  cases t with
  | int lo hi => simp only [typS, Except.ok.injEq] at ht; subst ht; rfl
  | bool =>
    simp only [typS, Except.ok.injEq] at ht; subst ht
    have : (devs.any fun x => strEq x "bool") = false := by
      rw [List.any_eq_false]; intro d hm; rw [hd d hm]; decide
    simp only [uGriffTyp, this, Bool.false_eq_true, ↓reduceIte]
  | _ => simp only [artErg, Option.isSome_none, Bool.false_eq_true] at ha

/-- The printed parameters read back: names `v{np-1-j}`, the types, their kinds. -/
theorem parListe_ok (otab : Int → Option Nat) (np : Nat) (als : List (String × (Int × Int))) (tabs : List UTab) (sums : List USum)
    (whys : List UWhy) (zeiger : List String) (zb : Nat) (devs : List String) (hd : ∀ d ∈ devs, d = "Dev") :
    ∀ (ts : List Ty) (j : Nat) (ps : List (String × STyp)) (ks : List UParamArt),
      parListe otab np j ts = .ok ps → ts.mapM artErg = some ks →
      uOhneGriffe devs ps = ps ∧
      uSeq (ps.map (uParam als tabs sums whys zeiger zb)) =
        .ok (((List.range' j ts.length).map fun i => nVar (np - 1 - i)).zip (ts.zip ks) |>.map
          fun (n, t, k) => (n, t, k)) := by
  intro ts
  induction ts with
  | nil =>
    intro j ps ks hp hk
    simp only [parListe, Except.ok.injEq] at hp; subst hp
    simp only [uOhneGriffe, List.filter_nil, List.map_nil, uSeq, Prod.mk.eta, List.length_nil, List.range'_zero,
  List.zip_nil_left, List.zip_nil_right, and_self]
  | cons t ts ih =>
    intro j ps ks hp hk
    simp only [parListe] at hp
    cases ht : typS otab t with
    | error _ => simp only [bind, Except.bind, ht, reduceCtorEq] at hp
    | ok st =>
    cases hr : parListe otab np (j + 1) ts with
    | error _ => simp only [bind, Except.bind, ht, hr, reduceCtorEq] at hp
    | ok pr =>
    simp only [ht, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hk
    cases ha : artErg t with
    | none => simp only [ha, Option.bind_none, reduceCtorEq] at hk
    | some a =>
    cases hks : ts.mapM artErg with
    | none => simp only [ha, hks, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hk
    | some kr =>
    simp only [ha, hks, Option.bind_some, Option.some.injEq] at hk
    subst hk
    obtain ⟨h1, h2⟩ := ih (j + 1) pr kr hr hks
    refine ⟨?_, ?_⟩
    · simp only [uOhneGriffe, List.filter_cons, typS_griff ht (by simp only [ha, Option.isSome_some]) devs hd, Option.isNone_none, ite_true]
      exact congrArg _ h1
    · simp only [List.map_cons, uSeq, typS_art ht ha als tabs sums whys zeiger zb, h2, List.length_cons, List.range'_succ,
        List.zip_cons_cons]

/-- The parameter `v{np-1-d}` is found at position `d`. -/
theorem parNr_ok (np : Nat) : ∀ (m k : Nat), k + m ≤ np → ∀ d, k ≤ d → d < k + m →
    uParamNrAux ((List.range' k m).map fun i => nVar (np - 1 - i)) k (nVar (np - 1 - d)) = .ok d := by
  intro m
  induction m with
  | zero => intro k _ d h1 h2; omega
  | succ m ih =>
    intro k hk d h1 h2
    simp only [List.range'_succ, List.map_cons, uParamNrAux]
    by_cases hd : d = k
    · subst hd; simp only [strEq_nVar, BEq.rfl, ↓reduceIte]
    · have : strEq (nVar (np - 1 - k)) (nVar (np - 1 - d)) = false := by
        simp only [strEq_nVar, beq_eq_false_iff_ne]; omega
      simp only [this, Bool.false_eq_true, ite_false]
      exact ih (k + 1) (by omega) d (by omega) (by omega)

/-! ### Held locks -/

theorem eindeutigAux_sub : ∀ (xs seen : List String) (y : String), y ∈ uEindeutigAux xs seen → y ∈ xs
  | [], _, y, h => by simp only [uEindeutigAux, List.not_mem_nil] at h
  | x :: xs, seen, y, h => by
    simp only [uEindeutigAux] at h
    split at h
    · exact List.mem_cons_of_mem _ (eindeutigAux_sub xs seen y h)
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (eindeutigAux_sub xs (x :: seen) y h)

theorem eindeutigAux_voll : ∀ (xs seen : List String) (y : String), y ∈ xs →
    (seen.any (strEq · y)) = true ∨ ((uEindeutigAux xs seen).any (strEq · y)) = true
  | [], _, y, h => by simp only [List.not_mem_nil] at h
  | x :: xs, seen, y, h => by
    simp only [uEindeutigAux]
    simp only [List.mem_cons] at h
    split
    · rename_i hs
      rcases h with rfl | h
      · exact Or.inl hs
      · exact eindeutigAux_voll xs seen y h
    · rcases h with rfl | h
      · right; simp only [strEq_eq, List.any_cons, decide_true, Bool.true_or]
      · rcases eindeutigAux_voll xs (x :: seen) y h with h' | h'
        · simp only [List.any_cons, Bool.or_eq_true] at h'
          rcases h' with h' | h'
          · right; simp only [List.any_cons, h', Bool.true_or]
          · left; exact h'
        · right; simp only [List.any_cons, h', Bool.or_true]

theorem eindeutig_sub {xs : List String} {y : String} (h : y ∈ uEindeutig xs) : y ∈ xs :=
  eindeutigAux_sub xs [] y h

theorem eindeutig_voll {xs : List String} {y : String} (h : y ∈ xs) : ((uEindeutig xs).any (strEq · y)) = true := by
  rcases eindeutigAux_voll xs [] y h with h' | h'
  · simp only [List.any_nil, Bool.false_eq_true] at h'
  · exact h'

/-! ### Clauses -/

/-- The clauses the delaborator prints: `requires`, `ensures`, `effects`. -/
def KlauselOk : SKlausel → Prop
  | .needs _ => True
  | .gives _ => True
  | .effs _ => True
  | _ => False

/-- A clause the generator writes carries no `decreases` measure. -/
theorem klauselOk_dropsOf {k : SKlausel} (h : KlauselOk k) : dropsOf k = none := by
  cases k <;> simp_all [KlauselOk, dropsOf]

theorem ohneKlauselForm_ok : ∀ (ks : List SKlausel), (∀ k ∈ ks, KlauselOk k) → uOhneKlauselForm ks = .ok ()
  | [], _ => rfl
  | k :: ks, h => by
    have hk := h k List.mem_cons_self
    have ih := ohneKlauselForm_ok ks (fun k' hm => h k' (List.mem_cons_of_mem _ hm))
    cases k <;> simp_all [KlauselOk, uOhneKlauselForm]

/-- Clauses with no `requires Held(..)`. -/
theorem gehalten_ohne (locks : List ULock) : ∀ (ks : List SKlausel),
    (∀ k ∈ ks, ∀ args, k ≠ .needs (.call "Held" args)) → uGehalten locks ks = .ok []
  | [], _ => rfl
  | k :: ks, h => by
    have hk := h k List.mem_cons_self
    have ih := gehalten_ohne locks ks (fun k' hm => h k' (List.mem_cons_of_mem _ hm))
    cases k with
    | needs e =>
      cases e with
      | call c args =>
        by_cases hc : c = "Held"
        · subst hc; exact absurd rfl (hk args)
        · rw [uGehalten.eq_3 _ _ _ (by intro a h; cases h; exact hc rfl)]; exact ih
      | _ => simpa [uGehalten] using ih
    | _ => simpa [uGehalten] using ih

theorem gehaltenAux_ok (locks : List ULock) : ∀ (ls : List String),
    (∀ l ∈ ls, ∃ lk, locks.find? (fun x => strEq x.name l) = some lk) →
    uGehaltenAux locks (ls.map SExpr.variable) = .ok ls
  | [], _ => rfl
  | l :: ls, h => by
    obtain ⟨lk, hlk⟩ := h l List.mem_cons_self
    simp only [List.map_cons, uGehaltenAux, hlk,
      gehaltenAux_ok locks ls (fun l' hm => h l' (List.mem_cons_of_mem _ hm))]

theorem stelle_fremd : ∀ (ns : List String) (p : String), (∀ n ∈ ns, strEq n p = false) → ∃ e, uStelle ns p = .error e
  | [], p, _ => ⟨_, rfl⟩
  | q :: ns, p, h => by
    obtain ⟨e, he⟩ := stelle_fremd ns p (fun n hm => h n (List.mem_cons_of_mem _ hm))
    exact ⟨e, by simp only [uStelle, h q List.mem_cons_self, Bool.false_eq_true, ↓reduceIte, he]⟩

/-! ### Effects -/

/-- What the effect reader needs of the head and the item lists. -/
structure EffOk (kopf : UFnKopf) (tabs : List UTab) (globs : List UGlob) : Prop where
  namen : ∀ n ∈ kopf.names, RumpfName n
  griffe : ∀ g ∈ kopf.griffe, g.2.1 = "d"
  tabsOk : ∀ tb ∈ tabs, tb.arena = false ∧ ∃ i, tb.name = nTab i

theorem griffOrt_nein {kopf : UFnKopf} {tabs : List UTab} {globs : List UGlob} (h : EffOk kopf tabs globs)
    (x : String) (hx : x.toList.head? ≠ some 'd') : uIstGriffOrt kopf (.variable x) = false := by
  simp only [uIstGriffOrt, List.any_eq_false]
  intro g hg
  rw [h.griffe g hg]
  intro he
  have : ("d" : String) = x := by simpa [strEq_eq] using he
  subst this
  exact hx rfl

theorem eff_tab {kopf : UFnKopf} {tabs : List UTab} {locks : List ULock} {globs : List UGlob}
    (h : EffOk kopf tabs globs) (i : Nat) (tb : UTab) (hf : tabs.find? (fun x => strEq x.name (nTab i)) = some tb)
    (hn : tb.name = nTab i) (rest : List SEffekt) :
    uEffekteAux kopf tabs locks globs (.writes (.field (.variable (nTab i)) "slots") :: rest) =
      (uEffekteAux kopf tabs locks globs rest).map fun r => { r with puts := nTab i :: r.puts } := by
  have hg : uIstGriffOrt kopf (.field (.variable (nTab i)) "slots") = false := by
    simp only [uIstGriffOrt]
    exact griffOrt_nein h _ (by simp only [nTab_toList, ↓Char.isValue, Nat.toString_eq_repr, Nat.toList_repr, List.head?_cons, ne_eq,
  Option.some.injEq, Char.reduceEq, not_false_eq_true])
  obtain ⟨e, he⟩ := stelle_fremd kopf.names (nTab i) (fun n hm => strEq_rumpf_nTab (h.namen n hm) i)
  have hs : strEq "slots" "slots" = true := by decide
  simp only [uEffekteAux, hg, Bool.false_eq_true, ite_false, uSchreibtOrt, hs, Bool.not_true, he, hf, hn]
  cases uEffekteAux kopf tabs locks globs rest <;> rfl

theorem eff_glob {kopf : UFnKopf} {tabs : List UTab} {locks : List ULock} {globs : List UGlob}
    (h : EffOk kopf tabs globs) (i : Nat) (hg : globs.any (fun x => strEq x.name (nGlob i)) = true)
    (rest : List SEffekt) :
    uEffekteAux kopf tabs locks globs (.writes (.variable (nGlob i)) :: rest) =
      (uEffekteAux kopf tabs locks globs rest).map fun r => { r with gputs := nGlob i :: r.gputs } := by
  have hgr : uIstGriffOrt kopf (.variable (nGlob i)) = false := griffOrt_nein h _ (by simp only [nGlob_toList, ↓Char.isValue, Nat.toString_eq_repr, Nat.toList_repr, List.head?_cons, ne_eq,
  Option.some.injEq, Char.reduceEq, not_false_eq_true])
  have ha : (tabs.any fun x => x.arena && strEq x.name (nGlob i)) = false := by
    rw [List.any_eq_false]; intro tb hm; simp only [(h.tabsOk tb hm).1, Bool.false_and, Bool.false_eq_true, not_false_eq_true]
  have hn : (kopf.names.any (strEq · (nGlob i))) = false := by
    rw [List.any_eq_false]; intro n hm; simp only [strEq_rumpf_nGlob (h.namen n hm) i, Bool.false_eq_true, not_false_eq_true]
  have ht : (tabs.any fun x => strEq x.name (nGlob i)) = false := by
    rw [List.any_eq_false]; intro tb hm
    obtain ⟨j, hj⟩ := (h.tabsOk tb hm).2
    rw [hj]; simp only [strEq_kopf (nTab_toList j) (nGlob_toList i) (by decide), Bool.false_eq_true, not_false_eq_true]
  simp only [uEffekteAux, hgr, Bool.false_eq_true, ite_false, ha, uIstGlobName, hn, ht, hg, Bool.not_false,
    Bool.and_self, ite_true]
  cases uEffekteAux kopf tabs locks globs rest <;> rfl

theorem eff_lock {kopf : UFnKopf} {tabs : List UTab} {locks : List ULock} {globs : List UGlob}
    (l : String) (lk : ULock) (hl : locks.find? (fun x => strEq x.name l) = some lk) (rest : List SEffekt) :
    uEffekteAux kopf tabs locks globs (.locks false (.variable l) :: rest) =
      (uEffekteAux kopf tabs locks globs rest).map fun r => { r with locks := l :: r.locks } := by
  simp only [uEffekteAux, hl]
  cases uEffekteAux kopf tabs locks globs rest <;> rfl

theorem eff_alle {kopf : UFnKopf} {tabs : List UTab} {locks : List ULock} {globs : List UGlob}
    (h : EffOk kopf tabs globs) :
    ∀ (ts gs : List Nat) (ls : List String),
      (∀ i ∈ ts, ∃ tb, tabs.find? (fun x => strEq x.name (nTab i)) = some tb ∧ tb.name = nTab i) →
      (∀ i ∈ gs, globs.any (fun x => strEq x.name (nGlob i)) = true) →
      (∀ l ∈ ls, ∃ lk, locks.find? (fun x => strEq x.name l) = some lk) →
      uEffekteAux kopf tabs locks globs (ts.map (fun i => .writes (.field (.variable (nTab i)) "slots")) ++
        gs.map (fun i => .writes (.variable (nGlob i))) ++ ls.map (fun l => .locks false (.variable l))) =
        .ok { locks := ls, puts := ts.map nTab, gputs := gs.map nGlob } := by
  intro ts gs ls ht hg hl
  induction ts with
  | cons i ts ih =>
    obtain ⟨tb, hf, hn⟩ := ht i List.mem_cons_self
    simp only [List.map_cons, List.cons_append]
    rw [eff_tab h i tb hf hn, ih (fun j hj => ht j (List.mem_cons_of_mem _ hj))]
    rfl
  | nil =>
    simp only [List.map_nil, List.nil_append]
    induction gs with
    | cons i gs ih =>
      simp only [List.map_cons, List.cons_append]
      rw [eff_glob h i (hg i List.mem_cons_self) _, ih (fun j hj => hg j (List.mem_cons_of_mem _ hj))]
      rfl
    | nil =>
      simp only [List.map_nil, List.nil_append]
      induction ls with
      | cons l ls ih =>
        obtain ⟨lk, hlk⟩ := hl l List.mem_cons_self
        simp only [List.map_cons]
        rw [eff_lock l lk hlk _, ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))]
        rfl
      | nil => rfl

/-! ### The head -/

section Kopf
variable (z : Spez)

/-- The result range of a result type. -/
def ergBereich : Option Ty → Option (Int × Int)
  | some (.int lo hi) => some (lo, hi)
  | _ => none

/-- The reason channel of a function: the position of its reason type and its number of cases. -/
def kanalVon (gNr : Nat → Nat) (n : Nat) : Option (Nat × Nat) := if n = 0 then none else some (gNr n, n)

/-- The printed parameter list with the device handle. -/
def mitGriffPs (ps : List (String × STyp)) (mitGriff : Bool) : List (String × STyp) :=
  ps ++ (if mitGriff then [("d", .atom "Dev")] else [])

/-- **The head the elaborator reads** for a printed function. -/
def kopfVon (gNr : Nat → Nat) (devs : List String) (f : z.deklaration.Fn) (ps : List (String × STyp))
    (ks : List UParamArt) (mitGriff : Bool) : UFnKopf :=
  let S := z.deklaration.signatur f
  let np := S.params.length
  { name := nFn (fN z f), names := (List.range' 0 np).map (fun i => nVar (np - 1 - i)), kinds := ks,
    types := S.params, res := ergBereich S.erg, resBool := decide (S.erg = some .bool),
    kanal := kanalVon gNr S.gruende, bits := ps.map (fun p => uParamBreite p.2),
    held := uEindeutig (heldNamen z f), gputs := uEindeutig ((gNamen z f).map nGlob),
    griffe := uGriffe devs 0 (mitGriffPs ps mitGriff) }

/-- What the head reader needs of the item lists and the printed clauses. -/
structure KopfVor (gNr : Nat → Nat) (P : Programm z.deklaration) (f : z.deklaration.Fn) (tabs : List UTab)
    (locks : List ULock) (globs : List UGlob) (whys : List UWhy) (devs : List String) (mitGriff : Bool)
    (req ens : List SKlausel) : Prop where
  devsOk : ∀ d ∈ devs, d = "Dev"
  griff : mitGriff = true → "Dev" ∈ devs
  erg : ∀ t, (z.deklaration.signatur f).erg = some t → (artErg t).isSome
  held : ∀ l ∈ heldNamen z f, ∃ lk, locks.find? (fun x => strEq x.name l) = some lk
  sperren : ∀ l ∈ lNamen z P f, ∃ lk, locks.find? (fun x => strEq x.name l) = some lk
  tab : ∀ i ∈ tNamen z f, ∃ tb, tabs.find? (fun x => strEq x.name (nTab i)) = some tb ∧ tb.name = nTab i
  glob : ∀ i ∈ gNamen z f, globs.any (fun x => strEq x.name (nGlob i)) = true
  tabsOk : ∀ tb ∈ tabs, tb.arena = false ∧ ∃ i, tb.name = nTab i
  why : (z.deklaration.signatur f).gruende ≠ 0 → ∃ w,
    whys.findIdx? (fun x => strEq x.name (nGrund (z.deklaration.signatur f).gruende)) =
      some (gNr (z.deklaration.signatur f).gruende) ∧
    whys[gNr (z.deklaration.signatur f).gruende]? = some w ∧ w.cases.length = (z.deklaration.signatur f).gruende
  klauseln : ∀ k ∈ req ++ ens, KlauselOk k ∧ (∀ args, k ≠ .needs (.call "Held" args)) ∧ (∀ es, k ≠ .effs es)

theorem wirkungen_ohne : ∀ (ks : List SKlausel), (∀ k ∈ ks, ∀ es, k ≠ .effs es) → uEffekte.uWirkungen ks = []
  | [], _ => rfl
  | k :: ks, h => by
    have hk := h k List.mem_cons_self
    have ih := wirkungen_ohne ks (fun k' hm => h k' (List.mem_cons_of_mem _ hm))
    cases k with
    | effs es => exact absurd rfl (hk es)
    | _ => simpa [uEffekte.uWirkungen] using ih

theorem wirkungen_append (a b : List SKlausel) :
    uEffekte.uWirkungen (a ++ b) = uEffekte.uWirkungen a ++ uEffekte.uWirkungen b := by
  induction a with
  | nil => rfl
  | cons k a ih => cases k <;> simp only [List.cons_append, uEffekte.uWirkungen, ih, List.append_assoc]

theorem griffe_append (devs : List String) : ∀ (ps q : List (String × STyp)) (k : Nat),
    (∀ p ∈ ps, uGriffTyp devs p.2 = none) → uGriffe devs k (ps ++ q) = uGriffe devs (k + ps.length) q
  | [], q, k, _ => by simp only [List.nil_append, List.length_nil, add_zero]
  | p :: ps, q, k, h => by
    simp only [List.cons_append, uGriffe, h p List.mem_cons_self]
    rw [griffe_append devs ps q (k + 1) (fun p' hm => h p' (List.mem_cons_of_mem _ hm))]
    simp only [Nat.add_assoc, Nat.add_comm 1, List.length_cons]

theorem griffe_d (devs : List String) (k : Nat) (b : Bool) :
    ∀ g ∈ uGriffe devs k (if b then [("d", STyp.atom "Dev")] else []), g.2.1 = "d" ∧ k ≤ g.1 := by
  intro g hg
  cases b with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, uGriffe, List.not_mem_nil] at hg
  | true =>
    simp only [ite_true, uGriffe] at hg
    split at hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg; simp only [Std.le_refl, and_self]
    · simp only [List.not_mem_nil] at hg

theorem mapM_length {α β : Type} (g : α → Option β) : ∀ (xs : List α) (ys : List β), xs.mapM g = some ys →
    ys.length = xs.length
  | [], ys, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq, List.nil_eq] at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hx : g x with
    | none => simp only [hx, Option.bind_none, reduceCtorEq] at h
    | some y =>
    cases hr : xs.mapM g with
    | none => simp only [hx, hr, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at h
    | some r =>
    simp only [hx, hr, Option.bind_some, Option.some.injEq] at h
    subst h
    simp only [List.length_cons, mapM_length g xs r hr, Nat.add_left_cancel_iff]

theorem tripel_proj {α β γ : Type} (as : List α) (bs : List β) (cs : List γ) (h1 : as.length = bs.length)
    (h2 : cs.length = bs.length) :
    let T := (as.zip (bs.zip cs)).map fun (n, t, k) => (n, t, k)
    T.map (·.1) = as ∧ T.map (·.2.1) = bs ∧ T.map (·.2.2) = cs := by
  induction as generalizing bs cs with
  | nil => cases bs <;> simp_all
  | cons a as ih =>
    cases bs with
    | nil => simp only [List.length_cons, List.length_nil, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero,
  and_false] at h1
    | cons b bs =>
      cases cs with
      | nil => simp only [List.length_nil, List.length_cons, Nat.right_eq_add, Nat.add_eq_zero_iff, List.length_eq_zero_iff,
  one_ne_zero, and_false] at h2
      | cons c cs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
        obtain ⟨i1, i2, i3⟩ := ih bs cs h1 h2
        simp_all

end Kopf
end Gabbro.Grammatik.Gen.Text
