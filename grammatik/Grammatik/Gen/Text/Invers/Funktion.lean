/-
  File:      Grammatik/Gen/Text/Invers/Funktion.lean
  Subject:   ONE FUNCTION READ BACK (Tier 2.1, step 3): the head (`elabKopf`: parameters, held locks, reason
             channel, effects, result) and the whole function (`elabUFunktion`: `requires`, `ensures`, body) of a
             printed function are the plain data computed from the model -- given the elaborated item lists
             (`LInv`, against the accessors of the declaration).
-/
import Grammatik.Gen.Text.Invers.Rumpf

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

/-! ### Parameters -/

theorem schranke_zahlE (als : List (String × (Int × Int))) (n : Int) : uSchranke als (zahlE n) = some n := by
  unfold zahlE
  split
  · rename_i h; simp [uSchranke, Int.toNat_of_nonneg h]
  · rename_i h; simp [uSchranke, Int.toNat_of_nonneg (show 0 ≤ -n by omega)]

theorem typS_art {otab : Int → Option Nat} {t : Ty} {st : STyp} {a : UParamArt} (ht : typS otab t = .ok st) (ha : artErg t = some a)
    (als : List (String × (Int × Int))) (tabs : List UTab) (sums : List USum) (whys : List UWhy)
    (zeiger : List String) (zb : Nat) (n : String) :
    uParam als tabs sums whys zeiger zb (n, st) = .ok (n, t, a) := by
  cases t with
  | int lo hi =>
    simp only [artErg, Option.some.injEq] at ha; subst ha
    simp only [typS, Except.ok.injEq] at ht; subst ht
    simp [uParam, uTyp, schranke_zahlE, uArtVon]
  | bool =>
    simp only [artErg, Option.some.injEq] at ha; subst ha
    simp only [typS, Except.ok.injEq] at ht; subst ht
    rfl
  | _ => simp [artErg] at ha

theorem typS_griff {otab : Int → Option Nat} {t : Ty} {st : STyp} (ht : typS otab t = .ok st) (ha : (artErg t).isSome)
    (devs : List String) (hd : ∀ d ∈ devs, d = "Dev") : uGriffTyp devs st = none := by
  cases t with
  | int lo hi => simp only [typS, Except.ok.injEq] at ht; subst ht; rfl
  | bool =>
    simp only [typS, Except.ok.injEq] at ht; subst ht
    have : (devs.any fun x => strEq x "bool") = false := by
      rw [List.any_eq_false]; intro d hm; rw [hd d hm]; decide
    simp [uGriffTyp, this]
  | _ => simp [artErg] at ha

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
    simp [uOhneGriffe, uSeq]
  | cons t ts ih =>
    intro j ps ks hp hk
    simp only [parListe] at hp
    cases ht : typS otab t with
    | error _ => simp [ht, bind, Except.bind] at hp
    | ok st =>
    cases hr : parListe otab np (j + 1) ts with
    | error _ => simp [ht, hr, bind, Except.bind] at hp
    | ok pr =>
    simp only [ht, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hk
    cases ha : artErg t with
    | none => simp [ha] at hk
    | some a =>
    cases hks : ts.mapM artErg with
    | none => simp [ha, hks] at hk
    | some kr =>
    simp only [ha, hks, Option.bind_some, Option.some.injEq] at hk
    subst hk
    obtain ⟨h1, h2⟩ := ih (j + 1) pr kr hr hks
    refine ⟨?_, ?_⟩
    · simp only [uOhneGriffe, List.filter_cons, typS_griff ht (by simp [ha]) devs hd, Option.isNone_none, ite_true]
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
    · subst hd; simp
    · have : strEq (nVar (np - 1 - k)) (nVar (np - 1 - d)) = false := by
        simp only [strEq_nVar, beq_eq_false_iff_ne]; omega
      simp only [this, Bool.false_eq_true, ite_false]
      exact ih (k + 1) (by omega) d (by omega) (by omega)

/-! ### Held locks -/

theorem eindeutigAux_sub : ∀ (xs seen : List String) (y : String), y ∈ uEindeutigAux xs seen → y ∈ xs
  | [], _, y, h => by simp [uEindeutigAux] at h
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
  | [], _, y, h => by simp at h
  | x :: xs, seen, y, h => by
    simp only [uEindeutigAux]
    simp only [List.mem_cons] at h
    split
    · rename_i hs
      rcases h with rfl | h
      · exact Or.inl hs
      · exact eindeutigAux_voll xs seen y h
    · rcases h with rfl | h
      · right; simp [strEq_eq]
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
  · simp at h'
  · exact h'

/-! ### Clauses -/

/-- The clauses the delaborator prints: `requires`, `ensures`, `effects`. -/
def KlauselOk : SKlausel → Prop
  | .needs _ => True
  | .gives _ => True
  | .effs _ => True
  | _ => False

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
    exact ⟨e, by simp [uStelle, h q List.mem_cons_self, he]⟩

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
    exact griffOrt_nein h _ (by simp [nTab_toList])
  obtain ⟨e, he⟩ := stelle_fremd kopf.names (nTab i) (fun n hm => strEq_rumpf_nTab (h.namen n hm) i)
  have hs : strEq "slots" "slots" = true := by decide
  simp only [uEffekteAux, hg, Bool.false_eq_true, ite_false, uSchreibtOrt, hs, Bool.not_true, he, hf, hn]
  cases uEffekteAux kopf tabs locks globs rest <;> rfl

theorem eff_glob {kopf : UFnKopf} {tabs : List UTab} {locks : List ULock} {globs : List UGlob}
    (h : EffOk kopf tabs globs) (i : Nat) (hg : globs.any (fun x => strEq x.name (nGlob i)) = true)
    (rest : List SEffekt) :
    uEffekteAux kopf tabs locks globs (.writes (.variable (nGlob i)) :: rest) =
      (uEffekteAux kopf tabs locks globs rest).map fun r => { r with gputs := nGlob i :: r.gputs } := by
  have hgr : uIstGriffOrt kopf (.variable (nGlob i)) = false := griffOrt_nein h _ (by simp [nGlob_toList])
  have ha : (tabs.any fun x => x.arena && strEq x.name (nGlob i)) = false := by
    rw [List.any_eq_false]; intro tb hm; simp [(h.tabsOk tb hm).1]
  have hn : (kopf.names.any (strEq · (nGlob i))) = false := by
    rw [List.any_eq_false]; intro n hm; simp [strEq_rumpf_nGlob (h.namen n hm) i]
  have ht : (tabs.any fun x => strEq x.name (nGlob i)) = false := by
    rw [List.any_eq_false]; intro tb hm
    obtain ⟨j, hj⟩ := (h.tabsOk tb hm).2
    rw [hj]; simp [strEq_kopf (nTab_toList j) (nGlob_toList i) (by decide)]
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
  | cons k a ih => cases k <;> simp [uEffekte.uWirkungen, ih]

theorem griffe_append (devs : List String) : ∀ (ps q : List (String × STyp)) (k : Nat),
    (∀ p ∈ ps, uGriffTyp devs p.2 = none) → uGriffe devs k (ps ++ q) = uGriffe devs (k + ps.length) q
  | [], q, k, _ => by simp
  | p :: ps, q, k, h => by
    simp only [List.cons_append, uGriffe, h p List.mem_cons_self]
    rw [griffe_append devs ps q (k + 1) (fun p' hm => h p' (List.mem_cons_of_mem _ hm))]
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem griffe_d (devs : List String) (k : Nat) (b : Bool) :
    ∀ g ∈ uGriffe devs k (if b then [("d", STyp.atom "Dev")] else []), g.2.1 = "d" ∧ k ≤ g.1 := by
  intro g hg
  cases b with
  | false => simp [uGriffe] at hg
  | true =>
    simp only [ite_true, uGriffe] at hg
    split at hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; subst hg; simp
    · simp at hg

theorem mapM_length {α β : Type} (g : α → Option β) : ∀ (xs : List α) (ys : List β), xs.mapM g = some ys →
    ys.length = xs.length
  | [], ys, h => by simp at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hx : g x with
    | none => simp [hx] at h
    | some y =>
    cases hr : xs.mapM g with
    | none => simp [hx, hr] at h
    | some r =>
    simp only [hx, hr, Option.bind_some, Option.some.injEq] at h
    subst h
    simp [mapM_length g xs r hr]

theorem tripel_proj {α β γ : Type} (as : List α) (bs : List β) (cs : List γ) (h1 : as.length = bs.length)
    (h2 : cs.length = bs.length) :
    let T := (as.zip (bs.zip cs)).map fun (n, t, k) => (n, t, k)
    T.map (·.1) = as ∧ T.map (·.2.1) = bs ∧ T.map (·.2.2) = cs := by
  induction as generalizing bs cs with
  | nil => cases bs <;> simp_all
  | cons a as ih =>
    cases bs with
    | nil => simp at h1
    | cons b bs =>
      cases cs with
      | nil => simp at h2
      | cons c cs =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
        obtain ⟨i1, i2, i3⟩ := ih bs cs h1 h2
        simp_all

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
        klauseln := klauselnVon z P f req ens } devs zeiger zb =
      .ok (kopfVon z gNr devs f ps ks mitGriff, uEindeutig ((tNamen z f).map nTab)) := by
  set S := z.deklaration.signatur f with hS
  set np := S.params.length with hnp
  obtain ⟨hfilt, hseq⟩ := parListe_ok (optTab z) np als tabs sums whys zeiger zb devs hV.devsOk S.params 0 ps ks hps hks
  have hlen := mapM_length artErg S.params ks hks
  obtain ⟨p1, p2, p3⟩ := tripel_proj ((List.range' 0 S.params.length).map fun i => nVar (np - 1 - i)) S.params ks
    (by simp) hlen
  -- the device handle is dropped
  have hog : uOhneGriffe devs (mitGriffPs ps mitGriff) = ps := by
    unfold mitGriffPs
    unfold uOhneGriffe at hfilt ⊢
    rw [List.filter_append, hfilt]
    cases mitGriff with
    | false => simp
    | true =>
      simp [uGriffTyp]
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
      simp [hrest]
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
    · simp [hg, kanalVon]
    · obtain ⟨w, hw1, hw2, hw3⟩ := hV.why hg
      rw [← hS] at hw1 hw2 hw3
      have hne : w.cases.isEmpty = false := by
        cases hc : w.cases with
        | nil => rw [hc] at hw3; simp at hw3; exact absurd hw3.symm hg
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
    · rename_i he; simp [uEffekte.uWirkungen, List.isEmpty_iff.1 he]
    · simp [uEffekte.uWirkungen]
  have heff : ∀ (kopf : UFnKopf), EffOk kopf tabs globs →
      uEffekte kopf tabs locks globs (klauselnVon z P f req ens) =
        .ok { locks := lNamen z P f, puts := (tNamen z f).map nTab, gputs := (gNamen z f).map nGlob } := by
    intro kopf hE
    unfold uEffekte
    simp only [hwirk, effListe]
    exact eff_alle hE _ _ _ hV.tab hV.glob hV.sperren
  have himpl : strEq "impl" "impl" = true := by decide
  unfold elabKopf
  simp only [hog, himpl, Bool.not_true, Bool.false_eq_true, ite_false, hok, hseq, hgeh]
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
      simp [hnp]
    · rename_i t ht
      cases t with
      | bool =>
        simp only [typS, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres; subst hres
        simp only [kopfVon, ← hS, ht, ergBereich, p1, p2, p3]
        simp [hnp]
      | int lo hi =>
        simp only [typS, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hres; subst hres
        simp only [kopfVon, ← hS, ht, ergBereich, p1, p2, p3, uErgBereich, schranke_zahlE]
        simp [hnp]
      | _ => have := hV.erg _ (by rw [← hS]; exact ht); simp [artErg] at this

end Kopf

end Gabbro.Grammatik.Gen.Text