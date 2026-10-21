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

theorem typS_art {t : Ty} {st : STyp} {a : UParamArt} (ht : typS t = .ok st) (ha : artErg t = some a)
    (als : List (String × (Int × Int))) (tabs : List UTab) (sums : List USum) (n : String) :
    uParam als tabs sums (n, st) = .ok (n, t, a) := by
  cases t with
  | int lo hi =>
    simp only [artErg, Option.some.injEq] at ha; subst ha
    simp only [typS, Except.ok.injEq] at ht; subst ht
    simp [uParam, uTyp, schranke_zahlE]
  | bool =>
    simp only [artErg, Option.some.injEq] at ha; subst ha
    simp only [typS, Except.ok.injEq] at ht; subst ht
    rfl
  | _ => simp [artErg] at ha

theorem typS_griff {t : Ty} {st : STyp} (ht : typS t = .ok st) (ha : (artErg t).isSome)
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
theorem parListe_ok (np : Nat) (als : List (String × (Int × Int))) (tabs : List UTab) (sums : List USum)
    (devs : List String) (hd : ∀ d ∈ devs, d = "Dev") :
    ∀ (ts : List Ty) (j : Nat) (ps : List (String × STyp)) (ks : List UParamArt),
      parListe np j ts = .ok ps → ts.mapM artErg = some ks →
      uOhneGriffe devs ps = ps ∧
      uSeq (ps.map (uParam als tabs sums)) =
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
    cases ht : typS t with
    | error _ => simp [ht, bind, Except.bind] at hp
    | ok st =>
    cases hr : parListe np (j + 1) ts with
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
    · simp only [List.map_cons, uSeq, typS_art ht ha als tabs sums, h2, List.length_cons, List.range'_succ,
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

end Gabbro.Grammatik.Gen.Text