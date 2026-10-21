/-
  File:      Grammatik/Gen/Text/Invers/Rumpf.lean
  Subject:   THE BODY READ BACK (Tier 2.1, step 2): for every statement, block and end block of the fragment of
             `uOfSt`/`uOfBl`/`uOfEnd`, in every context `SInv` describes, the elaborator's run reader `uAnwReihe`
             (with fuel above the term's size) builds exactly the plain statements `uOf*` computes from the model
             term, and `uEnde` the trailing return; the fragment keeps the held resources (`Λ' = Λ`).
-/
import Grammatik.Gen.Text.Invers.Anweisung

namespace Gabbro.Grammatik.Gen.Text

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

variable {z : Spez} {V : Vertrag z.deklaration} (tabs : List UTab) (koepfe : List UFnKopf)

/-- What the run reader does with a printed statement, a block, an end block (of size below `n`). -/
def RumpfSatz (n : Nat) : Prop :=
  (∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} (s : Stmt z.deklaration V l Γ Λ Λ') (ctx : UCtx)
      (art : Nat → UParamArt) (f : Nat) (ss : List SAnw) (us : List UStmt),
      sizeOf s < n → sizeOf s < f → SInv z V ctx Γ Λ art → delabS z V s = .ok ss → uOfSt z V art s = some us →
      Λ' = Λ ∧ ∃ x, ss = [x] ∧ ∀ tail xs cE, uAnwReihe tabs koepfe f ctx tail = .ok (xs, cE) →
        uAnwReihe tabs koepfe (f + 1) ctx (x :: tail) = .ok (us ++ xs, cE)) ∧
  (∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} (b : Block z.deklaration V l Γ Λ Λ') (ctx : UCtx)
      (art : Nat → UParamArt) (f : Nat) (ss : List SAnw) (us : List UStmt),
      sizeOf b < n → sizeOf b < f → SInv z V ctx Γ Λ art → delabB z V b = .ok ss → uOfBl z V art b = some us →
      Λ' = Λ ∧ ∃ cE, uAnwReihe tabs koepfe f ctx ss = .ok (us, cE)) ∧
  (∀ {l : Bool} {Γ : Ctx} {Λ : List (Res z.deklaration)} (e : Endblock z.deklaration V l Γ Λ) (ctx : UCtx)
      (art : Nat → UParamArt) (f : Nat) (es : List SAnw) (en : Option SEnde) (us : List UStmt) (r : URet),
      sizeOf e < n → sizeOf e < f → SInv z V ctx Γ Λ art → delabEnd z V e = .ok (es, en) →
      uOfEnd z V art e = some (us, r) →
      ∃ cE, uAnwReihe tabs koepfe f ctx es = .ok (us, cE) ∧ uEnde cE en = .ok r)

theorem rumpf_satz (n : Nat) : RumpfSatz (z := z) (V := V) tabs koepfe n := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ _ h => by omega, fun _ _ _ _ _ _ h => by omega, fun _ _ _ _ _ _ _ _ h => by omega⟩
  | succ n ih =>
  obtain ⟨ihS, ihB, ihE⟩ := ih
  refine ⟨?_, ?_, ?_⟩
  · intro l Γ Λ Λ' s ctx art f ss us hn hf H hd hu
    cases s with
    | assignSlot t fd i e hw hL =>
      simp only [delabS] at hd
      cases hi : delabE z none i with
      | error _ => simp [hi, bind, Except.bind] at hd
      | ok i' =>
      cases he : delabE z none e with
      | error _ => simp [hi, he, bind, Except.bind] at hd
      | ok se =>
      simp only [hi, he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      simp only [uOfSt] at hu
      cases hx : uOfIdx z art none (tN z t) (z.deklaration.count t) i with
      | none => simp [hx] at hu
      | some ix =>
      have hix := idx_ok H.einv none t (sizeOf i + 1) i (by omega) i' ix hi hx
      have ha := anw1_slot H tabs koepfe t fd i' se ix hix hL
      refine ⟨rfl, _, rfl, fun tail xs cE ht => ?_⟩
      simp only [hx, Option.bind_eq_bind, Option.bind_some] at hu
      split at hu
      · rename_i hb
        cases hv : uOfB z art none e with
        | none => simp [hv] at hu
        | some v =>
        simp only [hv, Option.bind_some, Option.some.injEq] at hu; subst hu
        exact reihe_anw1 tabs koepfe f ctx _ se tail _ xs cE (ha.1 hb v (bool_ok H.einv e se v he hv)) ht
      · rename_i hb
        cases hv : uOfS z art none e with
        | none => simp [hv] at hu
        | some v =>
        simp only [hv, Option.bind_some, Option.some.injEq] at hu; subst hu
        exact reihe_anw1 tabs koepfe f ctx _ se tail _ xs cE (ha.2 hb v (wert_ok H.einv e se v he hv)) ht
    | assignGlob g e hw hL =>
      simp only [delabS] at hd
      cases he : delabE z none e with
      | error _ => simp [he, bind, Except.bind] at hd
      | ok se =>
      simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      simp only [uOfSt] at hu
      split at hu
      · simp at hu
      · rename_i hat
        have ha := anw1_glob H tabs koepfe g (by simpa using hat) se
        refine ⟨rfl, _, rfl, fun tail xs cE ht => ?_⟩
        split at hu
        · rename_i hb
          cases hv : uOfB z art none e with
          | none => simp [hv] at hu
          | some v =>
          simp only [hv, Option.map_some, Option.some.injEq] at hu; subst hu
          exact reihe_anw1 tabs koepfe f ctx _ se tail _ xs cE (ha.1 hb v (bool_ok H.einv e se v he hv)) ht
        · rename_i hb
          cases hv : uOfS z art none e with
          | none => simp [hv] at hu
          | some v =>
          simp only [hv, Option.map_some, Option.some.injEq] at hu; subst hu
          exact reihe_anw1 tabs koepfe f ctx _ se tail _ xs cE (ha.2 hb v (wert_ok H.einv e se v he hv)) ht
    | ret e hΛ =>
      simp only [delabS] at hd
      cases hv : delabR z e with
      | error _ => simp [hv, bind, Except.bind] at hd
      | ok v =>
      simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      simp only [uOfSt] at hu
      cases hr : uOfR z art e with
      | none => simp [hr] at hu
      | some r =>
      simp only [hr, Option.map_some, Option.some.injEq] at hu; subst hu
      exact ⟨rfl, _, rfl, fun tail xs cE ht => reihe_ret tabs koepfe f ctx v tail r xs cE (ende_ok H rfl e v r hv hr) ht⟩
    | retWhy r hΛ =>
      simp only [delabS, Except.ok.injEq] at hd
      subst hd
      simp only [uOfSt, Option.some.injEq] at hu; subst hu
      exact ⟨rfl, _, rfl, fun tail xs cE ht => reihe_ret tabs koepfe f ctx _ tail _ xs cE (ende_why H r) ht⟩
    | ite c t e =>
      simp only [delabS] at hd
      cases hc : delabE z none c with
      | error _ => simp [hc, bind, Except.bind] at hd
      | ok sc =>
      cases ht : delabB z V t with
      | error _ => simp [hc, ht, bind, Except.bind] at hd
      | ok st =>
      cases he : delabB z V e with
      | error _ => simp [hc, ht, he, bind, Except.bind] at hd
      | ok se =>
      simp only [hc, ht, he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      simp only [uOfSt] at hu
      cases hcv : uOfB z art none c with
      | none => simp [hcv] at hu
      | some cv =>
      cases htu : uOfBl z V art t with
      | none => simp [hcv, htu] at hu
      | some tu =>
      cases heu : uOfBl z V art e with
      | none => simp [hcv, htu, heu] at hu
      | some eu =>
      simp only [hcv, htu, heu, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
      subst hu
      simp at hn hf
      obtain ⟨hΛ, cB, hT⟩ := ihB t ctx art f st tu (by omega) (by omega) H ht htu
      obtain ⟨_, c2, hE⟩ := ihB e ctx art f se eu (by omega) (by omega) H he heu
      refine ⟨hΛ, _, rfl, fun tail xs cE hr => ?_⟩
      have hE' : ((if se.isEmpty then none else some (SAnw.block se none)) = none ∧ eu = []) ∨
          ∃ ss2 c2, (if se.isEmpty then none else some (SAnw.block se none)) = some (.block ss2 none) ∧
            uAnwReihe tabs koepfe f ctx ss2 = .ok (eu, c2) := by
        by_cases hs : se.isEmpty
        · left
          have : se = [] := List.isEmpty_iff.1 hs
          subst this
          obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
          rw [reihe_nil] at hE
          simp only [Except.ok.injEq, Prod.mk.injEq] at hE
          simp [hE.1]
        · right
          exact ⟨se, c2, by simp [hs], hE⟩
      have := reihe_cond tabs koepfe f ctx sc st _ tail cv tu eu xs cB cE (bool_ok H.einv c sc cv hc hcv) hT hE' hr
      simpa [List.append_assoc] using this
    | locks L hr body =>
      simp only [delabS] at hd
      cases hb : delabB z V body with
      | error _ => simp [hb, bind, Except.bind] at hd
      | ok sb =>
      simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      simp only [uOfSt] at hu
      cases hbu : uOfBl z V art body with
      | none => simp [hbu] at hu
      | some bu =>
      simp only [hbu, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
      subst hu
      simp at hn hf
      obtain ⟨_, cB, hB⟩ := ihB body _ art f sb bu (by omega) (by omega) (H.lock L) hb hbu
      obtain ⟨lk, hlk⟩ := H.lockFind L
      refine ⟨rfl, _, rfl, fun tail xs cE hr => ?_⟩
      have := reihe_locks tabs koepfe f ctx _ sb tail lk bu xs cB cE hlk hB hr
      simpa [List.append_assoc] using this
    | traverse t inv body =>
      simp only [delabS] at hd
      cases hb : delabB z V body with
      | error _ =>
        simp only [hb, bind, Except.bind] at hd
        split at hd
        · simp [pure, Except.pure] at hd
        · cases hp : delabE z none inv <;> simp [hp, pure, Except.pure] at hd
      | ok sb =>
      simp only [uOfSt] at hu
      cases hiv : uOfB z art none inv with
      | none => simp [hiv] at hu
      | some iv =>
      cases hbu : uOfBl z V (artAuf (.index (tN z t)) art) body with
      | none => simp [hiv, hbu] at hu
      | some bu =>
      simp only [hiv, hbu, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
      subst hu
      simp at hn hf
      have hk : ∃ i', (∃ x, ss = [.each (nVar Γ.length) none "slots" (.variable (nTab (tN z t))) "unvisited" "" i'
          (.block sb none)] ∧ x = ()) ∧ ((i' = none ∧ iv = .tru) ∨ ∃ p, i' = some p ∧ uBool ctx p = .ok iv) := by
        split at hd
        · simp only [hb, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hd
          subst hd
          simp only [uOfB, Option.some.injEq] at hiv
          exact ⟨none, ⟨(), rfl, rfl⟩, Or.inl ⟨rfl, hiv.symm⟩⟩
        · cases hp : delabE z none inv with
          | error _ => simp [hp, bind, Except.bind] at hd
          | ok p =>
          simp only [hp, hb, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hd
          subst hd
          exact ⟨some p, ⟨(), rfl, rfl⟩, Or.inr ⟨p, rfl, bool_ok H.einv inv p iv hp hiv⟩⟩
      obtain ⟨i', ⟨_, hss, _⟩, hi⟩ := hk
      subst hss
      obtain ⟨cnt, hkopf⟩ := schleifenKopf_ok H t i' iv hi
      have H' := H.push (.index (z.deklaration.count t)) (.index (tN z t)) (.index cnt) 0 ctx.muts
        (nVar Γ.length :: ctx.loops) H.muts
      obtain ⟨_, cB, hB⟩ := ihB body _ _ f sb bu (by omega) (by omega) H' hb hbu
      refine ⟨rfl, _, rfl, fun tail xs cE hr => ?_⟩
      have := reihe_each tabs koepfe f ctx _ _ _ i' sb tail _ iv bu xs cB cE hkopf hB hr
      simpa [List.append_assoc] using this
    | _ => simp [uOfSt] at hu
  · intro l Γ Λ Λ' b ctx art f ss us hn hf H hd hu
    cases b with
    | nil =>
      simp only [delabB, Except.ok.injEq] at hd; subst hd
      simp only [uOfBl, Option.some.injEq] at hu; subst hu
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      exact ⟨rfl, ctx, reihe_nil tabs koepfe f' ctx⟩
    | cons s rest =>
      simp only [delabB] at hd
      cases hs : delabS z V s with
      | error _ => simp [hs, bind, Except.bind] at hd
      | ok ss1 =>
      cases hr : delabB z V rest with
      | error _ => simp [hs, hr, bind, Except.bind] at hd
      | ok ss2 =>
      simp only [hs, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      simp only [uOfBl] at hu
      cases hus : uOfSt z V art s with
      | none => simp [hus] at hu
      | some us1 =>
      cases hur : uOfBl z V art rest with
      | none => simp [hus, hur] at hu
      | some us2 =>
      simp only [hus, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
      subst hu
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      simp at hn hf
      obtain ⟨hΛ, x, hx, hstep⟩ := ihS s ctx art f' ss1 us1 (by omega) (by omega) H hs hus
      subst hx
      subst hΛ
      obtain ⟨hΛ2, cE, hrest⟩ := ihB rest ctx art f' ss2 us2 (by omega) (by omega) H hr hur
      exact ⟨hΛ2, cE, hstep ss2 us2 cE hrest⟩
    | bind e rest =>
      rename_i τ
      simp only [delabB] at hd
      cases he : delabE z none e with
      | error _ => simp [he, bind, Except.bind] at hd
      | ok se =>
      cases hr : delabB z V rest with
      | error _ => simp [he, hr, bind, Except.bind] at hd
      | ok ss2 =>
      simp only [he, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
      subst hd
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      simp at hn hf
      simp only [uOfBl] at hu
      split at hu
      · cases hb : uOfB z art none e with
        | none => simp [hb] at hu
        | some b =>
        cases hur : uOfBl z V (artAuf .bool art) rest with
        | none => simp [hb, hur] at hu
        | some us2 =>
        simp only [hb, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
        subst hu
        have H' := H.push τ .bool .bool 0 [] ctx.loops rfl
        obtain ⟨hΛ2, cE, hrest⟩ := ihB rest _ _ f' ss2 us2 (by omega) (by omega) H' hr hur
        exact ⟨hΛ2, cE, reihe_bind tabs koepfe f' ctx _ _ se ss2 _ us2 cE
          (bindWert_bool H tabs koepfe e se b he hb) hrest⟩
      · cases hb : uOfS z art none e with
        | none => simp [hb] at hu
        | some b =>
        cases hur : uOfBl z V (artAuf .int art) rest with
        | none => simp [hb, hur] at hu
        | some us2 =>
        simp only [hb, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
        subst hu
        have H' := H.push τ .int (.int 0 0) 0 [] ctx.loops rfl
        obtain ⟨hΛ2, cE, hrest⟩ := ihB rest _ _ f' ss2 us2 (by omega) (by omega) H' hr hur
        exact ⟨hΛ2, cE, reihe_bind tabs koepfe f' ctx _ _ se ss2 _ us2 cE
          (bindWert_int H tabs koepfe e se b he hb) hrest⟩
    | _ => simp [uOfBl] at hu
  · intro l Γ Λ e ctx art f es en us r hn hf H hd hu
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    cases e with
    | ret e hΛ =>
      simp only [delabEnd] at hd
      cases hv : delabR z e with
      | error _ => simp [hv, bind, Except.bind] at hd
      | ok v =>
      simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      simp only [uOfEnd] at hu
      cases hr : uOfR z art e with
      | none => simp [hr] at hu
      | some r' =>
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      exact ⟨ctx, reihe_nil tabs koepfe f' ctx, ende_ok H rfl e v r' hv hr⟩
    | retWhy r' hΛ =>
      simp only [delabEnd, Except.ok.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      simp only [uOfEnd, Option.some.injEq, Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      exact ⟨ctx, reihe_nil tabs koepfe f' ctx, ende_why H r'⟩
    | cons s rest =>
      simp only [delabEnd] at hd
      cases hs : delabS z V s with
      | error _ => simp [hs, bind, Except.bind] at hd
      | ok ss1 =>
      cases hr : delabEnd z V rest with
      | error _ => simp [hs, hr, bind, Except.bind] at hd
      | ok p =>
      obtain ⟨rs, en'⟩ := p
      simp only [hs, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      simp only [uOfEnd] at hu
      cases hus : uOfSt z V art s with
      | none => simp [hus] at hu
      | some us1 =>
      cases hur : uOfEnd z V art rest with
      | none => simp [hus, hur] at hu
      | some q =>
      obtain ⟨us2, r2⟩ := q
      simp only [hus, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      simp at hn hf
      obtain ⟨hΛ, x, hx, hstep⟩ := ihS s ctx art f' ss1 us1 (by omega) (by omega) H hs hus
      subst hx; subst hΛ
      obtain ⟨cE, hrest, hende⟩ := ihE rest ctx art f' rs en' us2 r2 (by omega) (by omega) H hr hur
      exact ⟨cE, hstep rs us2 cE hrest, hende⟩
    | bind e rest =>
      rename_i τ
      simp only [delabEnd] at hd
      cases he : delabE z none e with
      | error _ => simp [he, bind, Except.bind] at hd
      | ok se =>
      cases hr : delabEnd z V rest with
      | error _ => simp [he, hr, bind, Except.bind] at hd
      | ok p =>
      obtain ⟨rs, en'⟩ := p
      simp only [he, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      simp at hn hf
      simp only [uOfEnd] at hu
      split at hu
      · cases hb : uOfB z art none e with
        | none => simp [hb] at hu
        | some b =>
        cases hur : uOfEnd z V (artAuf .bool art) rest with
        | none => simp [hb, hur] at hu
        | some q =>
        obtain ⟨us2, r2⟩ := q
        simp only [hb, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        have H' := H.push τ .bool .bool 0 [] ctx.loops rfl
        obtain ⟨cE, hrest, hende⟩ := ihE rest _ _ f' rs en' us2 r2 (by omega) (by omega) H' hr hur
        exact ⟨cE, reihe_bind tabs koepfe f' ctx _ _ se rs _ us2 cE (bindWert_bool H tabs koepfe e se b he hb) hrest,
          hende⟩
      · cases hb : uOfS z art none e with
        | none => simp [hb] at hu
        | some b =>
        cases hur : uOfEnd z V (artAuf .int art) rest with
        | none => simp [hb, hur] at hu
        | some q =>
        obtain ⟨us2, r2⟩ := q
        simp only [hb, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        have H' := H.push τ .int (.int 0 0) 0 [] ctx.loops rfl
        obtain ⟨cE, hrest, hende⟩ := ihE rest _ _ f' rs en' us2 r2 (by omega) (by omega) H' hr hur
        exact ⟨cE, reihe_bind tabs koepfe f' ctx _ _ se rs _ us2 cE (bindWert_int H tabs koepfe e se b he hb) hrest,
          hende⟩
    | _ => simp [uOfEnd] at hu

end Gabbro.Grammatik.Gen.Text
