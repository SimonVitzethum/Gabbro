module

public import Grammatik.Gen.Text.Invers.Geraet
public import Grammatik.Gen.Text.Invers.Rumpf_satzFaelle.Basis

@[expose] public section

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

set_option maxHeartbeats 4000000 in
theorem rumpf_satz_stmt : ∀ {z : Spez} {V : Vertrag z.deklaration}
  (gNr : ℕ → ℕ) (tabs : List UTab) (koepfe : List UFnKopf),
  (∀ (m : z.deklaration.Marke), False) →
    KInv (z := z) gNr koepfe →
      KIdx (z := z) koepfe →
        ∀ (n : ℕ),
          (∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} (s : Stmt z.deklaration V l Γ Λ Λ') (ctx : UCtx)
              (art : ℕ → UParamArt) (ss : List SAnw) (us : List UStmt),
              sizeOf s < n →
                SInv z V ctx Γ Λ art →
                  delabS z V s = Except.ok ss →
                    uOfSt z V gNr art s = some us →
                      Λ' = Λ ∧
                        ss.length ≤ 2 ∧
                          ∃ ctx',
                            SInv z V ctx' Γ Λ art ∧
                              ∀ (f : ℕ) (tail : List SAnw) (xs : List UStmt) (cE : UCtx),
                                sizeOf s < f →
                                  uAnwReihe tabs koepfe f ctx' tail = Except.ok (xs, cE) →
                                    uAnwReihe tabs koepfe (f + ss.length) ctx (ss ++ tail) = Except.ok (us ++ xs, cE)) →
            (∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} (b : Block z.deklaration V l Γ Λ Λ') (ctx : UCtx)
                (art : ℕ → UParamArt) (f : ℕ) (ss : List SAnw) (us : List UStmt),
                sizeOf b < n →
                  sizeOf b < f →
                    SInv z V ctx Γ Λ art →
                      delabB z V b = Except.ok ss →
                        uOfBl z V gNr art b = some us →
                          Λ' = Λ ∧ ∃ cE, uAnwReihe tabs koepfe f ctx ss = Except.ok (us, cE)) →
              (∀ {l : Bool} {Γ : Ctx} {Λ : List (Res z.deklaration)} (e : Endblock z.deklaration V l Γ Λ) (ctx : UCtx)
                  (art : ℕ → UParamArt) (f : ℕ) (es : List SAnw) (en : Option SEnde) (us : List UStmt) (r : URet),
                  sizeOf e < n →
                    sizeOf e < f →
                      SInv z V ctx Γ Λ art →
                        delabEnd z V e = Except.ok (es, en) →
                          uOfEnd z V gNr art e = some (us, r) →
                            ∃ cE,
                              uAnwReihe tabs koepfe f ctx es = Except.ok (us, cE) ∧
                                uEnde cE en = Except.ok r ∧ ∃ v, en = some (SEnde.ret v)) →
                ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} (s : Stmt z.deklaration V l Γ Λ Λ')
                  (ctx : UCtx) (art : ℕ → UParamArt) (ss : List SAnw) (us : List UStmt),
                  sizeOf s < n + 1 →
                    SInv z V ctx Γ Λ art →
                      delabS z V s = Except.ok ss →
                        uOfSt z V gNr art s = some us →
                          Λ' = Λ ∧
                            ss.length ≤ 2 ∧
                              ∃ ctx',
                                SInv z V ctx' Γ Λ art ∧
                                  ∀ (f : ℕ) (tail : List SAnw) (xs : List UStmt) (cE : UCtx),
                                    sizeOf s < f →
                                      uAnwReihe tabs koepfe f ctx' tail = Except.ok (xs, cE) →
                                        uAnwReihe tabs koepfe (f + ss.length) ctx (ss ++ tail) =
                                          Except.ok (us ++ xs, cE) := by
  intro z V gNr tabs koepfe hM hK hI n ihS ihB ihE
  intro l Γ Λ Λ' s ctx art ss us hn H hd hu
  cases s with
  | assignSlot t fd i e hw hL =>
    simp only [delabS] at hd
    cases hi : delabE z none i with
    | error _ => simp only [bind, Except.bind, hi, reduceCtorEq] at hd
    | ok i' =>
    cases he : delabE z none e with
    | error _ => simp only [bind, Except.bind, hi, he, reduceCtorEq] at hd
    | ok se =>
    simp only [hi, he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfSt] at hu
    cases hx : uOfIdx z art none (tN z t) (z.deklaration.count t) i with
    | none => simp only [hx, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some ix =>
    have hix := idx_ok H.einv t (sizeOf i + 1) i (by omega) i' ix hi hx
    have ha := anw1_slot H tabs koepfe t fd i' se ix hix hL
    refine ⟨rfl, by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceLeDiff], ctx, H, fun f tail xs cE hf ht => ?_⟩
    simp only [List.length_singleton, List.singleton_append]
    simp only [hx, Option.bind_eq_bind, Option.bind_some] at hu
    split at hu
    · rename_i hb
      cases hv : uOfB z art none e with
      | none => simp only [hv, Option.bind_none, reduceCtorEq] at hu
      | some v =>
      simp only [hv, Option.bind_some, Option.some.injEq] at hu; subst hu
      exact reihe_anw1 tabs koepfe f ctx _ se tail _ xs cE (ha.1 hb v (bool_ok H.einv e se v he hv)) ht
    · rename_i hb
      cases hv : uOfS z art none e with
      | none => simp only [hv, Option.bind_none, reduceCtorEq] at hu
      | some v =>
      simp only [hv, Option.bind_some, Option.some.injEq] at hu; subst hu
      exact reihe_anw1 tabs koepfe f ctx _ se tail _ xs cE (ha.2 hb v (wert_ok H.einv e se v he hv)) ht
  | assignGlob g e hw hL =>
    simp only [delabS] at hd
    cases he : delabE z none e with
    | error _ => simp only [bind, Except.bind, he, reduceCtorEq] at hd
    | ok se =>
    simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfSt] at hu
    split at hu
    · simp only [reduceCtorEq] at hu
    · rename_i hat
      have ha := anw1_glob H tabs koepfe g (by simpa using hat) se
      refine ⟨rfl, by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceLeDiff], ctx, H, fun f tail xs cE hf ht => ?_⟩
      simp only [List.length_singleton, List.singleton_append]
      split at hu
      · rename_i hb
        cases hv : uOfB z art none e with
        | none => simp only [hv, Option.map_none, reduceCtorEq] at hu
        | some v =>
        simp only [hv, Option.map_some, Option.some.injEq] at hu; subst hu
        exact reihe_anw1 tabs koepfe f ctx _ se tail _ xs cE (ha.1 hb v (bool_ok H.einv e se v he hv)) ht
      · rename_i hb
        cases hv : uOfS z art none e with
        | none => simp only [hv, Option.map_none, reduceCtorEq] at hu
        | some v =>
        simp only [hv, Option.map_some, Option.some.injEq] at hu; subst hu
        exact reihe_anw1 tabs koepfe f ctx _ se tail _ xs cE (ha.2 hb v (wert_ok H.einv e se v he hv)) ht
  | ret e hΛ =>
    simp only [delabS] at hd
    cases hv : delabR z e with
    | error _ => simp only [bind, Except.bind, hv, reduceCtorEq] at hd
    | ok v =>
    simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfSt] at hu
    cases hr : uOfR z art e with
    | none => simp only [hr, Option.map_none, reduceCtorEq] at hu
    | some r =>
    simp only [hr, Option.map_some, Option.some.injEq] at hu; subst hu
    exact ⟨rfl, by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceLeDiff], ctx, H, fun f tail xs cE hf ht => by
      simpa using reihe_ret tabs koepfe f ctx v tail r xs cE (ende_ok H rfl e v r hv hr) ht⟩
  | retWhy r hΛ =>
    simp only [delabS, Except.ok.injEq] at hd
    subst hd
    simp only [uOfSt, Option.some.injEq] at hu; subst hu
    exact ⟨rfl, by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceLeDiff], ctx, H, fun f tail xs cE hf ht => by
      simpa using reihe_ret tabs koepfe f ctx _ tail _ xs cE (ende_why H r) ht⟩
  | ite c t e =>
    simp only [delabS] at hd
    cases hc : delabE z none c with
    | error _ => simp only [bind, Except.bind, hc, reduceCtorEq] at hd
    | ok sc =>
    cases ht : delabB z V t with
    | error _ => simp only [bind, Except.bind, hc, ht, reduceCtorEq] at hd
    | ok st =>
    cases he : delabB z V e with
    | error _ => simp only [bind, Except.bind, hc, ht, he, reduceCtorEq] at hd
    | ok se =>
    simp only [hc, ht, he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfSt] at hu
    cases hcv : uOfB z art none c with
    | none => simp only [hcv, List.cons_append, List.nil_append, List.append_assoc, Option.bind_eq_bind, Option.bind_none,
reduceCtorEq] at hu
    | some cv =>
    cases htu : uOfBl z V gNr art t with
    | none => simp only [hcv, htu, List.cons_append, List.nil_append, List.append_assoc, Option.bind_eq_bind,
Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some tu =>
    cases heu : uOfBl z V gNr art e with
    | none => simp only [hcv, htu, heu, List.cons_append, List.nil_append, List.append_assoc, Option.bind_eq_bind,
Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some eu =>
    simp only [hcv, htu, heu, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Stmt.ite.sizeOf_spec, Bool.sizeOf_eq_one] at hn
    have hΛ := (ihB t ctx art (sizeOf t + 1) st tu (by omega) (by omega) H ht htu).1
    refine ⟨hΛ, by simp only [List.isEmpty_iff, List.length_cons, List.length_nil, zero_add, Nat.reduceLeDiff], ctx, H, fun f tail xs cE hf hr => ?_⟩
    simp only [Stmt.ite.sizeOf_spec, Bool.sizeOf_eq_one] at hf
    simp only [List.length_singleton, List.singleton_append]
    obtain ⟨_, cB, hT⟩ := ihB t ctx art f st tu (by omega) (by omega) H ht htu
    obtain ⟨_, c2, hE⟩ := ihB e ctx art f se eu (by omega) (by omega) H he heu
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
        simp only [List.isEmpty_nil, ↓reduceIte, hE.1, and_self]
      · right
        exact ⟨se, c2, by simp only [hs, Bool.false_eq_true, ↓reduceIte], hE⟩
    have := reihe_cond tabs koepfe f ctx sc st _ tail cv tu eu xs cB cE (bool_ok H.einv c sc cv hc hcv) hT hE' hr
    simpa [List.append_assoc] using this
  | locks L hr body =>
    simp only [delabS] at hd
    cases hb : delabB z V body with
    | error _ => simp only [bind, Except.bind, hb, reduceCtorEq] at hd
    | ok sb =>
    simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfSt] at hu
    cases hbu : uOfBl z V gNr art body with
    | none => simp only [hbu, List.cons_append, List.nil_append, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some bu =>
    simp only [hbu, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Stmt.locks.sizeOf_spec, Bool.sizeOf_eq_one, sizeOf_default, add_zero] at hn
    refine ⟨rfl, by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceLeDiff], ctx, H, fun f tail xs cE hf hr => ?_⟩
    simp only [Stmt.locks.sizeOf_spec, Bool.sizeOf_eq_one, sizeOf_default, add_zero] at hf
    simp only [List.length_singleton, List.singleton_append]
    obtain ⟨_, cB, hB⟩ := ihB body _ art f sb bu (by omega) (by omega) (H.lock L) hb hbu
    obtain ⟨lk, hlk⟩ := H.lockFind L
    have := reihe_locks tabs koepfe f ctx _ sb tail lk bu xs cB cE hlk hB hr
    simpa [List.append_assoc] using this
  | traverse t inv body =>
    simp only [delabS] at hd
    cases hb : delabB z V body with
    | error _ =>
      simp only [hb, bind, Except.bind] at hd
      split at hd
      · simp only [pure, Except.pure, reduceCtorEq] at hd
      · cases hp : delabE z none inv <;> simp only [hp, reduceCtorEq, pure, Except.pure] at hd
    | ok sb =>
    simp only [uOfSt] at hu
    cases hiv : uOfB z art none inv with
    | none => simp only [hiv, List.cons_append, List.nil_append, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some iv =>
    cases hbu : uOfBl z V gNr (artAuf (.index (tN z t)) art) body with
    | none => simp only [hiv, hbu, List.cons_append, List.nil_append, Option.bind_eq_bind, Option.bind_none,
Option.bind_fun_none, reduceCtorEq] at hu
    | some bu =>
    simp only [hiv, hbu, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Stmt.traverse.sizeOf_spec, Bool.sizeOf_eq_one, sizeOf_default, add_zero] at hn
    have hk : ∃ i', (∃ x, ss = [.each (nVar Γ.length) none "slots" (.variable (nTab (tN z t))) "unvisited" "" i'
        (.block sb none)] ∧ x = ()) ∧ ((i' = none ∧ iv = .tru) ∨ ∃ p, i' = some p ∧ uBool ctx p = .ok iv) := by
      split at hd
      · simp only [hb, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hd
        subst hd
        simp only [uOfB, Option.some.injEq] at hiv
        exact ⟨none, ⟨(), rfl, rfl⟩, Or.inl ⟨rfl, hiv.symm⟩⟩
      · cases hp : delabE z none inv with
        | error _ => simp only [bind, Except.bind, hp, reduceCtorEq] at hd
        | ok p =>
        simp only [hp, hb, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at hd
        subst hd
        exact ⟨some p, ⟨(), rfl, rfl⟩, Or.inr ⟨p, rfl, bool_ok H.einv inv p iv hp hiv⟩⟩
    obtain ⟨i', ⟨_, hss, _⟩, hi⟩ := hk
    subst hss
    obtain ⟨cnt, hkopf⟩ := schleifenKopf_ok H t i' iv hi
    have H' := H.push (.index (z.deklaration.count t)) (.index (tN z t)) (.index cnt) 0 ctx.muts
      (nVar Γ.length :: ctx.loops) H.muts
    refine ⟨rfl, by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceLeDiff], ctx, H, fun f tail xs cE hf hr => ?_⟩
    simp only [Stmt.traverse.sizeOf_spec, Bool.sizeOf_eq_one, sizeOf_default, add_zero] at hf
    simp only [List.length_singleton, List.singleton_append]
    obtain ⟨_, cB, hB⟩ := ihB body _ _ f sb bu (by omega) (by omega) H' hb hbu
    have := reihe_each tabs koepfe f ctx _ _ _ i' sb tail _ iv bu xs cB cE hkopf hB hr
    simpa [List.append_assoc] using this
  | call f args hp hr =>
    simp only [delabS] at hd
    cases ha : delabA z args with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok as =>
    simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfSt] at hu
    cases hx : uOfArgs z art args with
    | none => simp only [hx, Option.map_none, reduceCtorEq] at hu
    | some xs =>
    simp only [hx, Option.map_some, Option.some.injEq] at hu
    subst hu
    obtain ⟨k, hf, hKP⟩ := hK f
    refine ⟨nach_ohne_marken hM _ Λ, by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceLeDiff], ctx, H, fun g tail ys cE hg ht => ?_⟩
    simp only [List.length_singleton, List.singleton_append]
    exact reihe_call tabs koepfe g ctx _ as tail _ ys cE (anw1_call H tabs f k hf hKP hp.hh hr args as xs ha hx) ht
  | callInd p args hp hr =>
    simp only [uOfSt] at hu
    split at hu
    · rename_i f _
      split at hu
      · rename_i hn
        subst hn
        simp only [delabS] at hd
        cases ha : delabA z args with
        | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
        | ok as =>
        simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
        subst hd
        cases hx : uOfArgs z art args with
        | none => simp only [hx, Option.map_none, reduceCtorEq] at hu
        | some xs =>
        simp only [hx, Option.map_some, Option.some.injEq] at hu
        subst hu
        obtain ⟨k, hf, hKP⟩ := hK f
        obtain ⟨i, hi, hk⟩ := kinv_idx (gNr := gNr) hf
        have hiE : i = z.deklaration.sig f := by rw [hI f] at hi; exact (Option.some.inj hi).symm
        subst hiE
        have H' := H.pushZ Γ.length (.fnptr (z.deklaration.sig f)) (.fnptr (z.deklaration.sig f)) 0 ctx.loops
        refine ⟨nach_ohne_marken hM _ Λ, by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Std.le_refl], _, H', fun g tail ys cE hg ht => ?_⟩
        have h2 := reihe_call tabs koepfe g _ _ as tail _ ys cE
          (anw1_callInd H tabs f k _ hf hk hKP hp.hh hr args as xs ha hx (H.zb f) Γ.length ctx.loops) ht
        have h1 := reihe_bind tabs koepfe (g + 1) ctx _ _ _ _ _ _ cE
          (bindWert_fnref H tabs f k _ hi hk hKP (nZeiger Γ.length)) h2
        simpa using h1
      · simp only [reduceCtorEq] at hu
    · simp only [reduceCtorEq] at hu
  | regWrite r hk e =>
    simp only [delabS] at hd
    cases he : delabE z none e with
    | error _ => simp only [bind, Except.bind, he, reduceCtorEq] at hd
    | ok se =>
    simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    have ha := anw1_regWrite H tabs koepfe r se
    refine ⟨rfl, by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceLeDiff], ctx, H, fun f tail xs cE hf ht => ?_⟩
    simp only [List.length_singleton, List.singleton_append]
    simp only [uOfSt] at hu
    split at hu
    · rename_i hb
      cases hv : uOfB z art none e with
      | none => simp only [hv, Option.map_none, reduceCtorEq] at hu
      | some v =>
      simp only [hv, Option.map_some, Option.some.injEq] at hu; subst hu
      exact reihe_anw1 tabs koepfe f ctx _ se tail _ xs cE (ha.1 hb v (bool_ok H.einv e se v he hv)) ht
    · rename_i hb
      cases hv : uOfS z art none e with
      | none => simp only [hv, Option.map_none, reduceCtorEq] at hu
      | some v =>
      simp only [hv, Option.map_some, Option.some.injEq] at hu; subst hu
      exact reihe_anw1 tabs koepfe f ctx _ se tail _ xs cE (ha.2 hb v (wert_ok H.einv e se v he hv)) ht
  | publish g e payload hp hw hL =>
    subst hp
    simp only [delabS] at hd
    cases he : delabE z none e with
    | error _ => simp only [bind, Except.bind, he, reduceCtorEq] at hd
    | ok se =>
    simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfSt] at hu
    split at hu
    · rename_i hat
      have ha := anw1_publish H tabs koepfe g hat se
      refine ⟨rfl, by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceLeDiff], ctx, H, fun f tail xs cE hf ht => ?_⟩
      simp only [List.length_singleton, List.singleton_append]
      split at hu
      · rename_i hb
        cases hv : uOfB z art none e with
        | none => simp only [hv, Option.map_none, reduceCtorEq] at hu
        | some v =>
        simp only [hv, Option.map_some, Option.some.injEq] at hu; subst hu
        exact reihe_emit tabs koepfe f ctx _ se _ tail _ xs cE (ha.1 hb v (bool_ok H.einv e se v he hv)) ht
      · rename_i hb
        cases hv : uOfS z art none e with
        | none => simp only [hv, Option.map_none, reduceCtorEq] at hu
        | some v =>
        simp only [hv, Option.map_some, Option.some.injEq] at hu; subst hu
        exact reihe_emit tabs koepfe f ctx _ se _ tail _ xs cE (ha.2 hb v (wert_ok H.einv e se v he hv)) ht
    · simp only [reduceCtorEq] at hu
  | _ => simp only [uOfSt, reduceCtorEq] at hu

end Gabbro.Grammatik.Gen.Text
