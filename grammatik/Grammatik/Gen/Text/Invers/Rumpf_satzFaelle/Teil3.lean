module

public import Grammatik.Gen.Text.Invers.Geraet
public import Grammatik.Gen.Text.Invers.Rumpf_satzFaelle.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

set_option maxHeartbeats 4000000 in
theorem rumpf_satz_ende : ∀ {z : Spez} {V : Vertrag z.deklaration}
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
                ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res z.deklaration)} (e : Endblock z.deklaration V l Γ Λ) (ctx : UCtx)
                  (art : ℕ → UParamArt) (f : ℕ) (es : List SAnw) (en : Option SEnde) (us : List UStmt) (r : URet),
                  sizeOf e < n + 1 →
                    sizeOf e < f →
                      SInv z V ctx Γ Λ art →
                        delabEnd z V e = Except.ok (es, en) →
                          uOfEnd z V gNr art e = some (us, r) →
                            ∃ cE,
                              uAnwReihe tabs koepfe f ctx es = Except.ok (us, cE) ∧
                                uEnde cE en = Except.ok r ∧ ∃ v, en = some (SEnde.ret v) := by
  intro z V gNr tabs koepfe hM hK hI n ihS ihB ihE
  intro l Γ Λ e ctx art f es en us r hn hf H hd hu
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  cases e with
  | ret e hΛ =>
    simp only [delabEnd] at hd
    cases hv : delabR z e with
    | error _ => simp only [bind, Except.bind, hv, reduceCtorEq] at hd
    | ok v =>
    simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [uOfEnd] at hu
    cases hr : uOfR z art e with
    | none => simp only [hr, Option.map_none, reduceCtorEq] at hu
    | some r' =>
    simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    exact ⟨ctx, reihe_nil tabs koepfe f' ctx, ende_ok H rfl e v r' hv hr, v, rfl⟩
  | retWhy r' hΛ =>
    simp only [delabEnd, Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [uOfEnd, Option.some.injEq, Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    exact ⟨ctx, reihe_nil tabs koepfe f' ctx, ende_why H r', _, rfl⟩
  | cons s rest =>
    simp only [delabEnd] at hd
    cases hs : delabS z V s with
    | error _ => simp only [bind, Except.bind, hs, reduceCtorEq] at hd
    | ok ss1 =>
    cases hr : delabEnd z V rest with
    | error _ => simp only [bind, Except.bind, hs, hr, reduceCtorEq] at hd
    | ok p =>
    obtain ⟨rs, en'⟩ := p
    simp only [hs, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [uOfEnd] at hu
    cases hus : uOfSt z V gNr art s with
    | none => simp only [hus, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some us1 =>
    cases hur : uOfEnd z V gNr art rest with
    | none => simp only [hus, hur, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some q =>
    obtain ⟨us2, r2⟩ := q
    simp only [hus, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    simp only [Endblock.cons.sizeOf_spec, Bool.sizeOf_eq_one, Nat.reduceAdd] at hn hf
    obtain ⟨hΛ, hlen, ctx', H', hstep⟩ := ihS s ctx art ss1 us1 (by omega) H hs hus
    subst hΛ
    obtain ⟨g, hg⟩ : ∃ g, f' + 1 = g + ss1.length := ⟨f' + 1 - ss1.length, by omega⟩
    obtain ⟨cE, hrest, hende, hv⟩ := ihE rest ctx' art g rs en' us2 r2 (by omega) (by omega) H' hr hur
    exact ⟨cE, hg ▸ hstep g rs us2 cE (by omega) hrest, hende, hv⟩
  | bind e rest =>
    rename_i τ
    simp only [delabEnd] at hd
    cases he : delabE z none e with
    | error _ => simp only [bind, Except.bind, he, reduceCtorEq] at hd
    | ok se =>
    cases hr : delabEnd z V rest with
    | error _ => simp only [bind, Except.bind, he, hr, reduceCtorEq] at hd
    | ok p =>
    obtain ⟨rs, en'⟩ := p
    simp only [he, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [Endblock.bind.sizeOf_spec, Bool.sizeOf_eq_one] at hn hf
    simp only [uOfEnd] at hu
    split at hu
    · cases hb : uOfB z art none e with
      | none => simp only [hb, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
      | some b =>
      cases hur : uOfEnd z V gNr (artAuf .bool art) rest with
      | none => simp only [hb, hur, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
      | some q =>
      obtain ⟨us2, r2⟩ := q
      simp only [hb, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      have H' := H.push τ .bool .bool 0 [] ctx.loops rfl trivial
      obtain ⟨cE, hrest, hende, hv⟩ := ihE rest _ _ f' rs en' us2 r2 (by omega) (by omega) H' hr hur
      exact ⟨cE, reihe_bind tabs koepfe f' ctx _ _ se rs _ us2 cE (bindWert_bool H tabs koepfe e se b he hb) hrest,
        hende, hv⟩
    · cases hb : uOfS z art none e with
      | none => simp only [hb, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
      | some b =>
      cases hur : uOfEnd z V gNr (artAuf .int art) rest with
      | none => simp only [hb, hur, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
      | some q =>
      obtain ⟨us2, r2⟩ := q
      simp only [hb, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      have H' := H.push τ .int (.int 0 0) 0 [] ctx.loops rfl trivial
      obtain ⟨cE, hrest, hende, hv⟩ := ihE rest _ _ f' rs en' us2 r2 (by omega) (by omega) H' hr hur
      exact ⟨cE, reihe_bind tabs koepfe f' ctx _ _ se rs _ us2 cE (bindWert_int H tabs koepfe e se b he hb) hrest,
        hende, hv⟩
  | bindCall fk args he hp hr rest =>
    rename_i τ
    simp only [delabEnd] at hd
    cases ha : delabA z args with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok as =>
    cases hr' : delabEnd z V rest with
    | error _ => simp only [bind, Except.bind, ha, hr', reduceCtorEq] at hd
    | ok p =>
    obtain ⟨rs, en'⟩ := p
    simp only [ha, hr', bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [uOfEnd] at hu
    cases hτ : artErg τ with
    | none => simp only [hτ, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some a =>
    cases hx : uOfArgs z art args with
    | none => simp only [hτ, hx, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some xs =>
    cases hur : uOfEnd z V gNr (artAuf a art) rest with
    | none => simp only [hτ, hx, Option.bind_eq_bind, Option.bind_some, hur, Option.bind_none, reduceCtorEq] at hu
    | some q =>
    obtain ⟨us2, r2⟩ := q
    simp only [hτ, hx, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    simp only [Endblock.bindCall.sizeOf_spec, Bool.sizeOf_eq_one, sizeOf_default, add_zero] at hn hf
    obtain ⟨k, hfk, hKP⟩ := hK fk
    obtain ⟨ty, hmeta, hb⟩ := bindWert_call H tabs fk k hfk hKP hp.hh hr τ he a hτ args as xs ha hx (nVar Γ.length)
    have hN : nach z.deklaration fk Λ = Λ := nach_ohne_marken hM _ Λ
    have H' : SInv z V (ctxMit ctx (nVar Γ.length) a ty 0 [] ctx.loops) (τ :: Γ) (nach z.deklaration fk Λ)
        (artAuf a art) := by rw [hN]; exact H.push τ a ty 0 [] ctx.loops rfl hmeta
    obtain ⟨cE, hrest, hende, hv⟩ := ihE rest _ _ f' rs en' us2 r2 (by omega) (by omega) H' hr' hur
    exact ⟨cE, reihe_bind tabs koepfe f' ctx _ _ _ rs _ us2 cE hb hrest, hende, hv⟩
  | bindCallElse fk args he hp hr err rest =>
    rename_i τ
    simp only [delabEnd] at hd
    cases ha : delabA z args with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok as =>
    cases hde : delabEnd z V err with
    | error _ => simp only [bind, Except.bind, ha, hde, reduceCtorEq] at hd
    | ok q =>
    obtain ⟨es, ende⟩ := q
    cases hr' : delabEnd z V rest with
    | error _ => simp only [bind, Except.bind, ha, hde, hr', reduceCtorEq] at hd
    | ok p =>
    obtain ⟨rs, en'⟩ := p
    simp only [ha, hde, hr', bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [uOfEnd] at hu
    cases hτ : artErg τ with
    | none => simp only [hτ, List.cons_append, List.nil_append, List.append_assoc, Option.bind_eq_bind, Option.bind_none,
reduceCtorEq] at hu
    | some a =>
    cases hx : uOfArgs z art args with
    | none => simp only [hτ, hx, List.cons_append, List.nil_append, List.append_assoc, Option.bind_eq_bind,
Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some xs =>
    cases hue : uOfEnd z V gNr (artAuf (.why (gNr (z.deklaration.gruende fk))) art) err with
    | none => simp only [hτ, hx, hue, List.cons_append, List.nil_append, List.append_assoc, Option.bind_eq_bind,
Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some q =>
    obtain ⟨eu, er⟩ := q
    cases hur : uOfEnd z V gNr (artAuf a art) rest with
    | none => simp only [hτ, hx, hue, List.cons_append, List.nil_append, List.append_assoc, Option.bind_eq_bind,
Option.bind_some, hur, Option.bind_none, reduceCtorEq] at hu
    | some q =>
    obtain ⟨us2, r2⟩ := q
    simp only [hτ, hx, hue, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    simp only [Endblock.bindCallElse.sizeOf_spec, Bool.sizeOf_eq_one, sizeOf_default, add_zero] at hn hf
    obtain ⟨k, hfk, hKP⟩ := hK fk
    have hR := ruf_ok H tabs fk k hfk hKP hp.hh args as xs ha hx
    have hN : nach z.deklaration fk Λ = Λ := nach_ohne_marken hM _ Λ
    have hgr : z.deklaration.gruende fk ≠ 0 := by omega
    obtain ⟨ty, hmeta, hv⟩ : ∃ ty, ScalarMeta a ty ∧ uWertArt k = some (a, ty) := by
      cases τ with
      | bool => simp only [artErg, Option.some.injEq] at hτ; subst hτ; exact ⟨.bool, trivial, by simp only [uWertArt, hKP.resTy, hKP.ergBool he, ↓reduceIte]⟩
      | int lo hi =>
        simp only [artErg, Option.some.injEq] at hτ; subst hτ
        obtain ⟨h1, h2⟩ := hKP.ergInt lo hi he
        exact ⟨.int lo hi, trivial, by simp only [uWertArt, hKP.resTy, h1, Bool.false_eq_true, ↓reduceIte, h2]⟩
      | _ => simp only [artErg, reduceCtorEq] at hτ
    have HE : SInv z V (ctxMit ctx (nVar Γ.length) (.why (gNr (z.deklaration.gruende fk)))
        (.why (z.deklaration.gruende fk)) 0 [] ctx.loops) (.why (z.deklaration.gruende fk) :: Γ)
        (nach z.deklaration fk Λ) (artAuf (.why (gNr (z.deklaration.gruende fk))) art) := by
      rw [hN]; exact H.push _ _ _ 0 [] ctx.loops rfl trivial
    obtain ⟨cEB, hEB, hende1, v, hen⟩ := ihE err _ _ f' es ende eu er (by omega) (by omega) HE hde hue
    have H' : SInv z V (ctxMit ctx (nVar Γ.length) a ty 0 [] ctx.loops) (τ :: Γ) (nach z.deklaration fk Λ)
        (artAuf a art) := by rw [hN]; exact H.push τ a ty 0 [] ctx.loops rfl hmeta
    obtain ⟨cE, hrest, hende, hv2⟩ := ihE rest _ _ f' rs en' us2 r2 (by omega) (by omega) H' hr' hur
    have hes : uEndeStmt cEB ende = .ok [.ret er] := by subst hen; simp only [uEndeStmt, hende1]
    have := reihe_bindElse tabs koepfe f' ctx _ _ _ as es ende rs k xs _ _ a ty eu cEB _ us2 cE hR
      (hKP.kanal hgr) hKP.ext hv (by rw [mitLokal_eq ctx H.muts]; exact hEB) hes
      (by rw [mitLokal_eq ctx H.muts]; exact hrest)
    exact ⟨cE, by simpa using this, hende, hv2⟩
  | _ => simp only [uOfEnd, reduceCtorEq] at hu

end Gabbro.Grammatik.Gen.Text
