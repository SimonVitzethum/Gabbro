module

public import Grammatik.Gen.Text.Invers.Geraet
public import Grammatik.Gen.Text.Invers.Rumpf_satzFaelle.Teil1

@[expose] public section

namespace Gabbro.Grammatik.Gen.Text
open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze

set_option maxHeartbeats 4000000 in
theorem rumpf_satz_block : ∀ {z : Spez} {V : Vertrag z.deklaration}
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
                ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res z.deklaration)} (b : Block z.deklaration V l Γ Λ Λ')
                  (ctx : UCtx) (art : ℕ → UParamArt) (f : ℕ) (ss : List SAnw) (us : List UStmt),
                  sizeOf b < n + 1 →
                    sizeOf b < f →
                      SInv z V ctx Γ Λ art →
                        delabB z V b = Except.ok ss →
                          uOfBl z V gNr art b = some us →
                            Λ' = Λ ∧ ∃ cE, uAnwReihe tabs koepfe f ctx ss = Except.ok (us, cE) := by
  intro z V gNr tabs koepfe hM hK hI n ihS ihB ihE
  intro l Γ Λ Λ' b ctx art f ss us hn hf H hd hu
  cases b with
  | nil =>
    simp only [delabB, Except.ok.injEq] at hd; subst hd
    simp only [uOfBl, Option.some.injEq] at hu; subst hu
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    exact ⟨rfl, ctx, reihe_nil tabs koepfe f' ctx⟩
  | cons s rest =>
    simp only [delabB] at hd
    cases hs : delabS z V s with
    | error _ => simp only [bind, Except.bind, hs, reduceCtorEq] at hd
    | ok ss1 =>
    cases hr : delabB z V rest with
    | error _ => simp only [bind, Except.bind, hs, hr, reduceCtorEq] at hd
    | ok ss2 =>
    simp only [hs, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfBl] at hu
    cases hus : uOfSt z V gNr art s with
    | none => simp only [hus, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some us1 =>
    cases hur : uOfBl z V gNr art rest with
    | none => simp only [hus, hur, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some us2 =>
    simp only [hus, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    simp only [Block.cons.sizeOf_spec, Bool.sizeOf_eq_one, Nat.reduceAdd] at hn hf
    obtain ⟨hΛ, hlen, ctx', H', hstep⟩ := ihS s ctx art ss1 us1 (by omega) H hs hus
    subst hΛ
    obtain ⟨g, rfl⟩ : ∃ g, f = g + ss1.length := ⟨f - ss1.length, by omega⟩
    obtain ⟨hΛ2, cE, hrest⟩ := ihB rest ctx' art g ss2 us2 (by omega) (by omega) H' hr hur
    exact ⟨hΛ2, cE, hstep g ss2 us2 cE (by omega) hrest⟩
  | bind e rest =>
    rename_i τ
    simp only [delabB] at hd
    cases he : delabE z none e with
    | error _ => simp only [bind, Except.bind, he, reduceCtorEq] at hd
    | ok se =>
    cases hr : delabB z V rest with
    | error _ => simp only [bind, Except.bind, he, hr, reduceCtorEq] at hd
    | ok ss2 =>
    simp only [he, hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [Block.bind.sizeOf_spec, Bool.sizeOf_eq_one] at hn hf
    simp only [uOfBl] at hu
    split at hu
    · cases hb : uOfB z art none e with
      | none => simp only [hb, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
      | some b =>
      cases hur : uOfBl z V gNr (artAuf .bool art) rest with
      | none => simp only [hb, hur, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
      | some us2 =>
      simp only [hb, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
      subst hu
      have H' := H.push τ .bool .bool 0 [] ctx.loops rfl trivial
      obtain ⟨hΛ2, cE, hrest⟩ := ihB rest _ _ f' ss2 us2 (by omega) (by omega) H' hr hur
      exact ⟨hΛ2, cE, reihe_bind tabs koepfe f' ctx _ _ se ss2 _ us2 cE
        (bindWert_bool H tabs koepfe e se b he hb) hrest⟩
    · cases hb : uOfS z art none e with
      | none => simp only [hb, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
      | some b =>
      cases hur : uOfBl z V gNr (artAuf .int art) rest with
      | none => simp only [hb, hur, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
      | some us2 =>
      simp only [hb, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
      subst hu
      have H' := H.push τ .int (.int 0 0) 0 [] ctx.loops rfl trivial
      obtain ⟨hΛ2, cE, hrest⟩ := ihB rest _ _ f' ss2 us2 (by omega) (by omega) H' hr hur
      exact ⟨hΛ2, cE, reihe_bind tabs koepfe f' ctx _ _ se ss2 _ us2 cE
        (bindWert_int H tabs koepfe e se b he hb) hrest⟩
  | bindCall fk args he hp hr rest =>
    rename_i τ
    simp only [delabB] at hd
    cases ha : delabA z args with
    | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
    | ok as =>
    cases hr' : delabB z V rest with
    | error _ => simp only [bind, Except.bind, ha, hr', reduceCtorEq] at hd
    | ok ss2 =>
    simp only [ha, hr', bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfBl] at hu
    cases hτ : artErg τ with
    | none => simp only [hτ, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some a =>
    cases hx : uOfArgs z art args with
    | none => simp only [hτ, hx, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none, reduceCtorEq] at hu
    | some xs =>
    cases hur : uOfBl z V gNr (artAuf a art) rest with
    | none => simp only [hτ, hx, Option.bind_eq_bind, Option.bind_some, hur, Option.bind_none, reduceCtorEq] at hu
    | some us2 =>
    simp only [hτ, hx, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [Block.bindCall.sizeOf_spec, Bool.sizeOf_eq_one, sizeOf_default, add_zero] at hn hf
    obtain ⟨k, hfk, hKP⟩ := hK fk
    obtain ⟨ty, hmeta, hb⟩ := bindWert_call H tabs fk k hfk hKP hp.hh hr τ he a hτ args as xs ha hx (nVar Γ.length)
    have hN : nach z.deklaration fk Λ = Λ := nach_ohne_marken hM _ Λ
    have H' : SInv z V (ctxMit ctx (nVar Γ.length) a ty 0 [] ctx.loops) (τ :: Γ) (nach z.deklaration fk Λ)
        (artAuf a art) := by rw [hN]; exact H.push τ a ty 0 [] ctx.loops rfl hmeta
    obtain ⟨hΛ, cE, hrest⟩ := ihB rest _ _ f' ss2 us2 (by omega) (by omega) H' hr' hur
    exact ⟨hΛ.trans hN, cE, reihe_bind tabs koepfe f' ctx _ _ _ ss2 _ us2 cE hb hrest⟩
  | bindCallInd p args he hp hr rest =>
    rename_i τ
    simp only [uOfBl] at hu
    cases hτ : artErg τ with
    | none => simp only [hτ, List.cons_append, List.nil_append, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some a =>
    cases hx : uOfArgs z art args with
    | none => simp only [hτ, hx, List.cons_append, List.nil_append, Option.bind_eq_bind, Option.bind_none,
Option.bind_fun_none, reduceCtorEq] at hu
    | some xs =>
    cases hur : uOfBl z V gNr (artAuf a art) rest with
    | none => simp only [hτ, hx, List.cons_append, List.nil_append, Option.bind_eq_bind, Option.bind_some, hur,
Option.bind_none, reduceCtorEq] at hu
    | some us2 =>
    simp only [hτ, hx, hur, Option.bind_eq_bind, Option.bind_some] at hu
    split at hu
    · rename_i fk _
      split at hu
      · rename_i hn
        subst hn
        simp only [Option.some.injEq] at hu
        subst hu
        simp only [delabB] at hd
        cases ha : delabA z args with
        | error _ => simp only [bind, Except.bind, ha, reduceCtorEq] at hd
        | ok as =>
        cases hr' : delabB z V rest with
        | error _ => simp only [bind, Except.bind, ha, hr', reduceCtorEq] at hd
        | ok ss2 =>
        simp only [ha, hr', bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
        subst hd
        obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by simp at hf; omega⟩
        simp only [Block.bindCallInd.sizeOf_spec, sizeOf_nat, Bool.sizeOf_eq_one, Expr.fnref.sizeOf_spec,
sizeOf_default, add_zero] at hn hf
        obtain ⟨k, hfk, hKP⟩ := hK fk
        obtain ⟨i, hi, hk⟩ := kinv_idx (gNr := gNr) hfk
        have hiE : i = z.deklaration.sig fk := by rw [hI fk] at hi; exact (Option.some.inj hi).symm
        subst hiE
        obtain ⟨ty, hmeta, hb⟩ := bindWert_callInd H tabs fk k _ hfk hk hKP hp.hh hr τ he a hτ args as xs ha hx (H.zb fk) Γ.length
          ctx.loops (nVar Γ.length)
        have hN : nachSig z.deklaration (z.deklaration.sigNr (z.deklaration.sig fk)) Λ = Λ := nach_ohne_marken hM _ Λ
        have H' : SInv z V (ctxMit (ctxMit ctx (nZeiger Γ.length) (.fnptr (z.deklaration.sig fk)) (.fnptr (z.deklaration.sig fk)) 0 [] ctx.loops)
            (nVar Γ.length) a ty 0 [] ctx.loops) (τ :: Γ)
            (nachSig z.deklaration (z.deklaration.sigNr (z.deklaration.sig fk)) Λ) (artAuf a art) := by
          rw [hN]; exact (H.pushZ Γ.length (.fnptr (z.deklaration.sig fk)) (.fnptr (z.deklaration.sig fk)) 0 ctx.loops).push τ a ty 0 [] ctx.loops rfl hmeta
        obtain ⟨hΛ, cE, hrest⟩ := ihB rest _ _ f' ss2 us2 (by omega) (by omega) H' hr' hur
        refine ⟨hΛ.trans hN, cE, ?_⟩
        have h2 := reihe_bind tabs koepfe f' _ _ _ _ ss2 _ us2 cE hb hrest
        have h1 := reihe_bind tabs koepfe (f' + 1) ctx _ _ _ _ _ _ cE
          (bindWert_fnref H tabs fk k _ hi hk hKP (nZeiger Γ.length)) h2
        simpa using h1
      · simp only [reduceCtorEq] at hu
    · simp only [reduceCtorEq] at hu
  | bindCallElse fk args he hp hr err rest =>
    rename_i τ
    simp only [delabB] at hd
    cases hde : delabEnd z V err with
    | error _ => simp only [bind, Except.bind, hde, reduceCtorEq] at hd
    | ok q =>
    obtain ⟨es, ende⟩ := q
    cases ha : delabA z args with
    | error _ => simp only [bind, Except.bind, hde, ha, reduceCtorEq] at hd
    | ok as =>
    cases hr' : delabB z V rest with
    | error _ => simp only [bind, Except.bind, hde, ha, hr', reduceCtorEq] at hd
    | ok ss2 =>
    simp only [hde, ha, hr', bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfBl] at hu
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
    cases hur : uOfBl z V gNr (artAuf a art) rest with
    | none => simp only [hτ, hx, hue, List.cons_append, List.nil_append, List.append_assoc, Option.bind_eq_bind,
Option.bind_some, hur, Option.bind_none, reduceCtorEq] at hu
    | some us2 =>
    simp only [hτ, hx, hue, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [Block.bindCallElse.sizeOf_spec, Bool.sizeOf_eq_one, sizeOf_default, add_zero] at hn hf
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
    obtain ⟨cEB, hEB, hende, v, hen⟩ := ihE err _ _ f' es ende eu er (by omega) (by omega) HE hde hue
    have H' : SInv z V (ctxMit ctx (nVar Γ.length) a ty 0 [] ctx.loops) (τ :: Γ) (nach z.deklaration fk Λ)
        (artAuf a art) := by rw [hN]; exact H.push τ a ty 0 [] ctx.loops rfl hmeta
    obtain ⟨hΛ, cE, hrest⟩ := ihB rest _ _ f' ss2 us2 (by omega) (by omega) H' hr' hur
    refine ⟨hΛ.trans hN, cE, ?_⟩
    have hes : uEndeStmt cEB ende = .ok [.ret er] := by subst hen; simp only [uEndeStmt, hende]
    have := reihe_bindElse tabs koepfe f' ctx _ _ _ as es ende ss2 k xs _ _ a ty eu cEB _ us2 cE hR
      (hKP.kanal hgr) hKP.ext hv (by rw [mitLokal_eq ctx H.muts]; exact hEB) hes
      (by rw [mitLokal_eq ctx H.muts]; exact hrest)
    simpa using this
  | regRead r hk rest =>
    simp only [delabB] at hd
    cases hr' : delabB z V rest with
    | error _ => simp only [bind, Except.bind, hr', reduceCtorEq] at hd
    | ok ss2 =>
    simp only [hr', bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    simp only [uOfBl] at hu
    cases hτ : artErg (z.deklaration.rtyp r) with
    | none => simp only [hτ, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some a =>
    cases hur : uOfBl z V gNr (artAuf a art) rest with
    | none => simp only [hτ, Option.bind_eq_bind, Option.bind_some, hur, Option.bind_none, reduceCtorEq] at hu
    | some us2 =>
    simp only [hτ, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [Block.regRead.sizeOf_spec, Bool.sizeOf_eq_one, Nat.reduceAdd, sizeOf_default, add_zero] at hn hf
    obtain ⟨ty, hmeta, hb⟩ := bindWert_regRead H tabs koepfe r (nVar Γ.length) a hτ
    have H' := H.push (z.deklaration.rtyp r) a ty 0 [] ctx.loops rfl hmeta
    obtain ⟨hΛ, cE, hrest⟩ := ihB rest _ _ f' ss2 us2 (by omega) (by omega) H' hr' hur
    exact ⟨hΛ, cE, reihe_bind tabs koepfe f' ctx _ _ _ ss2 _ us2 cE hb hrest⟩
  | awaits g payload hp hL hat rest =>
    subst hp
    simp only [delabB] at hd
    simp only [uOfBl] at hu
    cases hr' : delabB z V rest with
    | error _ => simp only [bind, Except.bind, hr', reduceCtorEq] at hd
    | ok ss2 =>
    simp only [hr', bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hd
    subst hd
    cases hτ : artErg (z.deklaration.gtyp g) with
    | none => simp only [hτ, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hu
    | some a =>
    cases hur : uOfBl z V gNr (artAuf a art) rest with
    | none => simp only [hτ, Option.bind_eq_bind, Option.bind_some, hur, Option.bind_none, reduceCtorEq] at hu
    | some us2 =>
    simp only [hτ, hur, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hu
    subst hu
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [Block.awaits.sizeOf_spec, Bool.sizeOf_eq_one, sizeOf_default, add_zero] at hn hf
    obtain ⟨ty, hmeta, hstep⟩ := reihe_await H tabs koepfe f' g hat (nVar Γ.length) a hτ ss2
    have H' := H.push (z.deklaration.gtyp g) a ty 0 [] ctx.loops rfl hmeta
    obtain ⟨hΛ, cE, hrest⟩ := ihB rest _ _ f' ss2 us2 (by omega) (by omega) H' hr' hur
    exact ⟨hΛ, cE, hstep us2 cE hrest⟩
  | _ => simp only [uOfBl, reduceCtorEq] at hu

end Gabbro.Grammatik.Gen.Text
