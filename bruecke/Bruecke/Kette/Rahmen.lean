module
public import Bruecke.Kette.RahmenBlock
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {C : Fin u.fns.length → Prop}

theorem statisch_G (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρB : Gabbro.Body.Env) (r : URet) :
    ∀ (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
      (b0 : Endblock (declOf u) (verOf u c) false Γ Λ) (bs : List Gabbro.Body.Stmt),
      Γ = fn.params.map (·.2) → Sicht u fT fn → (∀ st ∈ ss, st ∈ (fnAt u c).body) →
      lowBodyF u c Γ fn n Λ ss r = .ok b0 → stmtsBodyZ u k fT ns ss r = some bs →
      (∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
        Gabbro.Body.Frame ρB cname (writesU gf)) →
      Statisch ρB (writesU (fnAt u c)) bs
  | 0, k, ss, Γ, fn, fT, ns, Λ, b0, bs, hΓ, hS, hmem, hlow, hbs, hF => by
      simp only [lowBodyF] at hlow <;> cases hlow
  | n + 1, 0, ss, Γ, fn, fT, ns, Λ, b0, bs, hΓ, hS, hmem, hlow, hbs, hF => by
      exact absurd hbs (by simp only [stmtsBodyZ, reduceCtorEq, not_false_eq_true])
  | n + 1, k + 1, [], Γ, fn, fT, ns, Λ, b0, bs, hΓ, hS, hmem, hlow, hbs, hF => by
      simp only [stmtsBodyZ] at hbs
      exact statisch_rets bs (namedEnd_rets (fn := fT) (r := r) hbs)
  | n + 1, k + 1, s0 :: ss, Γ, fn, fT, ns, Λ, b0, bs, hΓ, hS, hmem, hlow, hbs, hF => by
      have hmemss : ∀ st ∈ ss, st ∈ (fnAt u c).body :=
        fun st hm => hmem st (List.mem_cons_of_mem _ hm)
      have hhead : s0 ∈ (fnAt u c).body := hmem s0 (List.mem_cons_self ..)
      have hFss : ∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
          Gabbro.Body.Frame ρB cname (writesU gf) :=
        fun cn gf hgf ⟨args, hm⟩ => hF cn gf hgf ⟨args, List.mem_cons_of_mem _ hm⟩
      cases s0
      case bind x d v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bind hstep0
        obtain ⟨ls, rest, hls, hrest, rfl⟩ := lowBodyF_bind_ok c hlow
        exact .bindName _ _ _ (statisch_G S c hc ρB r n k ss (fn.mitBindung x ls.range)
          (fT.mitBindung x (0, 0)) (ns.push x) rest bs'
          (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
          (hS.bind x (0, 0) ls.range) hmemss hrest hbs' hFss)
      case bindMut x lo hi v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨eT, heT, rfl, rfl, rfl⟩ := schrittB_bindMut hstep0
        obtain ⟨ev, rest, hev, hrest, rfl⟩ := lowBodyF_bindMut_ok c hlow
        exact .bindName _ _ _ (statisch_G S c hc ρB r n k ss (fn.mitBindung x (lo, hi))
          (fT.mitBindung x (lo, hi)) (ns.push x) rest bs'
          (by rw [mitBindung_ctx]; exact congrArg (List.cons _) hΓ)
          (hS.bind x (lo, hi) (lo, hi)) hmemss hrest hbs' hFss)
      case setVar x v =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨-, id, eT, -, -, rfl, rfl, rfl⟩ := schrittB_setVar hstep0
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r (.setVar x v) ss trivial hlow
        exact .bindName _ _ _ (statisch_G S c hc ρB r n k ss fn _ _ rest bs' hΓ hS hmemss hrest hbs' hFss)
      case assign | assignTab | assignGlob | call =>
        obtain ⟨bB, fT', ns', bs', hstep0, hbs', rfl⟩ :=
          stmtsBodyZ_schritt_some hbs (by exact True.intro)
        obtain ⟨hstepN, rfl, rfl⟩ := schrittB_einzeln_sicht hS hstep0 (by exact True.intro)
        obtain ⟨hx, -, -⟩ := schrittB_stmt hstepN (fun _ _ _ h => by cases h)
          (fun _ _ _ _ h => by cases h) (fun _ _ h => by cases h)
        obtain ⟨Λ', gst, rest, hgst, hrest, rfl⟩ :=
          lowBodyF_cons_ok c r _ ss (by exact True.intro) hlow
        exact statisch_schritt_G S c hc ρB hΓ _ ss hhead hgst hx hF
          (statisch_G S c hc ρB r n k ss fn _ _ rest bs' hΓ hS hmemss hrest hbs' hFss)
      case ifBeg cnd =>
        obtain ⟨ce, tt, te, r1, r2, bs', used1, used2, hce, hTZ, hEZ, hbs', rfl⟩ := stmtsBodyZ_ifBeg_some hbs
        obtain ⟨Λ₁, st, rest', e, hst, hrest, rfl⟩ := lowBodyF_ifBeg_ok hlow
        obtain ⟨m, hm⟩ : ∃ m, blockFuel = m + 1 := ⟨99999, rfl⟩
        rw [hm] at hst
        obtain ⟨cv, tb, eb, rest1, hcv, hT, hE, rfl⟩ := lowStruct_ite_ok hst
        obtain ⟨hr1, hsuf1, hSt⟩ := statischSeq_G S c hc ρB m k ss fn _ ns ⟨Λ₁, tb⟩ (.ifElse :: rest1)
          tt (.ifElse :: r1) used1 hΓ hS hmemss hT hTZ hFss
        have h1 : r1 = rest1 := (List.cons.inj hr1).2
        rw [h1] at hEZ
        have hsuf1' : rest1 <:+ ss := (List.suffix_cons _ _).trans hsuf1
        obtain ⟨hr2, hsuf2, hSe⟩ := statischSeq_G S c hc ρB m k rest1 fn _ (ns.resume used1) ⟨Λ₁, eb⟩
          (.blkEnd :: rest') te (.blkEnd :: r2) used2 hΓ hS (fun st hm => hmemss st (mem_of_suffix hsuf1' hm)) hE hEZ
          (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, mem_of_suffix hsuf1' hm⟩)
        have h2 : r2 = rest' := (List.cons.inj hr2).2
        rw [h2] at hbs'
        have hsuf2' : rest' <:+ ss := ((List.suffix_cons _ _).trans hsuf2).trans hsuf1'
        exact .ite _ _ _ _ hSt hSe (statisch_G S c hc ρB r n k rest' fn _ (ns.resume used2) e bs' hΓ hS (fun st hm => hmemss st (mem_of_suffix hsuf2' hm)) hrest hbs'
          (fun cn gf hgf ⟨args, hm⟩ => hFss cn gf hgf ⟨args, mem_of_suffix hsuf2' hm⟩))
      all_goals exact absurd hbs (by simp only [stmtsBodyZ, schrittB, namedStmt, stmtBody, Option.bind_none, Option.map_none, reduceCtorEq, not_false_eq_true])

theorem exec_rahmen_G (S : Getragen u C) (c : Fin u.fns.length) (hc : C c) (ρB : Gabbro.Body.Env) (r : URet)
    (n k : Nat) (ss : List UStmt) {Γ : Ctx} (fn fT : UFn) (ns : BodyNames) {Λ : List (Res (declOf u))}
    (b0 : Endblock (declOf u) (verOf u c) false Γ Λ) (bs : List Gabbro.Body.Stmt)
    (hΓ : Γ = fn.params.map (·.2)) (hS : Sicht u fT fn)
    (hmem : ∀ st ∈ ss, st ∈ (fnAt u c).body)
    (hlow : lowBodyF u c Γ fn n Λ ss r = .ok b0) (hbs : stmtsBodyZ u k fT ns ss r = some bs)
    (hF : ∀ cname gf, fnSuch u cname = some gf → (∃ args, UStmt.call cname args ∈ ss) →
      Gabbro.Body.Frame ρB cname (writesU gf)) :
    ∀ t s', Gabbro.Body.finalState (Gabbro.Body.exec ρB bs t) = some s' →
      ∀ p, p.carrier ∉ (writesU (fnAt u c)) → s'.world p = t.world p :=
  exec_statisch (statisch_G S c hc ρB r n k ss fn _ ns b0 bs hΓ hS hmem hlow hbs hF)

end Gabbro.Bruecke
